# lambda_function.py  (Python 3.13)
# Trigger: S3:ObjectCreated on B2B-Interchange 837P JSON (segments/loop style)
# Action:  Build a FHIR Transaction Bundle and write to <same-prefix>/Outgoing-FHIR/<base>.fhir.transaction.json
#          (ADDED) Optionally POST the transaction Bundle to Amazon HealthLake FHIR R4.
#
# Env (optional):
#   LOG_LEVEL=INFO|DEBUG
#   OUTPUT_BUCKET=<bucket>   (default: same as source)
#   ERROR_PREFIX=FAILED/     (default: FAILED/)
#   HL_R4_ENDPOINT=https://healthlake.../datastore/.../r4
#   POST_TO_HEALTHLAKE=true|false  (default: false)

import json
import os
import gzip
import uuid
import hashlib
import logging
from urllib.parse import unquote_plus
from datetime import datetime, timezone

import boto3

# --------- ADDED: HealthLake signing deps ----------
import urllib3
from botocore.session import Session
from botocore.auth import SigV4Auth
from botocore.awsrequest import AWSRequest
# ---------------------------------------------------

# ---------- One-time init ----------
s3  = boto3.client("s3")
log = logging.getLogger()
log.setLevel(os.getenv("LOG_LEVEL", "INFO"))

OUTPUT_BUCKET = os.getenv("OUTPUT_BUCKET")            # optional override
ERROR_PREFIX  = os.getenv("ERROR_PREFIX", "FAILED/")  # error marker prefix

# --------- ADDED: HealthLake one-time init ----------
HL_R4_ENDPOINT       = os.getenv("HL_R4_ENDPOINT", "").rstrip("/")
POST_TO_HEALTHLAKE   = os.getenv("POST_TO_HEALTHLAKE", "false").lower() == "true"

_http    = urllib3.PoolManager()
_session = Session()
_region  = os.getenv("AWS_REGION") or _session.get_config_variable("region")
_creds   = _session.get_credentials().get_frozen_credentials() if _session.get_credentials() else None
# ----------------------------------------------------
# --- add near other env vars ---
SECONDARY_S3_URI = os.getenv("SECONDARY_S3_URI")  # e.g. s3://medi-sagemaker-fraud-detection/data/train/Incoming-837-JSON-FHIR/

# --- add these small helpers somewhere with your other utils ---
def parse_s3_uri(uri: str):
    """
    Accepts s3://bucket/prefix[/]
    Returns (bucket, normalized_prefix_with_trailing_slash)
    """
    if not uri or not uri.startswith("s3://"):
        raise ValueError(f"SECONDARY_S3_URI must start with 's3://', got: {uri}")
    no_scheme = uri[len("s3://"):]
    parts = no_scheme.split("/", 1)
    bucket = parts[0]
    prefix = "" if len(parts) == 1 else parts[1]
    if prefix and not prefix.endswith("/"):
        prefix += "/"
    return bucket, prefix

# ---------- Utility helpers ----------
def new_uuid(seed: str) -> str:
    # Deterministic UUID from a seed so references are stable across runs
    h = hashlib.sha1(seed.encode()).hexdigest()
    return str(uuid.UUID(h[:32]))

def urn(u: str) -> str:
    return f"urn:uuid:{u}"

def cc(system, code, display=None):
    c = {"coding":[{"system":system, "code":code}]}
    if display:
        c["coding"][0]["display"] = display
    return c

def ref_urn(u: str):
    return {"reference": urn(u)}

def name_from_nm1(last, first=None):
    n = {"family": last}
    if first:
        n["given"] = [first]
    return [n]

def addr(line, city, state, postal):
    return [{"line":[line], "city":city, "state":state, "postalCode":postal}]

def gender_map(g):
    return {"M":"male","F":"female"}.get(g, "unknown")

def first(lst, predicate):
    if isinstance(lst, list):
        for x in lst:
            if predicate(x):
                return x
    return None

def get_loops(container, loop_key):
    if not isinstance(container, list):
        return []
    return [s[loop_key] for s in container if isinstance(s, dict) and loop_key in s]

def get(seg, key, default=None):
    if isinstance(seg, dict):
        return seg.get(key, default)
    return default

def clean(d):
    # recursively drop None and empty lists/dicts
    if isinstance(d, dict):
        out = {}
        for k, v in d.items():
            cv = clean(v)
            if cv is not None and cv != [] and cv != {}:
                out[k] = cv
        return out
    if isinstance(d, list):
        out = [clean(v) for v in d if v is not None]
        return [v for v in out if v != {} and v != []]
    return d

def yyyymmdd_to_yyyy_mm_dd(s):
    if isinstance(s, str) and len(s) == 8 and s.isdigit():
        return f"{s[0:4]}-{s[4:6]}-{s[6:8]}"
    return s

def first_value_for_key(obj, key):
    """Depth-first search to find the first value for 'key' in a nested structure."""
    if isinstance(obj, dict):
        if key in obj:
            return obj[key]
        for v in obj.values():
            found = first_value_for_key(v, key)
            if found is not None:
                return found
    elif isinstance(obj, list):
        for it in obj:
            found = first_value_for_key(it, key)
            if found is not None:
                return found
    return None

# ---------- Core mapping ----------
def map_837p_to_transaction_bundle(x12_json):
    # Conservative assumption (common in your samples): take the first TX
    tr = x12_json["interchanges"][0]["functional_groups"][0]["transactions"][0]
    segments = tr["segments"]
    bundle = {"resourceType":"Bundle", "type":"transaction", "entry":[]}
    made = set()  # avoid duplicates

    # Optional: derive a 'created' date from BHT_04 anywhere in the TX
    bht_date_raw = first_value_for_key(tr, "BHT_04") or first_value_for_key(segments, "BHT_04")
    default_created = yyyymmdd_to_yyyy_mm_dd(bht_date_raw) if bht_date_raw else datetime.now(timezone.utc).strftime("%Y-%m-%d")

    # 2000A Billing Provider loop
    for hl2000a in get_loops(segments, "HL-2000A_loop"):
        # 2010AA Billing Provider -> Organization
        org_id = None
        nm1aa_wrap = first(hl2000a, lambda n: "NM1-2010AA_loop" in n)
        if nm1aa_wrap:
            aa = nm1aa_wrap["NM1-2010AA_loop"]
            nm1 = first(aa, lambda s: get(s,"NM1_01")=="85")
            n3  = first(aa, lambda s: "N3_01" in s)
            n4  = first(aa, lambda s: "N4_01" in s)
            ref_ei = first(aa, lambda s: get(s,"REF_01")=="EI")
            npi = get(nm1,"NM1_09") if nm1 else None
            org_name = get(nm1,"NM1_03") if nm1 else None
            seed = (org_name or "") + (npi or "no-npi")
            org_id = new_uuid("org-"+seed)
            org = {
                "resourceType":"Organization", "id": org_id, "name": org_name,
                "identifier":[]
            }
            if npi:
                org["identifier"].append({"system":"http://hl7.org/fhir/sid/us-npi","value":npi})
            if ref_ei:
                org["identifier"].append({"system":"urn:oid:2.16.840.1.113883.4.2","value":get(ref_ei,"REF_02")})
            if n3 and n4:
                org["address"] = addr(get(n3,"N3_01"), get(n4,"N4_01"), get(n4,"N4_02"), get(n4,"N4_03"))
            org = clean(org)
            if org_id not in made and any(org.values()):
                bundle["entry"].append({"fullUrl": urn(org_id), "resource": org,
                                        "request":{"method":"POST","url":"Organization"}})
                made.add(org_id)

        # 2000B Subscriber/Patient loop(s)
        for hl2000b in get_loops(hl2000a, "HL-2000B_loop"):
            # Patient (2010BA)
            patient_id = None; member_id=None; patient_ref=None
            ba_wrap = first(hl2000b, lambda s: "NM1-2010BA_loop" in s)
            if ba_wrap:
                ba = ba_wrap["NM1-2010BA_loop"]
                nm1 = first(ba, lambda s: get(s,"NM1_01")=="IL")
                n3  = first(ba, lambda s: "N3_01" in s)
                n4  = first(ba, lambda s: "N4_01" in s)
                dmg = first(ba, lambda s: "DMG_01" in s)
                last  = get(nm1,"NM1_03") if nm1 else None
                first_ = get(nm1,"NM1_04") if nm1 else None
                member_id = get(nm1,"NM1_09") if nm1 else None
                gender = gender_map(get(dmg,"DMG_03")) if dmg else "unknown"
                birth  = yyyymmdd_to_yyyy_mm_dd(get(dmg,"DMG_02")) if dmg else None

                patient_id = new_uuid("pat-"+(last or "")+(first_ or "")+(member_id or ""))
                patient = {"resourceType":"Patient","id":patient_id}
                if last: patient["name"] = name_from_nm1(last, first_)
                if birth: patient["birthDate"] = birth
                if gender: patient["gender"] = gender
                if n3 and n4: patient["address"] = addr(get(n3,"N3_01"), get(n4,"N4_01"), get(n4,"N4_02"), get(n4,"N4_03"))
                if member_id:
                    patient["identifier"]=[{"system":"http://example.org/member-id","value":member_id}]
                patient = clean(patient)
                if patient_id not in made and any(patient.values()):
                    bundle["entry"].append({"fullUrl": urn(patient_id), "resource": patient,
                                            "request":{"method":"POST","url":"Patient"}})
                    made.add(patient_id)
                patient_ref = ref_urn(patient_id)

            # Payer (2010BB) -> Organization
            payer_org_id=None; payer_ref=None
            bb_wrap = first(hl2000b, lambda s: "NM1-2010BB_loop" in s)
            if bb_wrap:
                bb = bb_wrap["NM1-2010BB_loop"]
                nm1 = first(bb, lambda s: get(s,"NM1_01")=="PR")
                payer_name = get(nm1,"NM1_03") if nm1 else None
                payer_code = get(nm1,"NM1_09") if nm1 else None
                payer_org_id = new_uuid("payer-"+(payer_name or "")+(payer_code or ""))
                payer = {"resourceType":"Organization","id":payer_org_id,"name": payer_name}
                if payer_code:
                    payer["identifier"]=[{"system":"http://example.org/payerid","value":payer_code}]
                payer = clean(payer)
                if payer_org_id not in made and any(payer.values()):
                    bundle["entry"].append({"fullUrl": urn(payer_org_id), "resource": payer,
                                            "request":{"method":"POST","url":"Organization"}})
                    made.add(payer_org_id)
                payer_ref = ref_urn(payer_org_id)

            # Coverage from SBR + member id
            coverage_id=None; coverage_ref=None
            sbr = first(hl2000b, lambda s: "SBR_01" in s)
            if sbr and patient_id and payer_org_id and member_id:
                coverage_id = new_uuid(f"cov-{member_id}-{payer_org_id}")
                coverage = {
                    "resourceType":"Coverage","id":coverage_id,
                    "status":"active",
                    "beneficiary": ref_urn(patient_id),
                    "payor":[ref_urn(payer_org_id)],
                    "subscriberId": member_id,
                    "type": cc("http://terminology.hl7.org/CodeSystem/coverage-type","other")
                }
                coverage = clean(coverage)
                if coverage_id not in made:
                    bundle["entry"].append({"fullUrl": urn(coverage_id), "resource": coverage,
                                            "request":{"method":"POST","url":"Coverage"}})
                    made.add(coverage_id)
                coverage_ref = ref_urn(coverage_id)

            # ---- Claims (2300) under this subscriber/patient ----
            for clm in get_loops(hl2000b, "CLM-2300_loop"):
                clm_hdr = first(clm, lambda s: "CLM_01" in s)
                if not clm_hdr:
                    continue
                clm_number = get(clm_hdr,"CLM_01")
                clm_total  = get(clm_hdr,"CLM_02")
                claim_id = new_uuid("claim-"+(clm_number or ""))

                # Claim-level date: prefer 431 (onset) else 472 (service), else default_created
                clm_dtp = first(clm, lambda s: get(s,"DTP_01") in ("431","472"))
                serviced_date_raw = get(clm_dtp,"DTP_03") if clm_dtp else None
                serviced_date = yyyymmdd_to_yyyy_mm_dd(serviced_date_raw) if serviced_date_raw else None

                # Diagnoses (HI_*) -> Claim.diagnosis[]
                hi = first(clm, lambda s: isinstance(s, dict) and any(k.startswith("HI_") for k in s.keys()))
                diagnoses = []
                seq = 0
                if hi:
                    for k,v in hi.items():
                        if not k.startswith("HI_"): 
                            continue
                        # take first *_02 as code
                        code = None
                        if isinstance(v, dict):
                            for subk, subval in v.items():
                                if subk.endswith("_02"):
                                    code = subval; break
                        if code:
                            seq += 1
                            diagnoses.append({
                                "sequence": seq,
                                "diagnosisCodeableConcept": cc("http://hl7.org/fhir/sid/icd-10-cm", code)
                            })

                # Optional Provider (2310B) -> Practitioner + PractitionerRole
                rendering_prac_ref = None
                nm1_2310b_wrap = first(clm, lambda s: "NM1-2310B_loop" in s)
                if nm1_2310b_wrap:
                    b = nm1_2310b_wrap["NM1-2310B_loop"]
                    nm1 = first(b, lambda s: get(s,"NM1_01")=="82")
                    if nm1:
                        npi = get(nm1,"NM1_09")
                        last = get(nm1,"NM1_03"); first_ = get(nm1,"NM1_04")
                        prac_id = new_uuid("prac-"+(npi or (last or "")+(first_ or "")))
                        prac = {"resourceType":"Practitioner","id": prac_id}
                        if last: prac["name"] = name_from_nm1(last, first_)
                        if npi:  prac["identifier"]=[{"system":"http://hl7.org/fhir/sid/us-npi","value":npi}]
                        prac = clean(prac)
                        if prac_id not in made:
                            bundle["entry"].append({"fullUrl": urn(prac_id), "resource": prac,
                                                    "request":{"method":"POST","url":"Practitioner"}})
                            made.add(prac_id)
                        # Link practitioner to billing org if present
                        if 'org_id' in locals() and org_id:
                            role_id = new_uuid(f"role-{prac_id}-{org_id}")
                            role = {"resourceType":"PractitionerRole","id": role_id,
                                    "practitioner": ref_urn(prac_id),
                                    "organization": ref_urn(org_id)}
                            role = clean(role)
                            if role_id not in made:
                                bundle["entry"].append({"fullUrl": urn(role_id), "resource": role,
                                                        "request":{"method":"POST","url":"PractitionerRole"}})
                                made.add(role_id)
                        rendering_prac_ref = ref_urn(prac_id)

                # Build Claim (with created date and Money total)
                claim = {
                    "resourceType":"Claim","id":claim_id,
                    "status":"active",
                    "type": cc("http://terminology.hl7.org/CodeSystem/claim-type","professional"),
                    "use":"claim",
                    "created": default_created,
                    "patient": ref_urn(patient_id) if patient_id else None,
                    "provider": ref_urn(org_id) if 'org_id' in locals() and org_id else None,
                    "insurer": payer_ref if payer_ref else None,
                    "priority": cc("http://terminology.hl7.org/CodeSystem/processpriority","normal"),
                    "identifier":[{"system":"http://example.org/claim-number","value":clm_number}],
                    "insurance":[{"sequence":1, "focal":True, "coverage": coverage_ref}] if coverage_ref else None,
                    "diagnosis": diagnoses if diagnoses else None,
                    "item": []
                }
                if serviced_date:
                    claim["billablePeriod"] = {"start": serviced_date, "end": serviced_date}
                if clm_total:
                    try:
                        claim["total"] = {"value": float(clm_total), "currency": "USD"}
                    except Exception:
                        pass

                if rendering_prac_ref:
                    claim["careTeam"] = [{
                        "sequence":1,
                        "provider": rendering_prac_ref,
                        "role": cc("http://terminology.hl7.org/CodeSystem/claimcareteamrole","primary")
                    }]

                # Service lines with diagnosis pointers
                for lx_wrap in [x for x in clm if isinstance(x, dict) and "LX-2400_loop" in x]:
                    lx = lx_wrap["LX-2400_loop"]
                    sv1 = first(lx, lambda s: "SV1_01" in s)
                    if not sv1:
                        continue
                    dtp = first(lx, lambda s: get(s,"DTP_01")=="472")
                    sv1_01 = get(sv1,"SV1_01")
                    hc = None; modifiers = []
                    if isinstance(sv1_01, dict):
                        hc = get(sv1_01,"SV1_01_02") or get(sv1_01,"SV1_01_01")
                        for i in range(3, 7):
                            m = get(sv1_01, f"SV1_01_{i}")
                            if m: modifiers.append(m)
                    price = get(sv1,"SV1_02")
                    qty   = get(sv1,"SV1_04","1")
                    pos   = get(sv1,"SV1_08")
                    line_date_raw = get(dtp,"DTP_03") if dtp else None
                    line_date = yyyymmdd_to_yyyy_mm_dd(line_date_raw) if line_date_raw else None

                    diag_ptrs = []
                    raw_ptrs = get(sv1,"SV1_07")
                    if raw_ptrs:
                        if isinstance(raw_ptrs, str):
                            diag_ptrs = [int(p) for p in str(raw_ptrs).split(":") if p.isdigit()]
                        elif isinstance(raw_ptrs, dict):
                            for k,v in raw_ptrs.items():
                                if k.startswith("SV1_07_") and str(v).isdigit():
                                    diag_ptrs.append(int(v))
                        elif isinstance(raw_ptrs, list):
                            diag_ptrs = [int(x) for x in raw_ptrs if str(x).isdigit()]

                    item = {
                        "sequence": len(claim["item"])+1,
                        "productOrService": cc("http://www.ama-assn.org/go/cpt", hc) if hc else None,
                        "modifier": [cc("http://www.ama-assn.org/go/cpt", m) for m in modifiers] if modifiers else None,
                        "unitPrice": {"value": float(price)} if price else None,
                        "quantity": {"value": float(qty)} if qty else None,
                        "locationCodeableConcept": cc("http://terminology.hl7.org/CodeSystem/ex-serviceplace", pos) if pos else None,
                        "diagnosisSequence": diag_ptrs if diag_ptrs else None
                    }
                    if line_date:
                        item["servicedDate"] = line_date

                    claim["item"].append(clean(item))

                claim = clean(claim)
                if claim_id not in made:
                    bundle["entry"].append({"fullUrl": urn(claim_id), "resource": claim,
                                            "request":{"method":"POST","url":"Claim"}})
                    made.add(claim_id)

    return bundle

# ---------- S3 helpers ----------
def get_json_from_s3(bucket: str, key: str) -> dict:
    obj = s3.get_object(Bucket=bucket, Key=key)
    body = obj["Body"].read()
    if key.endswith(".gz"):
        body = gzip.decompress(body)
    return json.loads(body.decode("utf-8"))

def put_json_to_s3(bucket: str, key: str, payload: dict, content_type="application/fhir+json"):
    data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    s3.put_object(Bucket=bucket, Key=key, Body=data, ContentType=content_type)

def build_out_key(src_key: str) -> str:
    # <prefix>/Outgoing-FHIR/<base>.fhir.transaction.json
    src_dir = os.path.dirname(src_key)
    base_no_ext = os.path.splitext(os.path.basename(src_key))[0]
    return f"{src_dir}/Outgoing-FHIR/{base_no_ext}.fhir.transaction.json"

# ---------- ADDED: HealthLake helpers ----------
def _signed_post_healthlake(url: str, payload: dict) -> tuple[int, bytes]:
    """SigV4-signed POST to HealthLake FHIR endpoint."""
    if not _creds or not _region:
        raise RuntimeError("AWS credentials or region not resolved in Lambda environment.")
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    headers = {"Content-Type": "application/fhir+json"}
    req = AWSRequest(method="POST", url=url, data=body, headers=headers)
    SigV4Auth(_creds, "healthlake", _region).add_auth(req)
    signed_headers = {k: str(v) for k, v in req.headers.items()}
    resp = _http.request("POST", url, body=body, headers=signed_headers)
    return resp.status, resp.data

def post_bundle_to_healthlake(bundle: dict) -> dict:
    """
    POST the transaction Bundle to the datastore base ([...]/r4).
    """
    if not HL_R4_ENDPOINT:
        raise RuntimeError("HL_R4_ENDPOINT env var is not set.")
    url = HL_R4_ENDPOINT  # POST transaction to the base
    status, data = _signed_post_healthlake(url, bundle)
    text = (data or b"").decode("utf-8", "replace")
    if 200 <= status < 300:
        log.info(f"HealthLake POST OK (HTTP {status})")
        try:
            return json.loads(text)
        except Exception:
            return {"status": status, "raw": text}
    else:
        log.error(f"HealthLake POST failed (HTTP {status}): {text[:500]}")
        raise RuntimeError(f"HealthLake POST failed (HTTP {status})")
# ---------------------------------------------------

# ---------- Lambda handler ----------
def lambda_handler(event, context):
    results = []

    for rec in event.get("Records", []):
        bucket = rec["s3"]["bucket"]["name"]
        key    = unquote_plus(rec["s3"]["object"]["key"])

        # Skip our own outputs to avoid loops
        if "/Outgoing-FHIR/" in key or key.endswith(".fhir.transaction.json"):
            log.info(f"Skip self output: {key}")
            continue

        try:
            x12_json = get_json_from_s3(bucket, key)
            bundle   = map_837p_to_transaction_bundle(x12_json)

            # Primary write (current behavior)
            out_bucket = OUTPUT_BUCKET or bucket
            out_key    = build_out_key(key)
            put_json_to_s3(out_bucket, out_key, bundle)
            log.info(f"Wrote {len(bundle.get('entry', []))} resources to s3://{out_bucket}/{out_key}")

            # --------- ADDED: optional copy to SageMaker bucket/prefix ---------
            copy2_uri = None
            copy2_err = None
            if SECONDARY_S3_URI:
                try:
                    sbucket, sprefix = parse_s3_uri(SECONDARY_S3_URI)
                    # reuse file name so sets align
                    second_key = f"{sprefix}{os.path.basename(out_key)}"
                    put_json_to_s3(sbucket, second_key, bundle)
                    copy2_uri = f"s3://{sbucket}/{second_key}"
                    log.info(f"Also wrote copy to {copy2_uri}")
                except Exception as ce:
                    copy2_err = str(ce)
                    log.exception(f"Failed secondary write to {SECONDARY_S3_URI}: {ce}")
            # -------------------------------------------------------------------

            # Optional POST to HealthLake (unchanged)
            hl_status = "skipped"
            if POST_TO_HEALTHLAKE and HL_R4_ENDPOINT:
                post_bundle_to_healthlake(bundle)
                hl_status = "posted"

            result = {
                "source": f"s3://{bucket}/{key}",
                "output": f"s3://{out_bucket}/{out_key}",
                "count": len(bundle.get("entry", [])),
                "healthlake": hl_status
            }
            if copy2_uri:  result["copy2"] = copy2_uri
            if copy2_err:  result["copy2_error"] = copy2_err
            results.append(result)

        except Exception as e:
            log.exception(f"Failed processing s3://{bucket}/{key}")
            # Optional small error marker for quick triage
            err_key = f"{os.path.dirname(key)}/{ERROR_PREFIX}{os.path.basename(key)}.txt"
            s3.put_object(Bucket=OUTPUT_BUCKET or bucket, Key=err_key,
                          Body=str(e).encode("utf-8"), ContentType="text/plain")

    return {"ok": True, "outputs": results}
