import os
import json
import time
import argparse
from datetime import datetime
from typing import Dict, Any, List, Tuple, Iterable

# Optional .env
try:
    from dotenv import load_dotenv
    load_dotenv()
except Exception:
    pass

# SDKs
import anthropic
# Gemini Batch API uses the "google-genai" client (pip install google-genai)
from google import genai
from google.genai import types as genai_types  # for UploadFileConfig, etc.

# Configuration
DATASET_ROOT = os.environ.get("DATASET_ROOT", "dataset")
CURRENT_VERSION = os.environ.get("DATASET_VERSION", "version_1")

# Models (match your llm_judge.py defaults where possible)
CLAUDE_MODEL = "claude-sonnet-4-5"
GEMINI_MODEL = "models/gemini-2.5-pro"

ANTHROPIC_API_KEY = os.environ.get("ANTHROPIC_API_KEY")
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY")

# Output locations for batch IO artifacts
BATCH_DIR = os.path.join(DATASET_ROOT, CURRENT_VERSION, "metadata", "judging_batches")
os.makedirs(BATCH_DIR, exist_ok=True)

# Aggregation defaults (same as llm_judge.py)
BASE_WEIGHTS = {"claude": 0.55, "gemini": 0.45}
CONFIDENCE_ALPHA = 0.3

PROMPT_TEMPLATE = """You are an expert hardware verification reviewer.

Judge ONLY the SystemVerilog Assertions (SVA) quality for the given Verilog module.
- Ignore and do not score any testbench/harness/driver/monitor/scoreboard/stimulus/coverage groups, or non-SVA code. Treat them as context only.
- Evaluate the SVA content itself: assert/assume/cover statements, property/endproperty, sequence/endsequence, and any bind usage.
- Do not award or deduct points for testbench completeness, stimulus, or DUT implementation details.

Scoring rubric (each in [0,1], SVA-only):
- temporal_correctness (0.35): Are the SVA cause→effect relationships, timing/ordering, handshakes, and mutual exclusion specified correctly?
- signal_coverage (0.25): Do the SVA meaningfully reference major inputs/outputs and key state/flags for important behaviors?
- non_vacuity (0.20): Are properties non-trivial (not always true), with reachable triggers and minimal redundancy/overlap?
- syntax_structure (0.10): Valid SVA constructs; proper reset handling (e.g., disable iff); suitable to bind against the module.
- clarity_conciseness (0.10): Clear intent; minimal yet sufficient properties; avoids boilerplate or noise.

Special cases:
- If no SVA are present or they are unusable, set all sub-scores and score_overall to 0.0, confidence ≤ 0.3, and include "no_sva_found" in issues.
- If SVA reference missing/irrelevant signals (e.g., testbench-only or undefined in the module context), penalize non_vacuity and temporal_correctness and note it in issues.

Return ONLY a single JSON object with this schema and nothing else:
{{
  "model": "<judge-model-name>",
  "version": "<judge-model-version>",
  "score_overall": <float 0..1>,
  "confidence": <float 0..1>,
  "sub_scores": {{
    "temporal_correctness": <0..1>,
    "signal_coverage": <0..1>,
    "non_vacuity": <0..1>,
    "syntax_structure": <0..1>,
    "clarity_conciseness": <0..1>
  }},
  "issues": [ "short issue #1", "short issue #2" ],
  "rationale": "One or two concise sentences. No step-by-step reasoning."
}}

Module: {module_name}

Verilog (module.v):
{rtl_code}

SVA (sva.sv):
{sva_code}
"""

# Helper functions
def clamp01(x: float) -> float:
    try:
        return max(0.0, min(1.0, float(x)))
    except Exception:
        return 0.0

def agg_weights(claude_conf: float, gemini_conf: float) -> Tuple[float, float]:
    c = BASE_WEIGHTS["claude"] * (1.0 + CONFIDENCE_ALPHA * (claude_conf - 0.5))
    g = BASE_WEIGHTS["gemini"] * (1.0 + CONFIDENCE_ALPHA * (gemini_conf - 0.5))
    s = c + g
    if s <= 0:
        return 0.5, 0.5
    return c / s, g / s

def aggregate_scores(c_res: Dict[str, Any], g_res: Dict[str, Any]) -> Dict[str, Any]:
    c_score = clamp01(c_res.get("score_overall", 0.0))
    g_score = clamp01(g_res.get("score_overall", 0.0))
    c_conf = clamp01(c_res.get("confidence", 0.5))
    g_conf = clamp01(g_res.get("confidence", 0.5))
    wc, wg = agg_weights(c_conf, g_conf)
    aggregate = wc * c_score + wg * g_score
    return {
        "aggregate_score": aggregate,
        "weights_used": {"claude": wc, "gemini": wg},
        "disagreement": abs(c_score - g_score),
    }

def build_prompt(module_name: str, rtl_code: str, sva_code: str) -> str:
    return PROMPT_TEMPLATE.format(
        module_name=module_name,
        rtl_code=rtl_code,
        sva_code=sva_code,
    )

def read_jsonl(path: str) -> Iterable[Dict[str, Any]]:
    with open(path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                yield json.loads(line)
            except Exception:
                continue

def write_json(obj: Dict[str, Any], path: str):
    with open(path, "w") as f:
        json.dump(obj, f, indent=2)

def update_metadata_jsonl(version_dir: str, sample_id: str, update_fields: Dict[str, Any]):
    meta_dir = os.path.join(version_dir, "metadata")
    jsonl_path = os.path.join(meta_dir, "metadata.jsonl")
    tmp_path = jsonl_path + ".tmp"
    bak_path = jsonl_path + ".bak_" + datetime.now().strftime("%Y%m%d_%H%M%S")
    changed = False

    with open(jsonl_path, "r") as src, open(tmp_path, "w") as dst:
        for line in src:
            ls = line.strip()
            if not ls:
                dst.write(line)
                continue
            try:
                obj = json.loads(ls)
            except Exception:
                dst.write(line)
                continue
            if obj.get("id") == sample_id:
                for k, v in update_fields.items():
                    if k == "judging" and isinstance(v, dict):
                        j = obj.get("judging", {})
                        j.update(v)
                        obj["judging"] = j
                    else:
                        obj[k] = v
                dst.write(json.dumps(obj) + "\n")
                changed = True
            else:
                dst.write(line if line.endswith("\n") else (line + "\n"))

    if changed:
        os.replace(jsonl_path, bak_path)
        os.replace(tmp_path, jsonl_path)
    else:
        os.remove(tmp_path)

# Read dataset
def load_samples(version: str, only_unjudged: bool, limit: int = None) -> List[Dict[str, Any]]:
    version_dir = os.path.join(DATASET_ROOT, version)
    jsonl_path = os.path.join(version_dir, "metadata", "metadata.jsonl")
    if not os.path.isfile(jsonl_path):
        raise SystemExit(f"No metadata.jsonl at {jsonl_path}")

    samples = []
    for row in read_jsonl(jsonl_path):
        if only_unjudged and row.get("judging", {}).get("status") == "judged":
            continue
        sid = row.get("id")
        if not sid:
            continue
        # Ensure code present; if not, read from files
        if "verilog_code" not in row or "sva_code" not in row:
            try:
                sample_dir = os.path.join(version_dir, sid)
                with open(os.path.join(sample_dir, "module.v"), "r") as f:
                    row["verilog_code"] = f.read()
                with open(os.path.join(sample_dir, "sva.sv"), "r") as f:
                    row["sva_code"] = f.read()
            except Exception:
                continue
        samples.append(row)
        if limit and len(samples) >= limit:
            break
    return samples

# Build JSONL files for batch submission
def prepare_requests(version: str, out_prefix: str, limit: int, only_unjudged: bool):
    samples = load_samples(version, only_unjudged=only_unjudged, limit=limit)
    if not samples:
        print("No samples to prepare.")
        return

    # Paths
    gemini_jsonl = os.path.join(BATCH_DIR, f"{out_prefix}_gemini_requests.jsonl")
    # CHANGED: write Claude requests as JSONL, not JSON
    claude_jsonl = os.path.join(BATCH_DIR, f"{out_prefix}_claude_requests.jsonl")

    # Gemini: JSONL file of {"key": ..., "request": {GenerateContentRequest}}
    with open(gemini_jsonl, "w") as gf:
        for row in samples:
            sid = row["id"]
            prompt = build_prompt(row.get("module_name") or sid, row["verilog_code"], row["sva_code"])
            req = {
                "key": sid,
                "request": {
                    "contents": [{
                        "role": "user",
                        "parts": [{"text": prompt}]
                    }],
                    "generation_config": {
                        "temperature": 0,
                        "top_p": 0.1,
                        "max_output_tokens": 512,
                        "response_mime_type": "application/json"
                    }
                }
            }
            gf.write(json.dumps(req) + "\n")

    # CHANGED: Claude JSONL — one object per line: {"custom_id": "...", "params": {...}}
    with open(claude_jsonl, "w") as cf:
        for row in samples:
            sid = row["id"]
            prompt = build_prompt(row.get("module_name") or sid, row["verilog_code"], row["sva_code"])
            cf.write(json.dumps({
                "custom_id": sid,
                "params": {
                    "model": CLAUDE_MODEL,
                    "max_tokens": 512,
                    "temperature": 0,
                    "messages": [{"role": "user", "content": prompt}],
                }
            }) + "\n")

    # Save a small manifest for mapping
    manifest = {
        "version": version,
        "count": len(samples),
        "prepared_at": datetime.now().isoformat(),
        "gemini_file": gemini_jsonl,
        # CHANGED: point manifest to the JSONL path
        "claude_file": claude_jsonl,
        "ids": [s["id"] for s in samples]
    }
    write_json(manifest, os.path.join(BATCH_DIR, f"{out_prefix}_manifest.json"))

    print(f"Prepared {len(samples)} requests.")
    print(f"- Gemini JSONL: {gemini_jsonl}")
    print(f"- Claude JSONL: {claude_jsonl}")

# Create batch jobs
def submit_gemini(out_prefix: str, display_name: str = None) -> str:
    if not GEMINI_API_KEY:
        raise SystemExit("GEMINI_API_KEY not set")
    client = genai.Client(api_key=GEMINI_API_KEY)

    gemini_jsonl = os.path.join(BATCH_DIR, f"{out_prefix}_gemini_requests.jsonl")
    if not os.path.exists(gemini_jsonl):
        raise SystemExit(f"Not found: {gemini_jsonl}")

    uploaded = client.files.upload(
        file=gemini_jsonl,
        config=genai_types.UploadFileConfig(
            display_name=display_name or f"{out_prefix}-gemini-requests",
            mime_type="jsonl",
        ),
    )
    job = client.batches.create(
        model=GEMINI_MODEL,
        src=uploaded.name,
        config={"display_name": display_name or f"{out_prefix}-gemini-batch"},
    )
    job_name = job.name  # e.g., "batches/123..."
    write_json({"gemini_job_name": job_name, "uploaded_file": uploaded.name},
               os.path.join(BATCH_DIR, f"{out_prefix}_gemini_submit.json"))
    print(f"Gemini batch created: {job_name}")
    return job_name

def submit_claude(out_prefix: str) -> str:
    if not ANTHROPIC_API_KEY:
        raise SystemExit("ANTHROPIC_API_KEY not set")
    client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY)

    # CHANGED: read from JSONL file
    claude_jsonl = os.path.join(BATCH_DIR, f"{out_prefix}_claude_requests.jsonl")
    if not os.path.exists(claude_jsonl):
        raise SystemExit(f"Not found: {claude_jsonl}")

    # Load JSONL into a list of request objects expected by the API
    requests = []
    with open(claude_jsonl, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            # Validate minimum shape
            if "custom_id" in obj and "params" in obj:
                requests.append(obj)

    if not requests:
        raise SystemExit(f"No valid requests found in {claude_jsonl}")

    # NOTE: Anthropic's SDK currently accepts the list directly.
    # Using batch API still yields the 50% discount; input-as-file isn't required.
    batch = client.messages.batches.create(requests=requests)
    batch_id = batch.id  # e.g., "msgbatch_..."
    write_json({"claude_batch_id": batch_id, "source_file": claude_jsonl},
               os.path.join(BATCH_DIR, f"{out_prefix}_claude_submit.json"))
    print(f"Claude batch created: {batch_id} (from JSONL: {os.path.basename(claude_jsonl)})")
    return batch_id

# Checking status of batch jobs
def poll_gemini(job_name: str, interval: int = 30):
    client = genai.Client(api_key=GEMINI_API_KEY)
    completed = {"JOB_STATE_SUCCEEDED", "JOB_STATE_FAILED", "JOB_STATE_CANCELLED", "JOB_STATE_EXPIRED"}
    print(f"Polling Gemini job: {job_name}")
    while True:
        job = client.batches.get(name=job_name)
        state = job.state.name if hasattr(job.state, "name") else job.state
        print(f"State: {state}")
        if state in completed:
            print("Gemini job finished.")
            return state, job
        time.sleep(interval)

def poll_claude(batch_id: str, interval: int = 60):
    client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY)
    print(f"Polling Claude batch: {batch_id}")
    while True:
        batch = client.messages.batches.retrieve(batch_id)
        status = batch.processing_status  # "in_progress" or "ended"
        print(f"Status: {status}")
        if status == "ended":
            print("Claude batch finished.")
            return status, batch
        time.sleep(interval)

# DOWNLOAD / COLLECT RESULTS
def download_gemini_results(job, out_prefix: str) -> str:
    client = genai.Client(api_key=GEMINI_API_KEY)
    # If created with file input, results are in a file
    dest = getattr(job, "dest", None)
    file_name = getattr(dest, "file_name", None) if dest else None
    if not file_name:
        # Inline responses case (unlikely for file-based); fallback
        out_path = os.path.join(BATCH_DIR, f"{out_prefix}_gemini_results_inline.json")
        write_json({"job": job.to_dict() if hasattr(job, "to_dict") else str(job)}, out_path)
        print(f"Wrote inline Gemini results metadata: {out_path}")
        return out_path

    print(f"Downloading Gemini results file: {file_name}")
    content = client.files.download(file=file_name)  # bytes
    out_jsonl = os.path.join(BATCH_DIR, f"{out_prefix}_gemini_results.jsonl")
    with open(out_jsonl, "wb") as f:
        f.write(content)
    print(f"Wrote Gemini results JSONL: {out_jsonl}")
    return out_jsonl

def stream_claude_results(batch_id: str, out_prefix: str) -> str:
    client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY)
    out_jsonl = os.path.join(BATCH_DIR, f"{out_prefix}_claude_results.jsonl")
    print(f"Streaming Claude results to: {out_jsonl}")
    with open(out_jsonl, "w") as f:
        for res in client.messages.batches.results(batch_id):
            # Write each JSON line as-is
            try:
                f.write(json.dumps(res.model_dump()) + "\n")
            except Exception:
                # Best-effort robustness
                try:
                    f.write(json.dumps(res) + "\n")
                except Exception:
                    pass
    return out_jsonl

# Parse output JSONL files
def _try_parse_json_text(text: str) -> Dict[str, Any]:
    text = (text or "").strip()
    if not text:
        return {}
    try:
        return json.loads(text)
    except Exception:
        s, e = text.find("{"), text.rfind("}")
        if s >= 0 and e >= 0 and e > s:
            try:
                return json.loads(text[s : e + 1])
            except Exception:
                return {}
        return {}

def _gemini_line_to_key_and_text(obj: Dict[str, Any]):
    # Expect {"key": "<id>", "response": GenerateContentResponse} or {"error": ...}
    key = obj.get("key")
    resp = obj.get("response")
    if not key or not resp:
        return None, None
    # Try resp.text first (SDK shortcut on interactive; batch may not have)
    if isinstance(resp, dict) and "text" in resp and isinstance(resp["text"], str):
        return key, resp["text"]
    # Fallback: candidates[0].content.parts[].text
    try:
        cand = resp["candidates"][0]
        parts = cand["content"]["parts"]
        texts = [p.get("text", "") for p in parts if isinstance(p, dict) and "text" in p]
        return key, "\n".join([t for t in texts if t])
    except Exception:
        return key, None

def _claude_line_to_id_and_text(obj: Dict[str, Any]):
    # Expect {"custom_id": "<id>", "result": {"type": "succeeded", "message": {...}}}
    cid = obj.get("custom_id")
    res = obj.get("result") or {}
    if res.get("type") != "succeeded":
        return cid, None
    msg = res.get("message") or {}
    content = msg.get("content") or []
    texts = [b.get("text", "") for b in content if isinstance(b, dict) and b.get("type") == "text"]
    return cid, "\n".join([t for t in texts if t])

# Merge and apply reults to each metadata file
def merge_and_apply(version: str, out_prefix: str,
                    gemini_results_path: str, claude_results_path: str):
    version_dir = os.path.join(DATASET_ROOT, version)

    # Parse Gemini results
    gemini_map: Dict[str, Dict[str, Any]] = {}
    if gemini_results_path and os.path.exists(gemini_results_path):
        for line in read_jsonl(gemini_results_path):
            key, text = _gemini_line_to_key_and_text(line)
            if key and text:
                obj = _try_parse_json_text(text)
                if obj:
                    obj["model"] = obj.get("model") or GEMINI_MODEL
                    obj["version"] = obj.get("version") or GEMINI_MODEL
                    gemini_map[key] = obj

    # Parse Claude results
    claude_map: Dict[str, Dict[str, Any]] = {}
    if claude_results_path and os.path.exists(claude_results_path):
        for line in read_jsonl(claude_results_path):
            cid, text = _claude_line_to_id_and_text(line)
            if cid and text:
                obj = _try_parse_json_text(text)
                if obj:
                    obj["model"] = obj.get("model") or CLAUDE_MODEL
                    obj["version"] = obj.get("version") or CLAUDE_MODEL
                    claude_map[cid] = obj

    # For each sample id with both results, aggregate and write back
    all_ids = sorted(set(gemini_map.keys()) | set(claude_map.keys()))
    applied = 0
    for sid in all_ids:
        if sid not in gemini_map or sid not in claude_map:
            # You can choose to skip or accept single-judge results
            continue
        c_res, g_res = claude_map[sid], gemini_map[sid]

        # Sanitize like llm_judge.py
        def _sanitize(r: Dict[str, Any]):
            r["score_overall"] = clamp01(r.get("score_overall", 0.0))
            r["confidence"] = clamp01(r.get("confidence", 0.5))
            sub = r.get("sub_scores", {}) or {}
            for k in ["temporal_correctness","signal_coverage","non_vacuity","syntax_structure","clarity_conciseness"]:
                sub[k] = clamp01(sub.get(k, 0.0))
            r["sub_scores"] = sub
            r["issues"] = r.get("issues", []) or []
            r["rationale"] = (r.get("rationale") or "")[:300]
            return r

        c_res = _sanitize(c_res)
        g_res = _sanitize(g_res)
        agg = aggregate_scores(c_res, g_res)
        agg_score = agg["aggregate_score"]

        if agg_score >= 0.80:
            verdict, accepted = "accept", True
        elif agg_score <= 0.60:
            verdict, accepted = "reject", False
        else:
            verdict, accepted = "borderline", False

        # Update per-sample metadata.json
        sample_dir = os.path.join(version_dir, sid)
        meta_path = os.path.join(sample_dir, "metadata.json")
        try:
            with open(meta_path, "r") as f:
                meta = json.load(f)
        except Exception:
            meta = {}
        j = meta.get("judging", {}) or {}
        llm_scores = j.get("llm_scores", [])
        timestamp = datetime.now().isoformat()

        for jr in (c_res, g_res):
            llm_scores.append({
                "model": jr.get("model"),
                "version": jr.get("version"),
                "score_overall": jr.get("score_overall"),
                "confidence": jr.get("confidence"),
                "sub_scores": jr.get("sub_scores"),
                "issues": jr.get("issues"),
                "rationale": jr.get("rationale"),
                "timestamp": timestamp
            })
        j.update({
            "status": "judged",
            "llm_scores": llm_scores,
            "aggregate_score": agg_score,
            "accepted": accepted,
            "verdict": verdict  # <-- add this
        })
        meta["judging"] = j
        write_json(meta, meta_path)

        # Update metadata.jsonl entry
        update_metadata_jsonl(os.path.join(DATASET_ROOT, version), sid, {
            "judging": {
                "status": "judged",
                "llm_scores": llm_scores,
                "aggregate_score": agg_score,
                "accepted": accepted,
                "verdict": verdict  # <-- and here
            }
        })

        applied += 1
        # Optional: emit a clearer log line
        print(f"Applied {sid}: verdict={verdict} agg={agg_score:.3f} accepted={accepted}")
    print(f"Merged and applied results for {applied} samples.")

# CLI
def main():
    p = argparse.ArgumentParser("Batch LLM judge via Gemini + Claude")
    sub = p.add_subparsers(dest="cmd", required=True)

    sp = sub.add_parser("prepare", help="Prepare batch request files from dataset")
    sp.add_argument("--version", default=CURRENT_VERSION)
    sp.add_argument("--limit", type=int, default=1000)
    sp.add_argument("--only-unjudged", action="store_true", default=True)
    sp.add_argument("--prefix", default=datetime.now().strftime("judgebatch_%Y%m%d_%H%M%S"))

    sg = sub.add_parser("submit-gemini", help="Submit Gemini batch (file-based JSONL)")
    sg.add_argument("--prefix", required=True)
    sg.add_argument("--display-name", default=None)

    sc = sub.add_parser("submit-claude", help="Submit Claude batch (inline requests)")
    sc.add_argument("--prefix", required=True)

    pg = sub.add_parser("poll-gemini", help="Poll Gemini job until done")
    pg.add_argument("--job-name", required=True)
    pg.add_argument("--interval", type=int, default=30)
    pg.add_argument("--prefix", required=True)

    pc = sub.add_parser("poll-claude", help="Poll Claude batch until done")
    pc.add_argument("--batch-id", required=True)
    pc.add_argument("--interval", type=int, default=60)
    pc.add_argument("--prefix", required=True)

    mg = sub.add_parser("merge-apply", help="Merge results and update dataset metadata")
    mg.add_argument("--version", default=CURRENT_VERSION)
    mg.add_argument("--prefix", required=True)
    mg.add_argument("--gemini-results", default=None, help="Path to gemini results JSONL (if known)")
    mg.add_argument("--claude-results", default=None, help="Path to claude results JSONL (if known)")

    args = p.parse_args()

    if args.cmd == "prepare":
        os.makedirs(BATCH_DIR, exist_ok=True)
        prepare_requests(args.version, args.prefix, args.limit, args.only_unjudged)

    elif args.cmd == "submit-gemini":
        submit_gemini(args.prefix, args.display_name)

    elif args.cmd == "submit-claude":
        submit_claude(args.prefix)

    elif args.cmd == "poll-gemini":
        if not GEMINI_API_KEY:
            raise SystemExit("GEMINI_API_KEY not set")
        state, job = poll_gemini(args.job_name, args.interval)
        # Always try to download file results if succeeded
        out_path = download_gemini_results(job, args.prefix)
        print(f"Gemini results at: {out_path}")

    elif args.cmd == "poll-claude":
        if not ANTHROPIC_API_KEY:
            raise SystemExit("ANTHROPIC_API_KEY not set")
        status, _ = poll_claude(args.batch_id, args.interval)
        out_path = stream_claude_results(args.batch_id, args.prefix)
        print(f"Claude results at: {out_path}")

    elif args.cmd == "merge-apply":
        # Guess result file paths if not provided
        gem = args.gemini_results or os.path.join(BATCH_DIR, f"{args.prefix}_gemini_results.jsonl")
        cla = args.claude_results or os.path.join(BATCH_DIR, f"{args.prefix}_claude_results.jsonl")
        merge_and_apply(args.version, args.prefix, gem, cla)

if __name__ == "__main__":
    main()