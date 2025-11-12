import os
import json
import time
import argparse
from datetime import datetime
from typing import Dict, Any, Tuple

# Optional: load .env at repo root
try:
    from dotenv import load_dotenv
    load_dotenv()
except Exception:
    pass

# External APIs
import anthropic
import google as genai

DATASET_ROOT = os.environ.get("DATASET_ROOT", "dataset")
CURRENT_VERSION = os.environ.get("DATASET_VERSION", "version_1")

# Models can be overridden via ENV
CLAUDE_MODEL = os.environ.get("CLAUDE_MODEL", "claude-sonnet-4-5-20250929")
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-2.5-pro")

ANTHROPIC_API_KEY = os.environ.get("ANTHROPIC_API_KEY")
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY")

# Aggregation defaults
BASE_WEIGHTS = {"claude": 0.55, "gemini": 0.45}
CONFIDENCE_ALPHA = 0.3  # weight scaling by (conf - 0.5)

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

def clamp01(x: float) -> float:
    try:
        return max(0.0, min(1.0, float(x)))
    except Exception:
        return 0.0

def agg_weights(claude_conf: float, gemini_conf: float) -> Tuple[float,float]:
    c = BASE_WEIGHTS["claude"] * (1.0 + CONFIDENCE_ALPHA * (claude_conf - 0.5))
    g = BASE_WEIGHTS["gemini"] * (1.0 + CONFIDENCE_ALPHA * (gemini_conf - 0.5))
    s = c + g
    if s <= 0:
        return 0.5, 0.5
    return c/s, g/s

def aggregate_scores(c_res: Dict[str,Any], g_res: Dict[str,Any]) -> Dict[str,Any]:
    c_score = clamp01(c_res.get("score_overall", 0.0))
    g_score = clamp01(g_res.get("score_overall", 0.0))
    c_conf = clamp01(c_res.get("confidence", 0.5))
    g_conf = clamp01(g_res.get("confidence", 0.5))
    wc, wg = agg_weights(c_conf, g_conf)
    aggregate = wc * c_score + wg * g_score
    return {
        "aggregate_score": aggregate,
        "weights_used": {"claude": wc, "gemini": wg},
        "disagreement": abs(c_score - g_score)
    }

def build_prompt(module_name: str, rtl_code: str, sva_code: str) -> str:
    return PROMPT_TEMPLATE.format(
        module_name=module_name,
        rtl_code=rtl_code,
        sva_code=sva_code
    )

def call_claude(prompt: str) -> Dict[str,Any]:
    if not ANTHROPIC_API_KEY:
        raise RuntimeError("ANTHROPIC_API_KEY not set")
    client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY)
    # JSON-only prompt; we rely on constraint + temperature=0
    msg = client.messages.create(
        model=CLAUDE_MODEL,
        max_tokens=1024,
        temperature=0,
        messages=[{"role":"user","content":prompt}]
    )
    text = "".join([b.text for b in msg.content if getattr(b, "type", "") == "text"])
    try:
        obj = json.loads(text)
    except Exception:
        # attempt to extract JSON substring
        start = text.find("{")
        end = text.rfind("}")
        obj = json.loads(text[start:end+1]) if start >=0 and end >=0 else {}
    obj["model"] = obj.get("model") or CLAUDE_MODEL
    obj["version"] = obj.get("version") or CLAUDE_MODEL
    return obj

def call_gemini(prompt: str) -> Dict[str,Any]:
    if not GEMINI_API_KEY:
        raise RuntimeError("GEMINI_API_KEY not set")
    genai.configure(api_key=GEMINI_API_KEY)
    model = genai.GenerativeModel(GEMINI_MODEL)
    resp = model.generate_content(
        prompt,
        generation_config=genai.types.GenerationConfig(
            temperature=0,
            top_p=0.1,
            max_output_tokens=1024,
            response_mime_type="application/json",
        )
    )
    text = resp.text or ""
    try:
        obj = json.loads(text)
    except Exception:
        start = text.find("{")
        end = text.rfind("}")
        obj = json.loads(text[start:end+1]) if start >=0 and end >=0 else {}
    obj["model"] = obj.get("model") or GEMINI_MODEL
    obj["version"] = obj.get("version") or GEMINI_MODEL
    return obj

def read_jsonl(path: str):
    with open(path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                yield json.loads(line)
            except Exception:
                continue

def write_json(obj: Dict[str,Any], path: str):
    with open(path, "w") as f:
        json.dump(obj, f, indent=2)

def update_metadata_jsonl(version_dir: str, sample_id: str, update_fields: Dict[str,Any]):
    """Rewrite metadata.jsonl replacing the entry with id == sample_id (merge update_fields)."""
    meta_dir = os.path.join(version_dir, "metadata")
    jsonl_path = os.path.join(meta_dir, "metadata.jsonl")
    tmp_path = jsonl_path + ".tmp"
    bak_path = jsonl_path + ".bak_" + datetime.now().strftime("%Y%m%d_%H%M%S")
    changed = False

    with open(jsonl_path, "r") as src, open(tmp_path, "w") as dst:
        for line in src:
            line_stripped = line.strip()
            if not line_stripped:
                dst.write(line)
                continue
            try:
                obj = json.loads(line_stripped)
            except Exception:
                dst.write(line)
                continue
            if obj.get("id") == sample_id:
                # Merge update_fields shallowly
                for k,v in update_fields.items():
                    if k == "judging" and isinstance(v, dict):
                        # Merge judging block
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

def judge_sample(sample: Dict[str,Any]) -> Dict[str,Any]:
    module_name = sample.get("module_name") or sample.get("custom_id") or "unknown_module"
    rtl_code = sample.get("verilog_code", "")
    sva_code = sample.get("sva_code", "")

    prompt = build_prompt(module_name, rtl_code, sva_code)

    # Call judges with simple retry
    def with_retry(fn, name):
        backoff = 2.0
        for attempt in range(4):
            try:
                return fn(prompt)
            except Exception as e:
                if attempt == 3:
                    raise
                time.sleep(backoff)
                backoff *= 2
        return {}

    claude_res = with_retry(call_claude, "claude")
    gemini_res = with_retry(call_gemini, "gemini")

    # Sanitize fields
    for r in (claude_res, gemini_res):
        r["score_overall"] = clamp01(r.get("score_overall", 0.0))
        r["confidence"] = clamp01(r.get("confidence", 0.5))
        # Sub-scores: ensure keys exist
        sub = r.get("sub_scores", {}) or {}
        for key in ["temporal_correctness","signal_coverage","non_vacuity","syntax_structure","clarity_conciseness"]:
            sub[key] = clamp01(sub.get(key, 0.0))
        r["sub_scores"] = sub
        r["issues"] = r.get("issues", []) or []
        r["rationale"] = (r.get("rationale") or "")[:300]

    agg = aggregate_scores(claude_res, gemini_res)
    aggregate_score = agg["aggregate_score"]

    # Verdict policy (adjust as needed)
    if aggregate_score >= 0.80:
        accepted = True
        verdict = "accept"
    elif aggregate_score <= 0.60:
        accepted = False
        verdict = "reject"
    else:
        accepted = False
        verdict = "borderline"

    out = {
        "aggregate_score": aggregate_score,
        "accepted": accepted,
        "verdict": verdict,
        "weights_used": agg["weights_used"],
        "disagreement": agg["disagreement"],
        "judges": [claude_res, gemini_res],
        "timestamp": datetime.now().isoformat()
    }
    return out

def main():
    parser = argparse.ArgumentParser(description="Batch judge SVA with Claude and Gemini.")
    parser.add_argument("--version", default=CURRENT_VERSION, help="Dataset version (default: env DATASET_VERSION or version_1)")
    parser.add_argument("--limit", type=int, default=200, help="Max samples to judge this run")
    parser.add_argument("--only-unjudged", action="store_true", help="Process only unjudged items (default)")
    parser.add_argument("--include-borderline", action="store_true", help="Re-evaluate items marked borderline")
    args = parser.parse_args()

    version_dir = os.path.join(DATASET_ROOT, args.version)
    jsonl_path = os.path.join(version_dir, "metadata", "metadata.jsonl")
    if not os.path.isfile(jsonl_path):
        raise SystemExit(f"No metadata.jsonl at {jsonl_path}")

    processed = 0
    for row in read_jsonl(jsonl_path):
        if args.only_unjudged and row.get("judging", {}).get("status") == "judged":
            if not (args.include_borderline and row.get("judging", {}).get("accepted") is False and row.get("judging", {}).get("aggregate_score") is not None and 0.60 < row["judging"]["aggregate_score"] < 0.80):
                continue

        sample_id = row.get("id")
        if not sample_id:
            continue

        # Ensure we have code; if missing, read from files
        if "verilog_code" not in row or "sva_code" not in row:
            sample_dir = os.path.join(version_dir, sample_id)
            try:
                with open(os.path.join(sample_dir, "module.v"), "r") as f:
                    row["verilog_code"] = f.read()
                with open(os.path.join(sample_dir, "sva.sv"), "r") as f:
                    row["sva_code"] = f.read()
            except Exception:
                continue

        # Judge
        result = judge_sample(row)

        # Update per-sample metadata.json
        sample_dir = os.path.join(version_dir, sample_id)
        meta_path = os.path.join(sample_dir, "metadata.json")
        try:
            with open(meta_path, "r") as f:
                meta = json.load(f)
        except Exception:
            meta = {}
        # Append llm_scores and set aggregate fields
        j = meta.get("judging", {}) or {}
        llm_scores = j.get("llm_scores", [])
        # two entries from this run (claude & gemini)
        for jr in result["judges"]:
            llm_scores.append({
                "model": jr.get("model"),
                "version": jr.get("version"),
                "score_overall": jr.get("score_overall"),
                "confidence": jr.get("confidence"),
                "sub_scores": jr.get("sub_scores"),
                "issues": jr.get("issues"),
                "rationale": jr.get("rationale"),
                "timestamp": result["timestamp"]
            })
        j.update({
            "status": "judged",
            "llm_scores": llm_scores,
            "aggregate_score": result["aggregate_score"],
            "accepted": result["accepted"]
        })
        meta["judging"] = j
        write_json(meta, meta_path)

        # Update metadata.jsonl entry
        update_metadata_jsonl(version_dir, sample_id, {
            "judging": {
                "status": "judged",
                "llm_scores": llm_scores,
                "aggregate_score": result["aggregate_score"],
                "accepted": result["accepted"]
            }
        })

        processed += 1
        print(f"Judged {sample_id}: agg={result['aggregate_score']:.3f} accepted={result['accepted']} disagreement={result['disagreement']:.2f}")
        if processed >= args.limit:
            break

    print(f"\nDone. Judged {processed} samples in version {args.version}.")

if __name__ == "__main__":
    main()