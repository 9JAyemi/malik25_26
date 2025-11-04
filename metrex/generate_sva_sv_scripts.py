# generate_sva_sv_scripts.py
from datasets import load_dataset
from openai import OpenAI
from pathlib import Path
from dotenv import load_dotenv

import os
import re
import json
import random
import hashlib
from typing import Optional

load_dotenv()  # loads OPENAI_API_KEY from .env if present

# ====== Configuration ======
MODEL = os.getenv("OPENAI_MODEL", "gpt-5")
TARGET_MODULES = int(os.getenv("TARGET_MODULES", "1"))
TEMPERATURE = float(os.getenv("TEMPERATURE", "0.2"))
# Prefer MAX_OUTPUT_TOKENS; fallback to MAX_COMPLETION_TOKENS for compatibility
MAX_OUTPUT_TOKENS = int(os.getenv("MAX_OUTPUT_TOKENS", os.getenv("MAX_COMPLETION_TOKENS", "2048")))
MAX_INPUT_CHARS = int(os.getenv("MAX_INPUT_CHARS", str(350_000)))

# Artifact toggles
SAVE_PROMPTS = os.getenv("SAVE_PROMPTS", "0") == "1"
SAVE_RAW_RESPONSES = os.getenv("SAVE_RAW_RESPONSES", "1") == "1"
SAVE_VERILOG_USED = os.getenv("SAVE_VERILOG_USED", "1") == "1"     # save the verilog actually sent
SAVE_VERILOG_FULL = os.getenv("SAVE_VERILOG_FULL", "0") == "1"     # optionally also save full, untruncated

# Paths
SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR / "sva_sv_files"
JSONL_PATH = SCRIPT_DIR / "metrex_modules_sv.jsonl"
PROMPT_DIR = SCRIPT_DIR / "sva_prompts"
RAW_DIR = SCRIPT_DIR / "sva_raw"
VERILOG_DIR = SCRIPT_DIR / "sva_verilog"

# ====== Helpers ======

VERILOG_FIELD_CANDIDATES = ("rtl", "RTL", "verilog", "sv", "code", "text")

def get_verilog_from_row(row: dict) -> Optional[str]:
    """Return Verilog/SystemVerilog text from common MetRex fields or None."""
    for key in VERILOG_FIELD_CANDIDATES:
        v = row.get(key)
        if isinstance(v, str) and ("module" in v and "endmodule" in v):
            return v
    for v in row.values():
        if isinstance(v, str) and ("module" in v and "endmodule" in v):
            return v
    return None

MODULE_NAME_RE = re.compile(r"\bmodule\s+([A-Za-z_]\w*)", re.S)

def guess_first_module_name(text: str) -> str:
    m = MODULE_NAME_RE.search(text)
    return m.group(1) if m else "unknown_module"

def maybe_truncate_verilog(src: str, limit: int = MAX_INPUT_CHARS) -> str:
    """Keep large inputs under a safe character limit: head + tail."""
    if len(src) <= limit:
        return src
    head = src[: int(limit * 0.8)]
    tail = src[-int(limit * 0.15):]
    return head + "\n// ... truncated due to context limit ...\n" + tail

def build_prompt(verilog_src: str) -> str:
    return f"""
You are an expert formal verification engineer.

Generate a valid SystemVerilog SVA file that contains ONLY SVA constructs for the given Verilog.
Do not include any 'module', 'interface', 'bind', or TCL/Markdown. Only comments, property/endproperty,
and assert property statements. Use only signals that appear in the code.

Guidelines:
- If a clock/reset signal is evident (e.g., clk/clock, rst/reset), use @(posedge <clk>) and disable iff(<reset_active>).
- If ambiguous, still write meaningful properties that don't require a specific clock, or assume a reasonable clock name from the code.
- Include several meaningful properties: reset behavior if present, counter bounds, handshake req/ack or valid/ready if present,
  simple pipeline/valid-data relationships, and invariants.
- Keep the file well-structured with a short comment per property.

Verilog source to analyze:

{verilog_src}
""".strip()

def ensure_api_key() -> str:
    key = os.getenv("OPENAI_API_KEY")
    if not key:
        raise RuntimeError("OPENAI_API_KEY is not set. Export it or put it in a .env file.")
    return key

def strip_markdown_fences(s: str) -> str:
    """Always remove ``` fences if the model decides to add them."""
    CODE_FENCE_RE = re.compile(r"^\s*```(?:\w+)?\s*|\s*```\s*$", re.M)
    return CODE_FENCE_RE.sub("", s).strip()

# Minimal heuristic to confirm presence of SVA constructs
SVA_HEURISTIC_RE = re.compile(r"(?:\bproperty\b.*?\bendproperty\b)|\bassert\s+property\b", re.S | re.I)

def looks_like_sva(text: str) -> bool:
    return bool(SVA_HEURISTIC_RE.search(text))

def responses_call(client, model, system_text, user_text, temperature, max_tokens) -> str:
    """
    Use the Responses API (recommended for GPT-5). Returns text or empty string.
    """
    try:
        # Combine system + user for simplicity
        full_input = f"System:\n{system_text}\n\nUser:\n{user_text}"
        resp = client.responses.create(
            model=model,
            input=full_input,
            temperature=temperature,
            max_output_tokens=max_tokens,
        )
        # Prefer convenience accessor if present
        if hasattr(resp, "output_text"):
            return resp.output_text or ""
        # Fallback: attempt to stitch text parts
        out = []
        for item in getattr(resp, "output", []) or []:
            for c in getattr(item, "content", []) or []:
                if hasattr(c, "text") and c.text:
                    out.append(c.text)
        return "".join(out).strip()
    except Exception:
        return ""

# ====== Main flow ======

def main():
    ensure_api_key()
    client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

    ds = load_dataset("scale-lab/MetRex", split="train")

    # Collect unique code snippets that actually contain modules
    candidates = []
    seen_hashes = set()
    for i, row in enumerate(ds):
        raw = get_verilog_from_row(row)
        if not raw:
            continue
        norm = raw.strip()
        h = hashlib.md5(norm.encode("utf-8")).hexdigest()
        if h in seen_hashes:
            continue
        seen_hashes.add(h)
        candidates.append((i, norm))

    if not candidates:
        raise RuntimeError("No Verilog modules found in MetRex rows. Inspect dataset fields.")

    random.shuffle(candidates)
    picked = candidates[:TARGET_MODULES]

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    if SAVE_PROMPTS:
        PROMPT_DIR.mkdir(parents=True, exist_ok=True)
    if SAVE_RAW_RESPONSES:
        RAW_DIR.mkdir(parents=True, exist_ok=True)
    if SAVE_VERILOG_USED or SAVE_VERILOG_FULL:
        VERILOG_DIR.mkdir(parents=True, exist_ok=True)

    results = []

    for ordinal, (idx, verilog_src_full) in enumerate(picked, start=1):
        module_name = guess_first_module_name(verilog_src_full)
        safe_module = re.sub(r"[^A-Za-z0-9_]+", "_", module_name)[:80] or f"module_{idx}"

        # Save full verilog if requested
        if SAVE_VERILOG_FULL:
            (VERILOG_DIR / f"{ordinal:03d}_{safe_module}_verilog_full.v").write_text(verilog_src_full)

        # Truncate for prompt if needed, and save the used version
        verilog_src_used = maybe_truncate_verilog(verilog_src_full, MAX_INPUT_CHARS)
        if SAVE_VERILOG_USED:
            (VERILOG_DIR / f"{ordinal:03d}_{safe_module}_verilog_used.v").write_text(verilog_src_used)

        prompt = build_prompt(verilog_src_used)
        print(f"[{ordinal}/{len(picked)}] Requesting SVA for row {idx} module '{module_name}' ({len(verilog_src_used)} chars)...")

        if SAVE_PROMPTS:
            (PROMPT_DIR / f"{ordinal:03d}_{safe_module}_prompt.txt").write_text(prompt)

        # Responses API (primary path)
        raw_content = ""
        alt = responses_call(
            client=client,
            model=MODEL,
            system_text="Return ONLY raw SystemVerilog SVA code, no Markdown or TCL.",
            user_text=prompt,
            temperature=TEMPERATURE,
            max_tokens=MAX_OUTPUT_TOKENS,
        )
        if alt:
            raw_content = alt.strip()
        # If still empty, record and continue; no chat-completions fallback

        if SAVE_RAW_RESPONSES:
            # Save text, and if empty also save a JSON debug record if available
            (RAW_DIR / f"{ordinal:03d}_{safe_module}_raw.txt").write_text(raw_content)

        # Strip fences and validate SVA
        sva = strip_markdown_fences(raw_content)

        # Enforce: skip if empty or not SVA
        if not sva.strip() or not looks_like_sva(sva):
            print(f"✖ Skipping idx={idx}: empty or non-SVA response.")
            # Save additional debug info if we can
            try:
                debug_info = {
                    "dataset_index": idx,
                    "module_name": module_name,
                    "reason": "empty-or-non-sva",
                    "prompt_file": str((PROMPT_DIR / f"{ordinal:03d}_{safe_module}_prompt.txt").resolve()) if SAVE_PROMPTS else None,
                    "verilog_used_file": str((VERILOG_DIR / f"{ordinal:03d}_{safe_module}_verilog_used.v").resolve()) if SAVE_VERILOG_USED else None,
                }
                (RAW_DIR / f"{ordinal:03d}_{safe_module}_debug.json").write_text(json.dumps(debug_info, indent=2))
            except Exception:
                pass
            continue

        out_path = OUT_DIR / f"{ordinal:03d}_{safe_module}_sva.sv"
        out_path.write_text(sva)
        print(f"✔ Wrote {out_path.name} ({len(sva)} chars)")

        results.append({
            "dataset_index": idx,
            "module_name": module_name,
            "sva_file": str(out_path),
            "verilog_used_file": str(VERILOG_DIR / f"{ordinal:03d}_{safe_module}_verilog_used.v") if SAVE_VERILOG_USED else None,
            "verilog_full_file": str(VERILOG_DIR / f"{ordinal:03d}_{safe_module}_verilog_full.v") if SAVE_VERILOG_FULL else None,
            "input_chars": len(verilog_src_used),
            "sva_chars": len(sva),
        })

    if results:
        JSONL_PATH.write_text("\n".join(json.dumps(r) for r in results))
        print(f"✅ Summary: {JSONL_PATH} ({len(results)} entries)")
        print(f"🎉 Done: {len(results)} SVA files in '{OUT_DIR}/'")
    else:
        print("No files produced. Check 'sva_raw/' for raw responses and 'sva_verilog/' for inputs.")

if __name__ == "__main__":
    main()
