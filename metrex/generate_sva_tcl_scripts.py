# generate_sva_tcl_scripts.py

from dotenv import load_dotenv
load_dotenv()  # loads OPENAI_API_KEY from .env

from datasets import load_dataset
from openai import OpenAI
import random
import re
import json
import hashlib
import os
from pathlib import Path

# Initialize client using key from .env
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# === Configuration ===
TARGET_MODULES = 100
MAX_ASSERTS_PER_MODULE = 25          # hard cap per module
MAX_TOKENS_PER_INPUT = 200_000       # safety cap
CHARS_PER_TOKEN = 4                  # heuristic: ~4 chars/token
MAX_CHARS = MAX_TOKENS_PER_INPUT * CHARS_PER_TOKEN

# === Load dataset ===
ds = load_dataset("scale-lab/MetRex", split="train")
TOTAL_ROWS = len(ds)


def truncate_verilog(src: str) -> str:
    """Keep total text length under the character cap (~200k tokens)."""
    if len(src) <= MAX_CHARS:
        return src
    head = src[:100_000]
    tail = src[-20_000:]
    return head + "\n// ... truncated for token limit ...\n" + tail


def guess_top_and_ports(verilog_src: str):
    """Infer top module name, clock, and reset signals."""
    m = re.search(r"\bmodule\s+([A-Za-z_]\w*)", verilog_src)
    top = m.group(1) if m else "top"

    ports = re.search(r"module\s+[A-Za-z_]\w*\s*\((.*?)\);", verilog_src, re.S)
    text = (ports.group(1) if ports else "") + "\n" + verilog_src

    clk_candidates = re.findall(r"\b([A-Za-z_]\w*clk\w*|\w*clock\w*)\b", text, re.I)
    rst_candidates = re.findall(r"\b([A-Za-z_]\w*rst\w*|\w*reset\w*)\b", text, re.I)

    clk = clk_candidates[0] if clk_candidates else "clk"
    rst = rst_candidates[0] if rst_candidates else "reset"

    rst_active_low = rst.lower().endswith("n") or rst.lower().startswith("n")

    return top, clk, rst, rst_active_low


def build_prompt(verilog_src: str,
                 file_name: str,
                 top: str,
                 clk: str,
                 rst: str,
                 rst_active_low: bool,
                 max_asserts: int):
    """
    Ask for a Jasper-style TCL script with analyze/elaborate/clock/reset and assert { ... } lines.
    """
    rst_expr = f"!{rst}" if rst_active_low else rst
    active_str = "low" if rst_active_low else "high"

    return f"""
You are an expert formal verification engineer using a JasperGold-like tool.

Given the Verilog module below, output ONE TCL-style script suitable for Jasper,
with the following structure:

  analyze -sv {file_name}
  elaborate -top {top}

  clock {clk}
  reset {rst}

  # Comment describing property 1
  assert {{ <boolean or SVA-style expression over existing signals> }}

  # Comment describing property 2
  assert {{ <...> }}

  ...

  set_prove_time_limit 3600
  set_engine_mode Tri
  prove -all

Rules and guidelines:

1. Use only signals that exist in the given module.
2. Assume {clk} is the main clock and {rst} is an active-{active_str} reset.
   The TCL 'clock' and 'reset' commands will establish the temporal context,
   so inside 'assert {{ ... }}' you can use |-> and ##N as needed.
3. Generate several meaningful assertions (NO MORE THAN {max_asserts} total):
   - reset behavior (signals go to safe values when {rst_expr} is asserted)
   - handshake behavior (valid/ready, req/ack, etc.)
   - counter bounds and range checks
   - simple pipeline propagation (input valid/data flows to output after N cycles)
4. For each assertion:
   - Precede it by a brief comment (starting with '#') describing the intent.
   - Then a single-line 'assert {{ ... }}' statement.
5. Do NOT use 'property'/'endproperty' or 'assert property'.
6. Do NOT emit any module declarations or extra TCL beyond what is described.
7. Do NOT output Markdown or backticks. Only raw TCL-like script text.

Here is the Verilog module:

{verilog_src}
"""


results = []
used_indices = set()
seen_hashes = set()

while len(results) < TARGET_MODULES and len(used_indices) < TOTAL_ROWS:
    idx = random.randrange(TOTAL_ROWS)
    if idx in used_indices:
        continue
    used_indices.add(idx)

    row = ds[idx]
    text = row.get("text", "")
    if not text:
        continue

    # Extract the first module ... endmodule block
    m_mod = re.search(r"(module\b.*?endmodule)", text, re.S)
    if not m_mod:
        continue

    verilog_src = m_mod.group(1).strip()

    # Uniqueness by module text hash
    module_hash = hashlib.md5(verilog_src.encode("utf-8")).hexdigest()
    if module_hash in seen_hashes:
        continue
    seen_hashes.add(module_hash)

    verilog_src = truncate_verilog(verilog_src)
    top, clk, rst, rst_active_low = guess_top_and_ports(verilog_src)
    file_name = f"{top}.v"

    prompt = build_prompt(
        verilog_src=verilog_src,
        file_name=file_name,
        top=top,
        clk=clk,
        rst=rst,
        rst_active_low=rst_active_low,
        max_asserts=MAX_ASSERTS_PER_MODULE,
    )

    response = client.chat.completions.create(
        model="gpt-5-thinking",
        messages=[
            {
                "role": "system",
                "content": "You output only Jasper-style TCL scripts with 'assert { ... }' lines."
            },
            {"role": "user", "content": prompt},
        ],
        temperature=0.2,
    )

    tcl_script = response.choices[0].message.content

    results.append({
        "metrex_index": idx,
        "top": top,
        "tcl_script": tcl_script,
    })

    print(f"✔ {len(results):3d}/100  {top}  ({len(verilog_src)} chars)")

# === Save combined JSONL ===
jsonl_path = "metrex_100_unique_modules_tcl.jsonl"
with open(jsonl_path, "w") as f:
    for r in results:
        f.write(json.dumps(r) + "\n")

print(f"✅ Saved combined TCL JSONL: {jsonl_path}")

# === Save individual .tcl files per module ===
out_dir = Path("jasper_tcl_scripts")
out_dir.mkdir(exist_ok=True)

for i, entry in enumerate(results):
    top = entry["top"]
    tcl_script = entry["tcl_script"]

    safe_top = re.sub(r"[^A-Za-z0-9_]", "_", top)
    fname = out_dir / f"{i:03d}_{safe_top}.tcl"
    fname.write_text(tcl_script)
    print(f"💾 Wrote {fname}")

print("🎉 Done: 100 TCL scripts in 'jasper_tcl_scripts/' and JSONL summary.")
