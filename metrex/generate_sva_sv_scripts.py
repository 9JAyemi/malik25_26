# generate_sva_sv_scripts.py

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
MAX_ASSERTS_PER_MODULE = 25        # upper bound per module
MAX_TOKENS_PER_INPUT = 200_000     # safety limit
CHARS_PER_TOKEN = 4                # heuristic: ~4 chars/token
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
                 top: str,
                 clk: str,
                 rst: str,
                 rst_active_low: bool,
                 max_asserts: int):
    """
    Prompt: ask for a normal SystemVerilog .sv file containing SVA only.
    """
    rst_expr = f"!{rst}" if rst_active_low else rst
    active_str = "low" if rst_active_low else "high"

    return f"""
You are an expert formal verification engineer.

Given the following Verilog module, generate a syntactically correct
SystemVerilog assertion file (.sv) that only contains SVA (no design RTL).

Requirements for the output:

1. It must be valid SystemVerilog code, suitable to be compiled as a .sv file.
2. Do NOT include any module/interface/bind declarations. Only:
   - comments
   - `property` / `endproperty`
   - `assert property` statements
3. Use `{clk}` as the clock and `{rst}` as the reset.
   - Use an event like: `@(posedge {clk})`
   - Use reset in `disable iff ({rst_expr})`
     where reset is active-{active_str}.
4. Use ONLY signals that exist in the given module.
5. Create several meaningful properties (no more than {max_asserts} total):
   - reset behavior (outputs, valids, counters go to safe values)
   - counter bounds / range checks
   - handshake behavior (valid/ready, req/ack, etc. if present)
   - simple pipeline propagation (valid/data relationships)
6. For each property:
   - Start with a one-line comment describing the intent.
   - Then:
       property <unique_name>;
         @(posedge {clk}) disable iff ({rst_expr})
           <boolean or temporal expression>;
       endproperty

       assert property (<unique_name>);

7. Use SVA operators like `|->`, `##N`, `inside` etc. when appropriate.
8. Do NOT include any TCL commands (no 'analyze', 'elaborate', 'clock', etc.).
9. Do NOT output Markdown or backticks. Only raw SystemVerilog code.

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

    prompt = build_prompt(
        verilog_src=verilog_src,
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
                "content": "You output only SystemVerilog SVA code (no TCL, no Markdown)."
            },
            {"role": "user", "content": prompt},
        ],
        temperature=0.2,
    )

    sva_sv_text = response.choices[0].message.content

    results.append({
        "metrex_index": idx,
        "top": top,
        "sva_sv": sva_sv_text,
    })

    print(f"✔ {len(results):3d}/100  {top}  ({len(verilog_src)} chars)")

# === Save combined JSONL ===
jsonl_path = "metrex_100_unique_modules_sv.jsonl"
with open(jsonl_path, "w") as f:
    for r in results:
        f.write(json.dumps(r) + "\n")

print(f"✅ Saved combined SV JSONL: {jsonl_path}")

# === Save individual .sv files per module ===
out_dir = Path("sva_sv_files")
out_dir.mkdir(exist_ok=True)

for i, entry in enumerate(results):
    top = entry["top"]
    sva_sv_text = entry["sva_sv"]

    safe_top = re.sub(r"[^A-Za-z0-9_]", "_", top)
    fname = out_dir / f"{i:03d}_{safe_top}_sva.sv"

    fname.write_text(sva_sv_text)
    print(f"💾 Wrote {fname}")

print("🎉 Done: 100 SVA .sv files in 'sva_sv_files/' and JSONL summary.")
