from datasets import load_dataset
from openai import OpenAI
import random
import re
import json
import hashlib
import os

from dotenv import load_dotenv
load_dotenv()  # loads OPENAI_API_KEY from .env

# Initialize client using key from .env
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# === Configuration ===
TARGET_MODULES = 5
MAX_ASSERTS_PER_MODULE = 25
MAX_TOKENS_PER_INPUT = 200_000
CHARS_PER_TOKEN = 4
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


def guess_top_and_ports(verilog_src):
    """Infer top module, clock, and reset names."""
    m = re.search(r"\bmodule\s+([A-Za-z_]\w*)", verilog_src)
    top = m.group(1) if m else "top"
    ports = re.search(r"module\s+[A-Za-z_]\w*\s*\((.*?)\);", verilog_src, re.S)
    text = (ports.group(1) if ports else "") + "\n" + verilog_src

    clk = re.findall(r"\b([A-Za-z_]\w*clk\w*|\w*clock\w*)\b", text, re.I)
    rst = re.findall(r"\b([A-Za-z_]\w*rst\w*|\w*reset\w*)\b", text, re.I)
    clk = clk[0] if clk else "clk"
    rst = rst[0] if rst else "reset"
    rst_active_low = rst.lower().endswith("n") or rst.lower().startswith("n")
    return top, clk, rst, rst_active_low


def build_prompt(verilog_src, file_name, top, clk, rst, rst_active_low, max_asserts):
    rst_expr = f"!{rst}" if rst_active_low else rst
    return f"""
You are an expert formal verification engineer using a JasperGold-like tool.

Given the Verilog module below, output one script that:

  1. analyze/elaborate:
       analyze -sv {file_name}
       elaborate -top {top}
  2. clock/reset:
       clock {clk}
       reset {rst}   ;# active {'low' if rst_active_low else 'high'}
  3. emit several assertions (no more than {max_asserts}) each as:
       # comment
       assert {{ <boolean or SVA-style expression> }}
  4. finish with:
       set_prove_time_limit 3600
       set_engine_mode Tri
       prove -all

Rules:
- Use only signals from the module.
- Prefer reset, counter, handshake, and pipeline properties.
- No property/endproperty, no labels, no Markdown.

Module:
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

    m_mod = re.search(r"(module\b.*?endmodule)", text, re.S)
    if not m_mod:
        continue

    verilog_src = m_mod.group(1).strip()
    module_hash = hashlib.md5(verilog_src.encode()).hexdigest()
    if module_hash in seen_hashes:
        continue
    seen_hashes.add(module_hash)

    verilog_src = truncate_verilog(verilog_src)
    top, clk, rst, rst_active_low = guess_top_and_ports(verilog_src)
    file_name = f"{top}.v"

    prompt = build_prompt(verilog_src, file_name, top, clk, rst, rst_active_low, MAX_ASSERTS_PER_MODULE)

    response = client.chat.completions.create(
        model="gpt-5-thinking",
        messages=[
            {"role": "system", "content": "You output Jasper-style scripts with assert { ... } lines only."},
            {"role": "user", "content": prompt},
        ],
        temperature=0.2,
    )

    script_text = response.choices[0].message.content
    results.append({"metrex_index": idx, "top": top, "script": script_text})
    print(f"✔ {len(results):3d}/100  {top}  ({len(verilog_src)} chars)")

# === Save results ===
with open("metrex_100_unique_modules_token_safe.jsonl", "w") as f:
    for r in results:
        f.write(json.dumps(r) + "\n")

print("✅ All done. Saved 100 unique Jasper-style scripts.")
