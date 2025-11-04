# generate_sva_sv_scripts.py
from datasets import load_dataset
from openai import OpenAI
import random
import re
import json
import hashlib
import os
from pathlib import Path

from dotenv import load_dotenv
load_dotenv()  # loads OPENAI_API_KEY from .env

# === Configuration ===
TARGET_MODULES = 1
MAX_ASSERTS_PER_MODULE = 25
MAX_TOKENS_PER_INPUT = 200_000
CHARS_PER_TOKEN = 4
MAX_CHARS = MAX_TOKENS_PER_INPUT * CHARS_PER_TOKEN

# Initialize OpenAI client
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# Load MetRex dataset
ds = load_dataset("scale-lab/MetRex", split="train")

# Make paths relative to this script, not CWD
SCRIPT_DIR = Path(__file__).resolve().parent
jsonl_path = SCRIPT_DIR / "metrex_modules_sv.jsonl"
out_dir = SCRIPT_DIR / "sva_sv_files"

# --- helpers ---
def truncate_verilog(src: str) -> str:
    """Keep total text length under the character cap (~200k tokens)."""
    if len(src) <= MAX_CHARS:
        return src
    head = src[:100_000]
    tail = src[-20_000:]
    return head + "\n// ... truncated for token limit ...\n" + tail

def get_verilog_from_row(row: dict) -> str:
    """Return Verilog/SystemVerilog text from common MetRex fields."""
    for key in ("rtl", "RTL", "verilog", "sv", "code", "text"):
        v = row.get(key)
        if isinstance(v, str) and "module" in v:
            return v
    return ""

MODULE_BLOCK_RE = re.compile(r"\bmodule\b.*?\bendmodule\b", re.S | re.I)

def extract_first_module_block(src: str) -> str | None:
    m = MODULE_BLOCK_RE.search(src)
    return m.group(0).strip() if m else None

# Looser port list capture: handle parameterized headers `#(...) ( ... );`
PORTS_RE = re.compile(
    r"module\s+[A-Za-z_]\w*(?:\s*#\s*\([^)]*\))?\s*\((.*?)\)\s*;",
    re.S | re.I,
)

def guess_top_and_ports(verilog_src: str):
    """Infer top, clock, reset (more tolerant of parameter lists)."""
    m = re.search(r"\bmodule\s+([A-Za-z_]\w*)", verilog_src, re.I)
    top = m.group(1) if m else "top"

    ports = PORTS_RE.search(verilog_src)
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


# === Collect a pool of valid, unique modules first ===
candidates = []
seen_hashes = set()
for i, row in enumerate(ds):
    raw = get_verilog_from_row(row)
    if not raw:
        continue
    block = extract_first_module_block(raw)
    if not block:
        continue
    h = hashlib.md5(block.encode("utf-8")).hexdigest()
    if h in seen_hashes:
        continue
    seen_hashes.add(h)
    candidates.append((i, block))

if not candidates:
    raise RuntimeError("No valid 'rtl' modules found in MetRex; check dataset columns.")

random.shuffle(candidates)
picked = candidates[:TARGET_MODULES]

results = []
for idx, verilog_src in picked:
    verilog_src = truncate_verilog(verilog_src)
    top, clk, rst, rst_active_low = guess_top_and_ports(verilog_src)
    prompt = build_prompt(verilog_src, top, clk, rst, rst_active_low, MAX_ASSERTS_PER_MODULE)

    try:
        resp = client.chat.completions.create(
            model="gpt-5",
            messages=[
                {"role": "system", "content": "You output only SystemVerilog SVA code (no TCL, no Markdown)."},
                {"role": "user", "content": prompt},
            ],
            temperature=0.2,
            max_tokens=4096,
        )
        sva_sv_text = resp.choices[0].message.content or ""
    except Exception as e:
        print(f"✖ Skipping idx={idx} due to API error: {e}")
        continue

    if not sva_sv_text.strip():
        print(f"✖ Empty response for idx={idx} ({top}); skipping.")
        continue

    results.append({"metrex_index": idx, "top": top, "sva_sv": sva_sv_text})
    print(f"✔ {len(results):3d}/{TARGET_MODULES}  {top}  ({len(verilog_src)} chars)")

# === Save outputs ===
jsonl_path.write_text("\n".join(json.dumps(r) for r in results))
print(f"✅ Saved combined SV JSONL: {jsonl_path} ({len(results)} entries)")

out_dir.mkdir(exist_ok=True)
for i, entry in enumerate(results):
    safe_top = re.sub(r"[^A-Za-z0-9_]", "_", entry["top"])
    (out_dir / f"{i:03d}_{safe_top}_sva.sv").write_text(entry["sva_sv"])
print(f"🎉 Done: {len(results)} SVA .sv files in '{out_dir}/' and JSONL summary.")
