from openai import OpenAI
from datasets import load_dataset
from pathlib import Path
import random
import re
import os
from dotenv import load_dotenv

# Load environment variables from .env file
load_dotenv()

api_key = os.getenv('OPENAI_API_KEY')
client = OpenAI(api_key=api_key)

# ====== Configuration ======
OUT_DIR = Path("metrex_verilog_modules")
OUT_DIR.mkdir(parents=True, exist_ok=True)

# ====== Load dataset ======
print("Loading MetRex dataset...")
ds = load_dataset("scale-lab/MetRex", split="train")

# ====== Collect modules that have RTL code ======
modules = []
for row in ds:
    rtl = row.get("RTL")
    if isinstance(rtl, str) and "module" in rtl and "endmodule" in rtl:
        modules.append(rtl.strip())

if not modules:
    raise RuntimeError("No valid Verilog modules found in MetRex dataset.")

# ====== Pick one random module ======
verilog_src = random.choice(modules)

prompt = f"""You are a verification engineer. 
Generate SVA assertions for the following verilog module. 
Make sure it has full coverage and checks all important signals and functions: 
{verilog_src}"""

response = client.responses.create(
    model="gpt-5",
    input=prompt,
    reasoning={"effort": "medium"},
    text={
        "verbosity": "medium"
    }
)

# ====== Extract module name ======
m = re.search(r"\bmodule\s+([A-Za-z_]\w*)", verilog_src)
module_name = m.group(1) if m else "unknown_module"

# Sanitize name for filesystem safety
module_name = re.sub(r"[^A-Za-z0-9_]+", "_", module_name)

# ====== Save it ======
file_path = OUT_DIR / f"{module_name}.v"
file_path.write_text(verilog_src)

sv_path = file_path.with_name(f"{module_name}_sv.sv")
sv_path.write_text(response.output_text)

print(f"✅ Saved SVA file to: {sv_path}")
print(f"✅ Saved random module '{module_name}' to: {file_path}")

