import sys
from pathlib import Path

folder = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("inference_outputs/chatgpt_baseline")

total = 0
for sva_path in folder.glob("*/sva.sv"):
    sva = sva_path.read_text()
    total += sva.count("assert property") + sva.count("assume property")
print(f"Total assertions: {total}")