import os
import json
import sys
from datetime import datetime
from openai import OpenAI
from pathlib import Path
from dotenv import load_dotenv

REPO_ROOT = Path(__file__).resolve().parents[1]
load_dotenv(REPO_ROOT / ".env")

# Cumulative dataset and generation-run state
DATASET_ROOT = REPO_ROOT / "data" / "veri_thoughts" / "generated"
RUN_ROOT = REPO_ROOT / "runs" / "generation" / "veri_thoughts"
ID_WIDTH = 5
BATCH_REQUESTS_DIR = RUN_ROOT / "batch_requests_regen"
BATCH_SIZE = 200  # Number of requests per batch file
MAX_SAMPLES = None  # Cap total samples per run (None = no limit, set to e.g. 10 for testing)
TRACKING_FILE = RUN_ROOT / "regen_batch_tracking.json"
REGEN_DONE_FILE = RUN_ROOT / "regen_completed_ids.json"


def load_regen_done() -> set:
    """Load set of sample IDs that have already been regenerated."""
    if os.path.exists(REGEN_DONE_FILE):
        with open(REGEN_DONE_FILE, "r") as f:
            return set(json.load(f))
    return set()


def save_regen_done(done: set):
    with open(REGEN_DONE_FILE, "w") as f:
        json.dump(sorted(done), f, indent=2)


SYSTEM_PROMPT = """\
You are an expert SystemVerilog verification engineer writing SVA for Jasper \
formal verification.

OUTPUT REQUIREMENTS:
1. Output a single, complete .sv file that compiles in Jasper without modification.
2. The file must be a module that takes the DUT's ports as inputs and contains \
   SVA properties bound to those signals. You can use internal signals \
   if they are present in the RTL, but do NOT invent new ones.
3. Every property must use a clocked event (@(posedge clk) or the appropriate \
   clock from the RTL). NEVER use combinational or level-sensitive events in \
   property statements — Jasper rejects these. For modules with combinational \
   logic, still clock your assertions to the appropriate clock edge.
4. Use `disable iff` with the correct reset polarity as shown in the RTL.
5. Use descriptive labels for every assertion (e.g., `check_grant_mutex`, not `a1`).
6. Add a brief comment above each assertion explaining what it checks.
7. Only assert behaviors that the RTL actually implements. Do not invent \
   signals, states, or protocols that are not present in the code.
8. Focus on QUALITY and CORRECTNESS — 10 correct, meaningful assertions are \
   worth more than 30 trivial or speculative ones.
9. Do NOT wrap output in markdown code fences or add explanation outside the code.
10. Keep comments minimal — one short line per assertion. Do NOT include large \
   comment blocks, file headers, or explanations of your approach.

REFERENCE EXAMPLE — this is the style and quality level to target:

```systemverilog
module manual (
    input logic CLK,
    input logic RESETn,
    input logic QREQn,
    input logic QACCEPTn,
    input logic QDENY,
    input logic QACTIVE
);
    
    ///// Handshake rules /////
    // QREQn can only transition from HIGH to LOW when QACCEPTn is HIGH and QDENY is LOW.
    handshake_1: assume property (
        @(posedge CLK) disable iff (!RESETn) $fell(QREQn) |-> (QACCEPTn == 1'b1) && (QDENY == 1'b0)
    );
    // QACCEPTn can only transition from HIGH to LOW when QREQn is LOW and QDENY is LOW.
    handshake_3: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(QACCEPTn) |-> (QREQn == 1'b0) && (QDENY == 1'b0)
    );
    // QDENY can only transition from LOW to HIGH when QREQn is LOW and QACCEPTn is HIGH.
    handshake_6: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(QDENY) |-> (QREQn == 1'b0) && (QACCEPTn == 1'b1)
    );
    ///// Device reset /////
    // At reset assertion, a device must drive both QACCEPTn and QDENY LOW.
    reset: assert property (
        @(posedge CLK) !RESETn |-> (QACCEPTn == 1'b0) && (QDENY == 1'b0)
    );
endmodule
```

Note the pattern: module wrapper with DUT ports as inputs, descriptive labels, \
comments explaining intent, proper clocking and reset disable on every property, \
and appropriate use of assume vs assert."""


def compute_prompt_text(rtl_code: str) -> str:
    return f"""\
Analyze the following RTL module carefully. Identify:
- The clock(s) and reset signal(s), including reset polarity
- Whether the logic is sequential, combinational, or mixed
- The key signals, interfaces, and functional behaviors

Then generate a complete .sv assertion module following the style shown in \
your reference example. Only write assertions for behaviors that are actually \
present in this RTL — do not guess or assume functionality that isn't there. \
For combinational logic, still use clocked assertions (@(posedge clk)).

RTL module:
```verilog
{rtl_code}
```"""


def load_failed_ids(txt_path: str) -> list[str]:
    """Read one sample ID per line from a .txt file."""
    with open(txt_path, "r") as f:
        ids = [line.strip().zfill(ID_WIDTH) for line in f if line.strip()]
    print(f"Loaded {len(ids)} failed IDs from {txt_path}")
    return ids


def load_sample(sample_id: str) -> dict:
    """Load module.v and metadata for a given sample ID."""
    sample_dir = os.path.join(DATASET_ROOT, sample_id)
    v_path = os.path.join(sample_dir, "module.v")
    meta_path = os.path.join(sample_dir, "metadata.json")

    if not os.path.exists(v_path):
        raise FileNotFoundError(f"No module.v in {sample_dir}")

    with open(v_path, "r") as f:
        rtl_code = f.read()

    metadata = {}
    if os.path.exists(meta_path):
        with open(meta_path, "r") as f:
            metadata = json.load(f)

    return {
        "sample_id": sample_id,
        "rtl_code": rtl_code,
        "metadata": metadata,
        "sample_dir": sample_dir,
    }


def create_batch_request(rtl_code: str, custom_id: str) -> dict:
    prompt = compute_prompt_text(rtl_code)
    return {
        "custom_id": custom_id,
        "method": "POST",
        "url": "/v1/responses",
        "body": {
            "model": "gpt-5.4",
            "input": [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": prompt},
            ],
            "reasoning": {"effort": "high"},
            "text": {"verbosity": "low"},
        },
    }


def prepare_and_submit_batches(client: OpenAI, samples: list[dict]) -> list[dict]:
    """Split samples into BATCH_SIZE chunks, write JSONL files, upload & submit."""
    os.makedirs(BATCH_REQUESTS_DIR, exist_ok=True)
    batches = []

    for i in range(0, len(samples), BATCH_SIZE):
        chunk = samples[i : i + BATCH_SIZE]
        batch_num = i // BATCH_SIZE
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        jsonl_path = os.path.join(BATCH_REQUESTS_DIR, f"regen_batch_{batch_num}_{ts}.jsonl")

        # Use sample_id as custom_id so we can map results back
        with open(jsonl_path, "w") as f:
            for s in chunk:
                req = create_batch_request(s["rtl_code"], custom_id=s["sample_id"])
                f.write(json.dumps(req) + "\n")

        print(f"Wrote {len(chunk)} requests to {jsonl_path}")

        # Upload & create batch
        with open(jsonl_path, "rb") as f:
            uploaded = client.files.create(file=f, purpose="batch")

        batch = client.batches.create(
            input_file_id=uploaded.id,
            endpoint="/v1/responses",
            completion_window="24h",
            metadata={"description": f"SVA regen batch {batch_num} — {len(chunk)} failed samples"},
        )
        print(f"Submitted batch {batch.id} ({len(chunk)} samples)")
        batches.append({"batch_id": batch.id, "sample_ids": [s["sample_id"] for s in chunk]})

    return batches


def check_and_apply_results(client: OpenAI):
    """Check regen batches and overwrite sva.sv for completed results."""
    if not os.path.exists(TRACKING_FILE):
        print("No regen tracking file found. Run --submit first.")
        return

    with open(TRACKING_FILE, "r") as f:
        tracking = json.load(f)

    done = load_regen_done()

    for entry in tracking["batches"]:
        batch_id = entry["batch_id"]
        batch = client.batches.retrieve(batch_id)
        print(f"\nBatch {batch_id}: {batch.status}")

        if batch.status != "completed":
            if batch.status == "failed":
                print(f"  FAILED — check dashboard for details")
            else:
                print(f"  Still processing...")
            continue

        # Download results
        content = client.files.content(batch.output_file_id)
        results = [json.loads(line) for line in content.text.strip().split("\n")]

        updated = 0
        errors = 0
        for result in results:
            sample_id = result.get("custom_id")
            if not sample_id:
                errors += 1
                continue

            # Extract SVA text from response
            sva_code = None
            try:
                body = result.get("response", {}).get("body", {})
                for item in body.get("output", []):
                    if item.get("type") == "message" and isinstance(item.get("content"), list):
                        for c in item["content"]:
                            if c.get("type") == "output_text" and isinstance(c.get("text"), str):
                                sva_code = c["text"].strip()
                                break
                    if sva_code:
                        break

                # Fallback
                if not sva_code:
                    sva_code = body.get("output_text") or body.get("text")
                    if isinstance(sva_code, str):
                        sva_code = sva_code.strip()

                if not sva_code:
                    raise ValueError("No text in response")

            except Exception as e:
                print(f"  ✗ {sample_id}: {e}")
                errors += 1
                continue

            # Overwrite sva.sv in-place
            sample_dir = os.path.join(DATASET_ROOT, sample_id)
            sva_path = os.path.join(sample_dir, "sva.sv")
            with open(sva_path, "w") as f:
                f.write(sva_code)

            # Update metadata to reflect regeneration
            meta_path = os.path.join(sample_dir, "metadata.json")
            if os.path.exists(meta_path):
                with open(meta_path, "r") as f:
                    meta = json.load(f)
                meta["regenerated_at"] = datetime.now().isoformat()
                meta["regen_batch_id"] = batch_id
                meta["judging"] = {
                    "status": "unjudged",
                    "llm_scores": [],
                    "aggregate_score": None,
                    "accepted": None,
                }
                # Count assertions in new SVA
                meta.setdefault("validation", {})["num_assertions"] = sum(
                    1 for line in sva_code.splitlines() if "assert" in line.lower()
                )
                with open(meta_path, "w") as f:
                    json.dump(meta, f, indent=2)

            updated += 1
            done.add(sample_id)

        print(f"  ✓ Updated {updated} samples, {errors} errors")

    save_regen_done(done)


def main():
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        print("Error: OPENAI_API_KEY not set")
        sys.exit(1)

    client = OpenAI(api_key=api_key)

    if len(sys.argv) < 2:
        print("Usage:")
        print("  python regenerate_failed.py --submit failed_ids.txt   # Submit regen batches")
        print("  python regenerate_failed.py --check                   # Check & apply results")
        sys.exit(0)

    if sys.argv[1] == "--submit":
        if len(sys.argv) < 3:
            print("Provide path to failed IDs .txt file")
            sys.exit(1)

        txt_path = sys.argv[2]
        failed_ids = load_failed_ids(txt_path)

        # Skip IDs that were already regenerated
        done = load_regen_done()
        failed_ids = [sid for sid in failed_ids if sid not in done]
        if not failed_ids:
            print("All failed IDs have already been regenerated.")
            sys.exit(0)
        print(f"{len(failed_ids)} remaining after skipping {len(done)} already regenerated")

        # Cap total samples if MAX_SAMPLES is set
        if MAX_SAMPLES is not None and len(failed_ids) > MAX_SAMPLES:
            failed_ids = failed_ids[:MAX_SAMPLES]
            print(f"Capped to {MAX_SAMPLES} samples for this run")

        # Load RTL for each failed sample
        samples = []
        for sid in failed_ids:
            try:
                samples.append(load_sample(sid))
            except FileNotFoundError as e:
                print(f"  ⚠ Skipping {sid}: {e}")

        print(f"Loaded {len(samples)} samples for regeneration")

        # Submit batches
        batches = prepare_and_submit_batches(client, samples)

        # Save tracking
        tracking = {
            "created_at": datetime.now().isoformat(),
            "total_samples": len(samples),
            "batches": batches,
        }
        with open(TRACKING_FILE, "w") as f:
            json.dump(tracking, f, indent=2)

        print(f"\nSubmitted {len(batches)} batch(es). Run --check to poll results.")

    elif sys.argv[1] == "--check":
        check_and_apply_results(client)

    else:
        print(f"Unknown command: {sys.argv[1]}")


if __name__ == "__main__":
    main()
