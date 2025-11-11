import os
import json
import random
from datetime import datetime
from datasets import load_dataset
from openai import OpenAI
from dotenv import load_dotenv
import hashlib

# Load environment variables from .env file
load_dotenv()

# Configuration
MAX_TOKENS = 2500
CHARS_PER_TOKEN = 4
BATCH_SIZE = 500  # Number of modules to process in one batch
OUTPUT_DIR = "generated_modules"  # Single folder for all .v and .sv files
TRACKING_FILE = "processed_modules.json"  # Track what's been processed
BATCH_REQUESTS_DIR = "batch_requests"  # Store batch request files

# === New: dataset layout config and helpers (ID width = 5) ===
DATASET_ROOT = "dataset"
CURRENT_VERSION = os.getenv("DATASET_VERSION", "version_1")
ID_WIDTH = 5  # 00000, 00001, ...
GLOBAL_INDEX_FILE = os.path.join(DATASET_ROOT, "global_index.json")

def ensure_version_dirs():
    version_dir = os.path.join(DATASET_ROOT, CURRENT_VERSION)
    meta_dir = os.path.join(version_dir, "metadata")
    os.makedirs(version_dir, exist_ok=True)
    os.makedirs(meta_dir, exist_ok=True)
    # Ensure metadata files exist
    jsonl_path = os.path.join(meta_dir, "metadata.jsonl")
    stats_path = os.path.join(meta_dir, "stats.json")
    if not os.path.exists(jsonl_path):
        with open(jsonl_path, "w") as f:
            pass
    if not os.path.exists(stats_path):
        with open(stats_path, "w") as f:
            json.dump({"count": 0}, f)
    # Ensure global index exists
    if not os.path.exists(GLOBAL_INDEX_FILE):
        with open(GLOBAL_INDEX_FILE, "w") as f:
            json.dump(
                {"latest_version": CURRENT_VERSION, "next_id": 0, "versions": [CURRENT_VERSION]},
                f,
                indent=2
            )
    return version_dir, meta_dir

def load_global_index():
    if os.path.exists(GLOBAL_INDEX_FILE):
        with open(GLOBAL_INDEX_FILE, "r") as f:
            return json.load(f)
    return {"latest_version": CURRENT_VERSION, "next_id": 0, "versions": [CURRENT_VERSION]}

def save_global_index(idx):
    with open(GLOBAL_INDEX_FILE, "w") as f:
        json.dump(idx, f, indent=2)

def allocate_sample_id():
    # Single-writer assumption. Add a lock if you introduce concurrency.
    idx = load_global_index()
    sid = idx.get("next_id", 0)
    idx["next_id"] = sid + 1
    idx["latest_version"] = CURRENT_VERSION
    if "versions" not in idx:
        idx["versions"] = [CURRENT_VERSION]
    elif CURRENT_VERSION not in idx["versions"]:
        idx["versions"].append(CURRENT_VERSION)
    save_global_index(idx)
    return str(sid).zfill(ID_WIDTH)

def compute_prompt_text(rtl_code: str) -> str:
    return f"""You are a verification engineer. 
Generate SVA assertions for the following verilog module.
Make sure it has full coverage and checks all important
signals and functions, but make sure it is also concise. We
mostly care about quality over quantity and also mostly care
about SVA, not DUT or testbench code, the SVA is the most
important part of what you generate.:

{rtl_code}"""

def short_hash(text: str, n: int = 6) -> str:
    return hashlib.sha1(text.encode()).hexdigest()[:n]

def count_assertions(sva_code: str) -> int:
    # Simple heuristic; refine later if needed
    return sum(1 for line in sva_code.splitlines() if "assert" in line)

def update_stats(meta_dir: str, increment: int = 1):
    stats_path = os.path.join(meta_dir, "stats.json")
    try:
        with open(stats_path, "r") as f:
            stats = json.load(f)
    except Exception:
        stats = {"count": 0}
    stats["count"] = stats.get("count", 0) + increment
    with open(stats_path, "w") as f:
        json.dump(stats, f, indent=2)

def write_dataset_sample(rtl_code: str, sva_code: str, metadata: dict) -> dict:
    """
    Write one sample to dataset/<version>/<id> and append to metadata JSONL.
    Returns: {"id": "<zero-padded>", "dir": "<sample_dir>"}
    """
    version_dir, meta_dir = ensure_version_dirs()
    sample_id = allocate_sample_id()
    sample_dir = os.path.join(version_dir, sample_id)
    os.makedirs(sample_dir, exist_ok=True)

    # Write files
    verilog_file = os.path.join(sample_dir, "module.v")
    sva_file = os.path.join(sample_dir, "sva.sv")  # changed from properties.sv
    with open(verilog_file, "w") as f:
        f.write(rtl_code)
    with open(sva_file, "w") as f:
        f.write(sva_code)

    # Per-sample metadata (staging; unjudged by default)
    per_sample_meta = {
        "id": sample_id,
        "version": CURRENT_VERSION,
        "verilog_file": "module.v",
        "sva_file": "sva.sv",  # changed from properties.sv
        "created_at": datetime.now().isoformat(),
        **metadata,
        "judging": {
            "status": "unjudged",
            "llm_scores": [],
            "aggregate_score": None,
            "accepted": None
        }
    }
    with open(os.path.join(sample_dir, "metadata.json"), "w") as f:
        json.dump(per_sample_meta, f, indent=2)

    # Append JSONL entry with inline code for simple downstream loading
    jsonl_obj = {**per_sample_meta, "verilog_code": rtl_code, "sva_code": sva_code}
    with open(os.path.join(meta_dir, "metadata.jsonl"), "a") as f:
        f.write(json.dumps(jsonl_obj) + "\n")

    update_stats(meta_dir, increment=1)
    return {"id": sample_id, "dir": sample_dir}
# === end dataset helpers ===

def estimate_tokens(text):
    """Estimate token count based on character count."""
    return len(text) // CHARS_PER_TOKEN

def get_rtl_field(module):
    """Get RTL field, checking both 'RTL' and 'rtl'."""
    if 'RTL' in module:
        return module['RTL']
    elif 'rtl' in module:
        return module['rtl']
    else:
        raise KeyError("No 'RTL' or 'rtl' field found in module")

def get_module_name(rtl_code):
    """Extract module name from Verilog code."""
    lines = rtl_code.split('\n')
    for line in lines:
        line = line.strip()
        if line.startswith('module '):
            module_decl = line.split('module ')[1]
            module_name = module_decl.split('(')[0].split(';')[0].strip()
            return module_name
    return "unknown_module"

def get_module_hash(rtl_code):
    """Generate a hash of the RTL code to uniquely identify it."""
    return hashlib.md5(rtl_code.encode()).hexdigest()

def load_processed_modules():
    """Load the tracking file of processed modules."""
    if os.path.exists(TRACKING_FILE):
        with open(TRACKING_FILE, 'r') as f:
            return json.load(f)
    return {}

def save_processed_modules(processed):
    """Save the tracking file of processed modules."""
    with open(TRACKING_FILE, 'w') as f:
        json.dump(processed, f, indent=2)

def is_module_processed(module_hash, processed_modules):
    """Check if a module has already been processed."""
    return module_hash in processed_modules

def save_module_pair(rtl_code, sva_code, module_name, module_hash):
    """Save both .v and .sv files in the same folder with matching names."""
    # Create the output directory if it doesn't exist
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    
    # Handle duplicate module names by appending a number
    base_name = module_name
    v_filename = os.path.join(OUTPUT_DIR, f"{base_name}.v")
    sv_filename = os.path.join(OUTPUT_DIR, f"{base_name}.sv")
    
    # If file already exists, check if it's the same module
    if os.path.exists(v_filename):
        with open(v_filename, 'r') as f:
            existing_rtl = f.read()
            existing_hash = get_module_hash(existing_rtl)
        
        if existing_hash != module_hash:
            # Different module with same name - find next available number
            counter = 2
            while True:
                base_name = f"{module_name}_{counter}"
                v_filename = os.path.join(OUTPUT_DIR, f"{base_name}.v")
                sv_filename = os.path.join(OUTPUT_DIR, f"{base_name}.sv")
                
                if not os.path.exists(v_filename):
                    break
                
                # Check if this numbered version is also different
                with open(v_filename, 'r') as f:
                    existing_rtl = f.read()
                    existing_hash = get_module_hash(existing_rtl)
                
                if existing_hash == module_hash:
                    # Found the same module already saved with this number
                    break
                
                counter += 1
    
    # Save .v file
    with open(v_filename, 'w') as f:
        f.write(rtl_code)
    
    # Save .sv file
    with open(sv_filename, 'w') as f:
        f.write(sva_code)
    
    print(f"Saved: {base_name}.v and {base_name}.sv")
    return base_name

def create_batch_request(rtl_code, module_name, custom_id):
    """Create a single batch request object."""
    prompt = compute_prompt_text(rtl_code)
    return {
        "custom_id": custom_id,
        "method": "POST",
        "url": "/v1/responses",
        "body": {
            "model": "gpt-5",
            "input": [
                {"role": "system", "content": "You are a verification engineer expert in SystemVerilog Assertions."},
                {"role": "user", "content": prompt}
            ],
            "reasoning": {"effort": "medium"},
            "text": {"verbosity": "low"}
        }
    }

def prepare_batch_file(modules_data, batch_num):
    """Prepare a .jsonl batch file for OpenAI Batch API."""
    os.makedirs(BATCH_REQUESTS_DIR, exist_ok=True)
    batch_filename = os.path.join(BATCH_REQUESTS_DIR, f"batch_{batch_num}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.jsonl")
    
    with open(batch_filename, 'w') as f:
        for module_data in modules_data:
            request = create_batch_request(
                module_data['rtl_code'],
                module_data['module_name'],
                module_data['custom_id']
            )
            f.write(json.dumps(request) + '\n')
    
    print(f"Created batch file: {batch_filename}")
    return batch_filename

def upload_and_create_batch(client, batch_filename):
    """Upload batch file and create a batch job."""
    # Upload the file
    with open(batch_filename, 'rb') as f:
        batch_input_file = client.files.create(
            file=f,
            purpose="batch"
        )
    
    # Create the batch
    batch = client.batches.create(
        input_file_id=batch_input_file.id,
        endpoint="/v1/responses",
        completion_window="24h",
        metadata={
        "description": "SVA generation for Verilog modules from MetRex dataset"
    }
    )
    
    print(f"Batch created with ID: {batch.id}")
    return batch.id

def check_batch_status(client, batch_id):
    """Check the status of a batch job."""
    batch = client.batches.retrieve(batch_id)
    return batch.status, batch

def download_batch_results(client, batch):
    """Download and parse batch results."""
    if batch.status != "completed":
        print(f"Batch not completed. Status: {batch.status}")
        return None
    
    # Download output file
    output_file_id = batch.output_file_id
    content = client.files.content(output_file_id)
    
    results = []
    for line in content.text.strip().split('\n'):
        results.append(json.loads(line))
    
    return results

def process_batch_results(results, modules_metadata, processed_modules):
    """Process batch results and save module pairs."""
    for result in results:
        try:
            custom_id = result.get("custom_id")
            if not custom_id or custom_id not in modules_metadata:
                print(f"⚠️ Unknown or missing custom_id: {custom_id}")
                continue

            metadata = modules_metadata[custom_id]

            # --- Navigate into response body ---
            response = result.get("response", {})
            body = response.get("body", {})

            sva_code = None
            output = body.get("output", [])

            # Extract assistant text
            for item in output:
                if item.get("type") == "message" and isinstance(item.get("content"), list):
                    for content_item in item["content"]:
                        if content_item.get("type") == "output_text" and isinstance(content_item.get("text"), str):
                            sva_code = content_item["text"].strip()
                            break
                if sva_code:
                    break

            # Fallbacks
            if not sva_code:
                sva_code = body.get("output_text") or body.get("text")
                if isinstance(sva_code, dict):
                    sva_code = next((v for v in sva_code.values() if isinstance(v, str)), str(sva_code))
                if isinstance(sva_code, str):
                    sva_code = sva_code.strip()

            if not sva_code or not isinstance(sva_code, str):
                raise KeyError("No valid text field found in response body")

            # --- Write to dataset layout ---
            rtl_code = metadata["rtl_code"]
            module_name = metadata["module_name"]

            # Skip if we've already processed this RTL hash (e.g., from another batch)
            module_hash = metadata.get("module_hash")
            if module_hash and module_hash in processed_modules:
                print(f"↷ Skipping duplicate across batches: {module_name}")
                continue

            prompt_text = compute_prompt_text(rtl_code)

            meta_obj = {
                "source": "openai_batch",
                "model_used": body.get("model", "gpt-5"),
                "batch_id": result.get("id") or response.get("id"),
                "custom_id": custom_id,
                "module_name": module_name,
                "original_dataset": "scale-lab/MetRex",
                "prompt_hash": short_hash(prompt_text),
                "validation": {
                    "syntax_check": True,              # placeholder; no linting as requested
                    "compiles_with_sv_linter": False,  # placeholder
                    "num_assertions": count_assertions(sva_code),
                },
            }

            saved = write_dataset_sample(rtl_code, sva_code, meta_obj)

            # --- Mark as processed (by module hash) ---
            processed_modules[metadata["module_hash"]] = {
                "module_name": module_name,
                "saved_id": saved["id"],
                "saved_dir": saved["dir"],
                "processed_date": datetime.now().isoformat(),
                "custom_id": custom_id,
                "version": CURRENT_VERSION
            }

            print(f"✓ Processed: {module_name} -> {saved['id']}")

        except Exception as e:
            print(f"✗ Error processing result for {metadata.get('module_name', 'unknown')}: {e}")

    save_processed_modules(processed_modules)

def collect_modules_for_batch(dataset, processed_modules, batch_size):
    """Collect unprocessed modules for a batch."""
    modules_data = []
    modules_metadata = {}
    
    # Shuffle indices to get random modules
    indices = list(range(len(dataset)))
    random.shuffle(indices)
    
    for idx in indices:
        if len(modules_data) >= batch_size:
            break
        
        try:
            module = dataset[idx]
            rtl_code = get_rtl_field(module)
            
            # Check token limit
            estimated_tokens = estimate_tokens(rtl_code)
            if estimated_tokens > MAX_TOKENS:
                continue
            
            # Check if already processed
            module_hash = get_module_hash(rtl_code)
            if is_module_processed(module_hash, processed_modules):
                continue
            
            # Extract module name
            module_name = get_module_name(rtl_code)
            custom_id = f"{module_name}_{module_hash[:8]}"
            
            # Add to batch
            modules_data.append({
                'rtl_code': rtl_code,
                'module_name': module_name,
                'custom_id': custom_id,
                'module_hash': module_hash
            })
            
            modules_metadata[custom_id] = {
                'rtl_code': rtl_code,
                'module_name': module_name,
                'module_hash': module_hash,
                'dataset_index': idx
            }
            
        except Exception as e:
            print(f"Error processing module at index {idx}: {e}")
            continue
    
    return modules_data, modules_metadata

def main_batch_mode(num_batches=10):
    """Main function for batch processing mode."""
    # Get API key
    api_key = os.getenv('OPENAI_API_KEY')
    if not api_key:
        print("Error: OPENAI_API_KEY environment variable not set")
        exit(1)
    
    client = OpenAI(api_key=api_key)
    
    # Load dataset
    print("Loading MetRex dataset...")
    ds = load_dataset("scale-lab/MetRex", split="train")
    print(f"Dataset loaded with {len(ds)} modules")
    
    # Load processed modules
    processed_modules = load_processed_modules()
    print(f"Already processed: {len(processed_modules)} modules")
    
    # Process batches
    batch_ids = []
    all_metadata = {}
    
    for batch_num in range(num_batches):
        print(f"\n=== Preparing Batch {batch_num + 1}/{num_batches} ===")
        
        # Collect modules for this batch
        modules_data, modules_metadata = collect_modules_for_batch(
            ds, processed_modules, BATCH_SIZE
        )
        
        if not modules_data:
            print("No more unprocessed modules available")
            break
        
        print(f"Collected {len(modules_data)} modules for batch")
        
        # Prepare batch file
        batch_filename = prepare_batch_file(modules_data, batch_num)
        
        # Upload and create batch
        batch_id = upload_and_create_batch(client, batch_filename)
        batch_ids.append(batch_id)
        all_metadata[batch_id] = modules_metadata
    
    # Save batch tracking info
    batch_tracking = {
        'batch_ids': batch_ids,
        'metadata': all_metadata,
        'created_at': datetime.now().isoformat()
    }
    
    with open('batch_tracking.json', 'w') as f:
        json.dump(batch_tracking, f, indent=2)
    
    print(f"\n=== Created {len(batch_ids)} batches ===")
    print("Batch IDs saved to batch_tracking.json")
    print("\nTo check status and download results, run:")
    print("python generate_sva_batch.py --check-batches")

def check_and_download_batches():
    """Check status of batches and download completed results."""
    api_key = os.getenv('OPENAI_API_KEY')
    if not api_key:
        print("Error: OPENAI_API_KEY environment variable not set")
        exit(1)
    
    client = OpenAI(api_key=api_key)
    
    # Load batch tracking
    if not os.path.exists('batch_tracking.json'):
        print("No batch tracking file found")
        return
    
    with open('batch_tracking.json', 'r') as f:
        batch_tracking = json.load(f)
    
    processed_modules = load_processed_modules()
    
    for batch_id in batch_tracking['batch_ids']:
        print(f"\n=== Checking Batch {batch_id} ===")
        status, batch = check_batch_status(client, batch_id)
        print(f"Status: {status}")
        
        if status == "completed":
            print("Downloading results...")
            results = download_batch_results(client, batch)
            
            if results:
                modules_metadata = batch_tracking['metadata'][batch_id]
                process_batch_results(results, modules_metadata, processed_modules)
                print(f"Processed {len(results)} results")
        elif status == "failed":
            print(f"Batch failed: {batch}")
        elif status in ["validating", "in_progress", "finalizing"]:
            print("Batch still processing...")

def main_single_mode():
    """Original single-module generation mode for testing."""
    api_key = os.getenv('OPENAI_API_KEY')
    if not api_key:
        print("Error: OPENAI_API_KEY environment variable not set")
        exit(1)
    
    client = OpenAI(api_key=api_key)
    
    print("Loading MetRex dataset...")
    ds = load_dataset("scale-lab/MetRex", split="train")
    print(f"Dataset loaded with {len(ds)} modules")
    
    processed_modules = load_processed_modules()
    
    max_attempts = 100
    for _ in range(max_attempts):
        random_index = random.randint(0, len(ds) - 1)
        module = ds[random_index]
        
        try:
            rtl_code = get_rtl_field(module)
            module_hash = get_module_hash(rtl_code)
            if is_module_processed(module_hash, processed_modules):
                continue
            
            estimated_tokens = estimate_tokens(rtl_code)
            if estimated_tokens > MAX_TOKENS:
                continue
            
            module_name = get_module_name(rtl_code)
            print(f"Selected module: {module_name}")
            print(f"Estimated tokens: {estimated_tokens}")
            
            print("Generating SVA assertions...")
            prompt = compute_prompt_text(rtl_code)
            response = client.responses.create(
                model="gpt-5",
                input=[
                    {"role": "system", "content": "You are a verification engineer expert in SystemVerilog Assertions."},
                    {"role": "user", "content": prompt}
                ],
                reasoning={"effort": "medium"},
                text={"verbosity": "medium"}
            )
            sva_code = response.output_text
            
            # Save into dataset (staging)
            meta_obj = {
                "source": "single_mode",
                "model_used": "gpt-5",
                "module_name": module_name,
                "original_dataset": "scale-lab/MetRex",
                "prompt_hash": short_hash(prompt),
                "validation": {
                    "syntax_check": True,
                    "compiles_with_sv_linter": False,
                    "num_assertions": count_assertions(sva_code),
                },
            }
            saved = write_dataset_sample(rtl_code, sva_code, meta_obj)
            
            processed_modules[module_hash] = {
                'module_name': module_name,
                'saved_id': saved["id"],
                'saved_dir': saved["dir"],
                'processed_date': datetime.now().isoformat(),
                'version': CURRENT_VERSION
            }
            save_processed_modules(processed_modules)
            
            print("\nGeneration complete!")
            return
            
        except Exception as e:
            print(f"Error: {e}")
            continue
    
    print("Could not find an unprocessed module within attempt limit")

if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == "--check-batches":
        check_and_download_batches()
    elif len(sys.argv) > 1 and sys.argv[1] == "--single":
        main_single_mode()
    elif len(sys.argv) > 1 and sys.argv[1] == "--batch":
        num_batches = int(sys.argv[2]) if len(sys.argv) > 2 else 10
        main_batch_mode(num_batches)
    else:
        print("Usage:")
        print("  python generate_sva_batch.py --batch [num_batches]  # Create batch jobs")
        print("  python generate_sva_batch.py --check-batches        # Check and download results")
        print("  python generate_sva_batch.py --single               # Test single module")