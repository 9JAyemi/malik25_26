import os
import random
from datasets import load_dataset
from openai import OpenAI
from dotenv import load_dotenv

# Load environment variables from .env file
load_dotenv()

# Configuration
MAX_TOKENS = 20000
CHARS_PER_TOKEN = 4  # Rough estimate: 1 token ≈ 4 characters

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
            # Extract module name (between 'module' and '(' or ';')
            module_decl = line.split('module ')[1]
            module_name = module_decl.split('(')[0].split(';')[0].strip()
            return module_name
    return "unknown_module"

def save_verilog_module(rtl_code, module_name):
    """Save Verilog module to a .v file in verilog_modules subfolder."""
    os.makedirs("verilog_modules", exist_ok=True)
    filename = f"verilog_modules/{module_name}.v"
    with open(filename, 'w') as f:
        f.write(rtl_code)
    print(f"Saved Verilog module to: {filename}")
    return filename

def generate_sva(rtl_code, api_key):
    """Generate SVA assertions using GPT-5 Responses API."""
    client = OpenAI(api_key=api_key)
    
    prompt = f"""Generate SVA assertions for the following verilog module. Make sure it has full coverage and checks all important signals and functions: 

{rtl_code}"""
    
    try:
        response = client.responses.create(
            model="gpt-5",
            input=prompt
        )
        return response.output_text
    except Exception as e:
        print(f"Error calling GPT-5 Responses API: {e}")
        exit(1)

def save_sva(sva_code, module_name):
    """Save SVA assertions to a .sv file."""
    filename = f"{module_name}.sv"
    with open(filename, 'w') as f:
        f.write(sva_code)
    print(f"Saved SVA assertions to: {filename}")
    return filename

def main():
    # Get API key from environment
    api_key = os.getenv('OPENAI_API_KEY')
    if not api_key:
        print("Error: OPENAI_API_KEY environment variable not set")
        exit(1)
    
    print("Loading MetRex dataset...")
    ds = load_dataset("scale-lab/MetRex", split="train")
    print(f"Dataset loaded with {len(ds)} modules")
    
    # Select a random module
    random_index = random.randint(0, len(ds) - 1)
    module = ds[random_index]
    print(f"Selected module at index {random_index}")
    
    # Get RTL code
    try:
        rtl_code = get_rtl_field(module)
    except KeyError as e:
        print(f"Error: {e}")
        exit(1)
    
    # Check token limit
    estimated_tokens = estimate_tokens(rtl_code)
    print(f"Estimated tokens: {estimated_tokens}")
    
    if estimated_tokens > MAX_TOKENS:
        print(f"Error: RTL code exceeds token limit ({estimated_tokens} > {MAX_TOKENS})")
        print("Skipping this module")
        exit(1)
    
    # Extract module name and save Verilog file
    module_name = get_module_name(rtl_code)
    print(f"Module name: {module_name}")
    save_verilog_module(rtl_code, module_name)
    
    # Generate SVA using GPT-5
    print("Generating SVA assertions with GPT-5...")
    sva_code = generate_sva(rtl_code, api_key)
    
    # Save SVA file
    save_sva(sva_code, module_name)
    
    print("\nGeneration complete!")

if __name__ == "__main__":
    main()