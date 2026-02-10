import pandas as pd
import matplotlib.pyplot as plt

# ============================
# Config
# ============================
INPUT_CSV = "syntax_results/error_catalog.csv"
OUT_PNG = "syntax_results/primary_error_by_id.png"

# ============================
# Load data
# ============================
df = pd.read_csv(INPUT_CSV)

# Keep only rows with a primary error code
df = df[df["primary_code"].notna() & (df["primary_code"] != "")]

# Sort by ID (numeric-friendly)
df["id_num"] = df["id"].astype(int)
df = df.sort_values("id_num")

# Map each primary error code to a numeric index
codes = sorted(df["primary_code"].unique())
code_to_idx = {c: i for i, c in enumerate(codes)}
df["code_idx"] = df["primary_code"].map(code_to_idx)

# ============================
# Plot
# ============================
plt.figure(figsize=(14, 6))

plt.bar(
    df["id_num"],
    df["code_idx"],
)

plt.yticks(
    range(len(codes)),
    codes
)

plt.xlabel("ID")
plt.ylabel("Primary Error Code")
plt.title("Primary Jasper VERI-* Error Code per ID")

plt.tight_layout()
plt.savefig(OUT_PNG, dpi=300)
plt.close()

print(f"Saved plot to {OUT_PNG}")
