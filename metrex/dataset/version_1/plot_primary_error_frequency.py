import pandas as pd
import matplotlib.pyplot as plt

# ============================
# Config
# ============================
INPUT_CSV = "syntax_results/visual_data/error_catalog.csv"
OUT_PNG = "syntax_results/visual_data/primary_error_frequency.png"

# ============================
# Load data
# ============================
df = pd.read_csv(INPUT_CSV)

# Keep valid primary error codes
df = df[df["primary_code"].notna() & (df["primary_code"] != "")]

# Count how many IDs map to each primary error
freq = (
    df.groupby("primary_code")["id"]
      .nunique()
      .sort_values(ascending=False)
)

# ============================
# Plot
# ============================
plt.figure(figsize=(12, 6))

plt.bar(freq.index, freq.values)

plt.xlabel("Primary VERI Error Code")
plt.ylabel("Number of IDs")
plt.title("Frequency of Primary Jasper VERI-* Errors Across IDs")

plt.xticks(rotation=45, ha="right")

plt.tight_layout()
plt.savefig(OUT_PNG, dpi=300)
plt.close()

print(f"Saved plot to {OUT_PNG}")
