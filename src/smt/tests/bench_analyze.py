import sys
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

BIN_SIZE = int(sys.argv[1]) or 10
OUTPUT_PATH = Path("../../../bluejay-language/docs/public/difference_binned.png")

df = pd.read_csv(sys.stdin)

# Attempt numeric conversion
id_numeric = pd.to_numeric(df["id"], errors="coerce")

# Find bad rows
bad_rows = df[id_numeric.isna()]

if not bad_rows.empty:
    print("ERROR: Non-numeric 'id' values detected:", file=sys.stderr)
    for idx, row in bad_rows.iterrows():
        print(f"\nRow {idx}:", file=sys.stderr)
        print(row.to_string(), file=sys.stderr)
    sys.exit(1)

# Assign only after validation
df["id"] = id_numeric
df["blue3_time"] = pd.to_numeric(df["blue3_time"])
df["z3_only_time"] = pd.to_numeric(df["z3_only_time"])

# ---------- Order-based binning ----------
# Ensure original order by formula id
df = df.sort_values("id").reset_index(drop=True)

df["bin_index"] = df.index // BIN_SIZE

# ---------- Aggregate per bin ----------
grouped = (
    df
    .groupby("bin_index")
    .agg(
        z3_only_mean=("z3_only_time", "mean"),
        blue3_mean=("blue3_time", "mean"),
        f_min=("id", "min"),
        f_max=("id", "max"),
    )
    .reset_index(drop=True)
)

grouped["delta"] = grouped["blue3_mean"] - grouped["z3_only_mean"]

# ---------- Sort bins by z3 runtime ----------
grouped = grouped.sort_values("z3_only_mean").reset_index(drop=True)

# ---------- Labels ----------
labels = [
    f"F{int(row.f_min)}–F{int(row.f_max)}"
    for _, row in grouped.iterrows()
]

# ---------- Plot ----------
x = np.arange(len(grouped))
width = 0.6

plt.figure(figsize=(16, 8))

plt.bar(
    x,
    grouped["z3_only_mean"],
    width=width,
    label="Z3",
    color="red",
    alpha=0.6
)

plt.bar(
    x,
    grouped["blue3_mean"],
    width=width,
    label="Blue3",
    color="green",
    alpha=0.6
)

# ---------- Annotations ----------
for i, row in grouped.iterrows():
    b = row["z3_only_mean"]
    h = row["blue3_mean"]
    d = row["delta"]

    # Bar-top labels
    plt.text(i, b, f"{b:.0f}µs", ha="center", va="bottom", fontsize=8)
    plt.text(i, h, f"{h:.0f}µs", ha="center", va="bottom", fontsize=8)

    # Delta inside z3 bar
    delta_y = b * 0.55
    delta_y = max(delta_y, 12)

    plt.text(
        i,
        delta_y,
        f"Δ {d:+.0f}µs",
        ha="center",
        va="center",
        fontsize=9,
        fontweight="bold",
        color="black"
    )

# ---------- Axes ----------
plt.xticks(x, labels, rotation=45, ha="right")
plt.xlabel("Formula buckets (fixed-size, sorted by z3 runtime)")
plt.ylabel("Mean solve time (µs)")
plt.title("Blue3 vs Z3 Solve Time (Order-Based Bins)")
plt.legend()

plt.margins(x=0)
plt.xlim(-0.6, len(grouped) - 0.4)
plt.tight_layout()

# ---------- Save ----------
OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
plt.savefig(OUTPUT_PATH, dpi=200, bbox_inches="tight")

# ---------- Show ----------
plt.show()

