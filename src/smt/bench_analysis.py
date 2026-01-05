import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# ---------- Config ----------
CSV_FILE = "bench.csv"
BIN_SIZE = 200
OUTPUT_PATH = Path("../../bluejay-language/docs/public/difference_binned.png")

# ---------- Load ----------
df = pd.read_csv(CSV_FILE)

df["id"] = pd.to_numeric(df["id"])
df["hybrid_time"] = pd.to_numeric(df["hybrid_time"])
df["backend_only_time"] = pd.to_numeric(df["backend_only_time"])

# ---------- Order-based binning ----------
# Ensure original order by formula id
df = df.sort_values("id").reset_index(drop=True)

df["bin_index"] = df.index // BIN_SIZE

# ---------- Aggregate per bin ----------
grouped = (
    df
    .groupby("bin_index")
    .agg(
        backend_mean=("backend_only_time", "mean"),
        hybrid_mean=("hybrid_time", "mean"),
        f_min=("id", "min"),
        f_max=("id", "max"),
    )
    .reset_index(drop=True)
)

grouped["delta"] = grouped["hybrid_mean"] - grouped["backend_mean"]

# ---------- Sort bins by backend runtime ----------
grouped = grouped.sort_values("backend_mean").reset_index(drop=True)

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
    grouped["backend_mean"],
    width=width,
    label="Z3",
    color="red",
    alpha=0.6
)

plt.bar(
    x,
    grouped["hybrid_mean"],
    width=width,
    label="Mini",
    color="green",
    alpha=0.6
)

# ---------- Annotations ----------
for i, row in grouped.iterrows():
    b = row["backend_mean"]
    h = row["hybrid_mean"]
    d = row["delta"]

    # Bar-top labels
    plt.text(i, b, f"{b:.0f}µs", ha="center", va="bottom", fontsize=8)
    plt.text(i, h, f"{h:.0f}µs", ha="center", va="bottom", fontsize=8)

    # Delta inside backend bar
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
plt.xlabel("Formula buckets (fixed-size, sorted by backend runtime)")
plt.ylabel("Mean solve time (µs)")
plt.title("Mini vs Z3 Solve Time (Order-Based Bins)")
plt.legend()

plt.margins(x=0)
plt.xlim(-0.6, len(grouped) - 0.4)
plt.tight_layout()

# ---------- Save ----------
OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
plt.savefig(OUTPUT_PATH, dpi=200, bbox_inches="tight")

# ---------- Show ----------
plt.show()

