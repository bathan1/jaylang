import pandas as pd
import numpy as np
import matplotlib.pyplot as plt

# ---------- Config ----------
CSV_FILE = "bench.csv"
BIN_SIZE = 100 # first 20, next 20, etc.

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

plt.figure(figsize=(18, 8))

plt.bar(
    x,
    grouped["backend_mean"],
    width=width,
    label="Backend",
    color="red",
    alpha=0.6
)

plt.bar(
    x,
    grouped["hybrid_mean"],
    width=width,
    label="Hybrid",
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

    delta_y = b * 0.55          # mid–upper bar
    delta_y = max(delta_y, 12) # never too close to bottom

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
plt.title("Hybrid vs Backend Solve Time (Order-Based Bins)")
plt.legend()
plt.tight_layout()
plt.xlim(-0.6, len(grouped) - 0.4)
plt.show()

