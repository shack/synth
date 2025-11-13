import json
import tyro
import os
import matplotlib.pyplot as plt
import numpy as np
from dataclasses import dataclass
from pathlib import Path

def plot(file_name, set1_name, set2_name, set1_time, set2_time, freqs):
    plt.rcParams.update({ "figure.figsize": (6.5, 3.6), "font.family": "sans-serif", "font.sans-serif": ["Helvetica", "Arial"], "axes.labelsize": 12, "axes.titlesize": 10, "xtick.labelsize": 10, "ytick.labelsize": 10, "axes.linewidth": 0.8, "savefig.dpi": 600})

    fig, ax = plt.subplots()
    values = np.array(sorted(freqs.keys()))
    counts = np.array([freqs[v] for v in values])

    ax.bar(values, counts, width=0.8, color="#4C72B0", edgecolor="black", linewidth=0.1)
    ax.set_xlabel(f"Size Difference ({set1_name} - {set2_name})")
    ax.set_ylabel("Frequency")
    ax.set_title(f"{set1_name} ({set1_time}) Vs. {set2_name} ({set2_time})")

    #ax.spines['top'].set_visible(False)
    #ax.spines['right'].set_visible(False)
    ax.grid(axis='y', linestyle=':', linewidth=0.8, alpha=1)

    fig.tight_layout(pad=0.2)
    fig.savefig(f"{file_name}.pdf")
    #fig.savefig(f"{file_name}.png", dpi=600)

    plt.close()

@dataclass(frozen=True)
class Settings:
    folder_path: str = "../../terms/random"

    separate: bool = True

    def exec(self):
        folder = Path(f"{self.folder_path}")
        freqs = {}
        for file in folder.rglob("*"):
            if file.suffix == ".json" and "_" in file.name:
                with open(file, "r") as f:
                    data = json.load(f)
                    terms = data["terms"]
                if self.separate:
                    freqs = {}
                for term in terms:
                    freqs[term["set1_size"] - term["set2_size"]] = freqs.get(term["set1_size"] - term["set2_size"], 0) + 1
                if self.separate:
                    plot(os.path.splitext(file.name)[0], data["set1"], data["set2"], data["set1_time"], data["set2_time"], freqs)
        if not self.separate:
            plot("Histogram", freqs)

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()