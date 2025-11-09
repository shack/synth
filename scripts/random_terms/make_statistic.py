import json
import tyro
import os
import matplotlib.pyplot as plt
import numpy as np
from dataclasses import dataclass
from pathlib import Path

def plot(file_name, freqs):
    plt.rcParams.update({ "figure.figsize": (6.5, 3.6), "font.family": "sans-serif", "font.sans-serif": ["Helvetica", "Arial"], "axes.labelsize": 12, "axes.titlesize": 10, "xtick.labelsize": 10, "ytick.labelsize": 10, "axes.linewidth": 0.8, "savefig.dpi": 600})

    fig, ax = plt.subplots()
    values = np.array(sorted(freqs.keys()))
    counts = np.array([freqs[v] for v in values])

    ax.bar(values, counts, width=0.8, color="#4C72B0", edgecolor="black", linewidth=0.1)
    ax.set_xlabel("Size Difference (RuleGen - Ruler)")
    ax.set_ylabel("Frequency")

    #ax.spines['top'].set_visible(False)
    #ax.spines['right'].set_visible(False)
    ax.grid(axis='y', linestyle=':', linewidth=0.8, alpha=1)

    fig.tight_layout(pad=0.2)
    fig.savefig(f"{file_name}.pdf")
    fig.savefig(f"{file_name}.png", dpi=600)

    plt.close()

@dataclass(frozen=True)
class Settings:
    folder_path: str = "../../terms/random"

    separate: bool = True

    def exec(self):
        folder = Path(f"{self.folder_path}")
        freqs = {}
        for file in folder.rglob("*"):
            if file.suffix == ".json" and "rewritten" in file.name:
                with open(file, "r") as f:
                    data = json.load(f)
                if self.separate:
                    freqs = {}
                for term in data:
                    freqs[term["rewritten_size"] - term["egg_size"]] = freqs.get(term["rewritten_size"] - term["egg_size"], 0) + 1
                if self.separate:
                    plot(os.path.splitext(file.name)[0][:-10], freqs)
        if not self.separate:
            plot("Histogram", freqs)

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()