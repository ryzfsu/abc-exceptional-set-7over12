#!/usr/bin/env python3
"""Compute the exact uniform RHS-relaxation constant of the 7/12 certificate."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "certificate",
        nargs="?",
        default=str(Path(__file__).resolve().with_name("cert_leaves_tail.jsonl")),
    )
    args = parser.parse_args()

    maximum = Fraction(0)
    maximum_rows = 0
    maximizing_cell = None
    maximizing_depth = None
    leaves = 0
    for line in Path(args.certificate).open(encoding="utf-8"):
        record = json.loads(line)
        if "cell" not in record:
            continue
        leaves += 1
        total = sum((Fraction(value) for _, value in record["lam"]), Fraction(0))
        maximum_rows = max(maximum_rows, len(record["lam"]))
        if total > maximum:
            maximum = total
            maximizing_cell = record["cell"]
            maximizing_depth = len(record["path"])

    print(f"leaves={leaves}")
    print(f"max_sum_lambda={maximum}")
    print(f"max_nonzero_rows={maximum_rows}")
    print(f"maximizing_cell={maximizing_cell}")
    print(f"maximizing_path_depth={maximizing_depth}")
    print("relaxed_conclusion: D <= 7/12 + (18/7)*rho")


if __name__ == "__main__":
    main()
