#!/usr/bin/env python3
# Distribution of leaf right-hand sides, reusing the verifier own row code.
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import verify_712_independent as v712

CERTIFICATE = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else HERE / "cert_leaves_tail.jsonl"

rows = []
mult_total = 0
dens = set()
with CERTIFICATE.open(encoding="utf-8") as handle:
    for line in handle:
        rec = json.loads(line)
        if "meta" in rec:
            continue
        cell, path, rhs, surplus = v712.verify_leaf(rec)
        rows.append(rhs)
        mult_total += len(rec["lam"])
        for _, m in rec["lam"]:
            dens.add(Q(m).denominator)

rows.sort(reverse=True)
distinct = sorted(set(rows), reverse=True)
print("leaves                 ", len(rows))
print("multiplier entries     ", mult_total)
print("max multiplier denom   ", max(dens))
print("worst rhs              ", distinct[0], "=", float(distinct[0]))
print("second-worst rhs       ", distinct[1], "=", float(distinct[1]))
print("third-worst rhs        ", distinct[2], "=", float(distinct[2]))
print("leaves at worst        ", rows.count(distinct[0]))
print("gap worst-second       ", distinct[0] - distinct[1], "=", float(distinct[0] - distinct[1]))
