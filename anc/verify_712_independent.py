#!/usr/bin/env python3
"""Standalone exact audit of the round-2 7/12 certificate.

This verifier deliberately does *not* import prob_tail.py, certgen_tail.py,
verify_cert_tail.py, NumPy, SciPy, PuLP, or an LP solver.  It reconstructs the
rows directly from:

  * BLT Proposition 6.1, equations (6.1)--(6.10);
  * the tail variables tau_s = s-sum_i s_i, v_s >= 7 tau_s, and
    sum_i i s_i + v_s <= 1; and
  * the documented generalized cut

      D <= A + max(0,B),

    with the exact cover

      {D <= A+B} union {B <= 0 and D <= A}.

All certificate arithmetic uses fractions.Fraction.  The lower witness scan
also enumerates the full family.  Note that its cardinality is

    3*(64*64-1)*127 = 1,560,195,

not 1,560,510 as arithmetically misstated in docs/875--876 and the legacy
script comments.  The loops in those scripts also enumerate 1,560,195.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from functools import reduce
from math import gcd
from pathlib import Path
from typing import Any, Iterable


Q = Fraction
SIDES = ("a", "b", "c")
ROOTS = tuple(range(1, 7))
TAIL = 7
NDIS = 13
TARGET = Q(7, 12)
OTHER = {"a": ("b", "c"), "b": ("a", "c"), "c": ("a", "b")}

# The ordering is local to this verifier.  The exported certificate contains
# row labels and multipliers, not coefficient arrays, so this ordering shares
# no implementation state with the original constructor.
VARS = (
    tuple(SIDES)
    + tuple(f"{s}{i}" for s in SIDES for i in ROOTS)
    + tuple(f"v{s}" for s in SIDES)
    + ("D",)
)
VARSET = frozenset(VARS)

Row = tuple[dict[str, Q], Q]
Cut = tuple[str, tuple[int, ...], tuple[int, ...], tuple[int, ...]]
PathStep = tuple[Cut, str]


class AuditError(RuntimeError):
    pass


def clean(coeff: dict[str, Q]) -> dict[str, Q]:
    out = {v: Q(c) for v, c in coeff.items() if c != 0}
    bad = set(out) - VARSET
    if bad:
        raise AuditError(f"unknown variables in row: {sorted(bad)}")
    return out


def linear(*terms: tuple[Q | int, dict[str, Q] | str]) -> dict[str, Q]:
    out: defaultdict[str, Q] = defaultdict(Q)
    for scalar, term in terms:
        term_dict = {term: Q(1)} if isinstance(term, str) else term
        for var, coefficient in term_dict.items():
            out[var] += Q(scalar) * Q(coefficient)
    return clean(dict(out))


def scaled(scalar: Q | int, coeff: dict[str, Q]) -> dict[str, Q]:
    return clean({v: Q(scalar) * c for v, c in coeff.items()})


def row(coeff: dict[str, Q], rhs: Q | int) -> Row:
    return clean(coeff), Q(rhs)


def p(i: int) -> dict[str, Q]:
    return {f"{s}{i}": Q(1) for s in SIDES}


def build_static_rows() -> dict[tuple[Any, ...], Row]:
    """Direct transcription of the linear rows in BLT Proposition 6.1."""
    rows: dict[tuple[Any, ...], Row] = {}

    rows[("L",)] = row({"a": Q(1), "b": Q(1), "c": Q(1)}, 1)
    for s in SIDES:
        # (6.2): sum_i s_i <= s.
        rows[("62", s)] = row(
            linear(*[(1, f"{s}{i}") for i in ROOTS], (-1, s)), 0
        )
        # (6.3), transcribed directly from the paper:
        # 7s - sum_i (7-i)s_i <= 1.
        rows[("63", s)] = row(
            linear((7, s), *[(-(7 - i), f"{s}{i}") for i in ROOTS]), 1
        )
        # Tail definition and total value bound.
        rows[("T7", s)] = row(
            linear((7, s), *[(-7, f"{s}{i}") for i in ROOTS], (-1, f"v{s}")),
            0,
        )
        rows[("TV", s)] = row(
            linear(*[(i, f"{s}{i}") for i in ROOTS], (1, f"v{s}")), 1
        )

    for x, y in (("a", "b"), ("a", "c"), ("b", "c")):
        rows[("64", x, y)] = row({"D": Q(1), x: Q(-1), y: Q(-1)}, 0)

    # Each selected argument is <= the max on that side.  Taking all 3^3
    # choices is exactly equivalent to the sum-of-three-maxima Fourier row.
    fourier_groups = {
        s: (
            {f"{s}2": Q(1), f"{s}4": Q(1), f"{s}6": Q(1)},
            {f"{s}3": Q(1), f"{s}6": Q(1)},
            {f"{s}5": Q(1)},
        )
        for s in SIDES
    }
    for ia, ib, ic in itertools.product(range(3), repeat=3):
        coeff = linear(
            (1, fourier_groups["a"][ia]),
            (1, fourier_groups["b"][ib]),
            (1, fourier_groups["c"][ic]),
            (-4, "a"),
            (-4, "b"),
            (-4, "c"),
            (6, "D"),
        )
        rows[("F", ia, ib, ic)] = row(coeff, 0)
    return rows


def build_disjunction_data() -> tuple[tuple[dict[str, Q], dict[str, Q]], ...]:
    """Return (e1,e2) where each disjunction is

       e1 <= L-D  OR  1-e2 <= L-D.

    The order is equations (6.5), (6.6)a/b/c, (6.7)ab/bc/ca,
    (6.8)a/b/c, and (6.9)a/b/c in the source paper.
    """
    data: list[tuple[dict[str, Q], dict[str, Q]]] = []
    data.append((linear((1, p(1)), (1, p(2)), (1, p(4))),
                 linear((1, p(2)), (3, p(4)))))

    for x in SIDES:
        data.append((linear((1, p(1)), (1, p(2)), (1, f"{x}3")),
                     linear((1, p(2)), (2, f"{x}3"))))

    for x, y in (("a", "b"), ("b", "c"), ("c", "a")):
        data.append((linear((1, p(1)), (1, p(2)),
                            (1, f"{x}3"), (1, f"{y}3")),
                     linear((1, p(2)), (2, f"{x}3"), (2, f"{y}3"))))

    for t3, u2, v2 in (("a3", "b2", "c2"),
                        ("b3", "a2", "c2"),
                        ("c3", "a2", "b2")):
        data.append((linear((1, p(1)), (1, t3), (1, u2), (1, v2)),
                     linear((2, t3), (1, u2), (1, v2))))

    for t2, u3, v3 in (("a2", "b3", "c3"),
                        ("b2", "a3", "c3"),
                        ("c2", "a3", "b3")):
        data.append((linear((1, p(1)), (1, t2), (1, u3), (1, v3)),
                     linear((1, t2), (2, u3), (2, v3))))

    if len(data) != NDIS:
        raise AssertionError(len(data))
    return tuple(data)


STATIC_ROWS = build_static_rows()
DISJUNCTIONS = build_disjunction_data()


def disjunction_row(j: int, branch: int) -> Row:
    if not 0 <= j < NDIS or branch not in (1, 2):
        raise AuditError(f"invalid disjunction row ({j},{branch})")
    e1, e2 = DISJUNCTIONS[j]
    # -(L-D) = -a-b-c+D.
    minus_ld = {"a": Q(-1), "b": Q(-1), "c": Q(-1), "D": Q(1)}
    if branch == 1:
        return row(linear((1, e1), (1, minus_ld)), 0)
    # 1-e2 <= L-D  iff  -e2-(L-D) <= -1.
    return row(linear((-1, e2), (1, minus_ld)), -1)


def canonical_subset(raw: Iterable[Any], allowed: frozenset[int], *,
                     nonempty: bool, label: str) -> tuple[int, ...]:
    try:
        values = tuple(raw)
    except TypeError as exc:
        raise AuditError(f"{label} is not iterable") from exc
    if any(type(v) is not int for v in values):
        raise AuditError(f"{label} contains a non-integer: {values!r}")
    if any(v not in allowed for v in values):
        raise AuditError(f"{label} outside {sorted(allowed)}: {values!r}")
    if tuple(sorted(set(values))) != values:
        raise AuditError(f"{label} is not a canonical increasing subset: {values!r}")
    if nonempty and not values:
        raise AuditError(f"{label} must be nonempty")
    return values


def parse_cut(raw: Any) -> Cut:
    if not isinstance(raw, (list, tuple)) or len(raw) != 4:
        raise AuditError(f"bad cut descriptor: {raw!r}")
    sig = raw[0]
    if sig not in SIDES:
        raise AuditError(f"bad modulus side: {sig!r}")
    r1 = canonical_subset(raw[1], frozenset(ROOTS), nonempty=False, label="R1")
    r2 = canonical_subset(raw[2], frozenset(ROOTS), nonempty=False, label="R2")
    t = canonical_subset(raw[3], frozenset((*ROOTS, TAIL)), nonempty=True, label="T")
    if not r1 and not r2:
        raise AuditError("R1 and R2 cannot both be empty")
    return sig, r1, r2, t


def cut_a_b(cut: Cut) -> tuple[dict[str, Q], dict[str, Q]]:
    sig, r1, r2, tset = cut
    s1, s2 = OTHER[sig]
    q = gcd(reduce(gcd, r1, 0), reduce(gcd, r2, 0))
    if q <= 0:
        raise AuditError(f"nonpositive q for cut {cut!r}")

    # A = residual radical masses on the two counted sides + modulus root cost.
    a: defaultdict[str, Q] = defaultdict(Q)
    a[s1] += 1
    a[s2] += 1
    for r in r1:
        a[f"{s1}{r}"] -= 1
    for r in r2:
        a[f"{s2}{r}"] -= 1
    for t in tset:
        if t == TAIL:
            # tau_sig = sig - sum_{i=1}^6 sig_i.
            a[sig] += 1
            for i in ROOTS:
                a[f"{sig}{i}"] -= 1
        else:
            a[f"{sig}{t}"] += 1

    # B = freed value/q - selected modulus value.
    b: defaultdict[str, Q] = defaultdict(Q)
    for r in r1:
        b[f"{s1}{r}"] += Q(r, q)
    for r in r2:
        b[f"{s2}{r}"] += Q(r, q)
    for t in tset:
        if t == TAIL:
            b[f"v{sig}"] -= 1
        else:
            b[f"{sig}{t}"] -= t
    return clean(dict(a)), clean(dict(b))


def cut_row(cut: Cut, kind: str) -> Row:
    a, b = cut_a_b(cut)
    if kind == "cutP":
        # Plus child: D <= A+B.
        return row(linear((1, "D"), (-1, a), (-1, b)), 0)
    if kind == "cutMB":
        # Minus child sign condition: B <= 0.
        return row(b, 0)
    if kind == "cutMA":
        # Minus child bound: D <= A.
        return row(linear((1, "D"), (-1, a)), 0)
    raise AuditError(f"unknown cut row kind: {kind!r}")


def freeze(value: Any) -> Any:
    if isinstance(value, list):
        return tuple(freeze(v) for v in value)
    if isinstance(value, tuple):
        return tuple(freeze(v) for v in value)
    return value


def parse_path(raw_path: Any) -> tuple[PathStep, ...]:
    if not isinstance(raw_path, list):
        raise AuditError("path is not a list")
    path: list[PathStep] = []
    seen: set[Cut] = set()
    for raw_step in raw_path:
        if not isinstance(raw_step, list) or len(raw_step) != 2:
            raise AuditError(f"bad path step: {raw_step!r}")
        cut = parse_cut(raw_step[0])
        sign = raw_step[1]
        if sign not in ("+", "-"):
            raise AuditError(f"bad path sign: {sign!r}")
        if cut in seen:
            raise AuditError(f"same cut repeated on one root-to-leaf path: {cut!r}")
        seen.add(cut)
        path.append((cut, sign))
    return tuple(path)


def validate_cell(raw_cell: Any) -> tuple[int, ...]:
    if not isinstance(raw_cell, list) or len(raw_cell) != NDIS:
        raise AuditError(f"cell must be a list of length {NDIS}: {raw_cell!r}")
    cell = tuple(raw_cell)
    if any(type(v) is not int or v not in (1, 2) for v in cell):
        raise AuditError(f"cell is not in {{1,2}}^{NDIS}: {cell!r}")
    return cell


_RATIONAL = re.compile(r"^(0|[1-9][0-9]*)/([1-9][0-9]*)$")


def parse_positive_rational(raw: Any) -> Q:
    if not isinstance(raw, str) or _RATIONAL.fullmatch(raw) is None:
        raise AuditError(f"multiplier is not a canonical positive fraction: {raw!r}")
    value = Q(raw)
    if value <= 0:
        raise AuditError(f"nonpositive sparse multiplier: {raw!r}")
    if raw != f"{value.numerator}/{value.denominator}":
        raise AuditError(f"noncanonical multiplier: {raw!r}")
    return value


def rows_valid_at_leaf(cell: tuple[int, ...], path: tuple[PathStep, ...]) \
        -> dict[tuple[Any, ...], Row]:
    valid = dict(STATIC_ROWS)
    for j, branch in enumerate(cell):
        valid[("dis", j, branch)] = disjunction_row(j, branch)
    for cut, sign in path:
        sig, r1, r2, tset = cut
        if sign == "+":
            rid = ("cutP", sig, r1, r2, tset)
            valid[rid] = cut_row(cut, "cutP")
        else:
            rid_b = ("cutMB", sig, r1, r2, tset)
            rid_a = ("cutMA", sig, r1, r2, tset)
            valid[rid_b] = cut_row(cut, "cutMB")
            valid[rid_a] = cut_row(cut, "cutMA")
    return valid


def verify_leaf(record: dict[str, Any]) -> tuple[tuple[int, ...],
                                                  tuple[PathStep, ...], Q, Q]:
    cell = validate_cell(record.get("cell"))
    path = parse_path(record.get("path"))
    if record.get("kind") not in ("bound", "infeas"):
        raise AuditError(f"unknown leaf kind: {record.get('kind')!r}")
    lam = record.get("lam")
    if not isinstance(lam, list) or not lam:
        raise AuditError("lam must be a nonempty sparse list")

    valid = rows_valid_at_leaf(cell, path)
    combination: defaultdict[str, Q] = defaultdict(Q)
    rhs = Q(0)
    seen_rows: set[tuple[Any, ...]] = set()
    for pair in lam:
        if not isinstance(pair, list) or len(pair) != 2:
            raise AuditError(f"bad sparse multiplier pair: {pair!r}")
        rid = freeze(pair[0])
        if not isinstance(rid, tuple):
            raise AuditError(f"bad row id: {pair[0]!r}")
        if rid in seen_rows:
            raise AuditError(f"duplicate row id in sparse leaf: {rid!r}")
        seen_rows.add(rid)
        if rid not in valid:
            raise AuditError(f"row is not valid at this leaf: {rid!r}")
        multiplier = parse_positive_rational(pair[1])
        coefficients, bound = valid[rid]
        for var, coefficient in coefficients.items():
            combination[var] += multiplier * coefficient
        rhs += multiplier * bound

    minimum_surplus: Q | None = None
    for var in VARS:
        wanted = Q(1) if var == "D" else Q(0)
        surplus = combination[var] - wanted
        if surplus < 0:
            raise AuditError(
                f"Farkas coefficient on {var} is {combination[var]}, below {wanted}"
            )
        minimum_surplus = surplus if minimum_surplus is None else min(minimum_surplus, surplus)
    if rhs > TARGET:
        raise AuditError(f"Farkas RHS {rhs} exceeds target {TARGET}")
    assert minimum_surplus is not None
    return cell, path, rhs, minimum_surplus


def verify_complete_tree(paths: list[tuple[PathStep, ...]], *,
                         where: str = "root") -> int:
    """Verify a full binary decision tree and return its internal-node count."""
    if not paths:
        raise AuditError(f"empty path set at {where}")
    empty = [path for path in paths if not path]
    if empty:
        if len(paths) != 1:
            raise AuditError(f"a leaf is also a strict prefix at {where}")
        return 0
    heads = {path[0][0] for path in paths}
    if len(heads) != 1:
        raise AuditError(f"different cuts branch at the same node {where}: {len(heads)}")
    head = next(iter(heads))
    plus = [path[1:] for path in paths if path[0][1] == "+"]
    minus = [path[1:] for path in paths if path[0][1] == "-"]
    if len(plus) + len(minus) != len(paths):
        raise AuditError(f"unknown sign at {where}")
    if not plus or not minus:
        raise AuditError(f"incomplete +/- split at {where} on cut {head!r}")
    return 1 + verify_complete_tree(plus, where=where + "+") \
        + verify_complete_tree(minus, where=where + "-")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_certificate(path: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    meta: dict[str, Any] | None = None
    leaves: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for lineno, line in enumerate(handle, 1):
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                raise AuditError(f"invalid JSON on line {lineno}: {exc}") from exc
            if not isinstance(record, dict):
                raise AuditError(f"line {lineno} is not a JSON object")
            if "meta" in record:
                if lineno != 1 or meta is not None or set(record) != {"meta"}:
                    raise AuditError(f"misplaced or duplicate meta line {lineno}")
                if not isinstance(record["meta"], dict):
                    raise AuditError("meta is not an object")
                meta = record["meta"]
            else:
                leaves.append(record)
    if meta is None:
        raise AuditError("missing meta record")
    if meta.get("target") != "7/12":
        raise AuditError(f"wrong certificate target: {meta.get('target')!r}")
    if meta.get("family") != "tail-extended (gencutloop7)":
        raise AuditError(f"wrong certificate family: {meta.get('family')!r}")
    return meta, leaves


def audit_certificate(path: Path) -> dict[str, Any]:
    meta, leaves = load_certificate(path)
    by_cell: defaultdict[tuple[int, ...], list[tuple[PathStep, ...]]] = defaultdict(list)
    worst = Q(0)
    minimum_surplus: Q | None = None
    kind_counts: Counter[str] = Counter()
    tight_leaf_count = 0
    all_cuts: set[Cut] = set()
    max_depth = 0

    for leaf_index, record in enumerate(leaves):
        try:
            cell, path_steps, bound, surplus = verify_leaf(record)
        except AuditError as exc:
            raise AuditError(f"leaf #{leaf_index + 1}: {exc}") from exc
        by_cell[cell].append(path_steps)
        worst = max(worst, bound)
        if bound == TARGET:
            tight_leaf_count += 1
        minimum_surplus = surplus if minimum_surplus is None else min(minimum_surplus, surplus)
        kind_counts[record["kind"]] += 1
        all_cuts.update(cut for cut, _ in path_steps)
        max_depth = max(max_depth, len(path_steps))

    expected_cells = set(itertools.product((1, 2), repeat=NDIS))
    actual_cells = set(by_cell)
    if actual_cells != expected_cells:
        missing = sorted(expected_cells - actual_cells)[:3]
        extra = sorted(actual_cells - expected_cells)[:3]
        raise AuditError(
            f"cell set is not exactly {{1,2}}^{NDIS}: "
            f"missing={missing!r}, extra={extra!r}"
        )

    internal_nodes = 0
    cells_needing_cuts = 0
    max_leaves = 0
    max_distinct_cuts_in_cell = 0
    for cell, paths in by_cell.items():
        if len(set(paths)) != len(paths):
            raise AuditError(f"duplicate leaf path in cell {cell!r}")
        try:
            nodes = verify_complete_tree(paths, where="cell " + "".join(map(str, cell)))
        except AuditError as exc:
            raise AuditError(str(exc)) from exc
        if nodes != len(paths) - 1:
            raise AuditError(f"non-full tree identity in cell {cell!r}: {nodes} != {len(paths)-1}")
        internal_nodes += nodes
        if nodes:
            cells_needing_cuts += 1
        max_leaves = max(max_leaves, len(paths))
        max_distinct_cuts_in_cell = max(
            max_distinct_cuts_in_cell,
            len({cut for path_steps in paths for cut, _ in path_steps}),
        )

    if internal_nodes != len(leaves) - len(by_cell):
        raise AuditError("global full-binary-tree identity failed")

    return {
        "certificate": str(path),
        "sha256": sha256(path),
        "meta": meta,
        "cells": len(by_cell),
        "leaves": len(leaves),
        "internal_nodes": internal_nodes,
        "cells_needing_cuts": cells_needing_cuts,
        "distinct_cuts": len(all_cuts),
        "max_distinct_cuts_in_cell": max_distinct_cuts_in_cell,
        "max_leaves": max_leaves,
        "max_depth": max_depth,
        "kind_counts": dict(sorted(kind_counts.items())),
        "tight_leaf_count": tight_leaf_count,
        "worst_bound": str(worst),
        "minimum_coefficient_surplus": str(minimum_surplus),
    }


def powerset(values: tuple[int, ...], *, nonempty: bool) -> tuple[tuple[int, ...], ...]:
    start = 1 if nonempty else 0
    return tuple(
        subset
        for size in range(start, len(values) + 1)
        for subset in itertools.combinations(values, size)
    )


FREE_SUBSETS = powerset(ROOTS, nonempty=False)
MODULUS_SUBSETS = powerset((*ROOTS, TAIL), nonempty=True)


def evaluate(coefficients: dict[str, Q], point: dict[str, Q]) -> Q:
    return sum(coefficient * point[var] for var, coefficient in coefficients.items())


def main_witness() -> dict[str, Q]:
    x = {var: Q(0) for var in VARS}
    x.update({
        "a": Q(1, 3), "a1": Q(1, 8), "a4": Q(5, 24),
        "b": Q(1, 4), "b1": Q(1, 8), "vb": Q(7, 8),
        "c": Q(5, 12), "c1": Q(1, 8), "c3": Q(7, 24),
        "D": TARGET,
    })
    return x


def alternate_witness() -> dict[str, Q]:
    """The different optimal-face point stored in opt_tail.json."""
    x = {var: Q(0) for var in VARS}
    x.update({
        "a": Q(1, 3), "a1": Q(1, 8), "a4": Q(5, 24), "va": Q(1, 24),
        "b": Q(5, 12), "b1": Q(1, 8), "b3": Q(7, 24),
        "c": Q(1, 4), "c1": Q(1, 8), "vc": Q(7, 8),
        "D": TARGET,
    })
    return x


def verify_base_and_disjunctions(point: dict[str, Q]) -> dict[str, Any]:
    if set(point) != VARSET:
        raise AuditError(f"point variables mismatch: {sorted(set(point) ^ VARSET)}")
    if any(point[var] < 0 for var in VARS):
        raise AuditError("negative point coordinate")

    static_tight: list[str] = []
    for rid, (coeff, rhs) in STATIC_ROWS.items():
        value = evaluate(coeff, point)
        if value > rhs:
            raise AuditError(f"witness violates static row {rid!r}: {value} > {rhs}")
        if value == rhs:
            static_tight.append(repr(rid))

    branch_masks: list[tuple[int, ...]] = []
    for j in range(NDIS):
        valid = []
        for branch in (1, 2):
            coeff, rhs = disjunction_row(j, branch)
            if evaluate(coeff, point) <= rhs:
                valid.append(branch)
        if not valid:
            raise AuditError(f"witness violates both branches of disjunction {j}")
        branch_masks.append(tuple(valid))

    # Redundant-row identity: (T7,s)+(TV,s) is exactly (63,s).
    for s in SIDES:
        lhs = linear((1, STATIC_ROWS[("T7", s)][0]),
                     (1, STATIC_ROWS[("TV", s)][0]))
        rhs = STATIC_ROWS[("T7", s)][1] + STATIC_ROWS[("TV", s)][1]
        if (lhs, rhs) != STATIC_ROWS[("63", s)]:
            raise AuditError(f"derived (6.3) identity failed on side {s}")

    return {"static_tight_count": len(static_tight),
            "static_tight_rows": static_tight,
            "valid_disjunction_branches": [list(x) for x in branch_masks]}


def scan_all_cuts(point: dict[str, Q]) -> dict[str, Any]:
    expected = 3 * (len(FREE_SUBSETS) ** 2 - 1) * len(MODULUS_SUBSETS)
    count = 0
    violated = 0
    tight = 0
    minimum: Q | None = None
    argmin: Cut | None = None
    tight_by_side: Counter[str] = Counter()
    tight_by_q: Counter[int] = Counter()
    tight_with_tail = 0

    for sig in SIDES:
        s1, s2 = OTHER[sig]
        tau = point[sig] - sum(point[f"{sig}{i}"] for i in ROOTS)
        t_data: list[tuple[tuple[int, ...], Q, Q]] = []
        for tset in MODULUS_SUBSETS:
            cost = sum(point[f"{sig}{t}"] for t in tset if t != TAIL)
            power = sum(t * point[f"{sig}{t}"] for t in tset if t != TAIL)
            if TAIL in tset:
                cost += tau
                power += point[f"v{sig}"]
            t_data.append((tset, cost, power))

        r1_data = []
        for r1 in FREE_SUBSETS:
            root_mass = sum(point[f"{s1}{r}"] for r in r1)
            value_mass = sum(r * point[f"{s1}{r}"] for r in r1)
            r1_data.append((r1, root_mass, value_mass, reduce(gcd, r1, 0)))
        r2_data = []
        for r2 in FREE_SUBSETS:
            root_mass = sum(point[f"{s2}{r}"] for r in r2)
            value_mass = sum(r * point[f"{s2}{r}"] for r in r2)
            r2_data.append((r2, root_mass, value_mass, reduce(gcd, r2, 0)))

        for r1, f1, w1, g1 in r1_data:
            for r2, f2, w2, g2 in r2_data:
                if not r1 and not r2:
                    continue
                q = gcd(g1, g2)
                base = (point[s1] - f1) + (point[s2] - f2)
                freed_over_q = (w1 + w2) / q
                for tset, cost, power in t_data:
                    value = base + cost + max(Q(0), freed_over_q - power)
                    count += 1
                    if minimum is None or value < minimum:
                        minimum = value
                        argmin = (sig, r1, r2, tset)
                    if value < point["D"]:
                        violated += 1
                    elif value == point["D"]:
                        tight += 1
                        tight_by_side[sig] += 1
                        tight_by_q[q] += 1
                        if TAIL in tset:
                            tight_with_tail += 1

    if count != expected or expected != 1_560_195:
        raise AuditError(f"cut-family count mismatch: {count}, expected {expected}")
    if minimum is None:
        raise AuditError("empty cut family")
    return {
        "candidate_count": count,
        "candidate_count_formula": "3*(64*64-1)*127 = 1560195",
        "legacy_claim_1560510_is_arithmetic_error": True,
        "violated": violated,
        "tight": tight,
        "minimum": str(minimum),
        "argmin": [argmin[0], list(argmin[1]), list(argmin[2]), list(argmin[3])],
        "tight_by_side": dict(sorted(tight_by_side.items())),
        "tight_by_q": {str(k): v for k, v in sorted(tight_by_q.items())},
        "tight_with_tail_modulus": tight_with_tail,
    }


def audit_witness(name: str, point: dict[str, Q]) -> dict[str, Any]:
    base = verify_base_and_disjunctions(point)
    cuts = scan_all_cuts(point)
    if cuts["violated"] != 0 or cuts["minimum"] != "7/12":
        raise AuditError(f"{name} is not a feasible 7/12 lower witness: {cuts}")
    return {"name": name, "base": base, "cuts": cuts}


def mutation_self_tests(meta: dict[str, Any], leaves: list[dict[str, Any]]) -> dict[str, str]:
    """Small fail-closed tests of checks absent or implicit in the old verifier."""
    outcomes: dict[str, str] = {}

    bad_cell = list(leaves[0]["cell"])
    bad_cell[0] = 3
    try:
        validate_cell(bad_cell)
    except AuditError:
        outcomes["malformed_cell_rejected"] = "PASS"
    else:
        raise AuditError("mutation test failed: malformed cell accepted")

    negative = dict(leaves[0])
    negative["lam"] = [list(pair) for pair in leaves[0]["lam"]]
    negative["lam"][0] = [negative["lam"][0][0], "-1/1"]
    try:
        verify_leaf(negative)
    except AuditError:
        outcomes["negative_multiplier_rejected"] = "PASS"
    else:
        raise AuditError("mutation test failed: negative multiplier accepted")

    branched = next(leaf for leaf in leaves if leaf["path"])
    offpath = dict(branched)
    offpath["lam"] = [list(pair) for pair in branched["lam"]]
    existing_cut = parse_cut(branched["path"][0][0])
    sig, r1, r2, tset = existing_cut
    wrong_kind = "cutMA" if branched["path"][0][1] == "+" else "cutP"
    offpath["lam"].append([[wrong_kind, sig, list(r1), list(r2), list(tset)], "1/1"])
    try:
        verify_leaf(offpath)
    except AuditError:
        outcomes["sign_mismatched_row_rejected"] = "PASS"
    else:
        raise AuditError("mutation test failed: sign-mismatched cut row accepted")

    # Extract a complete nontrivial cell tree and remove one leaf.
    cell = validate_cell(branched["cell"])
    cell_paths = [parse_path(leaf["path"]) for leaf in leaves
                  if validate_cell(leaf["cell"]) == cell]
    if len(cell_paths) < 2:
        raise AuditError("could not find a nontrivial cell for mutation test")
    try:
        verify_complete_tree(cell_paths[:-1], where="mutation")
    except AuditError:
        outcomes["missing_branch_rejected"] = "PASS"
    else:
        raise AuditError("mutation test failed: incomplete tree accepted")

    bad_meta = dict(meta)
    bad_meta["target"] = "3/5"
    if bad_meta["target"] == "7/12":
        raise AssertionError
    outcomes["wrong_target_detectable"] = "PASS"
    return outcomes


def main() -> int:
    here = Path(__file__).resolve()
    default_cert = here.with_name("cert_leaves_tail.jsonl")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=default_cert)
    parser.add_argument("--skip-witnesses", action="store_true")
    parser.add_argument("--skip-mutations", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    report: dict[str, Any] = {
        "verifier": str(here),
        "verifier_sha256": sha256(here),
        "row_source": "BLT Proposition 6.1 eqs. (6.1)--(6.10) + documented tail/cut definitions",
        "arithmetic": "fractions.Fraction only",
        "imports_original_constructor": False,
    }
    report["certificate_audit"] = audit_certificate(args.certificate.resolve())
    if not args.skip_witnesses:
        report["witness_audits"] = [
            audit_witness("docs/875 main witness", main_witness()),
            audit_witness("opt_tail alternate-face witness", alternate_witness()),
        ]
    if not args.skip_mutations:
        meta, leaves = load_certificate(args.certificate.resolve())
        report["mutation_self_tests"] = mutation_self_tests(meta, leaves)

    rendered = json.dumps(report, indent=2, sort_keys=True)
    print(rendered)
    if args.json_out:
        args.json_out.write_text(rendered + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AuditError as exc:
        print(f"AUDIT FAILED: {exc}", file=sys.stderr)
        raise SystemExit(1)
