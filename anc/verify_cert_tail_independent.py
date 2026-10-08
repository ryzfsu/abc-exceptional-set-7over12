#!/usr/bin/env python3
"""Independent exact verifier for the round-2 7/12 certificate.

This verifier deliberately does NOT import ``prob_tail.py`` or any generator
module.  It reconstructs every inequality directly from the mathematical
specification:

* the base rows corresponding to (6.1)--(6.4) of the BBLT source;
* the tail definition rows ``v_s >= 7 tau_s`` and
  ``sum(i*s_i) + v_s <= 1``;
* all 27 linear rows equivalent to the Fourier max inequality (6.10);
* the two linear alternatives for each of the 13 min-disjunctions
  (6.5)--(6.9), including the corrected first row of (6.9);
* the plus/minus path rows for

      D <= A + max(0, B),

  where A and B are reconstructed from the modulus side, the two free-root
  subsets, and the selected regular/tail modulus blocks.

It then checks exact cell coverage, exact binary cut-tree coverage, row
authorization at every leaf, nonnegative Farkas multipliers, and the final
componentwise Farkas domination in ``fractions.Fraction`` arithmetic.

Usage (from any working directory):

    python3 verify_cert_tail_independent.py [cert_leaves_tail.jsonl]
"""

from __future__ import annotations

import hashlib
import itertools
import json
import sys
from fractions import Fraction as F
from functools import reduce
from math import gcd
from pathlib import Path
from typing import Any, Iterable


DEFAULT_CERT = Path(__file__).resolve().with_name("cert_leaves_tail.jsonl")
TARGET = F(7, 12)
REGULAR_INDICES = tuple(range(1, 7))
TAIL = 7

VARS = (
    ["a", "b", "c"]
    + [f"{side}{i}" for side in "abc" for i in REGULAR_INDICES]
    + ["va", "vb", "vc", "D"]
)
IDX = {name: i for i, name in enumerate(VARS)}
NVAR = len(VARS)


def normalize_nested(value: Any) -> Any:
    """Turn JSON lists recursively into hashable tuples."""

    if isinstance(value, list):
        return tuple(normalize_nested(item) for item in value)
    return value


def linear_combination(*terms: tuple[F | int, str | dict[str, F | int]]) -> dict[str, F]:
    """Build a sparse linear form from (coefficient, form-or-variable) terms."""

    result: dict[str, F] = {}
    for coefficient, form in terms:
        if isinstance(form, str):
            form = {form: 1}
        coefficient = F(coefficient)
        for variable, value in form.items():
            result[variable] = result.get(variable, F(0)) + coefficient * F(value)
    return {variable: value for variable, value in result.items() if value}


def dense_vector(form: dict[str, F | int]) -> tuple[F, ...]:
    vector = [F(0)] * NVAR
    for variable, coefficient in form.items():
        vector[IDX[variable]] += F(coefficient)
    return tuple(vector)


def row(form: dict[str, F | int], rhs: F | int) -> tuple[tuple[F, ...], F]:
    """Represent the inequality form(x) <= rhs."""

    return dense_vector(form), F(rhs)


L_FORM = {"a": F(1), "b": F(1), "c": F(1)}


def p_form(i: int) -> dict[str, F]:
    return {f"{side}{i}": F(1) for side in "abc"}


FOURIER_GROUPS = {
    side: (
        {f"{side}2": 1, f"{side}4": 1, f"{side}6": 1},
        {f"{side}3": 1, f"{side}6": 1},
        {f"{side}5": 1},
    )
    for side in "abc"
}


def construct_disjunctions() -> list[tuple[dict[str, F], dict[str, F]]]:
    """Construct the 13 pairs min(E1, 1-E2) <= L-D.

    The order is exactly (6.5), the three rows of (6.6), the three rows of
    (6.7), the three rows of (6.8), and the three rows of (6.9).  In
    particular, the first (6.9) row uses p1+a2+b3+c3, not the erroneous
    appendix-code transcription with a3 in the final position.
    """

    disjunctions: list[tuple[dict[str, F], dict[str, F]]] = []

    # (6.5)
    disjunctions.append(
        (
            linear_combination((1, p_form(1)), (1, p_form(2)), (1, p_form(4))),
            linear_combination((1, p_form(2)), (3, p_form(4))),
        )
    )

    # (6.6)
    for side in "abc":
        disjunctions.append(
            (
                linear_combination((1, p_form(1)), (1, p_form(2)), (1, f"{side}3")),
                linear_combination((1, p_form(2)), (2, f"{side}3")),
            )
        )

    # (6.7)
    for first, second in (("a", "b"), ("b", "c"), ("c", "a")):
        disjunctions.append(
            (
                linear_combination(
                    (1, p_form(1)),
                    (1, p_form(2)),
                    (1, f"{first}3"),
                    (1, f"{second}3"),
                ),
                linear_combination(
                    (1, p_form(2)),
                    (2, f"{first}3"),
                    (2, f"{second}3"),
                ),
            )
        )

    # (6.8)
    for cubic_side in "abc":
        other_sides = [side for side in "abc" if side != cubic_side]
        disjunctions.append(
            (
                linear_combination(
                    (1, p_form(1)),
                    (1, f"{cubic_side}3"),
                    (1, f"{other_sides[0]}2"),
                    (1, f"{other_sides[1]}2"),
                ),
                linear_combination(
                    (2, f"{cubic_side}3"),
                    (1, f"{other_sides[0]}2"),
                    (1, f"{other_sides[1]}2"),
                ),
            )
        )

    # (6.9), with the corrected z13/first-row transcription.
    for quadratic_side in "abc":
        other_sides = [side for side in "abc" if side != quadratic_side]
        disjunctions.append(
            (
                linear_combination(
                    (1, p_form(1)),
                    (1, f"{quadratic_side}2"),
                    (1, f"{other_sides[0]}3"),
                    (1, f"{other_sides[1]}3"),
                ),
                linear_combination(
                    (1, f"{quadratic_side}2"),
                    (2, f"{other_sides[0]}3"),
                    (2, f"{other_sides[1]}3"),
                ),
            )
        )

    assert len(disjunctions) == 13
    return disjunctions


DISJUNCTIONS = construct_disjunctions()


def cut_forms(
    modulus_side: str,
    free_first: tuple[int, ...],
    free_second: tuple[int, ...],
    modulus_blocks: tuple[int, ...],
) -> tuple[dict[str, F], dict[str, F]]:
    """Reconstruct A and B in D <= A + max(0,B).

    The two counted sides use the canonical order inherited from (a,b,c):
    a -> (b,c), b -> (a,c), c -> (a,b).  A pays all non-free roots on those
    sides and the selected roots on the modulus side.  Selecting TAIL pays
    tau_sigma = sigma-sum_{i<=6} sigma_i.  B is the q-reduced free value mass
    minus the selected modulus value; selecting TAIL subtracts v_sigma.
    """

    counted_sides = tuple(side for side in "abc" if side != modulus_side)
    q = gcd(reduce(gcd, free_first, 0), reduce(gcd, free_second, 0))
    if q <= 0:
        raise ValueError("both free-root subsets are empty")

    a_form = linear_combination(
        (1, counted_sides[0]),
        (1, counted_sides[1]),
        *[(-1, f"{counted_sides[0]}{i}") for i in free_first],
        *[(-1, f"{counted_sides[1]}{i}") for i in free_second],
        *[(1, f"{modulus_side}{i}") for i in modulus_blocks if i != TAIL],
    )
    b_form = linear_combination(
        *[(F(i, q), f"{counted_sides[0]}{i}") for i in free_first],
        *[(F(i, q), f"{counted_sides[1]}{i}") for i in free_second],
        *[(-i, f"{modulus_side}{i}") for i in modulus_blocks if i != TAIL],
    )

    if TAIL in modulus_blocks:
        a_form = linear_combination(
            (1, a_form),
            (1, modulus_side),
            *[(-1, f"{modulus_side}{i}") for i in REGULAR_INDICES],
        )
        b_form = linear_combination((1, b_form), (-1, f"v{modulus_side}"))

    return a_form, b_form


def reconstruct_row(row_id: tuple[Any, ...]) -> tuple[tuple[F, ...], F]:
    """Reconstruct one certificate row without consulting generator code."""

    tag = row_id[0]

    if tag == "L":
        return row(L_FORM, 1)

    if tag == "62":
        side = row_id[1]
        return row(
            linear_combination(
                *[(1, f"{side}{i}") for i in REGULAR_INDICES],
                (-1, side),
            ),
            0,
        )

    if tag == "63":
        side = row_id[1]
        return row(
            linear_combination(
                (7, side),
                *[(-(7 - i), f"{side}{i}") for i in REGULAR_INDICES],
            ),
            1,
        )

    if tag == "T7":
        side = row_id[1]
        return row(
            linear_combination(
                (7, side),
                *[(-7, f"{side}{i}") for i in REGULAR_INDICES],
                (-1, f"v{side}"),
            ),
            0,
        )

    if tag == "TV":
        side = row_id[1]
        return row(
            linear_combination(
                *[(i, f"{side}{i}") for i in REGULAR_INDICES],
                (1, f"v{side}"),
            ),
            1,
        )

    if tag == "64":
        first, second = row_id[1:]
        return row(linear_combination((1, "D"), (-1, first), (-1, second)), 0)

    if tag == "F":
        first_group, second_group, third_group = row_id[1:]
        return row(
            linear_combination(
                (1, FOURIER_GROUPS["a"][first_group]),
                (1, FOURIER_GROUPS["b"][second_group]),
                (1, FOURIER_GROUPS["c"][third_group]),
                (-4, L_FORM),
                (6, "D"),
            ),
            0,
        )

    if tag == "dis":
        disjunction_index, branch = row_id[1:]
        e1, e2 = DISJUNCTIONS[disjunction_index]
        if branch == 1:
            # E1 <= L-D.
            return row(linear_combination((1, e1), (-1, L_FORM), (1, "D")), 0)
        if branch == 2:
            # 1-E2 <= L-D, equivalently -E2-L+D <= -1.
            return row(linear_combination((-1, e2), (-1, L_FORM), (1, "D")), -1)
        raise ValueError(f"invalid disjunction branch: {branch}")

    if tag in {"cutP", "cutMA", "cutMB"}:
        modulus_side = row_id[1]
        free_first = tuple(row_id[2])
        free_second = tuple(row_id[3])
        modulus_blocks = tuple(row_id[4])
        a_form, b_form = cut_forms(
            modulus_side, free_first, free_second, modulus_blocks
        )
        if tag == "cutP":
            # The B>=0 side of the cover: D <= A+B.  The sign condition itself
            # is unnecessary for validity of this stronger child row.
            return row(
                linear_combination((1, "D"), (-1, a_form), (-1, b_form)), 0
            )
        if tag == "cutMA":
            # The B<=0 side: D <= A.
            return row(linear_combination((1, "D"), (-1, a_form)), 0)
        # The accompanying sign row B <= 0.
        return row(b_form, 0)

    raise ValueError(f"unknown row id: {row_id}")


def complete_cut_tree(paths: list[tuple[tuple[tuple[Any, ...], str], ...]]) -> bool:
    """Check that leaf paths form a complete binary sign tree."""

    if paths == [()]:
        return True
    if not paths or any(not path for path in paths):
        return False

    head_cuts = {path[0][0] for path in paths}
    if len(head_cuts) != 1:
        return False
    if any(path[0][1] not in {"+", "-"} for path in paths):
        return False

    plus_paths = [path[1:] for path in paths if path[0][1] == "+"]
    minus_paths = [path[1:] for path in paths if path[0][1] == "-"]
    return (
        bool(plus_paths)
        and bool(minus_paths)
        and complete_cut_tree(plus_paths)
        and complete_cut_tree(minus_paths)
    )


def static_authorized_rows() -> set[tuple[Any, ...]]:
    authorized: set[tuple[Any, ...]] = {("L",)}
    authorized.update(
        (tag, side) for tag in ("62", "63", "T7", "TV") for side in "abc"
    )
    authorized.update(("64", first, second) for first, second in (("a", "b"), ("a", "c"), ("b", "c")))
    authorized.update(
        ("F", u, v, w)
        for u in range(3)
        for v in range(3)
        for w in range(3)
    )
    return authorized


STATIC_AUTHORIZED = static_authorized_rows()


def authorized_rows_for_leaf(
    cell: tuple[int, ...], path: tuple[tuple[tuple[Any, ...], str], ...]
) -> set[tuple[Any, ...]]:
    authorized = set(STATIC_AUTHORIZED)
    authorized.update(("dis", j, cell[j]) for j in range(13))

    for cut_description, sign in path:
        modulus_side, free_first, free_second, modulus_blocks = cut_description
        prefix = (
            modulus_side,
            tuple(free_first),
            tuple(free_second),
            tuple(modulus_blocks),
        )
        if sign == "+":
            authorized.add(("cutP",) + prefix)
        elif sign == "-":
            authorized.add(("cutMA",) + prefix)
            authorized.add(("cutMB",) + prefix)
        else:
            raise ValueError(f"invalid cut sign: {sign}")

    return authorized


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def verify(certificate_path: Path) -> None:
    by_cell: dict[tuple[int, ...], list[tuple[tuple[tuple[Any, ...], str], ...]]] = {}
    worst_bound = F(0)
    leaf_count = 0
    meta_target: str | None = None

    with certificate_path.open() as handle:
        for line_number, line in enumerate(handle, 1):
            record = json.loads(line)
            if "meta" in record:
                meta_target = record["meta"].get("target")
                continue
            if "cell" not in record:
                raise AssertionError(f"line {line_number}: record has neither meta nor cell")

            cell = tuple(record["cell"])
            if len(cell) != 13 or any(branch not in (1, 2) for branch in cell):
                raise AssertionError(f"line {line_number}: invalid cell {cell}")

            path = tuple(
                (normalize_nested(cut_description), sign)
                for cut_description, sign in record["path"]
            )
            authorized = authorized_rows_for_leaf(cell, path)

            combined = [F(0)] * NVAR
            combined_rhs = F(0)
            for raw_row_id, raw_multiplier in record["lam"]:
                row_id = normalize_nested(raw_row_id)
                if row_id not in authorized:
                    raise AssertionError(
                        f"line {line_number}: unauthorized row {row_id} for cell/path"
                    )
                multiplier = F(raw_multiplier)
                if multiplier < 0:
                    raise AssertionError(
                        f"line {line_number}: negative multiplier on {row_id}"
                    )

                coefficients, rhs = reconstruct_row(row_id)
                for variable_index, coefficient in enumerate(coefficients):
                    combined[variable_index] += multiplier * coefficient
                combined_rhs += multiplier * rhs

            for variable_index, coefficient in enumerate(combined):
                required = F(1) if VARS[variable_index] == "D" else F(0)
                if coefficient < required:
                    raise AssertionError(
                        f"line {line_number}: coefficient on {VARS[variable_index]} "
                        f"is {coefficient}, below {required}"
                    )
            if combined_rhs > TARGET:
                raise AssertionError(
                    f"line {line_number}: leaf bound {combined_rhs} exceeds {TARGET}"
                )

            worst_bound = max(worst_bound, combined_rhs)
            by_cell.setdefault(cell, []).append(path)
            leaf_count += 1

    if meta_target != str(TARGET):
        raise AssertionError(f"certificate meta target {meta_target!r} != {str(TARGET)!r}")

    expected_cells = set(itertools.product((1, 2), repeat=13))
    actual_cells = set(by_cell)
    if actual_cells != expected_cells:
        raise AssertionError(
            f"cell coverage mismatch: missing={len(expected_cells-actual_cells)}, "
            f"extra={len(actual_cells-expected_cells)}"
        )

    for cell, paths in by_cell.items():
        if len(paths) != len(set(paths)):
            raise AssertionError(f"cell {cell}: duplicate leaf paths")
        if not complete_cut_tree(paths):
            raise AssertionError(f"cell {cell}: incomplete cut sign tree")

    print(f"certificate: {certificate_path}")
    print(f"certificate_sha256: {sha256(certificate_path)}")
    print(
        "INDEPENDENT RECONSTRUCTION PASS: "
        f"{len(by_cell)} cells, {leaf_count} leaves, exact worst={worst_bound}"
    )
    print("CONCLUSION: every feasible nonnegative profile has D <= 7/12.")


def main(argv: Iterable[str]) -> int:
    args = list(argv)
    if len(args) > 1:
        print("usage: verify_cert_tail_independent.py [certificate.jsonl]", file=sys.stderr)
        return 2
    certificate_path = Path(args[0]).resolve() if args else DEFAULT_CERT
    verify(certificate_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
