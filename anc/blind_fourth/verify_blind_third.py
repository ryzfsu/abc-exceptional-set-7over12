#!/usr/bin/env python3
"""
BLIND THIRD VERIFIER for the 7/12 abc-exceptional-set Farkas certificate.

Written from the text of main.tex only (A Primitive-Ratio Cut and a 7/12 Bound
for the abc Exceptional Set, Ruiyi Zhang), with no access to, and no knowledge
of, the two existing verifiers or the generator.

Every row is rebuilt from the paper's displayed formula plus the row id:
  (2.7)  L <= 1                                      id ("L",)
  (2.8)  sum_{i<=6} s_i <= s                         id ("62", s)
  (2.9)  7s - 1 <= 6s1+5s2+4s3+3s4+2s5+s6            id ("63", s)
  (2.10) D <= min(a+b, a+c, b+c)                     id ("64", s1, s2)
  (2.11) sum_s max(s2+s4+s6, s3+s6, s5) <= 4L-6D     id ("F", i, j, k)
  (3.1)  v_s >= 7 tau_s                              id ("T7", s)
         sum_{i<=6} i s_i + v_s <= 1                 id ("TV", s)
         ( tau_s >= 0 is (2.8), i.e. ("62", s) )
  App A  thirteen min-disjunctions                   id ("dis", j, branch)
  (5.3)  the cut, D <= A + (B)_+                     id ("cutP"/"cutMA"/"cutMB",
                                                          sigma, Ry, Rz, T)
Exact Fraction arithmetic, standard library only.
"""
import json, sys, collections
from pathlib import Path
from fractions import Fraction
from math import gcd

SIDES = ("a", "b", "c")

# ---------------------------------------------------------------- variables
# 25 nonnegative variables of (1.3):
#   a,b,c ; a_1..a_6,b_1..b_6,c_1..c_6 ; v_a,v_b,v_c ; D
VARS = list(SIDES)
for s in SIDES:
    VARS += ["%s%d" % (s, i) for i in range(1, 7)]
VARS += ["v" + s for s in SIDES] + ["D"]
IDX = {v: k for k, v in enumerate(VARS)}
N = len(VARS)
assert N == 25, N

def zero():
    return [Fraction(0)] * N

def add(g, name, coef):
    g[IDX[name]] += Fraction(coef)

# ---------------------------------------------------------- Appendix A rows
# Each row is Prop 4.1 of [BBLT] for one triple of index sets (I,I',I''):
#   branch 1:  D <= L - P ,  P = sum_{i in I} a_i + sum_{i in I'} b_i + sum_{i in I''} c_i
#   branch 2:  D <= L - Q ,  Q = 1 - sum_{i in I}(i-1)a_i - ... - ...
# The paper lists the choices as five families, of sizes 1,3,3,3,3, matching
# [BBLT] (6.5)--(6.9).  Within a family of three the paper writes "and its
# permutations" / "x running over {a,b,c}" without fixing the order; the order
# used here is the one the paper's own erratum pins for the last family
# (first line of (6.9) is p1+a2+b3+c3, i.e. x=a first) extended to all of them.
def _sets(fam, k):
    """return (I,I',I'') as dict side -> frozenset of indices"""
    if fam == 0:                       # I=I'=I''={1,2,4}
        return {s: {1, 2, 4} for s in SIDES}
    if fam == 1:                       # I=I'={1,2}, I''={1,2,3} ; x = the {1,2,3} side
        x = SIDES[k]
        return {s: ({1, 2, 3} if s == x else {1, 2}) for s in SIDES}
    if fam == 2:                       # I={1,2}, I'=I''={1,2,3} ; (x,y) = the two {1,2,3} sides
        pairs = [("a", "b"), ("b", "c"), ("c", "a")]
        x, y = pairs[k]
        return {s: ({1, 2, 3} if s in (x, y) else {1, 2}) for s in SIDES}
    if fam == 3:                       # I=I'={1,2}, I''={1,3} ; x = the {1,3} side
        x = SIDES[k]
        return {s: ({1, 3} if s == x else {1, 2}) for s in SIDES}
    if fam == 4:                       # I={1,2}, I'=I''={1,3} ; x = the {1,2} side
        x = SIDES[k]
        return {s: ({1, 2} if s == x else {1, 3}) for s in SIDES}
    raise KeyError(fam)

DIS_SETS = []
for fam, cnt in enumerate((1, 3, 3, 3, 3)):
    for k in range(cnt):
        DIS_SETS.append(_sets(fam, k))
assert len(DIS_SETS) == 13

# ------------------------------------------------- Fourier max arguments
def _fourier_arg(s, which):
    if which == 0:
        return ["%s2" % s, "%s4" % s, "%s6" % s]
    if which == 1:
        return ["%s3" % s, "%s6" % s]
    if which == 2:
        return ["%s5" % s]
    raise KeyError(which)

# --------------------------------------------- y,z assignment for a cut
# "Fix a box and a modulus side sigma, write y,z for the other two sides"
# -- the paper nowhere says WHICH of the two remaining sides is y.  Row (5.3)
# is not symmetric under Ry<->Rz alone, so a convention is needed to read the
# certificate's row ids.  All eight possible conventions were tried; exactly
# one makes the Farkas conditions hold at all 10820 leaves, namely taking
# (y,z) to be the two non-sigma sides in alphabetical order.  (The other seven
# give 433..1101 failing leaves.)  This is a labelling ambiguity of the paper,
# not a mathematical one: the enumeration of (5.3) runs over ORDERED pairs
# (Ry,Rz), so the row SET is invariant under the swap and the system S is the
# same under either convention.
YZ = {"a": ("b", "c"), "b": ("a", "c"), "c": ("a", "b")}

def _cut_parts(sigma, Ry, Rz, T):
    """return (gA, gB) with  A = -<gA,x>  ... see below.
    gA = coefficient vector of  -A   (so row D<=A is e_D + gA)
    gB = coefficient vector of  -B   (so row D<=A+B is e_D + gA + gB)
    """
    y, z = YZ[sigma]
    Ry = list(Ry); Rz = list(Rz); T = list(T)
    q = 0
    for r in Ry + Rz:
        q = gcd(q, r)
    gA = zero()
    # -(y - sum_{r in Ry} y_r)
    add(gA, y, -1)
    for r in Ry:
        add(gA, "%s%d" % (y, r), 1)
    # -(z - sum_{s in Rz} z_s)
    add(gA, z, -1)
    for r in Rz:
        add(gA, "%s%d" % (z, r), 1)
    # -C_T,  C_T = sum_{t in T cap [6]} sigma_t + 1{tail in T} tau_sigma
    for t in T:
        if t <= 6:
            add(gA, "%s%d" % (sigma, t), -1)
    if 7 in T:                                     # tau_sigma = sigma - sum_{i<=6} sigma_i
        add(gA, sigma, -1)
        for i in range(1, 7):
            add(gA, "%s%d" % (sigma, i), 1)
    # -B,  B = F/q - W_T
    gB = zero()
    if Ry or Rz:
        assert q >= 1
        for r in Ry:
            add(gB, "%s%d" % (y, r), -Fraction(r, q))
        for r in Rz:
            add(gB, "%s%d" % (z, r), -Fraction(r, q))
    for t in T:
        if t <= 6:
            add(gB, "%s%d" % (sigma, t), t)
    if 7 in T:
        add(gB, "v" + sigma, 1)
    return gA, gB

# ------------------------------------------------------------- row factory
def build_row(rid):
    """rid is a list; returns (g, h) meaning <g,x> <= h, rebuilt from the paper."""
    head = rid[0]
    g = zero(); h = Fraction(0)
    if head == "L":                                       # (2.7) a+b+c <= 1
        assert len(rid) == 1
        for s in SIDES:
            add(g, s, 1)
        h = Fraction(1)
    elif head == "62":                                    # (2.8) sum s_i <= s
        s = rid[1]
        for i in range(1, 7):
            add(g, "%s%d" % (s, i), 1)
        add(g, s, -1)
    elif head == "63":                                    # (2.9) 7s - sum (7-i)s_i <= 1
        s = rid[1]
        add(g, s, 7)
        for i in range(1, 7):
            add(g, "%s%d" % (s, i), -(7 - i))
        h = Fraction(1)
    elif head == "T7":                                    # (3.1b) 7 tau_s - v_s <= 0
        s = rid[1]
        add(g, s, 7)
        for i in range(1, 7):
            add(g, "%s%d" % (s, i), -7)
        add(g, "v" + s, -1)
    elif head == "TV":                                    # (3.1c) sum i s_i + v_s <= 1
        s = rid[1]
        for i in range(1, 7):
            add(g, "%s%d" % (s, i), i)
        add(g, "v" + s, 1)
        h = Fraction(1)
    elif head == "64":                                    # (2.10) D <= s1+s2
        s1, s2 = rid[1], rid[2]
        add(g, "D", 1); add(g, s1, -1); add(g, s2, -1)
    elif head == "F":                                     # (2.11) linearised
        add(g, "D", 6)
        for s in SIDES:
            add(g, s, -4)
        for s, w in zip(SIDES, rid[1:4]):
            for nm in _fourier_arg(s, w):
                add(g, nm, 1)
    elif head == "dis":                                   # Appendix A
        j, br = rid[1], rid[2]
        S = DIS_SETS[j]
        add(g, "D", 1)
        for s in SIDES:
            add(g, s, -1)                                 # -L
        if br == 1:                                       # D <= L - P
            for s in SIDES:
                for i in S[s]:
                    add(g, "%s%d" % (s, i), 1)
        elif br == 2:                                     # D <= L - Q, Q = 1 - sum (i-1)x_i
            for s in SIDES:
                for i in S[s]:
                    add(g, "%s%d" % (s, i), -(i - 1))
            h = Fraction(-1)
        else:
            raise KeyError(br)
    elif head in ("cutP", "cutMA", "cutMB"):              # (5.3)
        sigma, Ry, Rz, T = rid[1], rid[2], rid[3], rid[4]
        gA, gB = _cut_parts(sigma, Ry, Rz, T)
        if head == "cutP":                                # D <= A + B
            add(g, "D", 1)
            g = [x + y for x, y in zip(g, gA)]
            g = [x + y for x, y in zip(g, gB)]
        elif head == "cutMA":                             # D <= A
            add(g, "D", 1)
            g = [x + y for x, y in zip(g, gA)]
        else:                                             # cutMB : B <= 0
            g = [-x for x in gB]
    else:
        raise KeyError(head)
    return g, h

MAXDEN = 1
ROWCACHE = {}
def row(rid):
    k = json.dumps(rid)
    if k not in ROWCACHE:
        ROWCACHE[k] = build_row(rid)
    return ROWCACHE[k]


# ====================================================================
#  Extra check 1: every cut row id used is a legal instance of (5.3)
# ====================================================================
def check_cut_legality(keys, E):
    """keys: iterable of json-encoded [sigma, Ry, Rz, T]"""
    for k in keys:
        sigma, Ry, Rz, T = json.loads(k)
        if sigma not in SIDES:
            E("illegal cut modulus side %r" % sigma)
        if not set(Ry) <= set(range(1, 7)) or not set(Rz) <= set(range(1, 7)):
            E("illegal free set in %s" % k)
        if Ry != sorted(set(Ry)) or Rz != sorted(set(Rz)):
            E("non-canonical free set in %s" % k)
        if not Ry and not Rz:
            E("both free sets empty in %s (excluded by (5.4))" % k)
        if not set(T) <= set(range(1, 8)) or not T:
            E("illegal T in %s" % k)
        if T != sorted(set(T)):
            E("non-canonical T in %s" % k)

# ====================================================================
#  Extra check 2: the witness of Remark 6.2 against ALL 1 560 195 cuts
#  This exercises the cut-row reconstruction on the whole family, not
#  only on the 732 cuts the certificate happens to use.
# ====================================================================
WITNESS = {
    "a": Fraction(1, 3), "a1": Fraction(1, 8), "a4": Fraction(5, 24),
    "b": Fraction(1, 4), "b1": Fraction(1, 8), "vb": Fraction(7, 8),
    "c": Fraction(5, 12), "c1": Fraction(1, 8), "c3": Fraction(7, 24),
    "D": Fraction(7, 12),
}

def witness_vector():
    x = [Fraction(0)] * N
    for k, v in WITNESS.items():
        x[IDX[k]] = v
    return x

def scan_witness(verbose=True):
    """Return (min rhs over all cuts, how often attained, total rows scanned)."""
    x = witness_vector()
    g = lambda nm: x[IDX[nm]]
    tau = {s: g(s) - sum(g("%s%d" % (s, i)) for i in range(1, 7)) for s in SIDES}
    subsets6 = []
    for m in range(64):
        subsets6.append([i for i in range(1, 7) if m >> (i - 1) & 1])
    # C_T, W_T for every nonempty T subset of {1..7}, per sigma
    CW = {}
    for sigma in SIDES:
        lst = []
        for m in range(1, 128):
            T = [t for t in range(1, 8) if m >> (t - 1) & 1]
            C = sum(g("%s%d" % (sigma, t)) for t in T if t <= 6)
            W = sum(t * g("%s%d" % (sigma, t)) for t in T if t <= 6)
            if 7 in T:
                C += tau[sigma]
                W += g("v" + sigma)
            lst.append((C, W))
        CW[sigma] = lst
    best = None; cnt = 0; total = 0
    for sigma in SIDES:
        y, z = YZ[sigma]
        for Ry in subsets6:
            for Rz in subsets6:
                if not Ry and not Rz:
                    continue
                q = 0
                for r in Ry + Rz:
                    q = gcd(q, r)
                A0 = (g(y) - sum(g("%s%d" % (y, r)) for r in Ry)) \
                   + (g(z) - sum(g("%s%d" % (z, r)) for r in Rz))
                F = sum(r * g("%s%d" % (y, r)) for r in Ry) \
                  + sum(r * g("%s%d" % (z, r)) for r in Rz)
                Fq = Fraction(F, q)
                for C, W in CW[sigma]:
                    B = Fq - W
                    rhs = A0 + C + (B if B > 0 else Fraction(0))
                    total += 1
                    if best is None or rhs < best:
                        best = rhs; cnt = 1
                    elif rhs == best:
                        cnt += 1
    return best, cnt, total

def check_witness(E):
    x = witness_vector()
    Lv = sum(x[IDX[s]] for s in SIDES)
    if Lv != 1:
        E("witness: L = %s, not 1" % Lv)
    # (2.10) tight
    pr = min(x[IDX[u]] + x[IDX[v]] for u, v in (("a","b"),("a","c"),("b","c")))
    if pr != x[IDX["D"]]:
        E("witness: not tight in (2.10): min pair sum %s vs D %s" % (pr, x[IDX["D"]]))
    # (2.11) tight
    lhs = Fraction(0)
    for s in SIDES:
        lhs += max(x[IDX["%s2"%s]]+x[IDX["%s4"%s]]+x[IDX["%s6"%s]],
                   x[IDX["%s3"%s]]+x[IDX["%s6"%s]], x[IDX["%s5"%s]])
    if lhs != 4*Lv - 6*x[IDX["D"]]:
        E("witness: not tight in (2.11): %s vs %s" % (lhs, 4*Lv-6*x[IDX["D"]]))
    # all linear rows of S other than the cuts
    for rid in ([["L"]] + [["62",s] for s in SIDES] + [["63",s] for s in SIDES]
                + [["T7",s] for s in SIDES] + [["TV",s] for s in SIDES]
                + [["64",u,v] for u,v in (("a","b"),("a","c"),("b","c"))]
                + [["F",i,j,k] for i in range(3) for j in range(3) for k in range(3)]):
        g_, h_ = row(rid)
        val = sum(g_[t]*x[t] for t in range(N) if g_[t])
        if val > h_:
            E("witness violates row %s: %s > %s" % (rid, val, h_))
    for j in range(13):
        ok = False
        for br in (1, 2):
            g_, h_ = row(["dis", j, br])
            if sum(g_[t]*x[t] for t in range(N) if g_[t]) <= h_:
                ok = True
        if not ok:
            E("witness violates both branches of disjunction %d" % j)
    return scan_witness()

# --------------------------------------------------------------- read cert
def main(path):
    global MAXDEN
    MAXDEN = 1
    raw = open(path).read().splitlines()
    meta = json.loads(raw[0])
    target = Fraction(meta["meta"]["target"])
    leaves = [json.loads(l) for l in raw[1:]]
    errs = []
    E = errs.append

    if target != Fraction(7, 12):
        E("declared target is %s, not 7/12" % target)

    # ---------------- (b)+(c) per-leaf validity and Farkas
    per_leaf = []
    min_surplus = None
    worst_rhs = None
    rhs_counter = collections.Counter()
    max_lamsum = None
    max_nnz = 0
    total_mults = 0
    unused_branch_leaves = 0
    for li, L in enumerate(leaves):
        cell, pth, kind, lam = L["cell"], L["path"], L["kind"], L["lam"]
        if kind != "bound":
            E("leaf %d: unexpected kind %r" % (li, kind))
        if len(cell) != 13 or any(v not in (1, 2) for v in cell):
            E("leaf %d: malformed cell %r" % (li, cell))
            continue
        armof = {}
        for pk, sg in pth:
            key = json.dumps(pk)
            if sg not in ("+", "-"):
                E("leaf %d: bad sign %r" % (li, sg))
            if key in armof and armof[key] != sg:
                E("leaf %d: contradictory arms for cut %s" % (li, key))
            armof[key] = sg
        acc = zero(); rhs = Fraction(0); lamsum = Fraction(0); nnz = 0
        seen = set(); used_cuts = set()
        for rid, ms in lam:
            m = Fraction(ms)
            if m <= 0:
                E("leaf %d: non-positive multiplier %s on %s" % (li, ms, rid))
            key = json.dumps(rid)
            if key in seen:
                E("leaf %d: duplicate row %s" % (li, key))
            seen.add(key)
            # ---- validity on cell
            if rid[0] == "dis":
                if cell[rid[1]] != rid[2]:
                    E("leaf %d: disjunction %d branch %d not valid on cell "
                      "(cell has %d)" % (li, rid[1], rid[2], cell[rid[1]]))
            # ---- validity on path
            if rid[0] in ("cutP", "cutMA", "cutMB"):
                ck = json.dumps(rid[1:])
                used_cuts.add(ck)
                want = "+" if rid[0] == "cutP" else "-"
                got = armof.get(ck)
                if got is None:
                    E("leaf %d: %s uses cut %s with no sign step on the path"
                      % (li, rid[0], ck))
                elif got != want:
                    E("leaf %d: %s needs arm %s but path has %s for %s"
                      % (li, rid[0], want, got, ck))
            g, h = row(rid)
            for k in range(N):
                if g[k]:
                    acc[k] += m * g[k]
            rhs += m * h
            lamsum += m
            if m.denominator > MAXDEN:
                MAXDEN = m.denominator
            nnz += 1
            total_mults += 1
        if set(armof) - used_cuts:
            unused_branch_leaves += 1
        # Farkas (6.2): sum lam_i g_i >= e_D componentwise ; sum lam_i h_i <= 7/12
        eD = [Fraction(0)] * N
        eD[IDX["D"]] = Fraction(1)
        surp = [acc[k] - eD[k] for k in range(N)]
        ms_ = min(surp)
        if ms_ < 0:
            bad = [(VARS[k], str(surp[k])) for k in range(N) if surp[k] < 0]
            E("leaf %d: Farkas componentwise FAILS: %s  (cell=%s path=%s)"
              % (li, bad, cell, pth))
        if min_surplus is None or ms_ < min_surplus:
            min_surplus = ms_
        if rhs > target:
            E("leaf %d: right-hand side %s exceeds 7/12" % (li, rhs))
        if worst_rhs is None or rhs > worst_rhs:
            worst_rhs = rhs
        rhs_counter[rhs] += 1
        if max_lamsum is None or lamsum > max_lamsum:
            max_lamsum = lamsum
        max_nnz = max(max_nnz, nnz)
        per_leaf.append((tuple(cell), tuple((json.dumps(p[0]), p[1]) for p in pth),
                         rhs, lamsum, nnz, used_cuts, set(armof)))

    # ---------------- (d) tree checks
    bycell = collections.defaultdict(list)
    for rec in per_leaf:
        bycell[rec[0]].append(rec[1])
    allcells = set(bycell)
    full = set()
    import itertools
    for t in itertools.product((1, 2), repeat=13):
        full.add(t)
    missing = full - allcells
    extra = allcells - full
    if missing:
        E("%d cells of {1,2}^13 missing (e.g. %s)" % (len(missing), sorted(missing)[:3]))
    if extra:
        E("%d cells outside {1,2}^13 (e.g. %s)" % (len(extra), sorted(extra)[:3]))

    internal_nodes = 0
    for cell, paths in bycell.items():
        if len(paths) != len(set(paths)):
            E("cell %s: duplicate leaf path" % (cell,))
        P = set(paths)
        # build trie of all prefixes
        children = collections.defaultdict(dict)   # prefix -> {sign: ()}
        prefixes = set()
        for p in P:
            for k in range(len(p)):
                prefixes.add(p[:k])
                children[p[:k]][p[k][1]] = p[k][0]
        for p in P:
            if p in prefixes:
                E("cell %s: path %s is a strict prefix of another leaf" % (cell, p))
        for pre, ch in children.items():
            if set(ch) != {"+", "-"}:
                E("cell %s: node %s has arms %s, not both" % (cell, pre, sorted(ch)))
            if len(set(ch.values())) != 1:
                E("cell %s: node %s branches on two different cuts %s"
                  % (cell, pre, sorted(set(ch.values()))))
            internal_nodes += 1
        if internal_nodes is not None and len(P) - 1 != len(children):
            E("cell %s: %d leaves but %d internal nodes" % (cell, len(P), len(children)))

    # ---------------- (e) statistics
    cuts_per_cell = {}
    cells_with_cut = 0
    distinct_cuts = set()
    for cell, paths in bycell.items():
        ks = set()
        for p in paths:
            for key, sg in p:
                ks.add(key)
        cuts_per_cell[cell] = len(ks)
        distinct_cuts |= ks
        if ks:
            cells_with_cut += 1
    cuts_in_lam = set()
    cells_with_cut_lam = 0
    for rec in per_leaf:
        cuts_in_lam |= rec[5]
    for cell, paths in bycell.items():
        pass
    bycell_lam = collections.defaultdict(set)
    for rec in per_leaf:
        bycell_lam[rec[0]] |= rec[5]
    cells_with_cut_lam = sum(1 for c in bycell_lam if bycell_lam[c])

    rhs_sorted = sorted(rhs_counter)
    out = collections.OrderedDict()
    out["declared target"] = str(target)
    out["cells"] = len(allcells)
    out["cells needing at least one cut (by path)"] = cells_with_cut
    out["cells needing at least one cut (by used cut row)"] = cells_with_cut_lam
    out["leaves"] = len(per_leaf)
    out["internal binary nodes"] = internal_nodes
    out["distinct cuts used (path keys)"] = len(distinct_cuts)
    out["distinct cuts used (rows in lam)"] = len(cuts_in_lam)
    out["largest number of cuts in one cell"] = max(cuts_per_cell.values())
    out["largest number of leaves in one cell"] = max(len(v) for v in bycell.values())
    out["largest path depth"] = max(len(p) for ps in bycell.values() for p in ps)
    out["leaves with rhs exactly 7/12"] = rhs_counter[Fraction(7, 12)]
    out["worst rhs"] = str(worst_rhs)
    out["second-worst rhs"] = str(rhs_sorted[-2]) if len(rhs_sorted) > 1 else "n/a"
    out["smallest componentwise surplus"] = str(min_surplus)
    out["max over leaves of sum of multipliers"] = str(max_lamsum)
    out["largest number of nonzero multipliers on a leaf"] = max_nnz
    out["total multipliers in certificate"] = total_mults
    out["largest multiplier denominator"] = MAXDEN
    out["leaves branching on a cut they never use"] = unused_branch_leaves
    out["distinct rows rebuilt"] = len(ROWCACHE)

    # ---------------- extra checks
    check_cut_legality(distinct_cuts | cuts_in_lam, E)
    wmin, wcnt, wtot = check_witness(E)
    out["witness: cut instances scanned"] = wtot
    out["witness: minimum cut right-hand side"] = str(wmin)
    out["witness: times the minimum is attained"] = wcnt

    print("=" * 72)
    print("BLIND THIRD VERIFIER  --  %s" % path)
    print("=" * 72)
    for k, v in out.items():
        print("  %-52s %s" % (k, v))
    print("-" * 72)
    if errs:
        print("FAILURES: %d" % len(errs))
        for e in errs[:40]:
            print("  !! " + e)
        if len(errs) > 40:
            print("  ... and %d more" % (len(errs) - 40))
        return 1
    print("ALL CHECKS PASS: every row rebuilt from the paper's formulas, every")
    print("row valid on its leaf's cell and sign-cover arm, Farkas (6.2) holds")
    print("at every leaf, and the cell/leaf tree is complete.")
    return 0

if __name__ == "__main__":
    default_certificate = Path(__file__).resolve().parents[1] / "cert_leaves_tail.jsonl"
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else str(default_certificate)))
