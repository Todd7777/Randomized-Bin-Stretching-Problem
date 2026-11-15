#!/usr/bin/env python3
"""check_paper_numbers.py -- exact replay of the numbers of the paper.

Standard library only (fractions, itertools).  Exact rational arithmetic throughout; no floats
except for printing.

Every check prints PASS or FAIL; exit status 1 if any fails.

Sections
  1  generic exact solver for a catalog (all causal deterministic policies, Pareto rows, game value)
  2  Example 1 (7/6), three-way family, two-stream family, ladder catalogs, small record members
  2b-2d the four-stream catalogs at capacities 10, 7 and 2520
  2e the five-stream catalog at capacity 209 (best lower bound on R_3 in the paper)
  2f the four-stream catalog at capacity 325 (best lower bound on H_4 in the paper)
  2g catalogs that attain the complete-game values at granularity 3..8 (files in cats/)
  2h the same for granularity 9 and 10 (26 and 14 streams), by scalar recursions over all policies
  3  capacity-17 record: the ten policy classes of Table 2, value 1337/1122, prior, lottery
  4  record family: closed form on integer grids inside and outside the triangle
  5  capacity-10^6 member; the quintic P, root isolation, the elimination identities, (xi*, eta*)
  6  the menu U: record margins, A-trivial face (closed form, true value), the point with 0.196579444...
  7  further catalogs with six to ten streams (information for Section 3.5; files in cats/)
  8  other numbers of bins: the catalogs of the theorem on many bins for m = 2..12, and the
     three-stream catalog at capacity 33 on five bins

Sections 2g, 2h and 7 read catalogs with their certificates (prior, lottery) from JSON files in the
directory cats/ next to this script; everything else is typed in below as it is printed in the paper.
A catalog value is accepted only if (i) the stored prior gives every policy expected cost at least the
value, and (ii) the stored lottery, on cost rows that this script finds to be attainable, costs at most
the value on every stream.  For (i) and (ii) the script uses two routes of its own: the list of all
Pareto-minimal policies (frontier, frontier_m) and scalar recursions over all policies (best_response,
row_attainable).  The catalogs of section 2h are checked by the second route only.
"""
import sys
import os
import json
import itertools
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))

T0 = time.time()
FAILS = []


def check(name, cond, info=""):
    print(("PASS " if cond else "FAIL ") + name + ((" :: " + str(info)) if info != "" else ""))
    if not cond:
        FAILS.append(name)
    sys.stdout.flush()


# ------------------------------------------------------------------------------------------
# 1. generic exact solver
# ------------------------------------------------------------------------------------------
def pareto(vecs):
    """Pareto-minimal vectors.  A vector that is <= v in every coordinate and differs from v comes
    before v in sorted order, and domination is transitive, so it is enough to compare each vector
    with the vectors already kept."""
    out = []
    for v in sorted(set(vecs)):
        dom = False
        for w in out:
            if all(a <= b for a, b in zip(w, v)):
                dom = True
                break
        if not dom:
            out.append(v)
    return out


def best_completion(loads, jobs):
    """least final maximum load when the jobs are placed on the loads (brute force)."""
    best = None
    for assign in itertools.product(range(3), repeat=len(jobs)):
        l = list(loads)
        for z, b in zip(jobs, assign):
            l[b] += z
        m = max(l)
        if best is None or m < best:
            best = m
    return best


def frontier(streams):
    """Pareto-minimal cost vectors (one entry per stream) over all deterministic causal policies.
    A policy sees the sizes so far; it is not told when the stream ends."""
    n = len(streams)
    memo = {}

    def rec(active, pos, loads):
        key = (active, pos, loads)
        if key in memo:
            return memo[key]
        if len(active) == 1:
            i = active[0]
            res = [(best_completion(loads, streams[i][pos:]),)]
            memo[key] = res
            return res
        ended = [i for i in active if len(streams[i]) == pos]
        groups = {}
        for i in active:
            if len(streams[i]) > pos:
                groups.setdefault(streams[i][pos], []).append(i)
        res_lists = []
        for z in sorted(groups):
            idxs = tuple(groups[z])
            opts = set()
            for b in range(3):
                l = list(loads)
                l[b] += z
                for vec in rec(idxs, pos + 1, tuple(sorted(l, reverse=True))):
                    opts.add(vec)
            res_lists.append((idxs, pareto(opts)))
        out = set()
        for combo in itertools.product(*[o for _, o in res_lists]):
            d = {}
            for i in ended:
                d[i] = max(loads)
            for (idxs, _), vec in zip(res_lists, combo):
                for i, c in zip(idxs, vec):
                    d[i] = c
            out.add(tuple(d[i] for i in active))
        res = pareto(out)
        memo[key] = res
        return res

    zero = Fr(0)
    return pareto(rec(tuple(range(n)), 0, (zero, zero, zero)))


def solve_linear(A, b):
    n = len(A)
    M = [[Fr(x) for x in row] + [Fr(y)] for row, y in zip(A, b)]
    for c in range(n):
        piv = None
        for r in range(c, n):
            if M[r][c] != 0:
                piv = r
                break
        if piv is None:
            return None
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]


def game_value(rows):
    """max over priors mu of min over rows of mu.row, exact; returns (value, prior)."""
    rows = pareto(rows)
    m = len(rows[0])
    best = None
    for s in range(1, m + 1):
        for S in itertools.combinations(range(m), s):
            for T in itertools.combinations(range(len(rows)), s):
                A = [[1] * s + [0]]
                b = [1]
                for i in T:
                    A.append([rows[i][j] for j in S] + [-1])
                    b.append(0)
                sol = solve_linear(A, b)
                if sol is None:
                    continue
                if any(x < 0 for x in sol[:s]):
                    continue
                mu = [Fr(0)] * m
                for j, x in zip(S, sol[:s]):
                    mu[j] = x
                val = min(sum(mu[j] * r[j] for j in range(m)) for r in rows)
                if best is None or val > best[0]:
                    best = (val, tuple(mu))
    return best


def lottery_value(rows, weights):
    """worst-column expected cost of the lottery (list of (row, weight))."""
    m = len(rows[0])
    assert sum(weights) == 1
    return max(sum(w * r[j] for r, w in zip(rows, weights)) for j in range(m))


def prior_ok(rows, mu, val):
    """the prior mu certifies the value: min over rows of mu.row equals val."""
    return sum(mu) == 1 and all(x >= 0 for x in mu) and min(sum(m * c for m, c in zip(mu, r)) for r in rows) == val


def catalog_value(streams):
    fr = frontier([tuple(Fr(z) for z in s) for s in streams])
    v, mu = game_value(fr)
    return v, mu, fr


# ------------------------------------------------------------------------------------------
# 2. small catalogs
# ------------------------------------------------------------------------------------------
print("== 2. small catalogs ==")
v, mu, fr = catalog_value([(1, 1, 1, 3, 3), (1, 1, 2, 2, 3)])
check("Example 1 value 7/6 (capacity 3)", v / 3 == Fr(7, 6), (v, mu, fr))
check("Example 1 Pareto rows are (3,4),(4,3)", sorted(fr) == [(3, 4), (4, 3)], fr)
check("Example 1 deterministic value 4/3", min(max(r) for r in fr) / 3 == Fr(4, 3))


def threeway(t):
    t = Fr(t)
    return [(t, t, t, 1 - 3 * t, 1, 1), (t, t, t, 1 - 2 * t, 1 - t, 1), (t, t, t, 1 - t, 1 - t, 1 - t)]


for t, expect in [(Fr(34, 123), Fr(8057, 6765)), (Fr(2, 7), Fr(25, 21)), (Fr(1, 4), Fr(19, 16))]:
    v, mu, fr = catalog_value(threeway(t))
    form = 1 + t * (2 - 5 * t) / (2 - 4 * t)
    check("three-way family t=%s value %s" % (t, expect), v == expect == form, (v, mu))
    pri = ((1 - 3 * t) / (1 - 2 * t), t / (2 - 4 * t), t / (2 - 4 * t))
    check("three-way family t=%s prior" % t, prior_ok(fr, pri, v), mu)
    lam = (t / (2 - 4 * t), (1 - 3 * t) / (2 - 4 * t), (1 - 2 * t) / (2 - 4 * t))
    frows = [(Fr(1), 2 - 3 * t, 2 - 2 * t), (1 + t, Fr(1), 1 + t), (1 + t, 1 + t, Fr(1))]
    check("three-way family t=%s lottery" % t, lottery_value(frows, list(lam)) == v)
    ex = sorted(tuple(c - 1 for c in r) for r in fr)
    want = sorted([(Fr(0), 1 - 3 * t, 1 - 2 * t), (t, Fr(0), t), (t, t, Fr(0))])
    check("three-way family t=%s has exactly the three excess rows" % t, ex == want, ex)
cnt = 0
bad = 0
for g in range(8, 41):
    for k in range(1, g):
        t = Fr(k, g)
        if Fr(1, 4) <= t < Fr(1, 3):
            cnt += 1
            v, _, _ = catalog_value(threeway(t))
            if v != 1 + t * (2 - 5 * t) / (2 - 4 * t):
                bad += 1
check("three-way closed form on %d rational t in [1/4,1/3)" % cnt, bad == 0, bad)


def twostream(x):
    x = Fr(x)
    b = 1 - 3 * x
    return [(b, x, x, x, 1, 1), (b, x, x, 3 * x, 1 - x, 1 - x)]


v, mu, fr = catalog_value(twostream(Fr(29, 99)))
check("two-stream family x=29/99 value 8119/6930", v == Fr(8119, 6930), (v, mu))
cnt = 0
bad = 0
for g in range(8, 61):
    for k in range(1, g):
        x = Fr(k, g)
        if Fr(1, 4) <= x < Fr(1, 3):
            cnt += 1
            v, _, _ = catalog_value(twostream(x))
            if v != 1 + x * (1 - 2 * x) / (1 - x):
                bad += 1
check("two-stream closed form on %d rational x in [1/4,1/3)" % cnt, bad == 0, bad)

LADDER = [
    ("25/21", 9, [(5, 3, 9, 9, 1), (5, 3, 4, 3, 9, 3), (5, 3, 4, 3, 6, 6)], Fr(25, 21)),
    ("19/16", 12, [(1, 1, 3, 4, 10, 9, 8), (1, 1, 3, 4, 3, 12, 12), (1, 1, 3, 4, 3, 8, 8, 8)], Fr(19, 16)),
    ("4361/3672", 300, [(96, 74, 26, 26, 4, 204, 226, 244), (96, 74, 26, 26, 4, 74, 300, 300),
                        (96, 74, 26, 26, 4, 74, 200, 200, 200)], Fr(4361, 3672)),
    ("33/28", 12, [(3, 3, 3, 9, 9, 9), (3, 3, 3, 4, 4, 3, 8, 8), (3, 3, 3, 4, 4, 3, 12, 4)], Fr(33, 28)),
]
for name, cap, streams, expect in LADDER:
    v, mu, fr = catalog_value(streams)
    check("ladder catalog %s (capacity %d)" % (name, cap), v / cap == expect, (v / cap, mu))

# small members of the record family (capacities 6, 9, 10) and the capacity-7 three-way catalog
SMALL = [
    ("record (2,1)/6", 6, [(2, 2, 1, 1, 6, 6), (2, 2, 1, 5, 2, 6), (2, 2, 1, 5, 4, 4)], Fr(25, 21)),
    ("three-way t=2/7", 7, [(2, 2, 2, 1, 7, 7), (2, 2, 2, 3, 5, 7), (2, 2, 2, 5, 5, 5)], Fr(25, 21)),
    ("record (3,2)/9", 9, [(3, 3, 2, 1, 9, 9), (3, 3, 2, 7, 3, 9), (3, 3, 2, 7, 6, 6)], Fr(19, 16)),
    ("record (3,2)/10", 10, [(3, 3, 2, 2, 10, 10), (3, 3, 2, 8, 4, 10), (3, 3, 2, 8, 7, 7)], Fr(131, 110)),
]
for name, cap, streams, expect in SMALL:
    v, mu, fr = catalog_value(streams)
    check("small catalog %s (capacity %d) value %s" % (name, cap, expect), v / cap == expect, (v / cap, mu, len(fr)))

# ------------------------------------------------------------------------------------------
# 2b. the four-stream catalog at capacity 10
# ------------------------------------------------------------------------------------------
print("== 2b. four streams, capacity 10 ==")
A4 = (3, 3, 3, 10, 10, 1)
B4 = (3, 3, 3, 7, 7, 7)
C4 = (3, 3, 3, 2, 10, 7, 2)
D4 = (3, 3, 3, 2, 5, 10, 4)
for nm, st in (("A", A4), ("B", B4), ("C", C4), ("D", D4)):
    check("four streams: stream %s has total size 30" % nm, sum(st) == 30)
PACK4 = {"A": [(3, 3, 3, 1), (10,), (10,)], "B": [(3, 7), (3, 7), (3, 7)],
         "C": [(10,), (3, 7), (3, 3, 2, 2)], "D": [(10,), (3, 3, 4), (3, 2, 5)]}
for nm, st in (("A", A4), ("B", B4), ("C", C4), ("D", D4)):
    bins = PACK4[nm]
    check("four streams: offline packing of %s is feasible" % nm,
          all(sum(b) <= 10 for b in bins) and sorted(x for b in bins for x in b) == sorted(st))
v, mu, fr = catalog_value([A4, B4, C4, D4])
check("four streams: value 203/170", v / 10 == Fr(203, 170), (v / 10, mu))
ROWS4 = [(10, 14, 11, 11), (13, 10, 13, 13), (13, 13, 10, 12), (13, 13, 12, 10)]
check("four streams: the Pareto-minimal cost rows are exactly the four stated ones",
      sorted(fr) == sorted(tuple(Fr(c) for c in r) for r in ROWS4), fr)
MU4 = (Fr(4, 34), Fr(12, 34), Fr(9, 34), Fr(9, 34))
check("four streams: prior (4,12,9,9)/34 certifies the value", prior_ok(fr, MU4, v), mu)
check("four streams: lottery (12,16,3,3)/34 costs 203/17 on every stream",
      all(sum(w * r[j] for r, w in zip(ROWS4, [Fr(12, 34), Fr(16, 34), Fr(3, 34), Fr(3, 34)])) == Fr(203, 17)
          for j in range(4)))
check("four streams: best deterministic policy costs 13", min(max(r) for r in fr) == 13)
check("four streams: 203/170 > capacity-10^6 record member > 19/16",
      Fr(203, 170) > Fr(2710434314855311, 2274563595940000) > Fr(19, 16))
check("four streams: 203/170 > 1.191628284078 (upper end of the interval of v*)",
      Fr(203, 170) > Fr(1191628284078, 10 ** 12))
# all six policies (root placement x placement of the job 2), as in the table of the paper
six = {}
for assign in itertools.product(range(3), repeat=3):
    l = [0, 0, 0]
    for z, b in zip((3, 3, 3), assign):
        l[b] += z
    key = tuple(sorted(l, reverse=True))
    cA = best_completion(key, (10, 10, 1))
    cB = best_completion(key, (7, 7, 7))
    for b in range(3):
        l2 = list(key)
        l2[b] += 2
        six[(key, key[b])] = (cA, cB, best_completion(l2, (10, 7, 2)), best_completion(l2, (5, 10, 4)))
WANT6 = {((9, 0, 0), 9): (10, 14, 11, 11), ((9, 0, 0), 0): (10, 14, 11, 11),
         ((6, 3, 0), 6): (13, 13, 10, 12), ((6, 3, 0), 3): (13, 13, 12, 10), ((6, 3, 0), 0): (13, 13, 12, 12),
         ((3, 3, 3), 3): (13, 10, 13, 13)}
check("four streams: the six policies of the table", six == WANT6, six)
check("four streams: weighted costs 406,406,406,406,424",
      sorted(4 * c[0] + 12 * c[1] + 9 * c[2] + 9 * c[3] for c in six.values()) == [406, 406, 406, 406, 406, 424])

# ------------------------------------------------------------------------------------------
# 2c. the four-stream catalog at capacity 7 (worked example of Section 3.5)
# ------------------------------------------------------------------------------------------
print("== 2c. four streams, capacity 7 ==")
A7 = (2, 2, 2, 7, 7, 1)
B7 = (2, 2, 2, 5, 5, 5)
C7 = (2, 2, 2, 3, 3, 5, 4)
D7 = (2, 2, 2, 3, 3, 7, 2)
PACK7 = {"A": [(2, 2, 2, 1), (7,), (7,)], "B": [(2, 5), (2, 5), (2, 5)],
         "C": [(2, 5), (3, 4), (2, 2, 3)], "D": [(7,), (2, 2, 3), (2, 3, 2)]}
for nm, st in (("A", A7), ("B", B7), ("C", C7), ("D", D7)):
    bins = PACK7[nm]
    check("capacity 7: stream %s has total size 21 and its offline packing is feasible" % nm,
          sum(st) == 21 and all(sum(b) <= 7 for b in bins)
          and sorted(x for b in bins for x in b) == sorted(st))
v, mu, fr = catalog_value([A7, B7, C7, D7])
check("capacity 7: value 109/91", v / 7 == Fr(109, 91), (v / 7, mu))
ROWS7 = [(7, 10, 9, 8), (7, 10, 8, 10), (9, 9, 9, 7), (9, 9, 7, 9), (9, 9, 8, 8), (9, 7, 8, 9)]
check("capacity 7: the Pareto-minimal cost rows are exactly the six stated ones",
      sorted(fr) == sorted(tuple(Fr(c) for c in r) for r in ROWS7), fr)
MU7 = (Fr(3, 13), Fr(2, 13), Fr(4, 13), Fr(4, 13))
check("capacity 7: prior (3,2,4,4)/13 certifies the value", prior_ok(fr, MU7, v), mu)
LOT7 = [((7, 10, 9, 8), Fr(4, 13)), ((9, 7, 8, 9), Fr(6, 13)), ((9, 9, 7, 9), Fr(1, 13)),
        ((9, 9, 9, 7), Fr(2, 13))]
check("capacity 7: lottery (4,6,1,2)/13 costs 109/13 on every stream",
      sum(w for _, w in LOT7) == 1
      and all(sum(w * r[j] for r, w in LOT7) == Fr(109, 13) for j in range(4)))
check("capacity 7: best deterministic policy costs 9", min(max(r) for r in fr) == 9)
check("capacity 7: 6/5 > 109/91 > 203/170 > 1.191628284078",
      Fr(6, 5) > Fr(109, 91) > Fr(203, 170) > Fr(1191628284078, 10 ** 12))
# all twelve policies (root placement x placement of the two jobs 3), as in the table of the paper
twelve = {}
for assign in itertools.product(range(3), repeat=3):
    l = [0, 0, 0]
    for z, b in zip((2, 2, 2), assign):
        l[b] += z
    key = tuple(sorted(l, reverse=True))
    cA = best_completion(key, (7, 7, 1))
    cB = best_completion(key, (5, 5, 5))
    for b1 in range(3):
        for b2 in range(3):
            l2 = list(key)
            l2[b1] += 3
            l2[b2] += 3
            twelve[(key, tuple(sorted(l2, reverse=True)))] = (
                cA, cB, best_completion(l2, (5, 4)), best_completion(l2, (7, 2)))
WANT12 = {((6, 0, 0), (6, 6, 0)): (7, 10, 9, 8), ((6, 0, 0), (6, 3, 3)): (7, 10, 8, 10),
          ((6, 0, 0), (9, 3, 0)): (7, 10, 9, 9), ((6, 0, 0), (12, 0, 0)): (7, 10, 12, 12),
          ((4, 2, 0), (7, 5, 0)): (9, 9, 9, 7), ((4, 2, 0), (7, 3, 2)): (9, 9, 7, 9),
          ((4, 2, 0), (8, 4, 0)): (9, 9, 8, 8), ((4, 2, 0), (10, 2, 0)): (9, 9, 10, 10),
          ((4, 2, 0), (6, 4, 2)): (9, 9, 8, 9), ((4, 2, 0), (5, 4, 3)): (9, 9, 8, 10),
          ((2, 2, 2), (8, 2, 2)): (9, 7, 8, 9), ((2, 2, 2), (5, 5, 2)): (9, 7, 9, 9)}
check("capacity 7: the twelve policies of the table", twelve == WANT12, twelve)
check("capacity 7: weighted costs 3A+2B+4C+4D of the twelve policies",
      sorted(3 * c[0] + 2 * c[1] + 4 * c[2] + 4 * c[3] for c in twelve.values())
      == sorted([109, 113, 113, 137, 109, 109, 109, 125, 113, 117, 109, 113]))

# ------------------------------------------------------------------------------------------
# 2d. the four-stream catalog at capacity 2520 (best lower bound of the paper)
# ------------------------------------------------------------------------------------------
print("== 2d. four streams, capacity 2520 ==")
GB = 2520
ROOTB = (685, 685, 342, 219, 123)
Ab = ROOTB + (2520, 2520, 466)
Bb = ROOTB + (1836, 1835, 1835)
Cb = ROOTB + (1027, 1493, 1493, 1493)
Db = ROOTB + (1027, 2520, 1959)
PACKB = {"A": [(685, 685, 342, 219, 123, 466), (2520,), (2520,)],
         "B": [(342, 219, 123, 1836), (685, 1835), (685, 1835)],
         "C": [(685, 219, 123, 1493), (685, 342, 1493), (1027, 1493)],
         "D": [(342, 219, 1959), (685, 685, 123, 1027), (2520,)]}
for nm, st in (("A", Ab), ("B", Bb), ("C", Cb), ("D", Db)):
    bins = PACKB[nm]
    check("capacity 2520: stream %s has total size 7560 and its offline packing is feasible" % nm,
          sum(st) == 3 * GB and all(sum(b) <= GB for b in bins)
          and sorted(x for b in bins for x in b) == sorted(st))
tb = time.time()
v, mu, fr = catalog_value([Ab, Bb, Cb, Db])
print("   solved in %.1f s; %d Pareto-minimal rows" % (time.time() - tb, len(fr)))
VALB = Fr(1271831579, 1059615900)
check("capacity 2520: value 1271831579/1059615900", v / GB == VALB, (v / GB, mu))
check("capacity 2520: value in size units is 2543663158/840965", v == Fr(2543663158, 840965))
check("capacity 2520: 40 Pareto-minimal cost rows", len(fr) == 40, len(fr))
MUB = (Fr(509210, 1681930), Fr(442069, 1681930), Fr(442069, 1681930), Fr(288582, 1681930))
check("capacity 2520: the stated prior is a probability vector", sum(MUB) == 1)
check("capacity 2520: the stated prior certifies the value", prior_ok(fr, MUB, v), mu)
LOTB = [((2520, 3670, 2986, 2986), Fr(29825565, 130349575)),
        ((3205, 2520, 3204, 3205), Fr(51083852, 130349575)),
        ((3081, 3328, 2986, 2520), Fr(24774890, 130349575)),
        ((3205, 2985, 2739, 3205), Fr(24665268, 130349575))]
check("capacity 2520: the lottery weights sum to 1", sum(w for _, w in LOTB) == 1)
check("capacity 2520: the lottery costs exactly the value on every stream",
      all(sum(w * r[j] for r, w in LOTB) == v for j in range(4)))
# the four policies of the lottery: root loads, bin that receives the job 1027, costs
POLB = [((2054, 0, 0), 1, (2520, 3670, 2986, 2986)),
        ((685, 685, 684), 2, (3205, 2520, 3204, 3205)),
        ((1493, 561, 0), 0, (3081, 3328, 2986, 2520)),
        ((1150, 685, 219), 2, (3205, 2985, 2739, 3205))]
ROOTLOADS = set()
for assign in itertools.product(range(3), repeat=5):
    l = [0, 0, 0]
    for z, b in zip(ROOTB, assign):
        l[b] += z
    ROOTLOADS.add(tuple(sorted(l)))
print("   %d root placements up to renaming bins" % len(ROOTLOADS))
for loads, b, costs in POLB:
    l2 = list(loads)
    l2[b] += 1027
    got = (best_completion(loads, Ab[5:]), best_completion(loads, Bb[5:]),
           best_completion(l2, Cb[6:]), best_completion(l2, Db[6:]))
    check("capacity 2520: policy with root loads %s is a root placement" % (loads,),
          tuple(sorted(loads)) in ROOTLOADS)
    check("capacity 2520: policy with root loads %s, job 1027 into bin %d: costs" % (loads, b),
          got == costs, got)
    check("capacity 2520: that cost row is Pareto-minimal",
          tuple(Fr(c) for c in costs) in set(fr))
check("capacity 2520: best deterministic policy costs 3205 (641/504)",
      min(max(r) for r in fr) == 3205)
check("capacity 2520: value > 6/5 > 109/91 > 19/16", VALB > Fr(6, 5) > Fr(109, 91) > Fr(19, 16))
check("capacity 2520: 1.20027 < value < 1.20028", Fr(120027, 100000) < VALB < Fr(120028, 100000))
check("capacity 2520: value - 6/5 = 292499/1059615900", VALB - Fr(6, 5) == Fr(292499, 1059615900))


# ------------------------------------------------------------------------------------------
# certificates: a prior against all Pareto-minimal policies, and a lottery on attainable rows
# ------------------------------------------------------------------------------------------
def attainable(row, fr):
    """some policy costs at most `row` on every stream (fr = Pareto-minimal cost rows)"""
    return any(all(a <= b for a, b in zip(f, row)) for f in fr)


def best_response(streams, weights, nb=3, start=None):
    """Second route to the prior certificate: the least value of sum_i weights[i] * cost_i over all
    deterministic causal policies on nb bins, by a scalar recursion (no Pareto sets).  A policy
    chooses one bin for each prefix; streams with different next jobs have been told apart, so the
    minimum is a sum over the next job sizes.  Bins with equal loads are interchangeable, so one
    bin of each load is tried.  start = loads at the beginning (sorted, largest first)."""
    memo = {}

    def rec(active, pos, loads):
        key = (active, pos, loads)
        if key in memo:
            return memo[key]
        tot = 0
        groups = {}
        for i in active:
            if len(streams[i]) == pos:
                tot += weights[i] * loads[0]
            else:
                groups.setdefault(streams[i][pos], []).append(i)
        for z in sorted(groups):
            idxs = tuple(groups[z])
            best = None
            for b in range(nb):
                if b > 0 and loads[b] == loads[b - 1]:
                    continue
                l = list(loads)
                l[b] += z
                c = rec(idxs, pos + 1, tuple(sorted(l, reverse=True)))
                if best is None or c < best:
                    best = c
            tot += best
        memo[key] = tot
        return tot

    if start is None:
        start = tuple([0] * nb)
    assert len(start) == nb and list(start) == sorted(start, reverse=True)
    return rec(tuple(range(len(streams))), 0, tuple(start))


def row_attainable(streams, row, nb=3):
    """Second route to the lottery certificate: is there a deterministic causal policy on nb bins
    whose cost on stream i is at most row[i] for every i?  (Loads only grow, so a prefix on which
    the largest load already exceeds the allowance of a stream that is still possible is hopeless.)"""
    memo = {}

    def rec(active, pos, loads):
        key = (active, pos, loads)
        if key in memo:
            return memo[key]
        ok = all(loads[0] <= row[i] for i in active)
        if ok:
            groups = {}
            for i in active:
                if len(streams[i]) > pos:
                    groups.setdefault(streams[i][pos], []).append(i)
            for z in sorted(groups):
                idxs = tuple(groups[z])
                found = False
                for b in range(nb):
                    if b > 0 and loads[b] == loads[b - 1]:
                        continue
                    l = list(loads)
                    l[b] += z
                    if rec(idxs, pos + 1, tuple(sorted(l, reverse=True))):
                        found = True
                        break
                if not found:
                    ok = False
                    break
        memo[key] = ok
        return ok

    return rec(tuple(range(len(streams))), 0, tuple([0] * nb))


def certified_value(name, streams, cap, packs, mu, lot, vunits, npareto=None):
    """Checks that the catalog has value vunits (in size units): feasibility, the prior as a
    lower-bound certificate against every Pareto-minimal policy, the lottery as an upper-bound
    certificate.  lot = list of (cost row, weight).  Returns the Pareto-minimal rows."""
    k = len(streams)
    check("%s: every stream fits into three bins of capacity %s (stored packings)" % (name, cap),
          all(sorted(x for b in bins for x in b) == sorted(st) and len(bins) <= 3
              and all(sum(b) <= cap for b in bins) for st, bins in zip(streams, packs)))
    check("%s: the streams are distinct" % name, len(set(streams)) == k)
    t0 = time.time()
    fr = frontier([tuple(Fr(z) for z in s) for s in streams])
    print("   %s: %d Pareto-minimal cost rows (%.1f s)" % (name, len(fr), time.time() - t0))
    if npareto is not None:
        check("%s: %d Pareto-minimal cost rows" % (name, npareto), len(fr) == npareto, len(fr))
    check("%s: the stated prior is a probability vector" % name, sum(mu) == 1 and all(x >= 0 for x in mu))
    check("%s: under the stated prior every policy costs at least %s, with equality for some" % (name, vunits),
          prior_ok(fr, mu, vunits), min(sum(m * c for m, c in zip(mu, r)) for r in fr))
    check("%s: the lottery weights are a probability vector" % name,
          sum(w for _, w in lot) == 1 and all(w >= 0 for _, w in lot))
    check("%s: every cost row of the lottery is attained by a policy" % name,
          all(attainable(tuple(Fr(c) for c in r), fr) for r, _ in lot))
    worst = max(sum(w * r[j] for r, w in lot) for j in range(k))
    check("%s: the lottery costs at most %s on every stream" % (name, vunits), worst <= vunits, worst)
    check("%s: second route (scalar recursions): the best response to the prior costs exactly the value, "
          "and every lottery row is attainable" % name,
          best_response(streams, mu) == vunits and all(row_attainable(streams, r) for r, _ in lot))
    return fr


def bins_from_labels(stream, labels):
    return [tuple(z for z, b in zip(stream, labels) if b == q) for q in range(3)]


def root_placements(root):
    out = set()
    for assign in itertools.product(range(3), repeat=len(root)):
        l = [0, 0, 0]
        for z, b in zip(root, assign):
            l[b] += z
        out.add(tuple(sorted(l, reverse=True)))
    return out


# ------------------------------------------------------------------------------------------
# 2e. the five-stream catalog at capacity 209 (best lower bound on R_3 in the paper)
# ------------------------------------------------------------------------------------------
print("== 2e. five streams, capacity 209 ==")
G5 = 209
ROOT5 = (58, 29, 29, 26, 26, 6)
A5 = ROOT5 + (151, 151, 151)
B5 = ROOT5 + (209, 209, 35)
C5 = ROOT5 + (87, 209, 157)
D5 = ROOT5 + (87, 122, 122, 122)
E5 = ROOT5 + (87, 183, 183)
STREAMS5 = [A5, B5, C5, D5, E5]
PACK5 = [[(58, 151), (29, 29, 151), (26, 26, 6, 151)],
         [(58, 29, 29, 26, 26, 6, 35), (209,), (209,)],
         [(58, 29, 29, 6, 87), (26, 26, 157), (209,)],
         [(87, 122), (58, 29, 122), (29, 26, 26, 6, 122)],
         [(58, 29, 29, 6, 87), (26, 183), (26, 183)]]
check("capacity 209: every stream has total size 627 and every offline bin is exactly full",
      all(sum(s) == 3 * G5 for s in STREAMS5) and all(sum(b) == G5 for bins in PACK5 for b in bins))
V5 = Fr(240961012, 959723)
MU5 = tuple(Fr(x, 959723) for x in (217970, 242640, 78400, 319223, 101490))
LOT5 = [((302, 209, 244, 244, 270), Fr(382058, 2879169)),
        ((273, 261, 209, 244, 235), Fr(17536, 2879169)),
        ((290, 244, 226, 244, 226), Fr(692231, 2879169)),
        ((215, 264, 264, 264, 247), Fr(1018290, 2879169)),
        ((238, 261, 261, 244, 270), Fr(769054, 2879169))]
fr5 = certified_value("capacity 209", STREAMS5, G5, PACK5, MU5, LOT5, V5, npareto=82)
check("capacity 209: the lottery costs exactly the value on every stream",
      all(sum(w * r[j] for r, w in LOT5) == V5 for j in range(5)))
check("capacity 209: value 240961012/200582107 of the capacity", V5 / G5 == Fr(240961012, 200582107))
check("capacity 209: 1.20130 < value < 1.20131", Fr(120130, 100000) < V5 / G5 < Fr(120131, 100000), float(V5 / G5))
check("capacity 209: value > 6/5 > 403/336 > 109/91 > 19/16",
      V5 / G5 > Fr(6, 5) > Fr(403, 336) > Fr(109, 91) > Fr(19, 16))
# the five policies of the lottery: root loads, bin that receives the job 87, costs on (A,B,C,D,E)
POL5 = [((174, 0, 0), 1, (302, 209, 244, 244, 270)),      # 87 into an empty bin
        ((122, 52, 0), 0, (273, 261, 209, 244, 235)),     # 87 onto the 122
        ((139, 35, 0), 0, (290, 244, 226, 244, 226)),     # 87 onto the 139
        ((64, 55, 55), 1, (215, 264, 264, 264, 247)),     # 87 onto a 55
        ((87, 52, 35), 2, (238, 261, 261, 244, 270))]     # 87 onto the 35
RP5 = root_placements(ROOT5)
check("capacity 209: 46 root placements up to renaming bins", len(RP5) == 46, len(RP5))
for loads, b, costs in POL5:
    l2 = list(loads)
    l2[b] += 87
    got = (best_completion(loads, A5[6:]), best_completion(loads, B5[6:]),
           best_completion(l2, C5[7:]), best_completion(l2, D5[7:]), best_completion(l2, E5[7:]))
    check("capacity 209: root loads %s are a placement of the root" % (loads,), loads in RP5)
    check("capacity 209: root loads %s, job 87 into bin %d: costs %s" % (loads, b, costs), got == costs, got)
    check("capacity 209: that cost row is Pareto-minimal", tuple(Fr(c) for c in costs) in set(fr5))
check("capacity 209: best single policy costs 264 (264/209 = 24/19)", min(max(r) for r in fr5) == 264)
check("capacity 209: prior on the first lottery row gives 240961012/959723",
      sum(m * c for m, c in zip(MU5, LOT5[0][0])) == V5)

# ------------------------------------------------------------------------------------------
# 2f. the four-stream catalog at capacity 325 (best lower bound on H_4 in the paper)
# ------------------------------------------------------------------------------------------
print("== 2f. four streams, capacity 325 ==")
G4 = 325
ROOT4 = (88, 88, 44, 27, 17)
A4b = ROOT4 + (237, 237, 237)
B4b = ROOT4 + (325, 325, 61)
C4b = ROOT4 + (132, 325, 254)
D4b = ROOT4 + (132, 193, 193, 193)
STREAMS4 = [A4b, B4b, C4b, D4b]
PACK4b = [[(88, 237), (88, 237), (44, 27, 17, 237)],
          [(88, 88, 44, 27, 17, 61), (325,), (325,)],
          [(88, 88, 17, 132), (44, 27, 254), (325,)],
          [(132, 193), (88, 44, 193), (88, 27, 17, 193)]]
check("capacity 325: every stream has total size 975 and every offline bin is exactly full",
      all(sum(s) == 3 * G4 for s in STREAMS4) and all(sum(b) == G4 for bins in PACK4b for b in bins))
V4 = Fr(1091879, 2799)
MU4b = tuple(Fr(x, 5598) for x in (1457, 1726, 958, 1457))
LOT4b = [((325, 413, 413, 413), Fr(5503, 13995)),
         ((474, 325, 386, 386), Fr(3124, 13995)),
         ((430, 396, 325, 386), Fr(2684, 13995)),
         ((386, 413, 413, 352), Fr(2684, 13995))]
fr4 = certified_value("capacity 325", STREAMS4, G4, PACK4b, MU4b, LOT4b, V4, npareto=38)
check("capacity 325: the lottery costs exactly the value on every stream",
      all(sum(w * r[j] for r, w in LOT4b) == V4 for j in range(4)))
check("capacity 325: value 1091879/909675 of the capacity", V4 / G4 == Fr(1091879, 909675))
check("capacity 325: 1.20029 < value < 1.20030", Fr(120029, 100000) < V4 / G4 < Fr(120030, 100000), float(V4 / G4))
check("capacity 325: value - 6/5 = 269/909675 > 0", V4 / G4 - Fr(6, 5) == Fr(269, 909675))
check("capacity 325: value > the capacity-2520 value", V4 / G4 > VALB)
POL4b = [((88, 88, 88), 0, (325, 413, 413, 413)),         # 132 onto an 88
         ((264, 0, 0), 1, (474, 325, 386, 386)),          # 132 into an empty bin
         ((193, 71, 0), 0, (430, 396, 325, 386)),         # 132 onto the 193
         ((149, 88, 27), 2, (386, 413, 413, 352))]        # 132 onto the 27
RP4 = root_placements(ROOT4)
check("capacity 325: 25 root placements up to renaming bins", len(RP4) == 25, len(RP4))
for loads, b, costs in POL4b:
    l2 = list(loads)
    l2[b] += 132
    got = (best_completion(loads, A4b[5:]), best_completion(loads, B4b[5:]),
           best_completion(l2, C4b[6:]), best_completion(l2, D4b[6:]))
    check("capacity 325: root loads %s are a placement of the root" % (loads,), loads in RP4)
    check("capacity 325: root loads %s, job 132 into bin %d: costs %s" % (loads, b, costs), got == costs, got)
    check("capacity 325: that cost row is Pareto-minimal", tuple(Fr(c) for c in costs) in set(fr4))
check("capacity 325: best single policy costs 413 (413/325)", min(max(r) for r in fr4) == 413)


# ------------------------------------------------------------------------------------------
# 2g. catalogs that attain the values of the complete games at granularity 3..8 (from cats/)
# ------------------------------------------------------------------------------------------
def json_catalog(fname, expect, nstreams=None, npos=None):
    d = json.load(open(os.path.join(HERE, "cats", fname)))
    cap = d.get("g", d.get("capacity"))
    streams = [tuple(s) for s in d["streams"]]
    labels = d.get("packings", d.get("offline_packing"))
    packs = [bins_from_labels(s, lab) for s, lab in zip(streams, labels)]
    mu = tuple(Fr(x) for x in d["prior"])
    lot = []
    for item in d["mixture"]:
        if isinstance(item, dict):
            lot.append((tuple(item["costs"]), Fr(item["weight"])))
        else:
            lot.append((tuple(item[0]), Fr(item[1])))
    name = "%s (capacity %d, %d streams)" % (fname, cap, len(streams))
    check("%s: labels of the stored packings are bins 0, 1, 2 and cover every job" % name,
          all(len(s) == len(lab) and set(lab) <= {0, 1, 2} for s, lab in zip(streams, labels)))
    vunits = Fr(d["value_units"])
    fr = certified_value(name, streams, cap, packs, mu, lot, vunits)
    check("%s: value %s of the capacity" % (name, expect), vunits / cap == expect, vunits / cap)
    pos = sum(1 for x in mu if x > 0)
    print("   %s: %d streams, %d with positive prior, best single policy %s"
          % (name, len(streams), pos, min(max(r) for r in fr) / cap))
    if nstreams is not None:
        check("%s: %d streams, %d with positive prior" % (name, nstreams, npos),
              len(streams) == nstreams and pos == npos, (len(streams), pos))
    return streams, fr, mu


print("== 2g. catalogs attaining the complete-game values, granularity 3..8 ==")
COMPLETE = [("cat_lp_m3_g3.json", Fr(7, 6), 2, 2), ("cat_lp_m3_g4_grb.json", Fr(19, 16), 3, 3),
            ("cat_lp_m3_g5_grb.json", Fr(47, 40), 5, 4), ("cat_lp_m3_g6_nocross_vertex.json", Fr(143, 120), 9, 9),
            ("cat_lp2_m3_g7_full.json", Fr(403, 336), 6, 6), ("cat_lp2_m3_g8_full.json", Fr(55, 46), 8, 8)]
for fname, expect, ns, npos in COMPLETE:
    st, frc, muc = json_catalog(fname, expect, ns, npos)
    if fname == "cat_lp_m3_g4_grb.json":
        # (the stored catalog is (1,1,1,1,4,4), (1,1,1,3,2,4), (1,1,1,3,3,3): not a three-way fork)
        tw = [tuple(4 * z for z in s) for s in threeway(Fr(1, 4))]
        check("granularity 4: the three-way family at t = 1/4 is (1,1,1,1,4,4), (1,1,1,2,3,4), (1,1,1,3,3,3) "
              "in units of 1/4 and has the same value 19/16",
              tw == [(1, 1, 1, 1, 4, 4), (1, 1, 1, 2, 3, 4), (1, 1, 1, 3, 3, 3)]
              and catalog_value(threeway(Fr(1, 4)))[0] == Fr(19, 16))
    if fname == "cat_lp2_m3_g7_full.json":
        check("granularity 7: the six streams printed in the paper, in that order, with the prior (15,11,10,7,3,2)/48",
              st == [(1, 1, 2, 2, 3, 4, 4, 4), (1, 1, 2, 2, 5, 5, 5), (1, 1, 2, 2, 7, 1, 7),
                     (1, 1, 2, 2, 3, 6, 6), (1, 1, 2, 2, 6, 7, 2), (1, 1, 2, 2, 3, 3, 7, 2)]
              and muc == tuple(Fr(x, 48) for x in (15, 11, 10, 7, 3, 2)))
        check("granularity 7: 11 Pareto-minimal policies", len(frc) == 11, len(frc))
check("complete-game values: 143/120 > v* > 25/21 and 403/336 > 109/91 > 55/46 > 143/120 > 19/16 > 47/40 > 7/6",
      Fr(143, 120) > Fr(1191628284078, 10 ** 12) > Fr(25, 21)
      and Fr(403, 336) > Fr(109, 91) > Fr(55, 46) > Fr(143, 120) > Fr(19, 16) > Fr(47, 40) > Fr(7, 6))
check("truncated decimals of the table of complete games: 1.1666, 1.1875, 1.1750, 1.1916, 1.1994, 1.1956",
      all(Fr(lo4, 10 ** 4) <= v4 < Fr(lo4 + 1, 10 ** 4) for lo4, v4 in
          [(11666, Fr(7, 6)), (11875, Fr(19, 16)), (11750, Fr(47, 40)), (11916, Fr(143, 120)),
           (11994, Fr(403, 336)), (11956, Fr(55, 46))]))
check("240961012/200582107 > 403/336 (five streams beat every complete game computed)",
      Fr(240961012, 200582107) > Fr(403, 336))


# ------------------------------------------------------------------------------------------
# 2h. granularity 9 and 10: larger catalogs, certified by the scalar recursions only
# ------------------------------------------------------------------------------------------
def json_catalog_dp(fname, expect, nstreams, npos):
    """As json_catalog, but both certificates are checked by the scalar recursions best_response and
    row_attainable (which range over all policies) instead of the list of Pareto-minimal policies."""
    d = json.load(open(os.path.join(HERE, "cats", fname)))
    cap = d.get("g", d.get("capacity"))
    streams = [tuple(s) for s in d["streams"]]
    labels = d.get("packings", d.get("offline_packing"))
    packs = [bins_from_labels(s, lab) for s, lab in zip(streams, labels)]
    mu = tuple(Fr(x) for x in d["prior"])
    lot = []
    for item in d["mixture"]:
        if isinstance(item, dict):
            lot.append((tuple(item["costs"]), Fr(item["weight"])))
        else:
            lot.append((tuple(item[0]), Fr(item[1])))
    vunits = Fr(d["value_units"])
    k = len(streams)
    name = "%s (capacity %d, %d streams)" % (fname, cap, k)
    t0 = time.time()
    check("%s: labels of the stored packings are bins 0, 1, 2 and cover every job" % name,
          all(len(s) == len(lab) and set(lab) <= {0, 1, 2} for s, lab in zip(streams, labels)))
    check("%s: every stream fits into three bins of capacity %s (stored packings)" % (name, cap),
          all(sorted(x for b in bins for x in b) == sorted(st) and all(sum(b) <= cap for b in bins)
              for st, bins in zip(streams, packs)))
    check("%s: the streams are distinct and their sizes are positive integers" % name,
          len(set(streams)) == k and all(isinstance(z, int) and z > 0 for s in streams for z in s))
    check("%s: the stated prior is a probability vector" % name, sum(mu) == 1 and all(x >= 0 for x in mu))
    br = best_response(streams, mu)
    check("%s: under the stated prior the cheapest policy costs exactly %s" % (name, vunits), br == vunits, br)
    check("%s: the lottery weights are a probability vector" % name,
          sum(w for _, w in lot) == 1 and all(w >= 0 for _, w in lot))
    check("%s: every cost row of the lottery is attained by a policy" % name,
          all(len(r) == k and row_attainable(streams, r) for r, _ in lot))
    worst = max(sum(w * r[j] for r, w in lot) for j in range(k))
    check("%s: the lottery costs at most %s on every stream" % (name, vunits), worst <= vunits, worst)
    check("%s: value %s of the capacity" % (name, expect), vunits / cap == expect, vunits / cap)
    pos = sum(1 for x in mu if x > 0)
    check("%s: %d streams, %d with positive prior" % (name, nstreams, npos),
          k == nstreams and pos == npos, (k, pos))
    print("   %s: %d lottery rows (%.1f s)" % (name, len(lot), time.time() - t0))


print("== 2h. granularity 9 and 10 (scalar recursions) ==")
check("scalar recursions: a lottery row of the catalogs at capacity 209 and 325 lowered by 1 in any one "
      "coordinate is not attainable",
      not any(row_attainable(sts, r[:j] + (r[j] - 1,) + r[j + 1:])
              for sts, lot_ in ((STREAMS5, LOT5), (STREAMS4, LOT4b)) for r, _ in lot_ for j in range(len(r))))
json_catalog_dp("cat_lp2_m3_g9_full.json", Fr(6971, 5823), 26, 26)
json_catalog_dp("cat_lp2_m3_g10_nocross_vertex.json", Fr(1781, 1485), 14, 14)
check("granularity 9 and 10: 6971/5823 = 1.1971..., 1781/1485 = 1.1993..., and both are below 403/336",
      Fr(11971, 10 ** 4) <= Fr(6971, 5823) < Fr(11972, 10 ** 4)
      and Fr(11993, 10 ** 4) <= Fr(1781, 1485) < Fr(11994, 10 ** 4)
      and Fr(6971, 5823) < Fr(1781, 1485) < Fr(403, 336))

# ------------------------------------------------------------------------------------------
# 3. the capacity-17 record
# ------------------------------------------------------------------------------------------
print("== 3. capacity-17 record ==")
A17 = (5, 5, 4, 3, 17, 17)
B17 = (5, 5, 4, 13, 7, 17)
C17 = (5, 5, 4, 13, 12, 12)
v, mu, fr = catalog_value([A17, B17, C17])
check("capacity-17 value 1337/1122", v / 17 == Fr(1337, 1122), (v / 17, mu))
check("capacity-17 prior (25,18,23)/66 certifies the value", prior_ok(fr, (Fr(25, 66), Fr(18, 66), Fr(23, 66)), v), mu)
print("   optimal prior found:", mu)
check("capacity-17 deterministic value 22/17", min(max(r) for r in fr) == 22)
print("   Pareto-minimal cost rows:", [tuple(int(c) for c in r) for r in fr])
FOL = [(17, 20, 24), (21, 17, 22), (22, 22, 17)]
check("follow rows are Pareto rows", all(tuple(Fr(c) for c in r) in fr for r in FOL))
lv = lottery_value(FOL, [Fr(20, 66), Fr(15, 66), Fr(31, 66)])
check("lottery (20,15,31)/66 costs 1337/66 on every stream", lv == Fr(1337, 66), lv)
check("every column of the lottery equals 1337/66",
      all(sum(w * r[j] for r, w in zip(FOL, [Fr(20, 66), Fr(15, 66), Fr(31, 66)])) == Fr(1337, 66) for j in range(3)))

# the ten policy classes of Table 2
TABLE2 = {
    ((14, 0, 0), 0): (0, 3, 7), ((14, 0, 0), 14): (0, 10, 10),
    ((10, 4, 0), 4): (4, 0, 5), ((10, 4, 0), 0): (4, 4, 5), ((10, 4, 0), 10): (4, 6, 6),
    ((9, 5, 0), 0): (5, 5, 4), ((9, 5, 0), 5): (5, 1, 4), ((9, 5, 0), 9): (5, 5, 5),
    ((5, 5, 4), 4): (5, 5, 0), ((5, 5, 4), 5): (5, 4, 1),
}
seen = {}
for assign in itertools.product(range(3), repeat=3):
    l = [0, 0, 0]
    for z, b in zip((5, 5, 4), assign):
        l[b] += z
    key = tuple(sorted(l, reverse=True))
    cA = best_completion(key, (3, 17, 17))
    for b in range(3):
        l2 = list(key)
        l2[b] += 13
        e = (cA - 17, best_completion(l2, (7, 17)) - 17, best_completion(l2, (12, 12)) - 17)
        k2 = (key, key[b])
        if k2 in seen:
            assert seen[k2] == e
        seen[k2] = e
check("Table 2: exactly ten classes", len(seen) == 10, len(seen))
check("Table 2: all ten excess vectors", seen == TABLE2, seen)
w = {k: 25 * e[0] + 18 * e[1] + 23 * e[2] for k, e in seen.items()}
print("   weighted excess 25A+18B+23C:", sorted(w.items()))
WANT_W = {((14, 0, 0), 0): 215, ((14, 0, 0), 14): 410, ((10, 4, 0), 4): 215, ((10, 4, 0), 0): 287,
          ((10, 4, 0), 10): 346, ((9, 5, 0), 0): 307, ((9, 5, 0), 5): 235, ((9, 5, 0), 9): 330,
          ((5, 5, 4), 4): 215, ((5, 5, 4), 5): 220}
check("Table 2: weighted column", w == WANT_W)
check("Table 2: minimum weighted excess is 215", min(w.values()) == 215)
check("Table 2: least row maximum is 5 (deterministic 22/17)", min(max(e) for e in seen.values()) == 5)
# every Pareto row of the full game is one of the ten rows
ten = set(tuple(Fr(17 + x) for x in e) for e in seen.values())
check("every Pareto row of the complete game is among the ten rows", all(r in ten for r in fr))


# ------------------------------------------------------------------------------------------
# 4. record family: closed form on integer grids
# ------------------------------------------------------------------------------------------
print("== 4. record family, closed form ==")


def record(s, t):
    s, t = Fr(s), Fr(t)
    return [(s, s, t, 1 - 2 * s - t, 1, 1), (s, s, t, 1 - t, 1 - 2 * s, 1), (s, s, t, 1 - t, 1 - s, 1 - s)]


def vform(s, t):
    s, t = Fr(s), Fr(t)
    return 1 + s * (s + t - 2 * s * s - 3 * s * t) / (2 * s - 4 * s * s - s * t + t * t)


def prior_form(s, t):
    s, t = Fr(s), Fr(t)
    al, be = 1 - 2 * s - t, 1 - 2 * s
    pt = (s * (al + be - s), s * s - be * (s - t), t * s + al * (s - t))
    d = sum(pt)
    return tuple(x / d for x in pt)


inside = 0
bad = 0
badp = 0
badl = 0
for g in (17, 20, 23, 24, 29, 30, 36, 41, 48, 60):
    for s in range(1, g):
        for t in range(1, s):
            if 3 * s <= g and 2 * (s + t) >= g:
                inside += 1
                v, mu, _ = catalog_value(record(Fr(s, g), Fr(t, g)))
                if v != vform(Fr(s, g), Fr(t, g)):
                    bad += 1
                    print("   MISMATCH inside triangle", s, t, g, v, vform(Fr(s, g), Fr(t, g)))
                xs, xt = Fr(s, g), Fr(t, g)
                frr = catalog_value(record(xs, xt))[2]
                if not prior_ok(frr, prior_form(xs, xt), v):
                    badp += 1
                al, be = 1 - 2 * xs - xt, 1 - 2 * xs
                fol = [(Fr(1), 1 + al, 1 + be), (1 + xt, Fr(1), 1 + xs), (1 + xs, 1 + xs, Fr(1))]
                lam = (xt * xs, al * xs, al * xs + xt * xt)
                lam = [x / sum(lam) for x in lam]
                if lottery_value(fol, lam) != v:
                    badl += 1
                for fr_ in fol:
                    if not any(all(a <= b for a, b in zip(r, fr_)) for r in frr):
                        badl += 1
check("record family: closed form at %d grid points of the triangle" % inside, bad == 0 and inside > 50, bad)
check("record family: closed-form prior certifies the value (same points)", badp == 0, badp)
check("record family: closed-form lottery on the three follow rows attains the value (same points)", badl == 0, badl)
# information only: how the closed form behaves outside the triangle
out_n = 0
out_diff = 0
for g in (24, 30):
    for s in range(1, g // 2):
        for t in range(1, s):
            if 2 * s + t < g and not (3 * s <= g and 2 * (s + t) >= g):
                den = 2 * Fr(s, g) - 4 * Fr(s, g) ** 2 - Fr(s, g) * Fr(t, g) + Fr(t, g) ** 2
                if den == 0:
                    continue
                out_n += 1
                v, _, _ = catalog_value(record(Fr(s, g), Fr(t, g)))
                if v != vform(Fr(s, g), Fr(t, g)):
                    out_diff += 1
print("   INFO outside the triangle (g = 24, 30): %d points, closed form differs at %d" % (out_n, out_diff))

# ------------------------------------------------------------------------------------------
# 5. capacity-10^6 member, the quintic, the elimination, (xi*, eta*)
# ------------------------------------------------------------------------------------------
print("== 5. algebra ==")
s6, t6 = Fr(295605, 10 ** 6), Fr(235102, 10 ** 6)
claim6 = Fr(2710434314855311, 2274563595940000)
check("capacity-10^6 member lies in the triangle", 0 < t6 < s6 <= Fr(1, 3) and s6 + t6 >= Fr(1, 2))
check("capacity-10^6 closed form = 2710434314855311/2274563595940000", vform(s6, t6) == claim6, vform(s6, t6))
check("capacity-10^6 value > 1.191628284077", claim6 > Fr(1191628284077, 10 ** 12))
check("capacity-10^6 difference of cross products is 1318036152620000",
      2710434314855311 * 10 ** 12 - 1191628284077 * 2274563595940000 == 1318036152620000)
v, mu, _ = catalog_value(record(s6, t6))
check("capacity-10^6 brute-force game value equals the closed form", v == claim6, v)
check("capacity-10^6: 19/16 < value", Fr(19, 16) < claim6)


def peval(c, x):
    """c[0] + c[1] x + ..."""
    r = Fr(0)
    for a in reversed(c):
        r = r * x + a
    return r


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def padd(a, b, sb=1):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + sb * (b[i] if i < len(b) else 0) for i in range(n)]


def pstrip(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


P = [-18812, 78572, -130868, 108786, -45189, 7514]          # ascending powers of z
Q = [3, 8, -504, 3170, -7619, 7514]                         # ascending powers of w
# Q(w) = P(1+w)
shift = [0]
pw = [1]
for a in P:
    shift = padd(shift, [a * x for x in pw])
    pw = pmul(pw, [1, 1])
check("Q(w) = P(1+w)", pstrip(shift) == Q, pstrip(shift))
Ap = [-9, -6, 263]
Bp = [3, -37, 18, 442]
c_ = [3, 7]
d_ = [1, 6, 17]
calA = padd([108 * x for x in d_], [16 * x for x in pmul(c_, c_)], -1)
check("108 d - 16 c^2 = 4 A'", pstrip(calA) == [4 * x for x in Ap], calA)
calB = padd(padd([9 * x for x in pmul(d_, d_)], [108 * x for x in pmul(c_, [0, 0, 1])], -1), pmul(pmul(c_, c_), d_), -1)
check("9 d^2 - 108 c w^2 - c^2 d = 4 w B'", pstrip(calB) == pmul([0, 4], Bp), calB)
H = padd(padd(pmul(pmul(c_, [0, 1]), pmul(Ap, Ap)), pmul(d_, pmul(Ap, Bp)), -1), [12 * x for x in pmul([0, 1], pmul(Bp, Bp))])
Hw = [27, 198, -4053, 7754, 39873, -97042, -57743, 368186]
check("H(w) = c w A'^2 - d A' B' + 12 w B'^2 has the stated coefficients", pstrip(H) == Hw, pstrip(H))
check("H(w) = (7w+3)^2 Q(w)", pstrip(H) == pstrip(pmul(pmul([3, 7], [3, 7]), Q)))
# the polynomial identity c^2 E1 = (c(9s-c)+9d) E2 + (B s - w^2 A) at random rational points
import random
random.seed(1)
okid = True
for _ in range(200):
    s = Fr(random.randint(-50, 50), random.randint(1, 50))
    w = Fr(random.randint(-50, 50), random.randint(1, 50))
    c = 3 + 7 * w
    d = 1 + 6 * w + 17 * w * w
    E1 = 9 * s ** 3 - c * s * s + 4 * w * w
    E2 = c * s * s - d * s + 12 * w * w
    cA = 108 * d - 16 * c * c
    cB = 9 * d * d - 108 * c * w * w - c * c * d
    if c * c * E1 != (c * (9 * s - c) + 9 * d) * E2 + (cB * s - w * w * cA):
        okid = False
check("identity c^2 E1 = (c(9s-c)+9d) E2 + (B s - w^2 A) at 200 rational points", okid)
# (E_s), (E_0) reduce to (1'), (3') after t = s(1-3s+w)/(2w): check at random rational points
okred = True
for _ in range(200):
    s = Fr(random.randint(1, 50), random.randint(1, 50))
    w = Fr(random.randint(1, 50), random.randint(1, 50))
    t = s * (1 - 3 * s + w) / (2 * w)
    d = 1 + 6 * w + 17 * w * w
    one_p = 18 * s ** 3 - (9 + 21 * w) * s * s + d * s - 4 * w * w
    three_p = 9 * s ** 3 - (6 + 14 * w) * s * s + d * s - 8 * w * w
    Es = (2 * s + t - 6 * s * s - 6 * s * t) - w * (2 - 8 * s - t)
    E0 = (s * s + s * t - 2 * s ** 3 - 3 * s * s * t) - w * (2 * s - 4 * s * s - s * t + t * t)
    if 2 * w * Es != one_p or 4 * w * E0 != s * three_p:
        okred = False
check("2w(E_s) = (1') and 4w(E_0) = s(3') after substituting t", okred)

lo = Fr(1191628284077, 10 ** 12)
hi = lo + Fr(1, 10 ** 12)
plo, phi = peval(P, lo), peval(P, hi)
check("P changes sign on (1.191628284077, 1.191628284078)", plo * phi < 0, (float(plo), float(phi)))
dP = [k * a for k, a in enumerate(P)][1:]
ddP = [k * a for k, a in enumerate(dP)][1:]
M2 = sum(abs(a) * 2 ** k for k, a in enumerate(ddP))        # bound on |P''| over [0,2]
check("P is monotone on that interval (one root there)", abs(peval(dP, lo)) > M2 * Fr(1, 10 ** 12),
      (float(peval(dP, lo)), M2))
# bisection to width < 1e-40
a, b = lo, hi
sa = plo
while b - a > Fr(1, 10 ** 40):
    m = (a + b) / 2
    pm = peval(P, m)
    if pm == 0:
        a = b = m
        break
    if (pm > 0) == (sa > 0):
        a = m
    else:
        b = m
print("   v* in [%s, %s]" % ("%.30f" % a, "%.30f" % b))
VLO, VHI = a, b       # P changes sign on [VLO, VHI] and has one zero in (lo, hi): v* lies in [VLO, VHI]
check("bisection interval for v*: width below 1e-40, inside (lo, hi), sign change of P",
      VHI - VLO < Fr(1, 10 ** 40) and lo <= VLO < VHI <= hi and peval(P, VLO) * peval(P, VHI) < 0)
from decimal import Decimal, getcontext
getcontext().prec = 50


def dec(fr, digits=30):
    return str((Decimal(fr.numerator) / Decimal(fr.denominator)).quantize(Decimal(10) ** -digits))


print("   v*  =", dec(a), "..", dec(b))
check("v* = 1.19162828407762...", dec(a, 14) == "1.19162828407762" and dec(b, 14) == "1.19162828407762", (dec(a), dec(b)))


def st_of_w(w):
    s = w * peval(Ap, w) / peval(Bp, w)
    t = s * (1 - 3 * s + w) / (2 * w)
    return s, t


for nm, zz in (("lower end", a), ("upper end", b)):
    w = zz - 1
    s, t = st_of_w(w)
    print("   %s: xi = %s  eta = %s" % (nm, dec(s, 20), dec(t, 20)))
    check("(xi*, eta*) %s lies in the triangle" % nm, 0 < t < s <= Fr(1, 3) and s + t >= Fr(1, 2),
          (float(s), float(t)))
    N = s * s + s * t - 2 * s ** 3 - 3 * s * s * t
    D = 2 * s - 4 * s * s - s * t + t * t
    check("closed form at this point equals 1+w up to 1e-35 (%s)" % nm, abs(N / D - w) < Fr(1, 10 ** 35),
          float(N / D - w))
    check("B'(w) != 0 and 3+7w != 0 and D != 0 (%s)" % nm, peval(Bp, w) != 0 and 3 + 7 * w != 0 and D != 0)
    xi_poly = [-4, 84, -576, 1762, -2489, 1326]
    check("xi satisfies the stated quintic up to 1e-30 (%s)" % nm, abs(peval(xi_poly, s)) < Fr(1, 10 ** 30),
          float(peval(xi_poly, s)))
    eta_from_xi = (-86190 * s ** 4 + 124657 * s ** 3 - 64286 * s * s + 13624 * s - 912) / 254
    check("eta formula in xi agrees up to 1e-30 (%s)" % nm, abs(eta_from_xi - t) < Fr(1, 10 ** 30),
          float(eta_from_xi - t))
    check("xi in (0.29560515319670, 0.29560515319671) (%s)" % nm,
          Fr(29560515319670, 10 ** 14) < s < Fr(29560515319671, 10 ** 14))
    check("eta = 0.2351016242... (%s)" % nm, dec(t, 10) in ("0.2351016242", "0.2351016243"), dec(t, 12))
    pr = prior_form(s, t)
    al = 1 - 2 * s - t
    lam = (t * s, al * s, al * s + t * t)
    lam = tuple(x / sum(lam) for x in lam)
    print("   prior   ~", [dec(x, 8) for x in pr], " lottery ~", [dec(x, 8) for x in lam])
    # Hessian of v at (s,t) by exact formulas for the second derivatives of N/D
    # (information only; printed with 7 decimals)
xi_poly = [-4, 84, -576, 1762, -2489, 1326]
check("the xi-quintic changes sign on (0.29560515319670, 0.29560515319671)",
      peval(xi_poly, Fr(29560515319670, 10 ** 14)) * peval(xi_poly, Fr(29560515319671, 10 ** 14)) < 0)


# Rigorous enclosure of (xi*, eta*): rational interval arithmetic over a WHOLE interval that
# contains w* = v* - 1.  Two intervals are used: the isolating interval of the paper,
# [0.191628284077, 0.191628284078] - 1 (width 1e-12), for the hypotheses of the family theorem,
# and the bisection interval [VLO, VHI] - 1 (width below 1e-40) for the printed digits.  The zero
# v* of P lies in both, so xi* = xi(w*) and eta* = eta(w*) lie in the enclosures computed here.
def iv(x):
    return (Fr(x), Fr(x))


def iadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def isub(x, y):
    return (x[0] - y[1], x[1] - y[0])


def imul(x, y):
    c = [x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1]]
    return (min(c), max(c))


def idiv(x, y):
    assert y[0] > 0 or y[1] < 0, "division by an interval that contains 0"
    return imul(x, (1 / y[1], 1 / y[0]))


def ipoly(c, x):
    r = iv(0)
    for a in reversed(c):
        r = iadd(imul(r, x), iv(a))
    return r


WI = (lo - 1, hi - 1)
AI = ipoly(Ap, WI)
BI = ipoly(Bp, WI)
check("enclosure: b(w) = 442w^3+18w^2-37w+3 is negative on the whole interval, |b| > 0.31",
      BI[1] < -Fr(31, 100), (float(BI[0]), float(BI[1])))
check("enclosure: 7w+3 > 0 and w > 0 on the whole interval", WI[0] > 0)
SI = idiv(imul(WI, AI), BI)
TI = idiv(imul(SI, iadd(isub(iv(1), imul(iv(3), SI)), WI)), imul(iv(2), WI))
print("   enclosure of xi*:  [%s, %s]  width %.3e" % (dec(SI[0], 16), dec(SI[1], 16), float(SI[1] - SI[0])))
print("   enclosure of eta*: [%s, %s]  width %.3e" % (dec(TI[0], 16), dec(TI[1], 16), float(TI[1] - TI[0])))
check("enclosure: both enclosures have width below 1e-9",
      SI[1] - SI[0] < Fr(1, 10 ** 9) and TI[1] - TI[0] < Fr(1, 10 ** 9))
check("enclosure: 0 < eta* < xi* <= 1/3 and xi* + eta* >= 1/2 on the whole enclosure",
      TI[0] > 0 and TI[1] < SI[0] and SI[1] <= Fr(1, 3) and SI[0] + TI[0] >= Fr(1, 2))
check("enclosure: the three slacks exceed 0.03 (xi-eta > 0.0605, 1/3-xi > 0.0377, xi+eta-1/2 > 0.0307)",
      SI[0] - TI[1] > Fr(605, 10 ** 4) and Fr(1, 3) - SI[1] > Fr(377, 10 ** 4)
      and SI[0] + TI[0] - Fr(1, 2) > Fr(307, 10 ** 4),
      (float(SI[0] - TI[1]), float(Fr(1, 3) - SI[1]), float(SI[0] + TI[0] - Fr(1, 2))))
# the same over the bisection interval (width below 1e-40): digits of xi*, eta*, mu*, lambda*
WI = (VLO - 1, VHI - 1)
AI = ipoly(Ap, WI)
BI = ipoly(Bp, WI)
SI = idiv(imul(WI, AI), BI)
TI = idiv(imul(SI, iadd(isub(iv(1), imul(iv(3), SI)), WI)), imul(iv(2), WI))
check("fine enclosure: widths below 1e-35", SI[1] - SI[0] < Fr(1, 10 ** 35) and TI[1] - TI[0] < Fr(1, 10 ** 35))
check("fine enclosure: b(w*) = -0.3189...", -Fr(3190, 10 ** 4) < BI[0] and BI[1] < -Fr(3189, 10 ** 4),
      (dec(BI[0], 12), dec(BI[1], 12)))
check("fine enclosure: xi* = 0.2956051531967035... and eta* = 0.2351016242530568... (16 truncated digits)",
      Fr(2956051531967035, 10 ** 16) < SI[0] and SI[1] < Fr(2956051531967036, 10 ** 16)
      and Fr(2351016242530568, 10 ** 16) < TI[0] and TI[1] < Fr(2351016242530569, 10 ** 16),
      (dec(SI[0], 20), dec(TI[0], 20)))
check("fine enclosure: v* = 1.1916282840776246... (16 truncated digits)",
      Fr(11916282840776246, 10 ** 16) < VLO and VHI < Fr(11916282840776247, 10 ** 16), dec(VLO, 20))
check("fine enclosure: slacks 0.0605..., 0.0377..., 0.0307... (four truncated digits)",
      Fr(605, 10 ** 4) < SI[0] - TI[1] and SI[1] - TI[0] < Fr(606, 10 ** 4)
      and Fr(377, 10 ** 4) < Fr(1, 3) - SI[1] and Fr(1, 3) - SI[0] < Fr(378, 10 ** 4)
      and Fr(307, 10 ** 4) < SI[0] + TI[0] - Fr(1, 2) and SI[1] + TI[1] - Fr(1, 2) < Fr(308, 10 ** 4))
# prior and lottery at (xi*, eta*): enclosures, and the eight truncated digits printed in the paper
ALI = isub(isub(iv(1), imul(iv(2), SI)), TI)
BEI = isub(iv(1), imul(iv(2), SI))
PT = (imul(SI, isub(iadd(ALI, BEI), SI)), isub(imul(SI, SI), imul(BEI, isub(SI, TI))),
      iadd(imul(TI, SI), imul(ALI, isub(SI, TI))))
LT = (imul(TI, SI), imul(ALI, SI), iadd(imul(ALI, SI), imul(TI, TI)))
DEN = isub(isub(iadd(imul(iv(2), SI), imul(TI, TI)), imul(iv(4), imul(SI, SI))), imul(SI, TI))
check("enclosure: Delta = 2xi - 4xi^2 - xi eta + eta^2 > 0.2", DEN[0] > Fr(1, 5), float(DEN[0]))
MUS = [idiv(x, DEN) for x in PT]
LAS = [idiv(x, DEN) for x in LT]
print("   mu*     in", [(dec(x[0], 12), dec(x[1], 12)) for x in MUS])
print("   lambda* in", [(dec(x[0], 12), dec(x[1], 12)) for x in LAS])
TRUNC_MU = (37282351, 27543407, 35174241)
TRUNC_LA = (30554124, 22572736, 46873139)
check("mu* = (0.37282351, 0.27543407, 0.35174241) truncated to eight places",
      all(Fr(t, 10 ** 8) <= x[0] and x[1] < Fr(t + 1, 10 ** 8) for t, x in zip(TRUNC_MU, MUS)))
check("lambda* = (0.30554124, 0.22572736, 0.46873139) truncated to eight places",
      all(Fr(t, 10 ** 8) <= x[0] and x[1] < Fr(t + 1, 10 ** 8) for t, x in zip(TRUNC_LA, LAS)))

# ------------------------------------------------------------------------------------------
# 6. the menu U
# ------------------------------------------------------------------------------------------
print("== 6. menu U ==")
MAPS = list(itertools.product(range(3), repeat=3))


def push(f, vec):
    out = [Fr(0)] * 3
    for q in range(3):
        out[f[q]] += vec[q]
    return out


def ccost(h, packets):
    best = None
    for f in MAPS:
        pf = push(f, packets)
        m = max(h[b] + pf[b] for b in range(3))
        if best is None or m < best:
            best = m
    return best


def U_rows(RA, RB, RC, SB, SC):
    RA, RB, RC, SB, SC = [[Fr(x) for x in v] for v in (RA, RB, RC, SB, SC)]
    assert sum(RA) == sum(RB) == sum(RC) and sum(SB) == sum(SC)
    LA = RA
    LB = [RB[q] + SB[q] for q in range(3)]
    LC = [RC[q] + SC[q] for q in range(3)]
    assert all(0 <= x <= 1 for L in (LA, LB, LC) for x in L)
    pk = [[1 - x for x in L] for L in (LA, LB, LC)]
    hs = set()
    for R in (RA, RB, RC):
        for phi in MAPS:
            hs.add(tuple(push(phi, R)))
    gs = set()
    for S in (SB, SC):
        for psi in MAPS:
            gs.add(tuple(push(psi, S)))
    rows = set()
    for h in hs:
        cA = ccost(h, pk[0])
        for g in gs:
            k = [h[b] + g[b] for b in range(3)]
            rows.add((cA, ccost(k, pk[1]), ccost(k, pk[2])))
    return rows


def WU(*p):
    rows = U_rows(*p)
    v, mu = game_value(rows)
    return v - 1, mu, rows


# record margins at capacity 17
w17, mu17, rows17 = WU([Fr(14, 17), 0, 0], [Fr(10, 17), Fr(4, 17), 0], [Fr(5, 17), Fr(5, 17), Fr(4, 17)],
                       [0, Fr(13, 17), 0], [0, 0, Fr(13, 17)])
check("W_U at the capacity-17 record margins = 215/1122", w17 == Fr(215, 1122), (w17, mu17))
check("all entries of all rows are >= 1 there", all(c >= 1 for r in rows17 for c in r))

# A-trivial face
for s, expect in [(Fr(19, 25), Fr(817, 4200)), (Fr(764, 1000), Fr(81557, 419250)), (Fr(3, 4), None),
                  (Fr(9, 10), None), (Fr(1), None)]:
    w, mu, rows = WU([s, 0, 0], [s / 2, s / 2, 0], [s / 3, s / 3, s / 3], [0, 0, 0], [0, 0, 0])
    form = s * (4 - 3 * s) / (3 * (3 - s))
    check("A-trivial face s=%s: W_U = s(4-3s)/(3(3-s))" % s, w == form and (expect is None or w == expect), (w, mu))
    sig = (4 - 3 * s) / (3 * (3 - s))
    check("A-trivial face s=%s: prior (3sig-1/3, 1/3, 1-3sig)" % s,
          prior_ok(rows, (3 * sig - Fr(1, 3), Fr(1, 3), 1 - 3 * sig), 1 + w), mu)
    lam = [s / (3 - s), 2 * (1 - s) / (3 - s), 1 / (3 - s)]
    r3 = [(Fr(1), 2 - s, 2 - 2 * s / 3), (1 + s / 2, Fr(1), 1 + s / 6), (1 + s / 3, 1 + s / 3, Fr(1))]
    check("A-trivial face s=%s: lottery (s, 2(1-s), 1)/(3-s) on three rows of U" % s,
          lottery_value(r3, lam) == 1 + w and all(r in rows for r in r3))
    exs = pareto(tuple(c - 1 for c in r) for r in rows)
    print("   s=%s Pareto excess rows:" % s, exs)


def atrivial_catalog(s):
    s = Fr(s)
    root = (s / 3, s / 6, s / 6, s / 3)
    return [root + (1 - s, 1, 1), root + (1 - s / 2, 1 - s / 2, 1), root + (1 - s / 3, 1 - s / 3, 1 - s / 3)]


for s, expect in [(Fr(764, 1000), Fr(191, 1125)), (Fr(763932, 10 ** 6), Fr(63661, 375000)), (Fr(19, 25), Fr(38, 225)),
                  (Fr(3, 4), None), (Fr(6, 7), None), (Fr(4, 5), None)]:
    v, mu, fr = catalog_value(atrivial_catalog(s))
    check("A-trivial catalog s=%s: true value 1 + 2s/9" % s, v - 1 == 2 * s / 9 and (expect is None or v - 1 == expect),
          (v - 1, mu))
exs = sorted(tuple(c - 1 for c in r) for r in catalog_value(atrivial_catalog(Fr(4, 5)))[2])
print("   s=4/5 Pareto excess rows of the complete game:", exs)

# the rational point with W_U = 0.196579445...
D7 = 10 ** 7
x2u = ([Fr(2569504, D7), Fr(2569488, D7), Fr(2569526, D7)], [Fr(446461, D7), Fr(6815538, D7), Fr(446519, D7)],
       [Fr(0), Fr(7373036, D7), Fr(335482, D7)], [Fr(3184618, D7), Fr(3184461, D7), Fr(3184582, D7)],
       [Fr(0), Fr(0), Fr(9553661, D7)])
VAL = Fr(34932609166238639, 177702247424218750)
w, mu, rows = WU(*x2u)
check("W_U at the stated point = 34932609166238639/177702247424218750", w == VAL, (w, float(w)))
MU = (Fr(1200456350911, 7961060684605), Fr(3854400190234, 7961060684605), Fr(581240828692, 1592212136921))
check("the stated prior is a probability vector", sum(MU) == 1 and all(x >= 0 for x in MU))
print("   INFO optimal prior found equals the stated prior:", tuple(mu) == MU)
check("the stated prior certifies the value", prior_ok(rows, MU, 1 + VAL))
check("under the stated prior every row of U has excess >= the value",
      all(sum(m * (c - 1) for m, c in zip(MU, r)) >= VAL for r in rows))
E3 = [(Fr(0), Fr(66339, 312500), Fr(80297, 312500)), (Fr(1061503, 2500000), Fr(0), Fr(3631079, 10 ** 7)),
      (Fr(1061503, 2500000), Fr(136891, 500000), Fr(1, 10 ** 7))]
L3 = [Fr(610756308107, 1137294383515), Fr(36702361304, 227458876703), Fr(343026268888, 1137294383515)]
check("the three stated excess vectors are rows of U at that point",
      all(tuple(1 + x for x in e) in rows for e in E3))
check("the stated weights are a probability vector", sum(L3) == 1 and all(x >= 0 for x in L3))
check("the stated lottery has excess exactly the value on each stream",
      all(sum(l * e[j] for l, e in zip(L3, E3)) == VAL for j in range(3)))
check("0.196579 < value < 0.196580", Fr(196579, 10 ** 6) < VAL < Fr(196580, 10 ** 6), dec(VAL, 12))
check("number of distinct cost rows at that point <= 663", len(rows) <= 663, len(rows))
check("number of distinct cost rows at that point is 232", len(rows) == 232, len(rows))
# the rows (X, phi, X', psi) of the menu that have the three cost bounds of the lottery:
# the first one in the order X = A, B, C; phi lexicographic; X' = B, C; psi lexicographic
P1R = {"A": x2u[0], "B": x2u[1], "C": x2u[2]}
P1S = {"B": x2u[3], "C": x2u[4]}
P1L = {"A": x2u[0], "B": [x2u[1][q] + x2u[3][q] for q in range(3)], "C": [x2u[2][q] + x2u[4][q] for q in range(3)]}
P1PK = {Z: [1 - x for x in P1L[Z]] for Z in "ABC"}
TUPLES = {}
for X in "ABC":
    for phi in MAPS:
        hh = push(phi, P1R[X])
        cA = ccost(hh, P1PK["A"])
        for X2 in "BC":
            for psi in MAPS:
                gg = push(psi, P1S[X2])
                kk = [hh[b] + gg[b] for b in range(3)]
                TUPLES.setdefault((cA, ccost(kk, P1PK["B"]), ccost(kk, P1PK["C"])), []).append((X, phi, X2, psi))
check("the rows of U, generated tuple by tuple, give the same 232 cost bounds", set(TUPLES) == set(rows))
for e in E3:
    tl = TUPLES[tuple(1 + x for x in e)]
    hh = push(tl[0][1], P1R[tl[0][0]])
    gg = push(tl[0][3], P1S[tl[0][2]])
    print("   lottery row with excess %s: %d tuples; first: X=%s phi=%s X'=%s psi=%s; root loads %s, paired loads %s"
          % ([str(x) for x in e], len(tl), tl[0][0], tl[0][1], tl[0][2], tl[0][3],
             [str(x * D7) for x in hh], [str(x * D7) for x in gg]))
    print("      further tuples:", tl[1:6])
PRINTED = [("A", (0, 1, 2), "B", (2, 1, 2)), ("B", (0, 1, 2), "B", (0, 1, 2)), ("B", (0, 1, 0), "B", (0, 1, 0))]
check("the rows u_1 = (A,id,B,(2,1,2)), u_2 = (B,id,B,id), u_3 = (B,(0,1,0),B,(0,1,0)) printed in the paper "
      "have the three stated excess vectors",
      all(t in TUPLES[tuple(1 + x for x in e)] for t, e in zip(PRINTED, E3)))
check("W_U at the stated point = 0.196579444956... (truncated; 0.196579445 would be rounded)",
      Fr(196579444956, 10 ** 12) < VAL < Fr(196579444957, 10 ** 12), dec(VAL, 15))

# the capacity-8 example of Section 4.6: the member s = 3/4 of the family "one bin of A"
A8 = (2, 1, 1, 2, 2, 8, 8)
B8 = (2, 1, 1, 2, 5, 5, 8)
C8 = (2, 1, 1, 2, 6, 6, 6)
check("capacity-8 example is the catalog C_s at s = 3/4, in units of 1/8",
      [tuple(8 * z for z in st) for st in atrivial_catalog(Fr(3, 4))] == [A8, B8, C8])
PACK8 = [[(2, 1, 1, 2, 2), (8,), (8,)], [(2, 1, 5), (1, 2, 5), (8,)], [(2, 6), (1, 1, 6), (2, 6)]]
check("capacity-8 example: the packings by labels (0,0,0), (0,0,1), (0,1,1), (0,1,2) fill every bin",
      all(sorted(x for b in bins for x in b) == sorted(st) and all(sum(b) == 8 for b in bins)
          for st, bins in zip((A8, B8, C8), PACK8)))
v8, mu8, fr8 = catalog_value([A8, B8, C8])
check("capacity-8 example: value 7/6", v8 / 8 == Fr(7, 6), (v8 / 8, mu8))
check("capacity-8 example: uniform prior certifies the value", prior_ok(fr8, (Fr(1, 3), Fr(1, 3), Fr(1, 3)), v8))
rows8 = [(Fr(10), Fr(10), Fr(8)), (Fr(9), Fr(9), Fr(10))]     # loads (2,2,2) and (4,1,1)
check("capacity-8 example: lottery 1/3, 2/3 on the root loads (2,2,2) and (4,1,1) costs 28/3 on every stream",
      all(attainable(r, fr8) for r in rows8)
      and all(Fr(1, 3) * rows8[0][j] + Fr(2, 3) * rows8[1][j] == Fr(28, 3) for j in range(3)))
check("capacity-8 example: root loads (2,2,2) and (4,1,1) give the costs (10,10,8) and (9,9,10)",
      (best_completion((2, 2, 2), A8[4:]), best_completion((2, 2, 2), B8[4:]), best_completion((2, 2, 2), C8[4:]))
      == (10, 10, 8)
      and (best_completion((4, 1, 1), A8[4:]), best_completion((4, 1, 1), B8[4:]), best_completion((4, 1, 1), C8[4:]))
      == (9, 9, 10))
w8, mu8u, rows8u = WU([Fr(6, 8), 0, 0], [Fr(3, 8), Fr(3, 8), 0], [Fr(2, 8), Fr(2, 8), Fr(2, 8)], [0, 0, 0], [0, 0, 0])
check("capacity-8 example: W_U = 7/36 at its margins, so label maps prove only 43/36", w8 == Fr(7, 36), (w8, mu8u))
check("capacity-8 example: 7/6 < 43/36", Fr(7, 6) < Fr(43, 36))

print("== standard checks finished after %.1f s; %d failures so far ==" % (time.time() - T0, len(FAILS)))

# ------------------------------------------------------------------------------------------
# 7. further catalogs with six to ten streams (from cats/); slower, hence last
# ------------------------------------------------------------------------------------------
print("== 7. further catalogs ==")
FURTHER = [("g7_1122_L5.json", Fr(403, 336)), ("record_m3_cap21_k7_1411_1176.json", Fr(1411, 1176)),
           ("g22_3366_L4.json", Fr(1888, 1573)), ("record_m3_cap28_k8_6_5.json", Fr(6, 5)),
           ("v2_g43_661212_L4.json", Fr(11967725, 9967787))]
for fname, expect in FURTHER:
    json_catalog(fname, expect)
check("further catalogs: all values are below 240961012/200582107",
      all(e < Fr(240961012, 200582107) for _, e in FURTHER))
check("further catalogs: 11967725/9967787 = 1.20064..., 1888/1573 = 1.20025..., 1411/1176 = 1.19982...",
      Fr(120064, 10 ** 5) < Fr(11967725, 9967787) < Fr(120065, 10 ** 5)
      and Fr(120025, 10 ** 5) < Fr(1888, 1573) < Fr(120026, 10 ** 5)
      and Fr(119982, 10 ** 5) < Fr(1411, 1176) < Fr(119983, 10 ** 5))

# ------------------------------------------------------------------------------------------
# 8. other numbers of bins (Section 3.6 and the last part of Appendix C)
# ------------------------------------------------------------------------------------------
print("== 8. other numbers of bins ==")


def frontier_m(streams, nb):
    """Pareto-minimal cost vectors over all deterministic causal policies on nb bins.  The recursion
    of frontier(), for any number of bins; a stream that has been told apart from the others is
    completed by the same recursion.  Bins with equal loads are interchangeable."""
    memo = {}

    def rec(active, pos, loads):
        key = (active, pos, loads)
        if key in memo:
            return memo[key]
        ended = [i for i in active if len(streams[i]) == pos]
        groups = {}
        for i in active:
            if len(streams[i]) > pos:
                groups.setdefault(streams[i][pos], []).append(i)
        res_lists = []
        for z in sorted(groups):
            idxs = tuple(groups[z])
            opts = set()
            for b in range(nb):
                if b > 0 and loads[b] == loads[b - 1]:
                    continue
                l = list(loads)
                l[b] += z
                opts.update(rec(idxs, pos + 1, tuple(sorted(l, reverse=True))))
            res_lists.append((idxs, pareto(opts)))
        out = set()
        for combo in itertools.product(*[o for _, o in res_lists]):
            d = {}
            for i in ended:
                d[i] = loads[0]
            for (idxs, _), vec in zip(res_lists, combo):
                for i, c in zip(idxs, vec):
                    d[i] = c
            out.add(tuple(d[i] for i in active))
        res = pareto(out)
        memo[key] = res
        return res

    return pareto(rec(tuple(range(len(streams))), 0, tuple([0] * nb)))


for nm, sts in [("Example 1", [(1, 1, 1, 3, 3), (1, 1, 2, 2, 3)]),
                ("capacity 17", [A17, B17, C17]),
                ("four streams, capacity 7", [(2, 2, 2, 7, 7, 1), (2, 2, 2, 5, 5, 5), (2, 2, 2, 3, 3, 5, 4),
                                              (2, 2, 2, 3, 3, 7, 2)]),
                ("five streams, capacity 209", STREAMS5)]:
    check("the recursion for any number of bins agrees with the three-bin solver: %s" % nm,
          sorted(frontier_m(sts, 3)) == sorted(frontier([tuple(Fr(z) for z in s) for s in sts])))


def manybins(nb):
    """the streams sigma_0, ..., sigma_n of the theorem on many bins (capacity 3, n = floor(nb/2))"""
    n = nb // 2
    lead = (3,) if nb % 2 else ()
    return [lead + (1,) * (2 * n) + (3, 1) * j + (2,) * (2 * n - 2 * j) for j in range(n + 1)]


def manybins_packing(nb, j):
    n = nb // 2
    return ([(3,)] if nb % 2 else []) + [(3,)] * j + [(1, 1, 1)] * j + [(1, 2)] * (2 * n - 2 * j)


check("many bins: for m = 2 the streams are (1,1,2,2), (1,1,3,1); for m = 3 they are (3,1,1,2,2), (3,1,1,3,1)",
      manybins(2) == [(1, 1, 2, 2), (1, 1, 3, 1)] and manybins(3) == [(3, 1, 1, 2, 2), (3, 1, 1, 3, 1)])
MB_VALUES = {2: Fr(7, 6), 3: Fr(7, 6), 4: Fr(11, 9), 5: Fr(11, 9), 6: Fr(5, 4), 7: Fr(5, 4), 8: Fr(19, 15),
             9: Fr(19, 15), 10: Fr(23, 18), 11: Fr(23, 18), 12: Fr(9, 7)}
for nb in range(2, 13):
    n = nb // 2
    sts = manybins(nb)
    t0 = time.time()
    check("many bins, m = %d: %d distinct streams of total size %d; the stated packing fills %d bins of "
          "capacity 3 exactly" % (nb, n + 1, 3 * nb, nb),
          len(set(sts)) == n + 1 and all(sum(s) == 3 * nb for s in sts)
          and all(len(manybins_packing(nb, j)) == nb and all(sum(b) == 3 for b in manybins_packing(nb, j))
                  and sorted(x for b in manybins_packing(nb, j) for x in b) == sorted(sts[j])
                  for j in range(n + 1)))
    frm = frontier_m(sts, nb)
    want = sorted(tuple(3 if i == j else 4 for i in range(n + 1)) for j in range(n + 1))
    check("many bins, m = %d: exactly %d Pareto-minimal policies, each with cost 3 on one stream and 4 on "
          "the others" % (nb, n + 1), sorted(frm) == want, frm if len(frm) < 12 else len(frm))
    uni = tuple(Fr(1, n + 1) for _ in range(n + 1))
    lo = min(sum(u * c for u, c in zip(uni, r)) for r in frm)
    hi = max(sum(Fr(1, len(frm)) * r[j] for r in frm) for j in range(n + 1))
    bound = Fr(4 * n + 3, 3 * n + 3)
    check("many bins, m = %d: the uniform prior and the uniform lottery give the value %s of the capacity"
          % (nb, bound),
          lo / 3 == bound and hi / 3 == bound and best_response(sts, uni, nb) / 3 == bound
          and bound == MB_VALUES[nb] and bound == Fr(4, 3) - Fr(1, 3 * (n + 1)), (lo, hi))
    print("   many bins, m = %d: %.1f s" % (nb, time.time() - t0))
    sys.stdout.flush()
check("many bins: for even m the bound is (4m+6)/(3m+6); the bounds increase with n and stay below 4/3",
      all(Fr(4 * (nb // 2) + 3, 3 * (nb // 2) + 3) == Fr(4 * nb + 6, 3 * nb + 6) for nb in range(2, 61, 2))
      and all(Fr(4 * n + 3, 3 * n + 3) < Fr(4 * n + 7, 3 * n + 6) < Fr(4, 3) for n in range(1, 60)))

# five bins: a catalog of three streams at capacity 33
G33 = 33
A33 = (10,) * 5 + (23,) * 5
B33 = (10,) * 5 + (6, 27, 33, 23, 23, 3)
C33 = (10,) * 5 + (6, 33, 33, 33, 7, 3)
STREAMS33 = [A33, B33, C33]
PACK33 = [[(10, 23)] * 5,
          [(10, 10, 10, 3), (6, 27), (33,), (10, 23), (10, 23)],
          [(33,), (33,), (33,), (10, 10, 10, 3), (10, 10, 6, 7)]]
check("five bins, capacity 33: every stream has total size 165, and the stated packings fill five bins exactly",
      all(sum(s) == 5 * G33 for s in STREAMS33)
      and all(len(bins) == 5 and all(sum(b) == G33 for b in bins)
              and sorted(x for b in bins for x in b) == sorted(st) for st, bins in zip(STREAMS33, PACK33)))
fr33 = frontier_m(STREAMS33, 5)
print("   five bins, capacity 33: Pareto-minimal cost rows", sorted(fr33))
V33 = Fr(16157, 399)
MU33 = (Fr(100, 399), Fr(130, 399), Fr(169, 399))
LOT33 = [((33, 43, 43), Fr(169, 399)), ((46, 33, 43), Fr(130, 399)), ((46, 46, 33), Fr(100, 399))]
check("five bins, capacity 33: 6 Pareto-minimal policies", len(fr33) == 6, len(fr33))
check("five bins, capacity 33: under the prior (100,130,169)/399 every policy costs at least 16157/399, "
      "with equality for some (both routes)",
      prior_ok(fr33, MU33, V33) and best_response(STREAMS33, MU33, 5) == V33,
      min(sum(m * c for m, c in zip(MU33, r)) for r in fr33))
check("five bins, capacity 33: the rows (33,43,43), (46,33,43), (46,46,33) are Pareto-minimal (both routes)",
      all(r in set(fr33) for r, _ in LOT33) and all(row_attainable(STREAMS33, r, 5) for r, _ in LOT33))
check("five bins, capacity 33: the lottery (169,130,100)/399 on these rows costs exactly 16157/399 on every stream",
      sum(w for _, w in LOT33) == 1 and all(sum(w * r[j] for r, w in LOT33) == V33 for j in range(3)))
check("five bins, capacity 33: value 16157/13167 of the capacity; 1.2270 < value < 1.2271; value > 11/9",
      V33 / G33 == Fr(16157, 13167) and Fr(12270, 10 ** 4) < V33 / G33 < Fr(12271, 10 ** 4)
      and V33 / G33 > Fr(11, 9), float(V33 / G33))
# the three rows are the policies that place the shared jobs as the packings of A, B and C do:
# loads after the five jobs 10, then (for B and C) after the job 6; costs with optimal completions
POL33 = [((10, 10, 10, 10, 10), (16, 10, 10, 10, 10), (33, 43, 43)),
         ((30, 10, 10, 0, 0), (30, 10, 10, 6, 0), (46, 33, 43)),
         ((30, 20, 0, 0, 0), (30, 26, 0, 0, 0), (46, 46, 33))]
for root_l, pair_l, costs in POL33:
    got = (best_response([A33[5:]], (1,), 5, start=root_l), best_response([B33[6:]], (1,), 5, start=pair_l),
           best_response([C33[6:]], (1,), 5, start=pair_l))
    check("five bins, capacity 33: loads %s after the root and %s after the job 6 give the costs %s"
          % (root_l, pair_l, costs), got == costs, got)
check("five bins, capacity 33: the best single policy costs 43 (43/33)", min(max(r) for r in fr33) == 43,
      min(max(r) for r in fr33))
check("lower bounds on R_m: 240961012/200582107 > 7/6 (three bins), 16157/13167 > 11/9 (five bins), "
      "5/4 > 16157/13167 (six bins)",
      Fr(240961012, 200582107) > Fr(7, 6) and Fr(16157, 13167) > Fr(11, 9) and Fr(5, 4) > Fr(16157, 13167))

print("== done in %.1f s; %d failures ==" % (time.time() - T0, len(FAILS)))
for f in FAILS:
    print("FAILED:", f)
sys.exit(1 if FAILS else 0)
