#!/usr/bin/env python3
"""second_replay.py -- a second exact replay of the catalog values printed in the paper.

Standard library only; integers and fractions.Fraction only.  It shares no code with
check_paper_numbers.py.  Every catalog is typed in below exactly as the paper prints it, except those
of section 6: their values are typed in, and their streams, packings, priors and lotteries are read
from cats/.

Method.  A catalog is a list of streams (tuples of integer job sizes) for m bins.  The streams form a
tree by common prefixes; a deterministic causal policy chooses a bin at every node of the tree.  Bins
with equal loads are interchangeable, so loads are kept sorted.  Three recursions over (node, loads):

  best_response(w)   the minimum, over ALL policies, of sum_i w_i * cost_i   (integer weights w)
  attainable(c)      is there a policy with cost_i <= c_i on every stream i?
  frontier()         the set of Pareto-minimal cost vectors of all policies

A value v of a catalog is accepted only if
  (L) best_response(prior) = v   (every policy costs at least v on average: the prior certificate), and
  (U) the stated lottery rows are attainable and their mixture costs at most v on every stream.
(L) is the half that proves a lower bound on R_m.  frontier() is used only to confirm the printed
numbers of Pareto-minimal policies and best single policies.

Usage:  python3 second_replay.py [--max-bins M]     (default 16; exit status 1 if any check fails)
The many-bins catalogs are checked for m = 2, ..., M.
"""
import sys
import time
from fractions import Fraction as F

sys.setrecursionlimit(100000)
FAILS = []
NCHECK = [0]
T0 = time.time()


def check(name, cond, info=None):
    NCHECK[0] += 1
    print(("PASS  " if cond else "FAIL  ") + name + ("" if info is None else "   [" + str(info) + "]"))
    sys.stdout.flush()
    if not cond:
        FAILS.append(name)


# ---------------------------------------------------------------------------------------------
# the tree of a catalog
# ---------------------------------------------------------------------------------------------
class Node:
    __slots__ = ("id", "kids", "ends", "below")

    def __init__(self, ident):
        self.id = ident
        self.kids = {}      # job size -> Node
        self.ends = []      # indices of the streams that end here
        self.below = []     # indices of all streams through this node


def tree(streams):
    nodes = [Node(0)]
    for i, s in enumerate(streams):
        cur = nodes[0]
        cur.below.append(i)
        for z in s:
            if z not in cur.kids:
                nodes.append(Node(len(nodes)))
                cur.kids[z] = nodes[-1]
            cur = cur.kids[z]
            cur.below.append(i)
        cur.ends.append(i)
    return nodes[0]


def placements(loads, z):
    """the distinct sorted load vectors after adding a job z to one bin"""
    out = []
    prev = None
    for b, l in enumerate(loads):
        if l == prev:
            continue
        prev = l
        new = list(loads)
        new[b] = l + z
        new.sort(reverse=True)
        out.append(tuple(new))
    return out


def best_response(streams, m, w, cap=None):
    """min over all policies of sum_i w_i cost_i.  With cap, every cost is replaced by min(cost, cap),
    which can only lower the result; so the result is still a lower bound for every policy."""
    root = tree(streams)
    memo = {}

    def rec(node, loads):
        key = (node.id, loads)
        if key in memo:
            return memo[key]
        top = loads[0]
        tot = sum(w[i] for i in node.ends) * top
        for z, kid in node.kids.items():
            best = None
            for new in placements(loads, z):
                if cap is not None:
                    new = tuple(min(x, cap) for x in new)
                v = rec(kid, new)
                if best is None or v < best:
                    best = v
            tot += best
        memo[key] = tot
        return tot

    return rec(root, tuple([0] * m))



def best_response_from(streams, start):
    """cheapest completion cost of the given streams (weights 1) from the given start loads"""
    root = tree(streams)
    memo = {}

    def rec(node, loads):
        key = (node.id, loads)
        if key in memo:
            return memo[key]
        tot = len(node.ends) * loads[0]
        for z, kid in node.kids.items():
            tot += min(rec(kid, new) for new in placements(loads, z))
        memo[key] = tot
        return tot

    return rec(root, tuple(sorted(start, reverse=True)))


def attainable(streams, m, c):
    """is there a policy with cost_i <= c[i] for every stream i?"""
    root = tree(streams)
    memo = {}

    def rec(node, loads):
        if loads[0] > min(c[i] for i in node.below):
            return False        # loads never decrease, so some stream below is already too expensive
        key = (node.id, loads)
        if key in memo:
            return memo[key]
        ok = True
        for z, kid in node.kids.items():
            if not any(rec(kid, new) for new in placements(loads, z)):
                ok = False
                break
        memo[key] = ok
        return ok

    return rec(root, tuple([0] * m))


def pareto(vecs):
    vecs = sorted(set(vecs))
    keep = []
    for v in vecs:
        if not any(all(a <= b for a, b in zip(u, v)) for u in keep):
            keep.append(v)
    return keep


def frontier(streams, m):
    """Pareto-minimal cost vectors (one entry per stream) over all policies"""
    root = tree(streams)
    memo = {}

    def rec(node, loads):
        """list of dicts stream -> cost, Pareto-minimal, as sorted tuples of (stream, cost)"""
        key = (node.id, loads)
        if key in memo:
            return memo[key]
        partial = [tuple((i, loads[0]) for i in node.ends)]
        for z, kid in sorted(node.kids.items()):
            opts = set()
            for new in placements(loads, z):
                opts.update(rec(kid, new))
            order = [i for i, _ in next(iter(opts))]
            mins = pareto([tuple(c for _, c in o) for o in opts])
            opts = [tuple(zip(order, v)) for v in mins]
            partial = [p + o for p in partial for o in opts]
        res = [tuple(sorted(p)) for p in partial]
        order = [i for i, _ in res[0]]
        mins = pareto([tuple(c for _, c in r) for r in res])
        res = [tuple(zip(order, v)) for v in mins]
        memo[key] = res
        return res

    return sorted(tuple(c for _, c in r) for r in rec(root, tuple([0] * m)))


def packing_ok(stream, bins, g):
    return sorted(x for b in bins for x in b) == sorted(stream) and all(sum(b) <= g for b in bins)


def solve_square(A, b):
    """exact solution of a square system by Gaussian elimination, or None if it is singular"""
    n = len(A)
    M = [[F(x) for x in row] + [F(y)] for row, y in zip(A, b)]
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if piv is None:
            return None
        M[c], M[piv] = M[piv], M[c]
        M[c] = [x / M[c][c] for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                M[r] = [x - M[r][c] * y for x, y in zip(M[r], M[c])]
    return [M[r][n] for r in range(n)]


def find_lottery(rows, value):
    """a lottery on some of the given rows that costs exactly `value` on every stream, found by trying
    the square subsystems; the result is checked by the caller.  Returns a list of (row, weight)."""
    import itertools
    k = len(rows[0])
    for size in range(1, k + 1):
        for sub in itertools.combinations(rows, size):
            for cols in itertools.combinations(range(k), size - 1):
                A = [[1] * size] + [[r[j] for r in sub] for j in cols]
                x = solve_square(A, [1] + [value] * (size - 1))
                if x is None or min(x) < 0:
                    continue
                if all(sum(w * r[j] for w, r in zip(x, sub)) <= value for j in range(k)):
                    return [(r, w) for r, w in zip(sub, x) if w > 0]
    return None


def certify(name, streams, m, g, packs, prior, lottery, value, npareto=None, best_single=None):
    """prior: integer weights; lottery: list of (row, weight), or None to have one searched for;
    value: Fraction in units of the job sizes"""
    k = len(streams)
    check(name + ": %d distinct streams, each fits into %d bins of capacity %d (stated packings)" % (k, m, g),
          len(set(streams)) == k and all(len(p) <= m and packing_ok(s, p, g) for s, p in zip(streams, packs)))
    W = sum(prior)
    br = F(best_response(streams, m, prior), W)
    check(name + ": prior certificate, every policy costs at least %s under the prior" % value, br == value, br)
    if lottery is None:
        fr0 = frontier(streams, m)
        tight = [r for r in fr0 if F(sum(p * c for p, c in zip(prior, r)), W) == value]
        lottery = find_lottery(tight, value)
        check(name + ": a lottery on %d of the %d rows that are tight under the prior was found"
              % (len(lottery or []), len(tight)), lottery is not None,
              None if lottery is None else [(r, str(wt)) for r, wt in lottery])
        lottery = lottery or [(tight[0], 1)]
    L = sum(wt for _, wt in lottery)
    check(name + ": every row of the lottery is the cost vector of a policy (or dominates one)",
          all(attainable(streams, m, row) for row, _ in lottery))
    mix = [F(sum(wt * row[j] for row, wt in lottery)) / L for j in range(k)]
    check(name + ": lottery certificate, at most %s on every stream" % value, max(mix) <= value, max(mix))
    check(name + ": value %s of the capacity" % (value / g), True, "%.7f" % float(value / g))
    if npareto is not None or best_single is not None:
        fr = frontier(streams, m)
        if npareto is not None:
            check(name + ": %d Pareto-minimal policies" % npareto, len(fr) == npareto, len(fr))
        if best_single is not None:
            check(name + ": the best single policy costs %d" % best_single,
                  min(max(r) for r in fr) == best_single, min(max(r) for r in fr))
        check(name + ": the prior certificate also holds row by row on the list of Pareto-minimal policies",
              min(F(sum(p * c for p, c in zip(prior, r)), W) for r in fr) == value)
        return fr
    return None


# ---------------------------------------------------------------------------------------------
# 1. three bins
# ---------------------------------------------------------------------------------------------
print("== 1. three bins ==")
certify("Example 2.3 (capacity 3)", [(1, 1, 1, 3, 3), (1, 1, 2, 2, 3)], 3, 3,
        [[(1, 1, 1), (3,), (3,)], [(1, 2), (1, 2), (3,)]],
        (1, 1), [((3, 4), 1), ((4, 3), 1)], F(7, 2), npareto=2, best_single=4)

certify("Section 3.1 (capacity 7, three-way fork)",
        [(2, 2, 2, 1, 7, 7), (2, 2, 2, 3, 5, 7), (2, 2, 2, 5, 5, 5)], 3, 7,
        [[(2, 2, 2, 1), (7,), (7,)], [(2, 2, 3), (2, 5), (7,)], [(2, 5), (2, 5), (2, 5)]],
        (1, 1, 1), [((7, 8, 10), 2), ((9, 7, 9), 1), ((9, 9, 7), 3)], F(25, 3), npareto=3, best_single=9)

certify("Proposition 3.1 (capacity 17)",
        [(5, 5, 4, 3, 17, 17), (5, 5, 4, 13, 7, 17), (5, 5, 4, 13, 12, 12)], 3, 17,
        [[(5, 5, 4, 3), (17,), (17,)], [(5, 5, 7), (4, 13), (17,)], [(5, 12), (5, 12), (4, 13)]],
        (25, 18, 23), [((17, 20, 24), 20), ((21, 17, 22), 15), ((22, 22, 17), 31)], F(1337, 66),
        npareto=5, best_single=22)

certify("Proposition 3.5(i) (four streams, capacity 7)",
        [(2, 2, 2, 7, 7, 1), (2, 2, 2, 5, 5, 5), (2, 2, 2, 3, 3, 5, 4), (2, 2, 2, 3, 3, 7, 2)], 3, 7,
        [[(2, 2, 2, 1), (7,), (7,)], [(2, 5), (2, 5), (2, 5)], [(2, 5), (3, 4), (2, 2, 3)],
         [(7,), (2, 2, 3), (2, 3, 2)]],
        (3, 2, 4, 4), [((7, 10, 9, 8), 4), ((9, 9, 9, 7), 2), ((9, 9, 7, 9), 1), ((9, 7, 8, 9), 6)],
        F(109, 13), npareto=6, best_single=9)

certify("Appendix C (four streams, capacity 10)",
        [(3, 3, 3, 10, 10, 1), (3, 3, 3, 7, 7, 7), (3, 3, 3, 2, 10, 7, 2), (3, 3, 3, 2, 5, 10, 4)], 3, 10,
        [[(3, 3, 3, 1), (10,), (10,)], [(3, 7), (3, 7), (3, 7)], [(10,), (3, 7), (3, 3, 2, 2)],
         [(10,), (3, 3, 4), (3, 2, 5)]],
        (4, 12, 9, 9), [((10, 14, 11, 11), 12), ((13, 10, 13, 13), 16), ((13, 13, 10, 12), 3),
                        ((13, 13, 12, 10), 3)], F(203, 17), npareto=4, best_single=13)

R5 = (58, 29, 29, 26, 26, 6)
certify("Proposition 3.5(iii) (five streams, capacity 209)",
        [R5 + (151, 151, 151), R5 + (209, 209, 35), R5 + (87, 209, 157), R5 + (87, 122, 122, 122),
         R5 + (87, 183, 183)], 3, 209,
        [[(58, 151), (29, 29, 151), (26, 26, 6, 151)],
         [(58, 29, 29, 26, 26, 6, 35), (209,), (209,)],
         [(58, 29, 29, 6, 87), (26, 26, 157), (209,)],
         [(87, 122), (58, 29, 122), (29, 26, 26, 6, 122)],
         [(58, 29, 29, 6, 87), (26, 183), (26, 183)]],
        (217970, 242640, 78400, 319223, 101490),
        [((302, 209, 244, 244, 270), 382058), ((273, 261, 209, 244, 235), 17536),
         ((290, 244, 226, 244, 226), 692231), ((215, 264, 264, 264, 247), 1018290),
         ((238, 261, 261, 244, 270), 769054)],
        F(240961012, 959723), npareto=82, best_single=264)
check("Proposition 3.5(iii): 240961012/959723 divided by 209 is 240961012/200582107; 1.20130 < value < 1.20131",
      F(240961012, 959723) / 209 == F(240961012, 200582107)
      and F(120130, 10 ** 5) < F(240961012, 200582107) < F(120131, 10 ** 5)
      and sum((217970, 242640, 78400, 319223, 101490)) == 959723
      and sum((382058, 17536, 692231, 1018290, 769054)) == 2879169)

R4 = (88, 88, 44, 27, 17)
certify("Proposition 3.5(ii) (four streams, capacity 325)",
        [R4 + (237, 237, 237), R4 + (325, 325, 61), R4 + (132, 325, 254), R4 + (132, 193, 193, 193)], 3, 325,
        [[(88, 237), (88, 237), (44, 27, 17, 237)],
         [(88, 88, 44, 27, 17, 61), (325,), (325,)],
         [(88, 88, 17, 132), (44, 27, 254), (325,)],
         [(132, 193), (88, 44, 193), (88, 27, 17, 193)]],
        (1457, 1726, 958, 1457),
        [((325, 413, 413, 413), 5503), ((474, 325, 386, 386), 3124), ((430, 396, 325, 386), 2684),
         ((386, 413, 413, 352), 2684)],
        F(1091879, 2799), npareto=38, best_single=413)
check("Proposition 3.5(ii): 1091879/2799 divided by 325 is 1091879/909675, which exceeds 6/5 by 269/909675",
      F(1091879, 2799) / 325 == F(1091879, 909675) and F(1091879, 909675) - F(6, 5) == F(269, 909675)
      and sum((1457, 1726, 958, 1457)) == 5598 and sum((5503, 3124, 2684, 2684)) == 13995)

certify("Appendix C (six streams, capacity 7, complete game at granularity 7)",
        [(1, 1, 2, 2, 3, 4, 4, 4), (1, 1, 2, 2, 5, 5, 5), (1, 1, 2, 2, 7, 1, 7), (1, 1, 2, 2, 3, 6, 6),
         (1, 1, 2, 2, 6, 7, 2), (1, 1, 2, 2, 3, 3, 7, 2)], 3, 7,
        [[(1, 2, 4), (1, 2, 4), (3, 4)], [(2, 5), (2, 5), (1, 1, 5)], [(1, 1, 2, 2, 1), (7,), (7,)],
         [(1, 6), (1, 6), (2, 2, 3)], [(1, 6), (7,), (1, 2, 2, 2)], [(1, 1, 2, 3), (2, 3, 2), (7,)]],
        (15, 11, 10, 7, 3, 2), None, F(403, 48), npareto=11)

# ---------------------------------------------------------------------------------------------
# 2. the staircase catalogs of the theorem on many bins
# ---------------------------------------------------------------------------------------------
print("== 2. many bins ==")
MAXBINS = 16
if "--max-bins" in sys.argv:
    MAXBINS = int(sys.argv[sys.argv.index("--max-bins") + 1])


def staircase(m):
    n = m // 2
    lead = (3,) if m % 2 else ()
    return [lead + (1,) * (2 * n) + (3, 1) * j + (2,) * (2 * n - 2 * j) for j in range(n + 1)]


def staircase_packing(m, j):
    n = m // 2
    return ([(3,)] if m % 2 else []) + [(3,)] * j + [(1, 1, 1)] * j + [(1, 2)] * (2 * n - 2 * j)


check("many bins: m = 2 gives (1,1,2,2), (1,1,3,1); m = 4 gives the three streams printed in the paper",
      staircase(2) == [(1, 1, 2, 2), (1, 1, 3, 1)]
      and staircase(4) == [(1, 1, 1, 1, 2, 2, 2, 2), (1, 1, 1, 1, 3, 1, 2, 2), (1, 1, 1, 1, 3, 1, 3, 1)])
for m in range(2, MAXBINS + 1):
    t0 = time.time()
    n = m // 2
    sts = staircase(m)
    bound = F(4 * n + 3, 3 * n + 3)
    feas = (len(set(sts)) == n + 1 and all(sum(s) == 3 * m for s in sts)
            and all(len(staircase_packing(m, j)) == m and packing_ok(sts[j], staircase_packing(m, j), 3)
                    for j in range(n + 1)))
    # lower bound: under the uniform prior every policy pays at least (3 + 4n)/(n + 1); costs capped at 5,
    # which can only lower the minimum
    lo = F(best_response(sts, m, [1] * (n + 1), cap=5), n + 1)
    # upper bound: for every j some policy pays 3 on sigma_j and at most 4 on the other streams
    hi = all(attainable(sts, m, tuple(3 if i == j else 4 for i in range(n + 1))) for j in range(n + 1))
    # no policy is perfect on two streams (the claim in the proof), checked directly for all pairs
    two = any(attainable(sts, m, tuple(3 if i in (a, b) else 10 ** 6 for i in range(n + 1)))
              for a in range(n + 1) for b in range(a + 1, n + 1))
    check("many bins, m = %2d: %d feasible streams; value exactly %s = 4/3 - 1/(3*%d); no policy is perfect on "
          "two streams" % (m, n + 1, bound, n + 1),
          feas and lo / 3 == bound and hi and not two and bound == F(4, 3) - F(1, 3 * (n + 1)),
          "%.1f s" % (time.time() - t0))
fr4 = frontier(staircase(4), 4)
check("many bins, m = 4: the Pareto-minimal policies are (3,4,4), (4,3,4), (4,4,3); value 11/9",
      fr4 == [(3, 4, 4), (4, 3, 4), (4, 4, 3)], fr4)

# ---------------------------------------------------------------------------------------------
# 3. five bins: three streams at capacity 33
# ---------------------------------------------------------------------------------------------
print("== 3. five bins ==")
A33 = (10,) * 5 + (23,) * 5
B33 = (10,) * 5 + (6, 27, 33, 23, 23, 3)
C33 = (10,) * 5 + (6, 33, 33, 33, 7, 3)
fr33 = certify("five bins, capacity 33", [A33, B33, C33], 5, 33,
               [[(10, 23)] * 5,
                [(10, 10, 10, 3), (6, 27), (33,), (10, 23), (10, 23)],
                [(33,), (33,), (33,), (10, 10, 10, 3), (10, 10, 6, 7)]],
               (100, 130, 169), [((33, 43, 43), 169), ((46, 33, 43), 130), ((46, 46, 33), 100)],
               F(16157, 399), npareto=6, best_single=43)
print("      five bins, capacity 33: Pareto-minimal cost vectors", fr33)
check("five bins: 16157/399 divided by 33 is 16157/13167; 1.22708 < value < 1.22709; value > 11/9; value < 5/4",
      F(16157, 399) / 33 == F(16157, 13167) and F(122708, 10 ** 5) < F(16157, 13167) < F(122709, 10 ** 5)
      and F(16157, 13167) > F(11, 9) and F(16157, 13167) < F(5, 4))

# the numbers printed in the appendix on five bins
MU33 = (100, 130, 169)
check("five bins: the six Pareto-minimal cost vectors and their weighted sums 16157, 16377, 16157, 16560, "
      "16274, 16157 are as printed",
      fr33 == [(33, 43, 43), (43, 37, 43), (46, 33, 43), (46, 40, 40), (46, 43, 36), (46, 46, 33)]
      and [sum(a * b for a, b in zip(MU33, r)) for r in fr33] == [16157, 16377, 16157, 16560, 16274, 16157])
check("five bins: the loads printed for the three policies of the lottery give the costs (33,43,43), "
      "(46,33,43), (46,46,33)",
      [(F(best_response_from([A33[5:]], root)), F(best_response_from([B33[6:]], pair)),
        F(best_response_from([C33[6:]], pair)))
       for root, pair in [((10, 10, 10, 10, 10), (16, 10, 10, 10, 10)),
                          ((30, 10, 10, 0, 0), (30, 10, 10, 6, 0)),
                          ((30, 20, 0, 0, 0), (30, 26, 0, 0, 0))]]
      == [(33, 43, 43), (46, 33, 43), (46, 46, 33)])
X = F(10, 33)
ROWS3 = [(0, X, X), (1 - 2 * X, 0, X), (1 - 2 * X, 1 - 2 * X, 0)]
check("five bins: the excess vectors of the three policies are (0,x,x), (1-2x,0,x), (1-2x,1-2x,0) with x = 10/33",
      [tuple(F(c, 33) - 1 for c in r) for r in [(33, 43, 43), (46, 33, 43), (46, 46, 33)]] == ROWS3)
W3 = X * (1 - X) * (1 - 2 * X) / (1 - 3 * X + 3 * X * X)
check("five bins: the game of these three rows has excess value x(1-x)(1-2x)/(1-3x+3x^2) = 2990/13167 at "
      "x = 10/33 (prior (100,130,169)/399 and lottery (169,130,100)/399 both give it)",
      W3 == F(2990, 13167) == F(16157, 13167) - 1
      and all(sum(F(a, 399) * b for a, b in zip(MU33, r)) == W3 for r in ROWS3)
      and all(sum(F(wt, 399) * r[j] for wt, r in zip((169, 130, 100), ROWS3)) == W3 for j in range(3)))


class Q3:
    """numbers a + b*sqrt(3) with rational a, b"""

    def __init__(self, a, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(self, o):
        o = o if isinstance(o, Q3) else Q3(o)
        return Q3(self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        o = o if isinstance(o, Q3) else Q3(o)
        return Q3(self.a - o.a, self.b - o.b)

    def __mul__(self, o):
        o = o if isinstance(o, Q3) else Q3(o)
        return Q3(self.a * o.a + 3 * self.b * o.b, self.a * o.b + self.b * o.a)

    def __eq__(self, o):
        o = o if isinstance(o, Q3) else Q3(o)
        return self.a == o.a and self.b == o.b


# with u = x(1-x) the expression is u*sqrt(1-4u)/(1-3u); it is at most c, where 9c^2 = 2*sqrt(3) - 3,
# because c^2 (1-3u)^2 - u^2 (1-4u) = 4 (u - u0)^2 (u + sqrt(3)/6) with u0 = (3 - sqrt(3))/6
c2 = Q3(F(-3, 9), F(2, 9))
u0 = Q3(F(1, 2), F(-1, 6))
r3 = Q3(0, F(1, 6))
lhs = [c2, c2 * (-6), c2 * 9 - 1, Q3(4)]                       # coefficients of 1, u, u^2, u^3
rhs = [u0 * u0 * r3 * 4, (u0 * u0 - u0 * r3 * 2) * 4, (r3 - u0 * 2) * 4, Q3(4)]
check("five bins: c^2(1-3u)^2 - u^2(1-4u) = 4(u-u0)^2(u+sqrt(3)/6) with 9c^2 = 2 sqrt(3) - 3 and "
      "u0 = (3-sqrt(3))/6, so the expression is at most c = sqrt(2 sqrt(3) - 3)/3",
      all(a == b for a, b in zip(lhs, rhs)))
# c < 2990/13167 + 5e-7:  9M^2 > 2 sqrt(3) - 3  <=>  ((9M^2 + 3)/2)^2 > 3 ; and c > 0.2270833
M = F(2990, 13167) + F(5, 10 ** 7)
LO = F(2270833, 10 ** 7)
check("five bins: 0.2270833 < sqrt(2 sqrt(3) - 3)/3 < 2990/13167 + 5*10^-7",
      ((9 * M * M + 3) / 2) ** 2 > 3 and ((9 * LO * LO + 3) / 2) ** 2 < 3)

# ---------------------------------------------------------------------------------------------
# 4. decimals and comparisons printed with the new results
# ---------------------------------------------------------------------------------------------
print("== 4. printed decimals ==")


def trunc(fr, digits):
    return F(int(fr * 10 ** digits), 10 ** digits)


check("truncated decimals: 6971/5823 = 1.1971..., 1781/1485 = 1.1993..., 403/336 = 1.1994..., "
      "16157/13167 = 1.22708..., 240961012/200582107 = 1.20130...",
      trunc(F(6971, 5823), 4) == F(11971, 10 ** 4) and trunc(F(1781, 1485), 4) == F(11993, 10 ** 4)
      and trunc(F(403, 336), 4) == F(11994, 10 ** 4) and trunc(F(16157, 13167), 5) == F(122708, 10 ** 5)
      and trunc(F(240961012, 200582107), 5) == F(120130, 10 ** 5))
check("complete games: 403/336 is the largest of 7/6, 19/16, 47/40, 143/120, 403/336, 55/46, 6971/5823, "
      "1781/1485, and it is below 1.1995 and below 240961012/200582107",
      max(F(7, 6), F(19, 16), F(47, 40), F(143, 120), F(403, 336), F(55, 46), F(6971, 5823), F(1781, 1485))
      == F(403, 336) < F(11995, 10 ** 4) and F(403, 336) < F(240961012, 200582107))
check("table of bounds on R_m: 7/6, 11/9, 5/4, 19/15, 23/18 for m = 2, 4, 6, 8, 10 (and m + 1); increasing, "
      "below 4/3; 11/9 < 16157/13167 < 5/4; 91/76, 6/5 and 17/14 are below 11/9",
      [F(4 * n + 3, 3 * n + 3) for n in range(1, 6)] == [F(7, 6), F(11, 9), F(5, 4), F(19, 15), F(23, 18)]
      and all(F(4 * n + 3, 3 * n + 3) < F(4 * n + 7, 3 * n + 6) < F(4, 3) for n in range(1, 200))
      and F(11, 9) < F(16157, 13167) < F(5, 4) and max(F(91, 76), F(6, 5), F(17, 14)) < F(11, 9))

# ---------------------------------------------------------------------------------------------
# 5. catalogs found on 14 Nov 2026 (evening): the five-stream record on three bins (Prop. 3.5(iii)),
#    its member of capacity 58 (App. C.6), and four to eight bins (Prop. C.5)
# ---------------------------------------------------------------------------------------------
print("== 5. new catalogs ==")
certify('three bins, five streams, capacity 8580 (Prop. 3.5(iii))',
        [(1325, 1325, 1186, 1186, 1047, 1047, 6208, 6208, 6208), (1325, 1325, 1186, 1186, 1047, 1047, 8580, 8580, 1464), (1325, 1325, 1186, 1186, 1047, 1047, 3558, 7533, 7533), (1325, 1325, 1186, 1186, 1047, 1047, 3558, 8580, 6486), (1325, 1325, 1186, 1186, 1047, 1047, 3558, 5022, 5022, 5022)], 3, 8580,
        [[(1186, 1186, 6208), (1325, 1047, 6208), (1325, 1047, 6208)], [(1325, 1325, 1186, 1186, 1047, 1047, 1464), (8580,), (8580,)], [(1325, 1325, 1186, 1186, 3558), (1047, 7533), (1047, 7533)], [(1325, 1325, 1186, 1186, 3558), (8580,), (1047, 1047, 6486)], [(1325, 1186, 1047, 5022), (1325, 1186, 1047, 5022), (3558, 5022)]],
        (151718320467, 176258792429, 76869864428, 52329577698, 228588156539),
        [((12416, 8580, 11091, 10044, 10044), F(306980924240, 2971647083431)), ((11230, 10674, 9627, 8580, 10044), F(7398511150, 2971647083431)), ((11999, 9905, 9349, 9349, 10044), F(780445307085, 2971647083431)), ((8858, 10813, 10183, 10813, 10813), F(1157393330881, 2971647083431)), ((9905, 10674, 11230, 10674, 9905), F(719429010075, 2971647083431))],
        F(2356712165002156, 228588237187), npareto=69)
certify('three bins, five streams, capacity 58 (App. C.6)',
        [(9, 9, 8, 8, 7, 7, 42, 42, 42), (9, 9, 8, 8, 7, 7, 58, 58, 10), (9, 9, 8, 8, 7, 7, 24, 51, 51), (9, 9, 8, 8, 7, 7, 24, 58, 44), (9, 9, 8, 8, 7, 7, 24, 34, 34, 34)], 3, 58,
        [[(8, 8, 42), (9, 7, 42), (9, 7, 42)], [(9, 9, 8, 8, 7, 7, 10), (58,), (58,)], [(9, 9, 8, 8, 24), (7, 51), (7, 51)], [(9, 9, 8, 8, 24), (58,), (7, 7, 44)], [(9, 8, 7, 34), (9, 8, 7, 34), (24, 34)]],
        (113, 135, 58, 36, 171),
        [((58, 74, 67, 74, 74), F(7, 114)), ((84, 58, 75, 68, 68), F(2, 19)), ((68, 72, 77, 72, 66), F(25, 114)), ((81, 67, 63, 63, 68), F(5, 19)), ((60, 73, 69, 73, 73), F(20, 57))],
        F(1324, 19))
certify('four bins, capacity 9 (Prop. C.5(i))',
        [(3, 3, 3, 3, 6, 6, 6, 6), (3, 3, 3, 3, 3, 9, 6, 6), (3, 3, 3, 3, 3, 1, 1, 1, 9, 9), (3, 3, 3, 3, 3, 1, 8, 9, 3), (3, 3, 3, 3, 3, 1, 8, 6, 6)], 4, 9,
        [[(3, 6), (3, 6), (3, 6), (3, 6)], [(9,), (3, 6), (3, 6), (3, 3, 3)], [(9,), (9,), (3, 3, 3), (3, 3, 1, 1, 1)], [(9,), (1, 8), (3, 3, 3), (3, 3, 3)], [(1, 8), (3, 6), (3, 6), (3, 3, 3)]],
        (9, 7, 6, 6, 3),
        [((9, 12, 12, 12, 11), F(10, 31)), ((12, 9, 12, 12, 9), F(5, 31)), ((12, 12, 9, 10, 12), F(8, 31)), ((12, 12, 10, 9, 12), F(3, 31)), ((12, 9, 12, 11, 11), F(5, 31))],
        F(342, 31), npareto=5)
certify('five bins, capacity 10 (Prop. C.5(ii))',
        [(3, 3, 3, 3, 3, 10, 10, 7, 7, 1), (3, 3, 3, 3, 3, 7, 7, 7, 7, 7), (3, 3, 3, 3, 3, 3, 10, 10, 10, 1, 1), (3, 3, 3, 3, 3, 3, 7, 7, 7, 10, 1), (3, 3, 3, 3, 3, 3, 4, 10, 10, 7, 1), (3, 3, 3, 3, 3, 3, 4, 7, 7, 7, 7), (3, 3, 3, 3, 3, 3, 4, 4, 10, 7, 7), (3, 3, 3, 3, 3, 3, 4, 4, 4, 10, 10)], 5, 10,
        [[(10,), (10,), (3, 7), (3, 7), (3, 3, 3, 1)], [(3, 7), (3, 7), (3, 7), (3, 7), (3, 7)], [(10,), (10,), (10,), (3, 3, 3, 1), (3, 3, 3, 1)], [(10,), (3, 7), (3, 7), (3, 7), (3, 3, 3, 1)], [(10,), (10,), (3, 7), (3, 3, 4), (3, 3, 3, 1)], [(3, 7), (3, 7), (3, 7), (3, 7), (3, 3, 4)], [(10,), (3, 7), (3, 7), (3, 3, 4), (3, 3, 4)], [(10,), (10,), (3, 3, 4), (3, 3, 4), (3, 3, 4)]],
        (16, 48, 55, 26, 13, 3, 39, 78),
        [((13, 10, 13, 13, 13, 10, 13, 13), F(46, 139)), ((13, 14, 10, 14, 11, 14, 14, 12), F(15, 139)), ((13, 13, 13, 10, 13, 14, 11, 13), F(57, 278)), ((10, 14, 13, 13, 13, 14, 13, 11), F(9, 139)), ((12, 14, 12, 13, 12, 13, 12, 12), F(63, 278)), ((13, 13, 13, 13, 10, 14, 14, 11), F(3, 139)), ((10, 14, 13, 12, 12, 14, 12, 12), F(6, 139))],
        F(3461, 278), npareto=20)
certify('six bins, capacity 10 (Prop. C.5(iii))',
        [(3, 3, 3, 3, 3, 3, 10, 10, 10, 10, 1, 1), (3, 3, 3, 3, 3, 3, 1, 10, 10, 7, 7, 7), (3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7), (3, 3, 3, 3, 3, 3, 4, 10, 7, 7, 7, 7), (3, 3, 3, 3, 3, 3, 4, 4, 10, 10, 10, 4), (3, 3, 3, 3, 3, 3, 4, 4, 7, 7, 10, 10), (3, 3, 3, 3, 3, 3, 4, 4, 3, 10, 10, 10, 1), (3, 3, 3, 3, 3, 3, 4, 4, 3, 7, 7, 7, 10)], 6, 10,
        [[(10,), (10,), (10,), (10,), (3, 3, 3, 1), (3, 3, 3, 1)], [(10,), (10,), (3, 7), (3, 7), (3, 7), (3, 3, 3, 1)], [(3, 7), (3, 7), (3, 7), (3, 7), (3, 7), (3, 7)], [(10,), (3, 7), (3, 7), (3, 7), (3, 7), (3, 3, 4)], [(10,), (10,), (10,), (3, 3, 4), (3, 3, 4), (3, 3, 4)], [(10,), (10,), (3, 7), (3, 7), (3, 3, 4), (3, 3, 4)], [(10,), (10,), (10,), (3, 4, 3), (3, 3, 4), (3, 3, 3, 1)], [(10,), (3, 7), (3, 7), (3, 7), (3, 3, 4), (3, 3, 4)]],
        (29, 16, 24, 18, 43, 18, 12, 6),
        [((13, 10, 14, 11, 13, 13, 13, 11), F(69, 415)), ((13, 13, 10, 13, 13, 13, 13, 13), F(134, 415)), ((13, 13, 13, 10, 13, 13, 13, 10), F(23, 415)), ((16, 13, 13, 13, 10, 13, 10, 14), F(9, 415)), ((13, 13, 13, 13, 13, 10, 13, 10), F(27, 415)), ((10, 14, 14, 14, 12, 14, 11, 14), F(27, 415)), ((12, 13, 14, 13, 12, 12, 12, 14), F(99, 415)), ((12, 13, 14, 13, 12, 12, 13, 12), F(27, 415))],
        F(1043, 83), npareto=19)
certify('seven bins, capacity 20 (Prop. C.5(iv))',
        [(6, 6, 6, 6, 6, 6, 6, 20, 20, 20, 20, 14, 2, 2), (6, 6, 6, 6, 6, 6, 6, 2, 20, 20, 14, 14, 14, 14), (6, 6, 6, 6, 6, 6, 6, 14, 14, 14, 14, 14, 14, 14), (6, 6, 6, 6, 6, 6, 6, 8, 14, 14, 20, 20, 20, 2), (6, 6, 6, 6, 6, 6, 6, 8, 20, 14, 14, 14, 14, 14), (6, 6, 6, 6, 6, 6, 6, 8, 8, 20, 20, 20, 20, 2), (6, 6, 6, 6, 6, 6, 6, 8, 8, 8, 20, 20, 20, 14), (6, 6, 6, 6, 6, 6, 6, 8, 8, 14, 14, 14, 20, 20)], 7, 20,
        [[(20,), (20,), (20,), (20,), (6, 14), (6, 6, 6, 2), (6, 6, 6, 2)], [(20,), (20,), (6, 14), (6, 14), (6, 14), (6, 14), (6, 6, 6, 2)], [(6, 14), (6, 14), (6, 14), (6, 14), (6, 14), (6, 14), (6, 14)], [(20,), (20,), (20,), (6, 14), (6, 14), (6, 6, 8), (6, 6, 6, 2)], [(20,), (6, 14), (6, 14), (6, 14), (6, 14), (6, 14), (6, 6, 8)], [(20,), (20,), (20,), (20,), (6, 6, 8), (6, 6, 8), (6, 6, 6, 2)], [(20,), (20,), (20,), (6, 14), (6, 6, 8), (6, 6, 8), (6, 6, 8)], [(20,), (20,), (6, 14), (6, 14), (6, 14), (6, 6, 8), (6, 6, 8)]],
        (3, 2, 3, 3, 3, 4, 3, 3),
        [((20, 28, 28, 22, 28, 28, 26, 22), F(1, 8)), ((26, 20, 28, 26, 22, 26, 26, 26), F(1, 6)), ((26, 26, 20, 26, 26, 26, 26, 26), F(7, 24)), ((26, 26, 28, 20, 28, 26, 26, 22), F(1, 24)), ((26, 26, 26, 26, 20, 26, 26, 26), F(1, 8)), ((26, 26, 28, 26, 28, 20, 22, 28), F(1, 6)), ((26, 26, 26, 26, 26, 26, 20, 26), F(1, 72)), ((26, 26, 26, 26, 26, 26, 26, 20), F(5, 72))],
        F(101, 4), npareto=19)
certify('eight bins, capacity 25 (Prop. C.5(v))',
        [(8, 8, 8, 8, 8, 8, 8, 8, 25, 25, 17, 17, 17, 17, 17, 1), (8, 8, 8, 8, 8, 8, 8, 8, 17, 17, 17, 17, 17, 17, 17, 17), (8, 8, 8, 8, 8, 8, 8, 8, 7, 25, 25, 25, 25, 25, 2, 1, 1), (8, 8, 8, 8, 8, 8, 8, 8, 7, 2, 25, 25, 25, 17, 17, 17, 1), (8, 8, 8, 8, 8, 8, 8, 8, 7, 18, 25, 17, 17, 17, 17, 17, 1), (8, 8, 8, 8, 8, 8, 8, 8, 7, 17, 17, 17, 17, 17, 17, 25, 2), (8, 8, 8, 8, 8, 8, 8, 8, 7, 10, 25, 25, 17, 17, 17, 17, 1), (8, 8, 8, 8, 8, 8, 8, 8, 7, 10, 17, 17, 17, 17, 17, 17, 17), (8, 8, 8, 8, 8, 8, 8, 8, 7, 10, 9, 17, 17, 25, 25, 25, 1), (8, 8, 8, 8, 8, 8, 8, 8, 7, 10, 9, 25, 17, 17, 17, 17, 17), (8, 8, 8, 8, 8, 8, 8, 8, 7, 10, 9, 9, 25, 25, 25, 25, 1), (8, 8, 8, 8, 8, 8, 8, 8, 7, 10, 9, 9, 17, 17, 17, 25, 25)], 8, 25,
        [[(25,), (25,), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 8, 8, 1)], [(8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17)], [(25,), (25,), (25,), (25,), (25,), (8, 8, 7, 2), (8, 8, 8, 1), (8, 8, 8, 1)], [(25,), (25,), (25,), (8, 17), (8, 17), (8, 17), (8, 8, 7, 2), (8, 8, 8, 1)], [(25,), (7, 18), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 8, 8, 1)], [(25,), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 8, 7, 2)], [(25,), (25,), (8, 17), (8, 17), (8, 17), (8, 17), (8, 7, 10), (8, 8, 8, 1)], [(8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 7, 10)], [(25,), (25,), (25,), (8, 17), (8, 17), (8, 7, 10), (8, 8, 9), (8, 8, 8, 1)], [(25,), (8, 17), (8, 17), (8, 17), (8, 17), (8, 17), (8, 7, 10), (8, 8, 9)], [(25,), (25,), (25,), (25,), (8, 7, 10), (8, 8, 9), (8, 8, 9), (8, 8, 8, 1)], [(25,), (25,), (8, 17), (8, 17), (8, 17), (8, 7, 10), (8, 8, 9), (8, 8, 9)]],
        (1210253, 15467039, 10376135, 8000321, 3318840, 12741281, 14256912, 712908, 16474640, 831726, 24078992, 950544),
        [((25, 34, 33, 33, 25, 26, 32, 34, 33, 27, 33, 32), F(1521048, 15488513)), ((33, 25, 33, 33, 33, 33, 33, 25, 33, 33, 33, 33), F(3606537, 15488513)), ((33, 33, 33, 33, 26, 25, 33, 27, 33, 33, 33, 33), F(1521048, 108419591)), ((25, 34, 33, 33, 32, 32, 25, 34, 33, 26, 33, 33), F(9084624, 108419591)), ((33, 34, 33, 32, 33, 33, 33, 34, 25, 34, 33, 26), F(1473432, 15488513)), ((34, 34, 25, 34, 34, 34, 34, 34, 34, 34, 28, 34), F(2198744, 15488513)), ((25, 34, 33, 33, 32, 32, 25, 34, 33, 34, 33, 26), F(1562712, 108419591)), ((34, 34, 33, 26, 34, 34, 34, 34, 27, 34, 32, 34), F(1187736, 15488513)), ((34, 34, 32, 33, 34, 34, 34, 34, 33, 34, 26, 34), F(901416, 15488513)), ((33, 33, 33, 33, 26, 25, 33, 34, 33, 27, 33, 33), F(9126288, 108419591)), ((34, 34, 33, 26, 34, 34, 27, 34, 32, 34, 33, 27), F(1521048, 15488513)), ((34, 34, 33, 26, 34, 34, 34, 34, 26, 34, 33, 26), F(36456, 15488513))],
        F(492629561, 15488513), npareto=81)
check("decimals of the new results: 1.20161..., 662/551 = 1.20145..., 38/31 = 1.22580..., 1.24496..., "
      "1.25662..., 101/80 = 1.2625, 1.27224...; each exceeds the previous bound",
      trunc(F(45321387788503, 37717059135855), 5) == F(120161, 10 ** 5) and trunc(F(662, 551), 5) == F(120145, 10 ** 5)
      and trunc(F(38, 31), 5) == F(122580, 10 ** 5) and trunc(F(3461, 2780), 5) == F(124496, 10 ** 5)
      and trunc(F(1043, 830), 5) == F(125662, 10 ** 5) and trunc(F(492629561, 387212825), 5) == F(127224, 10 ** 5)
      and F(45321387788503, 37717059135855) > F(662, 551) > F(240961012, 200582107) and F(38, 31) > F(11, 9)
      and F(3461, 2780) > F(16157, 13167) and F(1043, 830) > F(5, 4) and F(101, 80) > F(5, 4)
      and F(492629561, 387212825) > F(19, 15))


# ---------------------------------------------------------------------------------------------
# 6. catalogs found on 15 Nov 2026: three bins with 6, 12 and 49 streams, and five to nine bins.
#    The streams, packings, priors and lotteries are read from cats/; the values are typed here.
# ---------------------------------------------------------------------------------------------
print("== 6. catalogs of 15 Nov ==")
import json
import os
from functools import reduce
from math import gcd

CATS = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cats')


def from_file(name, label, value):
    with open(os.path.join(CATS, name + '.json')) as f:
        d = json.load(f)
    m, g = d['bins'], d['capacity']
    streams = [tuple(s) for s in d['streams']]
    packs = [[tuple(x for x, b in zip(s, a) if b == j) for j in sorted(set(a))] for s, a in zip(streams, d['packing'])]
    prior = [F(p) for p in d['prior']]
    den = reduce(lambda x, y: x * y // gcd(x, y), (p.denominator for p in prior), 1)
    lottery = [(tuple(r['costs']), F(r['weight'])) for r in d['lottery']]
    check(label + ": the file states the value %s" % value, F(d['value']) == value)
    certify(label, streams, m, g, packs, tuple(int(p * den) for p in prior), lottery, value * g)


from_file('r3_k6_cap51', 'three bins, six streams, capacity 51', F(13666, 11373))
from_file('r3_k12_cap30', 'three bins, twelve streams, capacity 30', F(780, 649))
from_file('r3_k49_cap60', 'three bins, 49 streams, capacity 60', F(1007655800692805129, 838300203936349800))
from_file('m5_k12_cap10', 'five bins, capacity 10', F(39271, 31540))
from_file('m6_k12_cap10', 'six bins, capacity 10', F(81359, 64730))
from_file('m7_k24_cap25', 'seven bins, capacity 25', F(12140793962621627, 9605854834663025))
from_file('m8_k20_cap25', 'eight bins, capacity 25', F(2645831613297, 2077084641125))
from_file('m9_k11_cap25', 'nine bins, eleven streams, capacity 25', F(11280369, 8837825))

check("decimals of the catalogs of 15 Nov: 1.201617..., 1.20184..., 1.20202..., 1.24511..., 1.25689..., "
      "1.26389..., 1.27381..., 1.27637...; each exceeds the previous bound",
      trunc(F(13666, 11373), 6) == F(1201617, 10 ** 6) and trunc(F(780, 649), 5) == F(120184, 10 ** 5)
      and trunc(F(1007655800692805129, 838300203936349800), 5) == F(120202, 10 ** 5)
      and trunc(F(39271, 31540), 5) == F(124511, 10 ** 5) and trunc(F(81359, 64730), 5) == F(125689, 10 ** 5)
      and trunc(F(12140793962621627, 9605854834663025), 5) == F(126389, 10 ** 5)
      and trunc(F(2645831613297, 2077084641125), 5) == F(127381, 10 ** 5)
      and trunc(F(11280369, 8837825), 5) == F(127637, 10 ** 5)
      and F(1007655800692805129, 838300203936349800) > F(780, 649) > F(13666, 11373) > F(45321387788503, 37717059135855)
      and F(39271, 31540) > F(3461, 2780) and F(81359, 64730) > F(1043, 830)
      and F(12140793962621627, 9605854834663025) > F(101, 80) and F(2645831613297, 2077084641125) > F(492629561, 387212825)
      and F(11280369, 8837825) > F(19, 15))

print("== %d checks, %d failed, %.1f s ==" % (NCHECK[0], len(FAILS), time.time() - T0))
for f in FAILS:
    print("FAILED: " + f)
sys.exit(1 if FAILS else 0)
