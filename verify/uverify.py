"""uverify.py -- STANDALONE exact verifier for the region certificate of  V_U(p) <= T  on the fundamental domain F.
Agent ucert-region.  Imports nothing from the search code (ucore/bnb/frontier); numpy is used only for
vectorised int64 arithmetic whose magnitudes are bounded explicitly below 2^62 (asserted), i.e. exact integers.

Problem (re-derived here).  p = (LA, XB, XC, YB, YC) in R^15; free coordinates
  z = (LA0, LA1, LA2, XB0, XB1, XC0, XC1, YB0, YB1, YB2, YC0, YC1),  XB2 = V-XB0-XB1, XC2 = V-XC0-XC1,
  YC2 = W-YC0-YC1 with V = LA0+LA1+LA2, W = YB0+YB1+YB2.  Box coordinates x with z = Qi x ('z': Qi = I;
  'm': z3 = x3+x0, z4 = x4+x1, z5 = x5+x0, z6 = x6+x1, z10 = x10+x7, z11 = x11+x8).
Row (S, col, S2, col2): root online loads h_b = sum_{l: col[l]=b} M_S[l] (M = LA, XB, XC), paired
  g_b = sum_{l: col2[l]=b} Y_S2[l] (Y = YB, YC).  Stream A sees h, B and C see h+g.  Stream loads
  L_A = LA, L_B = XB+YB, L_C = XC+YC.  Completion f: {0,1,2} -> {0,1,2};
  ell_{j,f,b} = online_b + sum_{q: f(q)=b} (1 - L_j[q]);  cost_j(row) = min_f max_b ell <= max_b ell_{j,f,b}.
Certificate of a box: integer weights W[(r,j,f)] >= 0 with sum_f W[r,j,f] = Lam[r] independent of j and
  sum_r Lam[r] = DEN.  For every prior mu and every p in the box (feasible or not):
  min_rows mu.cost <= sum_r (Lam_r/DEN) mu.cost_r <= max_j sum_{r,f} (W/DEN) max_b ell_{j,f,b}(p) =: max_j Phi_j(p),
  and Phi_j is convex, so its max over the box is attained at a vertex; we check Phi_j(vertex) <= 1 + T exactly.
Root box: z-coords [0,1]^12, m-coords [0,1] x [-1,1] for the differences; it contains F because every free
  coordinate is a nonnegative part of a stream load <= 1.
Tree (v2): every node box is first TIGHTENED by deterministic bound propagation (2 passes over the constraints
  of F in a fixed order; each new bound is implied by one constraint and the current bounds, rounded outward --
  ceil for upper, floor for lower bounds; push-u22 fix, the original rounded inward), so the tightened box
  contains (box cap F).  Then one record in DFS preorder:
  'S c'           split the tightened box at mid = floor((lo_c+hi_c)/2) into [lo_c,mid], [mid,hi_c];
  'X'             tightened box empty or degenerate (some lo_c == hi_c), or 'X k1 y1 k2 y2 ..': y > 0 integers
                  with min over the tightened box of (sum y_k a_k).x >= sum y_k b_k, so the box misses int(F).
  Dropped boxes meet F in a closed set of measure zero; the certified leaves then cover a dense subset of F,
  and V_U (continuous: max over priors of a min of piecewise-affine functions) is <= T on all of F.
  'C r j f W ... [; j k N ...]' certificate on the tightened box (exact vertex check), optionally with
                  Lagrange multipliers N/2^30 >= 0 for constraints k of F per stream j (valid on box cap F);
  'P name'        subtree deferred to the block 'B name' ... 'E name' (top file: names 0,1,2,..; inside block
                  n: n.0, n.1, ...); every deferred name must have exactly one block.
  The top file covers the root box; the leaves of each replayed tree partition its root.
usage: python uverify.py <coords> <Tnum> <Tden> <rows.json> <top file> <block files...>
"""
import sys, os, json, itertools, time
import multiprocessing as mp
import numpy as np

DMAX = 30
ONE = 1 << DMAX
DEN = 1 << 24


def lin(**kw):
    v = [0] * 12
    for k, c in kw.items():
        v[int(k[1:])] += c
    return v


def add(*vs):
    return [sum(t) for t in zip(*vs)]


def scale(c, v):
    return [c * t for t in v]


# natural coordinates as linear forms in z
E = [[1 if i == k else 0 for i in range(12)] for k in range(12)]
Vz = add(E[0], E[1], E[2])
Wz = add(E[7], E[8], E[9])
PZ = [E[0], E[1], E[2],
      E[3], E[4], add(Vz, scale(-1, E[3]), scale(-1, E[4])),
      E[5], E[6], add(Vz, scale(-1, E[5]), scale(-1, E[6])),
      E[7], E[8], E[9],
      E[10], E[11], add(Wz, scale(-1, E[10]), scale(-1, E[11]))]


def Qi_of(name):
    Q = [[1 if i == k else 0 for i in range(12)] for k in range(12)]       # z_k = sum_i Q[k][i] x_i
    root_lo = [0] * 12
    if name == 'm':
        for k, base in [(3, 0), (4, 1), (5, 0), (6, 1), (10, 7), (11, 8)]:
            Q[k][base] = 1
            root_lo[k] = -1
    else:
        assert name == 'z'
    return Q, root_lo, [1] * 12


def to_x(vz, Q):
    """linear form over z -> over x."""
    return [sum(vz[k] * Q[k][i] for k in range(12)) for i in range(12)]


def F_constraints():
    """a.z <= b: D (nonnegativity, capacity) and the symmetry ordering defining F."""
    C = []
    XB2, XC2, YC2 = PZ[5], PZ[8], PZ[14]
    for k in range(15):
        C.append((scale(-1, PZ[k]), 0))                      # p_k >= 0 (15 constraints)
    for q in range(3):
        C.append((PZ[q], 1))                                 # LA_q <= 1
        C.append((add(PZ[3 + q], PZ[9 + q]), 1))             # LB_q <= 1
        C.append((add(PZ[6 + q], PZ[12 + q]), 1))            # LC_q <= 1
    for blk in (0, 3, 6):                                    # sorted LA, XB, XC
        C.append((add(PZ[blk + 1], scale(-1, PZ[blk])), 0))
        C.append((add(PZ[blk + 2], scale(-1, PZ[blk + 1])), 0))
    C.append((add(PZ[6], scale(-1, PZ[3])), 0))              # XB0 >= XC0
    return C


def row_forms(S, col, S2, col2):
    """online loads per stream: on[j][b] = linear form over z."""
    h = [[0] * 12 for _ in range(3)]
    g = [[0] * 12 for _ in range(3)]
    for l in range(3):
        h[col[l]] = add(h[col[l]], PZ[3 * S + l])
        g[col2[l]] = add(g[col2[l]], PZ[9 + 3 * S2 + l])
    kk = [add(h[b], g[b]) for b in range(3)]
    return [h, kk, kk]


LOADS = [[PZ[q] for q in range(3)],
         [add(PZ[3 + q], PZ[9 + q]) for q in range(3)],
         [add(PZ[6 + q], PZ[12 + q]) for q in range(3)]]


def ell_forms(on, j, f):
    """three affine forms (coef over z, const) for stream j, completion f (tuple f[q])."""
    out = []
    for b in range(3):
        a = list(on[j][b]); c = 0
        for q in range(3):
            if f[q] == b:
                a = add(a, scale(-1, LOADS[j][q])); c += 1
        out.append((a, c))
    return out


FMAP = list(itertools.product(range(3), repeat=3))


class Verifier:
    def __init__(self, name, Tn, Td, rows):
        self.Q, self.rlo, self.rhi = Qi_of(name)
        self.Tn, self.Td = Tn, Td
        self.rows = rows
        self.cache = {}
        self.cons = [(to_x(a, self.Q), b) for a, b in F_constraints()]
        self.CA = np.array([a for a, b in self.cons], dtype=np.int64)
        self.CB = np.array([b for a, b in self.cons], dtype=np.int64)
        assert int(np.abs(self.CA).max()) <= 4

    def forms(self, r, j, f):
        key = (r, j, f)
        if key not in self.cache:
            S, col, S2, col2 = self.rows[r]
            fl = ell_forms(row_forms(S, tuple(col), S2, tuple(col2)), j, FMAP[f])
            A = np.array([to_x(a, self.Q) for a, c in fl], dtype=np.int64)
            Bc = np.array([c for a, c in fl], dtype=np.int64)
            assert int(np.abs(A).sum(1).max()) + 3 < 32
            self.cache[key] = (A, Bc)
        return self.cache[key]

    def propagate(self, lo, hi):
        """tightened copy of [lo,hi] containing [lo,hi] cap F, or None if provably empty (|values| < 2^40).
        The box is the REAL box {lo <= x <= hi} (x scaled by ONE), so every new bound is rounded OUTWARD:
        a_k > 0: x_k <= rhs_k / a_k  ->  hi_k = min(hi_k, ceil(rhs_k / a_k));
        a_k < 0: x_k >= rhs_k / a_k  ->  lo_k = max(lo_k, floor(rhs_k / a_k)).
        (push-u22 fix of 2026-11-14: the original used floor / ceil, i.e. inward rounding, which can cut off real
        points of F within 2^-30 of a face with |a_k| = 2, e.g. XB1 = XB2 or XC1 = XC2.)"""
        lo = lo.copy(); hi = hi.copy()
        for _ in range(2):
            for c in range(len(self.CA)):
                a = self.CA[c]
                t = np.where(a > 0, a * lo, a * hi)
                rhs = int(self.CB[c]) * ONE - (int(t.sum()) - t)          # per k: b*ONE - sum_{i != k} min
                pos, neg = a > 0, a < 0
                if pos.any():
                    hi[pos] = np.minimum(hi[pos], -((-rhs[pos]) // a[pos]))     # ceil(rhs/a), a > 0
                if neg.any():
                    lo[neg] = np.maximum(lo[neg], (-rhs[neg]) // (-a[neg]))     # floor(rhs/a), a < 0
                if np.any(lo > hi):
                    return None
        return lo, hi

    def farkas_ok(self, lo, hi, ys):
        """y >= 0, y != 0 and min over the box of (y.A).x >= y.b: then the box misses int(F) (interior points
        satisfy every constraint strictly, hence (y.A).x < y.b)."""
        a = [0] * 12; b = 0
        if not ys:
            return False
        for k, y in ys:
            assert y > 0
            a = [ai + y * int(ci) for ai, ci in zip(a, self.CA[k])]
            b += y * int(self.CB[k])
        mn = sum(ai * (int(lo[i]) if ai > 0 else int(hi[i])) for i, ai in enumerate(a))
        return mn >= b * ONE

    def cert_ok(self, lo, hi, W, NU=None):
        """W[(r,j,f)] mixture weights (sum DEN per stream, common row marginals); NU[(j,k)] >= 0: Lagrange
        multiplier N/2^30 of constraint k of F for stream j.  Checks at every vertex X of the box, exactly:
        Td*(2^30 * sum W max_b ell(X) + DEN * sum_k N (b_k ONE - a_k.X)) <= (Td+Tn) DEN ONE 2^30."""
        NU = NU or {}
        assert all(abs(int(v)) <= ONE for v in list(lo) + list(hi))
        for (j, k), n in NU.items():
            if n < 0 or not (0 <= j < 3) or not (0 <= k < len(self.CA)):
                return False
        lam = {}
        tot = [0, 0, 0]
        for (r, j, f), w in W.items():
            if w < 0 or not (0 <= j < 3) or not (0 <= f < 27):
                return False
            lam.setdefault(r, [0, 0, 0])[j] += w
            tot[j] += w
        if tot != [DEN] * 3 or any(not (a == b == c) for a, b, c in lam.values()):
            return False
        act = [i for i in range(12) if hi[i] > lo[i]]
        nb = len(act)
        bits = (np.arange(1 << nb)[:, None] >> np.arange(nb)[None]) & 1
        Vt = np.tile(np.array(lo, dtype=np.int64), (1 << nb, 1))
        Vt[:, act] += bits * (np.array(hi, dtype=np.int64) - np.array(lo, dtype=np.int64))[act][None]
        for j in range(3):
            acc = np.zeros(len(Vt), dtype=np.int64)
            for (r, jj, f), w in W.items():
                if jj != j or w == 0:
                    continue
                A, Bc = self.forms(r, j, f)
                ell = Vt @ A.T + Bc[None, :] * ONE                 # |ell| < 2^35
                acc += w * ell.max(1)                              # sum of w = 2^24: |acc| < 2^59
            nj = [(k, n) for (jj, k), n in NU.items() if jj == j and n > 0]
            if not nj:
                m = int(acc.max())
                if m * self.Td > (self.Td + self.Tn) * DEN * ONE:
                    return False
                continue
            c = [0] * 12; beta = 0
            for k, n in nj:
                c = [ci + n * int(ak) for ci, ak in zip(c, self.CA[k])]
                beta += n * int(self.CB[k])
            g = beta * ONE - Vt.astype(object) @ np.array(c, dtype=object)        # python ints
            tot = acc.astype(object) * (1 << 30) + DEN * g
            m = max(tot)
            if m * self.Td > (self.Td + self.Tn) * DEN * ONE * (1 << 30):
                return False
        return True

    def replay(self, recs, lo0, hi0, stats, allow_p):
        """replay preorder records on root [lo0,hi0]; returns list of deferred boxes (P leaves) in order."""
        stack = [(lo0, hi0)]
        pend = []
        for t in recs:
            lo, hi = stack.pop()
            pr = self.propagate(lo, hi)
            if pr is not None and bool(np.any(pr[0] == pr[1])):
                pr = None                               # degenerate: (box cap F) has measure zero
            if t[0] == 'X':
                stats['excl'] += 1
                if pr is None:
                    continue
                ys = [(int(t[k]), int(t[k + 1])) for k in range(1, len(t), 2)]
                if not ys or not self.farkas_ok(pr[0], pr[1], ys):
                    stats['bad'] += 1
                continue
            if pr is None:
                stats['bad'] += 1                       # only 'X' may follow an empty box
                continue
            lo, hi = pr
            if t[0] == 'S':
                c = int(t[1])
                assert hi[c] - lo[c] >= 2
                mid = (int(lo[c]) + int(hi[c])) // 2
                l2, h1 = lo.copy(), hi.copy(); h1[c] = mid; l2[c] = mid
                stack.append((l2, hi)); stack.append((lo, h1))
            elif t[0] == 'C':
                stats['cert'] += 1
                sep = t.index(';') if ';' in t else len(t)
                v = list(map(int, t[1:sep]))
                W = {}
                for k in range(0, len(v), 4):
                    key = (v[k], v[k + 1], v[k + 2])
                    assert key not in W and 0 <= v[k] < len(self.rows)
                    W[key] = v[k + 3]
                u = list(map(int, t[sep + 1:]))
                NU = {}
                for k in range(0, len(u), 3):
                    assert (u[k], u[k + 1]) not in NU
                    NU[(u[k], u[k + 1])] = u[k + 2]
                if not self.cert_ok(lo, hi, W, NU):
                    stats['bad'] += 1
            elif t[0] == 'P':
                pend.append((t[1], lo, hi))
            else:
                raise ValueError(t)
        assert not stack, 'incomplete tree'
        return pend


DUPS = []


def index_blocks(files):
    """name -> (file, byte offset of the first record line) for every complete block 'B name' ... 'E name'."""
    idx = {}
    for fn in files:
        with open(fn, 'rb') as fh:
            cur = None
            pos = 0
            for l in fh:
                t = l.split()
                if t:
                    if t[0] == b'B':
                        cur = (t[1].decode(), pos + len(l))
                    elif t[0] == b'E':
                        assert cur is not None and t[1].decode() == cur[0]
                        if cur[0] in idx:                # a second complete block for the same box: the first
                            DUPS.append(cur[0])          # one is used (every used block is fully checked)
                        else:
                            idx[cur[0]] = (fn, cur[1])
                        cur = None
                    elif t[0] == b'F':
                        cur = None
                pos += len(l)
    return idx


def load_block(fn, off):
    recs = []
    with open(fn, 'rb') as fh:
        fh.seek(off)
        for l in fh:
            t = l.decode().split()
            if not t:
                continue
            if t[0] == 'E':
                return recs
            assert t[0] not in ('B', 'F')
            recs.append(t)
    raise ValueError('unterminated block')


_V = None


def _work(item):
    name, (fn, off), lo, hi = item
    st = dict(excl=0, cert=0, bad=0)
    pend = _V.replay(load_block(fn, off), lo, hi, st, True)
    return name, st, pend


def main():
    """worklist of deferred boxes: the top file's 'P i' leaves are named i; a block named n may defer subtrees with
    'P n.k' (k = 0, 1, 2, ... in order).  Every deferred name must have exactly one block 'B name' ... 'E name'."""
    global _V
    name, Tn, Td, rowsf, topf = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
    files = sys.argv[6:]
    t0 = time.time()
    rows = [tuple(r) for r in json.load(open(rowsf))]
    for S, col, S2, col2 in rows:
        assert S in (0, 1, 2) and S2 in (0, 1) and all(c in (0, 1, 2) for c in list(col) + list(col2))
    V = Verifier(name, Tn, Td, rows)
    _V = V
    stats = dict(excl=0, cert=0, bad=0)
    top = [l.split() for l in open(topf) if l.strip()]
    root = (np.array(V.rlo, dtype=np.int64) * ONE, np.array(V.rhi, dtype=np.int64) * ONE)
    pend = V.replay(top, root[0], root[1], stats, True)
    for k, (nm, lo, hi) in enumerate(pend):
        assert nm == str(k), 'top-level deferred names must be 0,1,2,...'
    print('top tree: %d deferred boxes, %s' % (len(pend), stats), flush=True)
    blocks = index_blocks(files)
    print('indexed %d blocks (%d duplicate names ignored)' % (len(blocks), len(DUPS)), flush=True)
    nproc = int(os.environ.get('UV_NPROC', '1'))
    work = list(pend)
    seen = set()
    missing = []
    pool = mp.Pool(nproc) if nproc > 1 else None
    nblocks = 0
    while work:
        items = []
        for nm, lo, hi in work:
            assert nm not in seen, 'name reused ' + nm
            seen.add(nm)
            if nm in blocks:
                items.append((nm, blocks[nm], lo, hi))
            else:
                missing.append(nm)
        work = []
        res = pool.imap_unordered(_work, items, chunksize=4) if pool else map(_work, items)
        for nm, st, sub in res:
            nblocks += 1
            for k in ('excl', 'cert', 'bad'):
                stats[k] += st[k]
            for k, (nm2, lo, hi) in enumerate(sub):
                if nm2 != '%s.%d' % (nm, k):
                    stats['bad'] += 1
                work.append((nm2, lo, hi))
    unused = set(blocks) - seen
    print('blocks used %d  missing %d  unused %d  leaves: cert %d excl %d  BAD %d  time %.1fs' % (
        nblocks, len(missing), len(unused), stats['cert'], stats['excl'], stats['bad'], time.time() - t0))
    if not missing and stats['bad'] == 0:
        print('VERIFIED: V_U(p) <= %d/%d for every p in F (coords %s)' % (Tn, Td, name))
    else:
        print('NOT VERIFIED (missing %d, bad %d); missing: %s' % (len(missing), stats['bad'], missing[:50]))


if __name__ == '__main__':
    main()
