# Exact certificates that the invariant R of the two-bin coin c14b is closed under every move.
# python3 lift.py hedge|late|aB|Ab OUT.jsonl [PREFIX]
import sys, json, time
from fractions import Fraction as F
from math import gcd
import numpy as np
from scipy.optimize import linprog

NV = 8
IV = dict(V=0, m=1, s=2, aA=3, aB=4, x=5, m2=6, s2=7)

class L:
    __slots__ = ('c',)
    def __init__(self, c): self.c = tuple(c)
    @staticmethod
    def var(n): c = [F(0)] * (NV + 1); c[IV[n]] = F(1); return L(c)
    @staticmethod
    def const(k): c = [F(0)] * (NV + 1); c[NV] = F(k); return L(c)
    def __add__(s, o): o = o if isinstance(o, L) else L.const(o); return L([a + b for a, b in zip(s.c, o.c)])
    __radd__ = __add__
    def __sub__(s, o): o = o if isinstance(o, L) else L.const(o); return L([a - b for a, b in zip(s.c, o.c)])
    def __rsub__(s, o): return L.const(o) - s
    def __neg__(s): return L([-a for a in s.c])
    def __mul__(s, k): return L([a * F(k) for a in s.c])
    __rmul__ = __mul__

def norm(form, strict):
    c = list(form.c); den = 1
    for a in c: den = den * a.denominator // gcd(den, a.denominator)
    ic = [int(a * den) for a in c]; g = 0
    for a in ic: g = gcd(g, abs(a))
    if g == 0: g = 1
    return tuple(a // g for a in ic) + (1 if strict else 0,)

def GE(f): return norm(f, False)
def GT(f): return norm(f, True)
def LE(f, g): return GE(g - f)
def LT(f, g): return GT(g - f)

STATS = dict(lp=0, cert=0, certfail=0)

def lp_empty(cons):
    A = []; b = []
    for r in cons:
        A.append([-float(v) for v in r[:NV]] + [1.0 if r[NV + 1] else 0.0]); b.append(float(r[NV]))
    STATS['lp'] += 1
    res = linprog([0.0] * NV + [-1.0], A_ub=np.array(A), b_ub=np.array(b),
                  bounds=[(None, None)] * NV + [(None, 1.0)], method='highs-ds')
    if res.status == 2:
        return certify(cons, None)
    if res.status != 0: return ('unk', None)
    t = -res.fun
    if t > 1e-9: return (False, None)
    duals = -res.ineqlin.marginals
    return certify(cons, duals)

def certify(cons, duals):
    supp = list(range(len(cons))) if duals is None else [i for i, d in enumerate(duals) if d > 1e-12]
    for attempt in range(2):
        if attempt == 1: supp = list(range(len(cons)))
        y = exact_mult([cons[i] for i in supp])
        if y is not None:
            yy = [F(0)] * len(cons)
            for k, i in enumerate(supp): yy[i] = y[k]
            if verify(cons, yy):
                STATS['cert'] += 1
                return (True, yy)
    STATS['certfail'] += 1
    return ('unk', None)

def exact_mult(rows):
    n = len(rows)
    if n == 0: return None
    Aeq = [[float(r[j]) for r in rows] for j in range(NV)] + [[1.0] * n]
    beq = [0.0] * NV + [1.0]
    cst = [float(r[NV]) for r in rows]
    res = linprog(cst, A_eq=np.array(Aeq), b_eq=np.array(beq), bounds=[(0, None)] * n, method='highs-ds')
    STATS['lp'] += 1
    if res.status != 0: return None
    cands = []
    if res.fun < -1e-9: cands.append(res.x)
    else:
        strict = [-(1.0 if r[NV + 1] else 0.0) for r in rows]
        res2 = linprog(strict, A_ub=np.array([cst]), b_ub=np.array([0.0]), A_eq=np.array(Aeq), b_eq=np.array(beq),
                       bounds=[(0, None)] * n, method='highs-ds')
        STATS['lp'] += 1
        if res2.status == 0 and res2.fun < -1e-9: cands.append(res2.x)
    for yf in cands:
        S = [i for i in range(n) if yf[i] > 1e-12]
        M = [[F(rows[i][j]) for i in S] for j in range(NV)] + [[F(1)] * len(S)]
        rhs = [F(0)] * NV + [F(1)]
        sol = solve_exact(M, rhs, [yf[i] for i in S])
        if sol is None or any(v < 0 for v in sol): continue
        y = [F(0)] * n
        for k, i in enumerate(S): y[i] = sol[k]
        return y
    return None

def solve_exact(M, rhs, guess):
    m = len(M); n = len(M[0]) if m else 0
    A = [list(M[i]) + [rhs[i]] for i in range(m)]; piv = []; r = 0
    for col in range(n):
        p = next((i for i in range(r, m) if A[i][col] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; pv = A[r][col]; A[r] = [t / pv for t in A[r]]
        for i in range(m):
            if i != r and A[i][col] != 0:
                f = A[i][col]; A[i] = [a - f * bb for a, bb in zip(A[i], A[r])]
        piv.append(col); r += 1
        if r == m: break
    for i in range(r, m):
        if A[i][n] != 0: return None
    free = [c for c in range(n) if c not in piv]
    z = [F(0)] * n
    for c in free: z[c] = F(guess[c]).limit_denominator(10 ** 6)
    for i, c in enumerate(piv): z[c] = A[i][n] - sum(A[i][f] * z[f] for f in free)
    return z

def verify(cons, y):
    if any(v < 0 for v in y): return False
    tot = [F(0)] * (NV + 1); st = False
    for r, v in zip(cons, y):
        if v == 0: continue
        for j in range(NV + 1): tot[j] += v * r[j]
        if r[NV + 1]: st = True
    if any(tot[j] != 0 for j in range(NV)): return False
    return tot[NV] < 0 or (tot[NV] == 0 and st)

class Ctx:
    def __init__(s, prefix, base):
        s.prefix = prefix; s.k = 0; s.cons = list(base); s.path = []; s.new_branches = []
    def choose(s, alts):
        if s.k < len(s.prefix):
            i = s.prefix[s.k]; s.k += 1; s.cons += alts[i]; s.path.append(i); return i
        feas = []
        for i, a in enumerate(alts):
            r, y = lp_empty(s.cons + a)
            if r is True:
                emit('prune', s.cons + a, y, s.path + [i])
            else:
                feas.append(i)
        if not feas:
            raise Dead()
        if feas[1:]: s.new_branches.append((list(s.path), feas[1:]))
        i = feas[0]; s.k += 1; s.cons += alts[i]; s.path.append(i); return i
    def test(s, c_true, c_false):
        return s.choose([[c_true], [c_false]]) == 0
    def ge(s, f): return s.test(GE(f), GT(-f))
    def gt(s, f): return s.test(GT(f), GE(-f))
    def le(s, f, g): return s.ge(g - f)
    def lt(s, f, g): return s.gt(g - f)
    def mx(s, f, g): return f if s.ge(f - g) else g
    def mn(s, f, g): return f if s.le(f, g) else g

class Dead(Exception): pass

OUT = None
def emit(kind, cons, y, path):
    rec = dict(k=kind, p=path, c=[list(r) for r, v in zip(cons, y) if v != 0], y=[str(v) for v in y if v != 0])
    OUT.write(json.dumps(rec) + '\n')

N9 = lambda k: F(k, 9)
V, m, s, aA, aB, x, m2, s2 = (L.var(n) for n in ('V', 'm', 's', 'aA', 'aB', 'x', 'm2', 's2'))
bA, bB = V - aA, V - aB
V2 = V + x; Y2 = 1 - m2; h2 = 1 - V2 + s2

def look(c, a, b, strict):
    tK = c.mx(b + x, a + Y2)
    tS = c.mx(c.mx(a + x, b), c.mn(a + x, b) + Y2)
    return c.lt(tK, tS) if strict else c.le(tK, tS)

def place(c, a, b, k):
    if k: return (a, b + x)
    if c.le(a + x, b): return (a + x, b)
    return (b, a + x)

def ruleA(c, a, b):
    if c.ge(b - N9(7)): return look(c, a, b, False)
    if c.le(b + x, N9(11)): return True
    return look(c, a, b, True)

def inW(c, f): return c.ge(f - N9(7)) and c.le(f, N9(11))

def ruleB(c, a, b, a_A, b_A, kA):
    if c.ge(b - N9(7)): return look(c, a, b, False)
    if c.le(b + x, N9(4)): return True
    wb = inW(c, b + x); wa = inW(c, a + x)
    if wb and wa: return look(c, a, b, False)
    if wb: return True
    if wa: return False
    if c.lt(b + x, N9(7)):
        if c.le(c.mn(a + x, b), N9(4)): return False
        nA = place(c, a_A, b_A, kA)
        hp = c.gt(h2)
        def J(k):
            nB = place(c, a, b, k)
            t = c.mx(nA[1] + nB[1], c.mx(nA[1], nA[0] + Y2) + c.mx(nB[1], nB[0] + Y2))
            if hp:
                cE = lambda p: c.mn(c.mx(p[1], p[0] + 2 * h2), p[1] + h2)
                t = c.mx(t, cE(nA) + cE(nB))
            return t
        jk = J(True); js = J(False)
        return c.le(jk, js)
    return False

def mode_constraints(md, Vv, mv, sv, a1, a2):
    b1, b2 = Vv - a1, Vv - a2; Y = 1 - mv
    D = []
    D += [[[GE(Vv)]], [[LE(Vv, 2)]], [[GE(mv)]], [[GE(mv - Vv + 1)]], [[LE(mv, sv)]], [[LE(2 * sv, Vv)]],
          [[GE(a1)]], [[LE(2 * a1, Vv)]], [[GE(a2)]], [[LE(2 * a2, Vv)]]]
    for a, bb in ((a1, b1), (a2, b2)):
        D.append([[GT(bb - 1)], [LE(mv, a), LE(a, sv)]])
    D.append([[LE(b1 + b2, N9(22))]])
    if md == 'hedge':
        D += [[[LE(a1, 0)]], [[LT(b1, N9(7))]], [[LT(b2, N9(7))]]]
        D.append([[GT(Vv - N9(4))], [LE(a2, 0)]])
        D.append([[LE(b2 - a2, N9(4))], [LE(sv, a2)]])
        D.append([[LE(b2, N9(4))], [LT(b2 - a2, Vv - N9(4))], [LE(sv, a2)]])
    elif md == 'late':
        D += [[[GT(a1)]], [[LT(b1, N9(7))]], [[LT(b2, N9(7))]]]
        D += [[[GT(Vv - N9(11))]], [[GT(mv - N9(4))]]]
        D.append([[GE(mv - a1)], [GE(mv - N9(11) + b1), GE(mv - 2 * a1 + N9(7))]])
    elif md == 'Ab':
        D += [[[GE(b1 - N9(7))]], [[LT(b2, N9(7))]]]
        D += [[[LE(b1, N9(11))]], [[LE(a1 + a2 + 2 * Y, N9(22))]], [[LE(b1 + a2 + Y, N9(22))]]]
        D.append([[GT(Vv - 1)], [LE(a1, 0)]])
        D.append([[GT(Vv - 1)], [LE(sv, a2 + N9(2))], [GE(6 * a2 - 1)], [LE(a2, 2 * Vv - N9(14))]])
        D.append([[LE(a1, 0)], [LT(Y, b1)]])
        D.append([[LE(Vv, 1)], [LE(sv, a2 + N9(2))], [GE(b1 + b2 - N9(14))], [LE(b2 - a2, N9(4))]])
    elif md == 'aB':
        D += [[[LT(b1, N9(7))]], [[GE(b2 - N9(7))]]]
        D += [[[GT(Vv - N9(11))]], [[LE(b2, N9(11))]], [[LE(a1 + Y + b2, N9(22))]], [[LE(a1 + Y + 2 - b2, N9(22))]]]
    return D

def target_checks(c, md, Vv, mv, sv, a1, a2):
    import itertools
    D = mode_constraints(md, Vv, mv, sv, a1, a2)
    nd = 0
    for di, disj in enumerate(D):
        negs = [[neg(r) for r in alt] for alt in disj]
        for combo in itertools.product(*negs):
            cons = c.cons + list(combo)
            r, y = lp_empty(cons)
            if r is not True:
                raise Fail((md, di, combo))
            emit('target', cons, y, c.path + ['T', md, di] + [norm_key(q) for q in combo])
            nd += 1
    return nd

def entry_checks(c, b1, b2):
    for f in (b1 + b2, b1 + 2 - b2, 2 - b1 + b2, 4 - b1 - b2):
        cons = c.cons + [GT(f - N9(22))]
        r, y = lp_empty(cons)
        if r is not True: raise Fail(('AB', f.c))
        emit('target', cons, y, c.path + ['E'])

def norm_key(r): return ','.join(map(str, r))
def neg(r):
    return tuple(-v for v in r[:NV + 1]) + (0 if r[NV + 1] else 1,)

class Fail(Exception): pass

def program(c, src):
    for disj in mode_constraints(src, V, m, s, aA, aB):
        if len(disj) == 1: c.cons += disj[0]
        else: c.choose(disj)
    c.cons += [GT(x), LE(x, 1 - m), LE(m2, s2), LE(2 * s2, V2)]
    lo = V2 - 1
    ivs = [(m, s), (V - s, V - m), (m + x, s + x), (V - s + x, V - m + x)]
    for w in (m2, s2):
        c.cons += [GE(w), GE(w - lo), LE(w, 1)]
        c.choose([[GE(w - p), LE(w, q)] for p, q in ivs])
    if src == 'Ab':
        for a, bb in ((aA, bA), (aB, bB)):
            if c.le(bb, 1):
                e = a + x
                c.choose([[GT(lo - e)], [GT(e - 1)], [LE(m2, e), GE(s2 - e)], [LE(m2, e), GE(s2 - (V2 - e))]])
    kA = ruleA(c, aA, bA)
    kB = ruleB(c, aB, bB, aA, bA, kA)
    nA = place(c, aA, bA, kA); nB = place(c, aB, bB, kB)
    for a, bb in (nA, nB):
        c.choose([[GT(bb - 1)], [LE(m2, a), LE(a, s2)]])
    cA = c.ge(nA[1] - N9(7)); cB = c.ge(nB[1] - N9(7))
    if cA and cB:
        entry_checks(c, nA[1], nB[1]); return 'AB'
    if cA: md = 'Ab'
    elif cB: md = 'aB'
    else: md = 'hedge' if c.le(nA[0], 0) else 'late'
    target_checks(c, md, V2, m2, s2, nA[0], nB[0]); return md

def main():
    global OUT
    src = sys.argv[1]; OUT = open(sys.argv[2], 'w')
    start = json.loads(sys.argv[3]) if len(sys.argv) > 3 else []
    stack = [start]; leaves = 0; dead = 0; fails = 0; t0 = time.time(); seen = 0
    while stack:
        prefix = stack.pop()
        c = Ctx(prefix, [])
        try:
            md = program(c, src); leaves += 1
        except Dead:
            dead += 1
        except Fail as e:
            fails += 1
            print('FAIL', src, 'path', c.path, e.args[0]); sys.stdout.flush()
        for pth, rest in c.new_branches:
            for i in reversed(rest): stack.append(pth + [i])
        seen += 1
    print('lift', src, 'prefix', start, 'leaves', leaves, 'dead', dead, 'fails', fails, 'lp', STATS['lp'], 'certs', STATS['cert'],
          'certfail', STATS['certfail'], 'time %.1f' % (time.time() - t0))
    OUT.close()

if __name__ == '__main__':
    main()
