# Lazy case tree for the closure of the invariant R of the two-bin coin c14b.
# python3 ltprod.py hedge|late|aB|Ab OUT.jsonl - 1000000 64
import sys, json, time, itertools
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
def neg(r): return tuple(-v for v in r[:NV + 1]) + (0 if r[NV + 1] else 1,)
def rkey(r): return ','.join(map(str, r))

STATS = dict(lp=0, cert=0, certfail=0)
CAP = 64

def lp_point(cons):
    A = []; b = []
    for r in cons:
        A.append([-float(v) for v in r[:NV]] + [1.0 if r[NV + 1] else 0.0]); b.append(float(r[NV]))
    STATS['lp'] += 1
    res = linprog([0.0] * NV + [-1.0], A_ub=np.array(A), b_ub=np.array(b),
                  bounds=[(None, None)] * NV + [(None, 1.0)], method='highs-ds')
    if res.status == 2:
        ok, y = certify(cons, None)
        return ('empty', y) if ok else ('unk', None)
    if res.status != 0: return ('unk', None)
    t = -res.fun
    if t > 1e-9: return ('point', list(res.x[:NV]))
    duals = -res.ineqlin.marginals
    ok, y = certify(cons, duals)
    return ('empty', y) if ok else ('unk', None)

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
                return True, yy
    STATS['certfail'] += 1
    return False, None

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

def rowval(r, z):
    return sum(r[i] * z[i] for i in range(NV)) + r[NV], r[NV + 1]
def holds(r, z, tol=1e-9):
    v, st = rowval(r, z)
    return v > tol if st else v >= -tol

OUT = None
def emit(rec): OUT.write(json.dumps(rec) + '\n')
def cert_rec(node, key, cons, y):
    return dict(n=node, k=key, c=[list(r) for r, v in zip(cons, y) if v != 0], y=[str(v) for v in y if v != 0])

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

def mode_constraints(md, Vv, mv, sv, a1, a2, drop=()):
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
    return [d for i, d in enumerate(D) if '%s:%d' % (md, i) not in DROP]
DROP = set()

def hypotheses(src):
    base = []; H = []
    for disj in mode_constraints(src, V, m, s, aA, aB):
        if len(disj) == 1: base += disj[0]
        else: H.append(disj)
    base += [GT(x), LE(x, 1 - m), LE(m2, s2), LE(2 * s2, V2)]
    lo = V2 - 1
    ivs = [(m, s), (V - s, V - m), (m + x, s + x), (V - s + x, V - m + x)]
    for w in (m2, s2):
        base += [GE(w), GE(w - lo), LE(w, 1)]
        H.append([[GE(w - p), LE(w, q)] for p, q in ivs])
    if src == 'Ab':
        for a, bb in ((aA, bA), (aB, bB)):
            e = a + x
            H.append([[GT(bb - 1)], [LE(bb, 1), GT(lo - e)], [LE(bb, 1), GT(e - 1)],
                      [LE(bb, 1), LE(m2, e), GE(s2 - e)], [LE(bb, 1), LE(m2, e), GE(s2 - (V2 - e))]])
    return base, H

class Fork(Exception): pass

class Eval:
    def __init__(self, node, prefix):
        self.node = node; self.prefix = prefix; self.k = 0; self.ch = []; self.newb = []; self.facts = {}; self.trail = []
    def q(self, typ, f):
        key = (typ, norm(f, False))
        if key in self.facts: return self.facts[key]
        d = self.node.decide(typ, f)
        if d is None:
            if self.k < len(self.prefix): v = self.prefix[self.k]
            else:
                v = 0; self.newb.append(self.ch + [1])
            self.k += 1; self.ch.append(v)
            d = (v == 0)
            self.trail.append((typ, f, d))
        self.facts[key] = d
        return d
    def ge(s, f): return s.q('ge', f)
    def gt(s, f): return s.q('gt', f)
    def le(s, f, g): return s.ge(g - f)
    def lt(s, f, g): return s.gt(g - f)
    def mx(s, f, g): return f if s.ge(f - g) else g
    def mn(s, f, g): return f if s.le(f, g) else g

def fkey(f): return ','.join(str(v) for v in f.c)

class Node:
    def __init__(self, path, cons, src):
        self.path = path; self.cons = cons; self.src = src; self.memo = {}; self.recs = []; self.fails = []
    def decide(self, typ, f):
        key = (typ, norm(f, False))
        if key in self.memo: return self.memo[key]
        if typ == 'ge': tneg, fneg = GT(-f), GE(f)
        else: tneg, fneg = GE(-f), GT(f)
        d = None
        for val, row in ((True, tneg), (False, fneg)):
            r, y = lp_point(self.cons + [row])
            if r == 'empty':
                self.recs.append(cert_rec(self.path, 'D|' + rkey(row), self.cons + [row], y)); d = val; break
        self.memo[key] = d
        return d
    def outcomes(self, cap):
        outs = {}
        stack = [[]]; runs = 0; self.over = False; self.firsttrail = None
        while stack:
            runs += 1
            if runs > cap: self.over = True; break
            pre = stack.pop()
            ev = Eval(self, pre)
            kA = ruleA(ev, aA, bA)
            kB = ruleB(ev, aB, bB, aA, bA, kA)
            nA = place(ev, aA, bA, kA); nB = place(ev, aB, bB, kB)
            cA = ev.ge(nA[1] - N9(7)); cB = ev.ge(nB[1] - N9(7))
            if cA and cB: md = 'AB'
            elif cA: md = 'Ab'
            elif cB: md = 'aB'
            else: md = 'hedge' if ev.le(nA[0], 0) else 'late'
            ok = md + ';' + ';'.join(fkey(f) for f in (nA[0], nA[1], nB[0], nB[1]))
            outs.setdefault(ok, (md, nA, nB, []))[3].append(list(ev.trail))
            if self.firsttrail is None and ev.trail: self.firsttrail = ev.trail[0]
            for b in reversed(ev.newb): stack.append(b)
        return outs
    def prove(self, stop_first=False):
        outs = self.outcomes(CAP)
        fails = []
        for ok, (md, nA, nB, trails) in sorted(outs.items()):
            alts = [[[GT(b - 1)], [LE(m2, a), LE(a, s2)]] for a, b in (nA, nB)]
            for i, j in itertools.product(range(2), range(2)):
                sub = self.cons + alts[0][i] + alts[1][j]
                base = 'O|' + ok + '|%d%d' % (i, j)
                r, y = lp_point(sub)
                if r == 'empty':
                    self.recs.append(cert_rec(self.path, base + '|X', sub, y)); continue
                if md == 'AB':
                    obl = [(base + '|E|%d' % k, [GT(f - N9(22))]) for k, f in enumerate(
                        (nA[1] + nB[1], nA[1] + 2 - nB[1], 2 - nA[1] + nB[1], 4 - nA[1] - nB[1]))]
                else:
                    obl = []
                    for di, disj in enumerate(mode_constraints(md, V2, m2, s2, nA[0], nB[0])):
                        for combo in itertools.product(*[[neg(rr) for rr in alt] for alt in disj]):
                            obl.append((base + '|T|%d|' % di + '|'.join(rkey(q) for q in combo), list(combo)))
                for key, extra in obl:
                    r, y = lp_point(sub + extra)
                    if r == 'empty': self.recs.append(cert_rec(self.path, key, sub + extra, y)); continue
                    fails.append((y if r == 'point' else None, trails, key))
                    break
                if fails and stop_first: return fails
        return fails

def choose_split(node, fails, hyp_left, H):
    score = {}
    for z, trails, key in fails:
        if z is None: continue
        cands = set()
        for tr in trails:
            for typ, f, d in tr:
                v = sum(float(f.c[i]) * z[i] for i in range(NV)) + float(f.c[NV])
                truth = (v >= -1e-12) if typ == 'ge' else (v > 1e-12)
                if truth != d:
                    cands.add(('c', GE(f) if typ == 'ge' else GT(f))); break
        for hi in hyp_left:
            if not any(all(holds(r, z) for r in alt) for alt in H[hi]):
                cands.add(('h', hi))
        for cnd in cands: score[cnd] = score.get(cnd, 0) + 1
    if not score:
        if hyp_left: return ('h', min(hyp_left))
        return None
    best = sorted(score.items(), key=lambda t: (-t[1], 0 if t[0][0] == 'c' else 1, str(t[0])))[0][0]
    return best

def solve(src, start, maxnodes):
    base, H = hypotheses(src)
    cons = list(base); hyp_left = set(range(len(H))); path0 = []
    for hi, ai in start:
        cons += H[hi][ai]; hyp_left.discard(hi); path0.append('h%d=%d' % (hi, ai))
    stack = [(path0, cons, hyp_left)]
    cnt = dict(nodes=0, leaves=0, empty=0, hsplit=0, csplit=0, failed=0, outcomes=0)
    while stack:
        path, cons, hl = stack.pop()
        cnt['nodes'] += 1
        if cnt['nodes'] > maxnodes:
            print('NODE LIMIT'); cnt['failed'] += 1; break
        node = Node(path, cons, src)
        r, y = lp_point(cons)
        if r == 'empty':
            emit(dict(n=path, t='empty')); emit(cert_rec(path, 'EMPTY', cons, y)); cnt['empty'] += 1; continue
        fails = node.prove()
        if node.over and not fails:
            typ, f, d = node.firsttrail
            fails = []; sp = ('c', GE(f) if typ == 'ge' else GT(f))
        else: sp = None
        if not fails and sp is None:
            emit(dict(n=path, t='leaf'))
            for rec in node.recs: emit(rec)
            cnt['leaves'] += 1; continue
        if sp is None: sp = choose_split(node, fails, hl, H)
        if sp is None:
            print('FAIL at', path, [f[2][:120] for f in fails[:3]]); cnt['failed'] += 1
            emit(dict(n=path, t='fail')); continue
        if sp[0] == 'h':
            hi = sp[1]; cnt['hsplit'] += 1
            emit(dict(n=path, t='hsplit', h=hi))
            for ai in reversed(range(len(H[hi]))):
                stack.append((path + ['h%d=%d' % (hi, ai)], cons + H[hi][ai], hl - {hi}))
        else:
            row = sp[1]; cnt['csplit'] += 1
            emit(dict(n=path, t='csplit', f=list(row)))
            stack.append((path + ['c1'], cons + [neg(row)], hl))
            stack.append((path + ['c0'], cons + [row], hl))
        OUT.flush()
    return cnt

def main():
    global OUT
    src = sys.argv[1]; OUT = open(sys.argv[2], 'w')
    start = json.loads(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else []
    maxnodes = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 7
    global CAP
    CAP = int(sys.argv[5]) if len(sys.argv) > 5 else 64
    if len(sys.argv) > 6 and sys.argv[6] != '-': DROP.update(sys.argv[6].split(','))
    t0 = time.time()
    cnt = solve(src, start, maxnodes)
    print('ltprod', src, 'start', start, cnt, 'lp', STATS['lp'], 'certs', STATS['cert'], 'certfail', STATS['certfail'],
          'time %.1f' % (time.time() - t0))
    OUT.close()

if __name__ == '__main__':
    main()
