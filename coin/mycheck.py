# A second checker of the same certificates, written from the definitions.
# python3 mycheck.py their|lp hedge|late|aB|Ab FILE.jsonl|- [PREFIX]
import sys, json, itertools, time
from fractions import Fraction as Fr
from math import gcd

NV = 8
NAMES = ('V', 'm', 's', 'aA', 'aB', 'x', 'm2', 's2')

def form(**kw):
    c = [Fr(0)] * 9
    for k, v in kw.items():
        c[8 if k == 'one' else NAMES.index(k)] += Fr(v)
    return tuple(c)
def plus(*fs): return tuple(sum(f[i] for f in fs) for i in range(9))
def minus(f, g): return tuple(f[i] - g[i] for i in range(9))
def times(k, f): k = Fr(k); return tuple(k * v for v in f)
def const(k): return form(one=k)

def row(f, strict):
    den = 1
    for v in f: den = den * v.denominator // gcd(den, v.denominator)
    iv = [int(v * den) for v in f]
    g = 0
    for v in iv: g = gcd(g, abs(v))
    if g == 0: g = 1
    return tuple(v // g for v in iv) + (strict,)
def negrow(r):
    return tuple(-v for v in r[:9]) + (1 - r[9],)

def holds(r, pt):
    v = sum(r[i] * pt[i] for i in range(8)) + r[8]
    return v > 0 if r[9] else v >= 0

V, m, s, aA, aB, x, m2, s2 = (form(**{n: 1}) for n in NAMES)
bA = minus(V, aA); bB = minus(V, aB)
V2 = plus(V, x)
Y2 = minus(const(1), m2)
H2 = plus(const(1), times(-1, V2), s2)
def ninth(k): return const(Fr(k, 9))

def cert_ok(case, rows, mults):
    tot = [Fr(0)] * 9; strict = False
    for r, y in zip(rows, mults):
        y = Fr(y)
        if y < 0: return False
        if y == 0: continue
        r = tuple(int(v) for v in r)
        f = tuple(Fr(v) for v in r[:9])
        p = row(f, r[9])
        if p not in case:
            if r[9] == 0 and (p[:9] + (1,)) in case: pass
            else: return False
        for i in range(9): tot[i] += y * r[i]
        if r[9]: strict = True
    if any(tot[i] != 0 for i in range(8)): return False
    return tot[8] < 0 or (tot[8] == 0 and strict)

LPSTAT = dict(lp=0, ok=0, fail=0)
def lp_cert(rows):
    import numpy as np
    from scipy.optimize import linprog
    n = len(rows)
    if n == 0: return None
    A = np.array([[float(r[j]) for r in rows] for j in range(NV)] + [[1.0] * n])
    b = np.array([0.0] * NV + [1.0])
    c0 = np.array([float(r[8]) for r in rows])
    LPSTAT['lp'] += 1
    res = linprog(c0, A_eq=A, b_eq=b, bounds=[(0, None)] * n, method='highs-ds')
    cands = []
    if res.status == 0:
        if res.fun < -1e-10: cands.append(res.x)
        else:
            st = np.array([-1.0 if r[9] else 0.0 for r in rows])
            LPSTAT['lp'] += 1
            res2 = linprog(st, A_ub=np.array([c0]), b_ub=np.array([0.0]), A_eq=A, b_eq=b,
                           bounds=[(0, None)] * n, method='highs-ds')
            if res2.status == 0 and res2.fun < -1e-10: cands.append(res2.x)
    for yf in cands:
        S = [i for i in range(n) if yf[i] > 1e-11]
        y = exact_on_support([rows[i] for i in S], [yf[i] for i in S])
        if y is None: continue
        crow = [rows[i] for i in S]
        if cert_ok(set(rows), crow, y):
            LPSTAT['ok'] += 1
            return (crow, y)
    LPSTAT['fail'] += 1
    return None

def exact_on_support(rows, guess):
    k = len(rows)
    M = [[Fr(r[j]) for r in rows] + [Fr(0)] for j in range(NV)] + [[Fr(1)] * k + [Fr(1)]]
    piv = []; rr = 0
    for col in range(k):
        p = next((i for i in range(rr, len(M)) if M[i][col] != 0), None)
        if p is None: continue
        M[rr], M[p] = M[p], M[rr]
        pv = M[rr][col]; M[rr] = [v / pv for v in M[rr]]
        for i in range(len(M)):
            if i != rr and M[i][col] != 0:
                f = M[i][col]; M[i] = [a - f * bb for a, bb in zip(M[i], M[rr])]
        piv.append(col); rr += 1
    for i in range(rr, len(M)):
        if M[i][k] != 0: return None
    free = [c for c in range(k) if c not in piv]
    y = [Fr(0)] * k
    for c in free: y[c] = Fr(guess[c]).limit_denominator(10 ** 7)
    for i, c in enumerate(piv): y[c] = M[i][k] - sum(M[i][f] * y[f] for f in free)
    if any(v < 0 for v in y): return None
    return y

class Empty(Exception): pass
class Missing(Exception): pass

class Walk:
    def __init__(self, W, prefix):
        self.W = W; self.prefix = prefix; self.k = 0; self.case = set(); self.path = []; self.todo = []
    def add(self, rows):
        for r in rows: self.case.add(r)
    def choose(self, alts):
        W = self.W
        if W.mode == 'point':
            ok = [i for i, a in enumerate(alts) if all(holds(r, W.pt) for r in a)]
            if not ok: raise RuntimeError('no alternative holds at the point: ' + repr(alts))
            W.trace.append((list(self.path), ok, [a for a in alts]))
            i = ok[0]; self.path.append(i); self.add(alts[i]); return i
        if self.k < len(self.prefix):
            i = self.prefix[self.k]; self.k += 1; self.path.append(i); self.add(alts[i]); return i
        live = []
        for i, a in enumerate(alts):
            if not W.empty(self.path, i, self.case | set(a)): live.append(i)
        if not live: raise Empty()
        if len(live) > 1: self.todo.append((list(self.path), live[1:]))
        i = live[0]; self.k += 1; self.path.append(i); self.add(alts[i]); return i
    def ge0(self, f): return self.choose([[row(f, 0)], [row(times(-1, f), 1)]]) == 0
    def gt0(self, f): return self.choose([[row(f, 1)], [row(times(-1, f), 0)]]) == 0
    def vmax(self, f, g): return f if self.ge0(minus(f, g)) else g
    def vmin(self, f, g): return f if self.ge0(minus(g, f)) else g

def program(w, src):
    for disj in invariant(src, V, m, s, aA, aB):
        if len(disj) == 1: w.add(disj[0])
        else: w.choose(disj)
    lo = minus(V2, const(1))
    w.add([row(x, 1), row(minus(minus(const(1), m), x), 0), row(minus(s2, m2), 0), row(minus(V2, times(2, s2)), 0)])
    pieces = [(m, s), (minus(V, s), minus(V, m)), (plus(m, x), plus(s, x)), (plus(minus(V, s), x), plus(minus(V, m), x))]
    for wv in (m2, s2):
        w.add([row(wv, 0), row(minus(wv, lo), 0), row(minus(const(1), wv), 0)])
        w.choose([[row(minus(wv, p), 0), row(minus(q, wv), 0)] for p, q in pieces])
    if src == 'Ab':
        for a, b in ((aA, bA), (aB, bB)):
            if w.ge0(minus(const(1), b)):
                e = plus(a, x)
                w.choose([[row(minus(lo, e), 1)], [row(minus(e, const(1)), 1)],
                          [row(minus(e, m2), 0), row(minus(s2, e), 0)],
                          [row(minus(e, m2), 0), row(minus(s2, minus(V2, e)), 0)]])
    kA = moveA(w, aA, bA)
    kB = moveB(w, aB, bB, aA, bA, kA)
    nA = put(w, aA, bA, kA); nB = put(w, aB, bB, kB)
    for a, b in (nA, nB):
        w.choose([[row(minus(b, const(1)), 1)], [row(minus(a, m2), 0), row(minus(s2, a), 0)]])
    cA = w.ge0(minus(nA[1], ninth(7))); cB = w.ge0(minus(nB[1], ninth(7)))
    if cA and cB:
        md = 'AB'
        targets = [[[row(minus(ninth(22), f), 0)]] for f in
                   (plus(nA[1], nB[1]), plus(nA[1], const(2), times(-1, nB[1])),
                    plus(const(2), times(-1, nA[1]), nB[1]), plus(const(4), times(-1, nA[1]), times(-1, nB[1])))]
    else:
        if cA: md = 'Ab'
        elif cB: md = 'aB'
        else: md = 'hedge' if w.ge0(times(-1, nA[0])) else 'late'
        targets = invariant(md, V2, m2, s2, nA[0], nB[0])
    w.nA, w.nB = nA, nB
    w.W.leaf(w, md, targets)
    return md

def look(w, a, b, strict):
    tK = w.vmax(plus(b, x), plus(a, Y2))
    t1 = w.vmax(plus(a, x), b)
    t2 = plus(w.vmin(plus(a, x), b), Y2)
    tS = w.vmax(t1, t2)
    return w.gt0(minus(tS, tK)) if strict else w.ge0(minus(tS, tK))

def put(w, a, b, k):
    if k: return (a, plus(b, x))
    if w.ge0(minus(b, plus(a, x))): return (plus(a, x), b)
    return (b, plus(a, x))

def moveA(w, a, b):
    if w.ge0(minus(b, ninth(7))): return look(w, a, b, False)
    if w.ge0(minus(ninth(11), plus(b, x))): return True
    return look(w, a, b, True)

def inW(w, f): return w.ge0(minus(f, ninth(7))) and w.ge0(minus(ninth(11), f))

def moveB(w, a, b, a_A, b_A, kA):
    if w.ge0(minus(b, ninth(7))): return look(w, a, b, False)
    if w.ge0(minus(ninth(4), plus(b, x))): return True
    wb = inW(w, plus(b, x)); wa = inW(w, plus(a, x))
    if wb and wa: return look(w, a, b, False)
    if wb: return True
    if wa: return False
    if w.gt0(minus(ninth(7), plus(b, x))):
        if w.ge0(minus(ninth(4), w.vmin(plus(a, x), b))): return False
        nA = put(w, a_A, b_A, kA)
        hpos = w.gt0(H2)
        def J(k):
            nB = put(w, a, b, k)
            t = w.vmax(plus(nA[1], nB[1]), plus(w.vmax(nA[1], plus(nA[0], Y2)), w.vmax(nB[1], plus(nB[0], Y2))))
            if hpos:
                def cE(p): return w.vmin(w.vmax(p[1], plus(p[0], times(2, H2))), plus(p[1], H2))
                t = w.vmax(t, plus(cE(nA), cE(nB)))
            return t
        jK = J(True); jS = J(False)
        return w.ge0(minus(jS, jK))
    return False

def invariant(md, V, m, s, a1, a2):
    b1, b2 = minus(V, a1), minus(V, a2); Y = minus(const(1), m)
    ge = lambda f: row(f, 0); gt = lambda f: row(f, 1)
    le = lambda f, g: ge(minus(g, f)); lt = lambda f, g: gt(minus(g, f))
    D = []
    one = lambda r: D.append([[r]])
    one(ge(V)); one(le(V, const(2))); one(ge(m)); one(le(minus(V, const(1)), m)); one(le(m, s)); one(le(times(2, s), V))
    for a, b in ((a1, b1), (a2, b2)):
        one(ge(a)); one(le(times(2, a), V))
    for a, b in ((a1, b1), (a2, b2)):
        D.append([[gt(minus(b, const(1)))], [le(m, a), le(a, s)]])
    one(le(plus(b1, b2), ninth(22)))
    if md == 'hedge':
        one(le(a1, const(0))); one(lt(b1, ninth(7))); one(lt(b2, ninth(7)))
        D.append([[gt(minus(V, ninth(4)))], [le(a2, const(0))]])
        D.append([[le(minus(b2, a2), ninth(4))], [le(s, a2)]])
        D.append([[le(b2, ninth(4))], [lt(minus(b2, a2), minus(V, ninth(4)))], [le(s, a2)]])
    elif md == 'late':
        one(gt(a1)); one(lt(b1, ninth(7))); one(lt(b2, ninth(7)))
        one(gt(minus(V, ninth(11))))
        one(gt(minus(m, ninth(4))))
        D.append([[ge(minus(m, a1))], [ge(minus(m, minus(ninth(11), b1))), ge(minus(m, minus(times(2, a1), ninth(7))))]])
    elif md == 'Ab':
        one(ge(minus(b1, ninth(7)))); one(lt(b2, ninth(7)))
        one(le(b1, ninth(11)))
        one(le(plus(a1, a2, times(2, Y)), ninth(22)))
        one(le(plus(b1, a2, Y), ninth(22)))
        D.append([[gt(minus(V, const(1)))], [le(a1, const(0))]])
        D.append([[gt(minus(V, const(1)))], [le(s, plus(a2, ninth(2)))], [ge(minus(a2, const(Fr(1, 6))))],
                  [le(a2, minus(times(2, V), ninth(14)))]])
        D.append([[le(a1, const(0))], [lt(Y, b1)]])
        D.append([[le(V, const(1))], [le(s, plus(a2, ninth(2)))], [ge(minus(plus(b1, b2), ninth(14)))],
                  [le(minus(b2, a2), ninth(4))]])
    elif md == 'aB':
        one(lt(b1, ninth(7))); one(ge(minus(b2, ninth(7))))
        one(gt(minus(V, ninth(11))))
        one(le(b2, ninth(11)))
        one(le(plus(a1, Y, b2), ninth(22)))
        one(le(plus(a1, Y, const(2), times(-1, b2)), ninth(22)))
    else:
        raise ValueError(md)
    return D

class Checker:
    def __init__(self, mode, certfile):
        self.mode = mode
        self.stats = dict(runs=0, leaves=0, empty=0, pruned_their=0, pruned_lp=0, targets_their=0, targets_lp=0,
                          missing=0, leafmodes={})
        self.byKey = {}; self.byLeaf = {}
        if certfile and certfile != '-':
            with open(certfile) as f:
                for line in f:
                    r = json.loads(line); p = r['p']
                    c = ([tuple(q) for q in r['c']], r['y'])
                    self.byKey.setdefault(json.dumps(p), []).append(c)
                    for j, t in enumerate(p):
                        if t in ('T', 'E'):
                            self.byLeaf.setdefault(json.dumps(p[:j]), []).append(c); break
    def empty(self, path, i, case):
        if self.mode in ('their', 'both'):
            for c in self.byKey.get(json.dumps(path + [i]), ()):
                if cert_ok(case, *c): self.stats['pruned_their'] += 1; return True
        if self.mode in ('lp', 'both'):
            if lp_cert(sorted(case)) is not None: self.stats['pruned_lp'] += 1; return True
        return False
    def leaf(self, w, md, targets):
        if self.mode == 'point':
            self.leafinfo = (md, targets); return
        pool = self.byLeaf.get(json.dumps(w.path), []) if self.mode in ('their', 'both') else []
        for disj in targets:
            for combo in itertools.product(*[[negrow(r) for r in alt] for alt in disj]):
                case = w.case | set(combo)
                done = False
                for c in pool:
                    if cert_ok(case, *c): self.stats['targets_their'] += 1; done = True; break
                if not done and self.mode in ('lp', 'both'):
                    if lp_cert(sorted(case)) is not None: self.stats['targets_lp'] += 1; done = True
                if not done: raise Missing((md, combo))
        self.stats['leafmodes'][md] = self.stats['leafmodes'].get(md, 0) + 1

def run(mode, src, certfile, start, logevery=0):
    C = Checker(mode, certfile)
    stack = [start]; t0 = time.time(); fails = []
    while stack:
        pre = stack.pop()
        w = Walk(C, pre); C.stats['runs'] += 1
        try:
            program(w, src); C.stats['leaves'] += 1
        except Empty:
            C.stats['empty'] += 1
        except Missing as e:
            C.stats['missing'] += 1
            if len(fails) < 5: fails.append((w.path, e.args[0]))
        for p, rest in w.todo:
            for i in reversed(rest): stack.append(p + [i])
        if logevery and C.stats['runs'] % logevery == 0:
            print('progress', C.stats, 'stack', len(stack), 'time %.0f' % (time.time() - t0)); sys.stdout.flush()
    for f in fails: print('MISSING at', f[0], f[1])
    ok = C.stats['missing'] == 0
    print('mycheck', mode, src, 'prefix', json.dumps(start), 'certs', certfile, C.stats, 'lp', LPSTAT,
          'time %.1f' % (time.time() - t0), 'RESULT', 'PASS' if ok else 'FAIL')

if __name__ == '__main__':
    mode, src, cf = sys.argv[1], sys.argv[2], sys.argv[3]
    start = json.loads(sys.argv[4]) if len(sys.argv) > 4 else []
    le = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    run(mode, src, cf, start, le)
