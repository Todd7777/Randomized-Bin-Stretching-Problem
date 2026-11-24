# Checks the certificates of lift.py in exact arithmetic.
# python3 liftcheck.py root | hedge|late|aB|Ab FILE.jsonl [PREFIX]
import sys, json, itertools
from fractions import Fraction as Q
from math import gcd

NVAR = 8
VARS = ['V', 'm', 's', 'aA', 'aB', 'x', 'm2', 's2']

def lin(**kw):
    out = [Q(0)] * 9
    for k, v in kw.items():
        out[8 if k == 'c' else VARS.index(k)] += Q(v)
    return out
def add(*fs):
    out = [Q(0)] * 9
    for f in fs:
        for i in range(9): out[i] += f[i]
    return out
def scl(f, k): return [Q(k) * v for v in f]
def sub(f, g): return add(f, scl(g, -1))
def cst(k): return lin(c=k)

def canon(f, strict):
    den = 1
    for v in f: den = den * v.denominator // gcd(den, v.denominator)
    iv = [int(v * den) for v in f]
    g = 0
    for v in iv: g = gcd(g, abs(v))
    if g == 0: g = 1
    return tuple(v // g for v in iv) + (1 if strict else 0,)

def ge0(f): return canon(f, False)
def gt0(f): return canon(f, True)
def leq(f, g): return ge0(sub(g, f))
def less(f, g): return gt0(sub(g, f))
def negate(r): return tuple(-v for v in r[:9]) + (1 - r[9],)

NINE = lambda k: Q(k, 9)
zV, zm, zs, zaA, zaB, zx, zm2, zs2 = (lin(**{n: 1}) for n in VARS)
zbA = sub(zV, zaA); zbB = sub(zV, zaB)
zV2 = add(zV, zx); zY2 = sub(cst(1), zm2); zh2 = add(cst(1), scl(zV2, -1), zs2)

def check_cert(region, cons, mults):
    regset = set(region)
    tot = [Q(0)] * 9; strict = False
    for r, y in zip(cons, mults):
        r = tuple(r)
        if r not in regset: return False
        y = Q(y)
        if y < 0: return False
        if y == 0: continue
        for i in range(9): tot[i] += y * r[i]
        if r[9]: strict = True
    if any(tot[i] != 0 for i in range(8)): return False
    return tot[8] < 0 or (tot[8] == 0 and strict)

class Missing(Exception): pass
class Empty(Exception): pass

class Run:
    def __init__(self, prefix, certs, stats):
        self.prefix = prefix; self.pos = 0; self.region = []; self.path = []; self.todo = []
        self.certs = certs; self.stats = stats
    def pruned(self, key, cons):
        for cc, yy in self.certs.get(key, ()):
            if check_cert(cons, cc, yy):
                self.stats['pruned'] += 1; return True
        return False
    def pick(self, alts):
        if self.pos < len(self.prefix):
            i = self.prefix[self.pos]; self.pos += 1
            self.region = self.region + alts[i]; self.path.append(i); return i
        live = [i for i, a in enumerate(alts) if not self.pruned(json.dumps(self.path + [i]), self.region + a)]
        if not live: raise Empty()
        if len(live) > 1: self.todo.append((list(self.path), live[1:]))
        i = live[0]; self.pos += 1; self.region = self.region + alts[i]; self.path.append(i); return i
    def cmp_ge(self, f): return self.pick([[ge0(f)], [gt0(scl(f, -1))]]) == 0
    def cmp_gt(self, f): return self.pick([[gt0(f)], [ge0(scl(f, -1))]]) == 0
    def is_le(self, f, g): return self.cmp_ge(sub(g, f))
    def is_lt(self, f, g): return self.cmp_gt(sub(g, f))
    def vmax(self, f, g): return f if self.cmp_ge(sub(f, g)) else g
    def vmin(self, f, g): return f if self.is_le(f, g) else g
    def need(self, key, cons):
        for cc, yy in self.certs.get(key, ()):
            if check_cert(cons, cc, yy):
                self.stats['targets'] += 1; return
        raise Missing(key)

def lookahead(R, a, b, strict):
    tK = R.vmax(add(b, zx), add(a, zY2))
    tS = R.vmax(R.vmax(add(a, zx), b), add(R.vmin(add(a, zx), b), zY2))
    return R.is_lt(tK, tS) if strict else R.is_le(tK, tS)

def put(R, a, b, stack):
    if stack: return (a, add(b, zx))
    if R.is_le(add(a, zx), b): return (add(a, zx), b)
    return (b, add(a, zx))

def policyA(R, a, b):
    if R.cmp_ge(sub(b, cst(NINE(7)))): return lookahead(R, a, b, False)
    if R.is_le(add(b, zx), cst(NINE(11))): return True
    return lookahead(R, a, b, True)

def window(R, f): return R.cmp_ge(sub(f, cst(NINE(7)))) and R.is_le(f, cst(NINE(11)))

def policyB(R, a, b, a_A, b_A, kA):
    if R.cmp_ge(sub(b, cst(NINE(7)))): return lookahead(R, a, b, False)
    if R.is_le(add(b, zx), cst(NINE(4))): return True
    wb = window(R, add(b, zx)); wa = window(R, add(a, zx))
    if wb and wa: return lookahead(R, a, b, False)
    if wb: return True
    if wa: return False
    if R.is_lt(add(b, zx), cst(NINE(7))):
        if R.is_le(R.vmin(add(a, zx), b), cst(NINE(4))): return False
        nA = put(R, a_A, b_A, kA)
        hpos = R.cmp_gt(zh2)
        def threat(k):
            nB = put(R, a, b, k)
            t = R.vmax(add(nA[1], nB[1]), add(R.vmax(nA[1], add(nA[0], zY2)), R.vmax(nB[1], add(nB[0], zY2))))
            if hpos:
                def cE(p): return R.vmin(R.vmax(p[1], add(p[0], scl(zh2, 2))), add(p[1], zh2))
                t = R.vmax(t, add(cE(nA), cE(nB)))
            return t
        jK = threat(True); jS = threat(False)
        return R.is_le(jK, jS)
    return False

def invariant(mode, V, m, s, a1, a2):
    b1, b2 = sub(V, a1), sub(V, a2); Y = sub(cst(1), m)
    one = lambda r: [[r]]
    D = [one(ge0(V)), one(leq(V, cst(2))), one(ge0(m)), one(ge0(add(m, scl(V, -1), cst(1)))), one(leq(m, s)),
         one(leq(scl(s, 2), V)), one(ge0(a1)), one(leq(scl(a1, 2), V)), one(ge0(a2)), one(leq(scl(a2, 2), V))]
    for a, b in ((a1, b1), (a2, b2)):
        D.append([[gt0(sub(b, cst(1)))], [leq(m, a), leq(a, s)]])
    D.append(one(leq(add(b1, b2), cst(NINE(22)))))
    if mode == 'hedge':
        D += [one(leq(a1, cst(0))), one(less(b1, cst(NINE(7)))), one(less(b2, cst(NINE(7))))]
        D.append([[gt0(sub(V, cst(NINE(4))))], [leq(a2, cst(0))]])
        D.append([[leq(sub(b2, a2), cst(NINE(4)))], [leq(s, a2)]])
        D.append([[leq(b2, cst(NINE(4)))], [less(sub(b2, a2), sub(V, cst(NINE(4))))], [leq(s, a2)]])
    elif mode == 'late':
        D += [one(gt0(a1)), one(less(b1, cst(NINE(7)))), one(less(b2, cst(NINE(7))))]
        D += [one(gt0(sub(V, cst(NINE(11))))), one(gt0(sub(m, cst(NINE(4)))))]
        D.append([[ge0(sub(m, a1))], [ge0(add(m, b1, cst(-NINE(11)))), ge0(add(m, scl(a1, -2), cst(NINE(7))))]])
    elif mode == 'Ab':
        D += [one(ge0(sub(b1, cst(NINE(7))))), one(less(b2, cst(NINE(7))))]
        D += [one(leq(b1, cst(NINE(11)))), one(leq(add(a1, a2, scl(Y, 2)), cst(NINE(22)))),
              one(leq(add(b1, a2, Y), cst(NINE(22))))]
        D.append([[gt0(sub(V, cst(1)))], [leq(a1, cst(0))]])
        D.append([[gt0(sub(V, cst(1)))], [leq(s, add(a2, cst(NINE(2))))], [ge0(sub(scl(a2, 6), cst(1)))],
                  [leq(a2, sub(scl(V, 2), cst(NINE(14))))]])
        D.append([[leq(a1, cst(0))], [less(Y, b1)]])
        D.append([[leq(V, cst(1))], [leq(s, add(a2, cst(NINE(2))))], [ge0(sub(add(b1, b2), cst(NINE(14))))],
                  [leq(sub(b2, a2), cst(NINE(4)))]])
    elif mode == 'aB':
        D += [one(less(b1, cst(NINE(7)))), one(ge0(sub(b2, cst(NINE(7)))))]
        D += [one(gt0(sub(V, cst(NINE(11))))), one(leq(b2, cst(NINE(11)))),
              one(leq(add(a1, Y, b2), cst(NINE(22)))), one(leq(add(a1, Y, cst(2), scl(b2, -1)), cst(NINE(22))))]
    return D

def run_case(R, src):
    for disj in invariant(src, zV, zm, zs, zaA, zaB):
        if len(disj) == 1: R.region = R.region + disj[0]
        else: R.pick(disj)
    R.region = R.region + [gt0(zx), leq(zx, sub(cst(1), zm)), leq(zm2, zs2), leq(scl(zs2, 2), zV2)]
    low = sub(zV2, cst(1))
    pieces = [(zm, zs), (sub(zV, zs), sub(zV, zm)), (add(zm, zx), add(zs, zx)), (add(sub(zV, zs), zx), add(sub(zV, zm), zx))]
    for w in (zm2, zs2):
        R.region = R.region + [ge0(w), ge0(sub(w, low)), leq(w, cst(1))]
        R.pick([[ge0(sub(w, p)), leq(w, q)] for p, q in pieces])
    if src == 'Ab':
        for a, b in ((zaA, zbA), (zaB, zbB)):
            if R.is_le(b, cst(1)):
                e = add(a, zx)
                R.pick([[gt0(sub(low, e))], [gt0(sub(e, cst(1)))], [leq(zm2, e), ge0(sub(zs2, e))],
                        [leq(zm2, e), ge0(sub(zs2, sub(zV2, e)))]])
    kA = policyA(R, zaA, zbA)
    kB = policyB(R, zaB, zbB, zaA, zbA, kA)
    nA = put(R, zaA, zbA, kA); nB = put(R, zaB, zbB, kB)
    for a, b in (nA, nB):
        R.pick([[gt0(sub(b, cst(1)))], [leq(zm2, a), leq(a, zs2)]])
    closedA = R.cmp_ge(sub(nA[1], cst(NINE(7)))); closedB = R.cmp_ge(sub(nB[1], cst(NINE(7))))
    if closedA and closedB:
        for f in (add(nA[1], nB[1]), add(nA[1], cst(2), scl(nB[1], -1)), add(cst(2), scl(nA[1], -1), nB[1]),
                  add(cst(4), scl(nA[1], -1), scl(nB[1], -1))):
            R.need(json.dumps(R.path + ['E']), R.region + [gt0(sub(f, cst(NINE(22))))])
        return 'AB'
    if closedA: md = 'Ab'
    elif closedB: md = 'aB'
    else: md = 'hedge' if R.is_le(nA[0], cst(0)) else 'late'
    for di, disj in enumerate(invariant(md, zV2, zm2, zs2, nA[0], nB[0])):
        for combo in itertools.product(*[[negate(r) for r in alt] for alt in disj]):
            key = json.dumps(R.path + ['T', md, di] + [','.join(map(str, q)) for q in combo])
            R.need(key, R.region + list(combo))
    return md

def root_in_R():
    point = [Q(0)] * 8
    def holds(r):
        v = sum(Q(r[i]) * point[i] for i in range(8)) + Q(r[8])
        return v > 0 if r[9] else v >= 0
    return all(any(all(holds(r) for r in alt) for alt in disj) for disj in invariant('hedge', zV, zm, zs, zaA, zaB))

def main():
    if sys.argv[1] == 'root':
        print('root in R(hedge):', 'PASS' if root_in_R() else 'FAIL'); return
    src = sys.argv[1]; fn = sys.argv[2]
    start = json.loads(sys.argv[3]) if len(sys.argv) > 3 else []
    certs = {}
    with open(fn) as f:
        for line in f:
            r = json.loads(line)
            key = json.dumps(r['p'])
            certs.setdefault(key, []).append(([tuple(c) for c in r['c']], r['y']))
    stats = dict(pruned=0, targets=0, leaves=0, empty=0, missing=0)
    stack = [start]
    while stack:
        pre = stack.pop()
        R = Run(pre, certs, stats)
        try:
            run_case(R, src); stats['leaves'] += 1
        except Empty:
            stats['empty'] += 1
        except Missing as e:
            stats['missing'] += 1
            if stats['missing'] <= 5: print('MISSING certificate', e.args[0][:200])
        for p, rest in R.todo:
            for i in reversed(rest): stack.append(p + [i])
    ok = stats['missing'] == 0
    print('liftcheck', src, 'prefix', start, 'file', fn, stats, 'RESULT', 'PASS' if ok else 'FAIL')

if __name__ == '__main__':
    main()
