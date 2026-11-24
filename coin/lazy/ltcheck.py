# Checks a lazy case tree in exact arithmetic.
# python3 ltcheck.py hedge|late|aB|Ab TREE.jsonl
import sys, json, itertools
from fractions import Fraction as Q
from math import gcd

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
def rkey(r): return ','.join(map(str, r))

NINE = lambda k: Q(k, 9)
zV, zm, zs, zaA, zaB, zx, zm2, zs2 = (lin(**{n: 1}) for n in VARS)
zbA = sub(zV, zaA); zbB = sub(zV, zaB)
zV2 = add(zV, zx); zY2 = sub(cst(1), zm2); zh2 = add(cst(1), scl(zV2, -1), zs2)

def check_cert(region, cons, mults):
    regset = set(region)
    tot = [Q(0)] * 9; strict = False
    if len(cons) != len(mults): return False
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
    return [d for i, d in enumerate(D) if '%s:%d' % (mode, i) not in DROP]
DROP = set()

def hypotheses(src):
    base = []; H = []
    for disj in invariant(src, zV, zm, zs, zaA, zaB):
        if len(disj) == 1: base += disj[0]
        else: H.append(disj)
    base += [gt0(zx), leq(zx, sub(cst(1), zm)), leq(zm2, zs2), leq(scl(zs2, 2), zV2)]
    low = sub(zV2, cst(1))
    pieces = [(zm, zs), (sub(zV, zs), sub(zV, zm)), (add(zm, zx), add(zs, zx)), (add(sub(zV, zs), zx), add(sub(zV, zm), zx))]
    for w in (zm2, zs2):
        base += [ge0(w), ge0(sub(w, low)), leq(w, cst(1))]
        H.append([[ge0(sub(w, p)), leq(w, q)] for p, q in pieces])
    if src == 'Ab':
        for a, b in ((zaA, zbA), (zaB, zbB)):
            e = add(a, zx); le1 = leq(b, cst(1))
            H.append([[gt0(sub(b, cst(1)))], [le1, gt0(sub(low, e))], [le1, gt0(sub(e, cst(1)))],
                      [le1, leq(zm2, e), ge0(sub(zs2, e))], [le1, leq(zm2, e), ge0(sub(zs2, sub(zV2, e)))]])
    return base, H

class Leaf:
    def __init__(self, region, certs, stats):
        self.region = region; self.certs = certs; self.stats = stats; self.memo = {}
    def has(self, key, cons):
        for cc, yy in self.certs.get(key, ()):
            if check_cert(cons, cc, yy): return True
        return False
    def decide(self, typ, f):
        k = (typ, canon(f, False))
        if k in self.memo: return self.memo[k]
        tneg, fneg = (gt0(scl(f, -1)), ge0(f)) if typ == 'ge' else (ge0(scl(f, -1)), gt0(f))
        d = None
        if self.has('D|' + rkey(tneg), self.region + [tneg]): d = True
        elif self.has('D|' + rkey(fneg), self.region + [fneg]): d = False
        if d is not None: self.stats['decided'] += 1
        self.memo[k] = d
        return d

class Ev:
    def __init__(self, leaf, prefix):
        self.leaf = leaf; self.prefix = prefix; self.k = 0; self.ch = []; self.newb = []; self.facts = {}
    def q(self, typ, f):
        k = (typ, canon(f, False))
        if k in self.facts: return self.facts[k]
        d = self.leaf.decide(typ, f)
        if d is None:
            if self.k < len(self.prefix): v = self.prefix[self.k]
            else:
                v = 0; self.newb.append(self.ch + [1])
            self.k += 1; self.ch.append(v); d = (v == 0)
        self.facts[k] = d
        return d
    def cmp_ge(self, f): return self.q('ge', f)
    def cmp_gt(self, f): return self.q('gt', f)
    def is_le(self, f, g): return self.cmp_ge(sub(g, f))
    def is_lt(self, f, g): return self.cmp_gt(sub(g, f))
    def vmax(self, f, g): return f if self.cmp_ge(sub(f, g)) else g
    def vmin(self, f, g): return f if self.is_le(f, g) else g

def fkey(f): return ','.join(str(v) for v in f)

MAXRUNS = 4096
def check_leaf(region, certs, stats):
    L = Leaf(region, certs, stats); nruns = 0
    outs = {}
    stack = [[]]
    while stack:
        pre = stack.pop()
        R = Ev(L, pre)
        kA = policyA(R, zaA, zbA)
        kB = policyB(R, zaB, zbB, zaA, zbA, kA)
        nA = put(R, zaA, zbA, kA); nB = put(R, zaB, zbB, kB)
        cA = R.cmp_ge(sub(nA[1], cst(NINE(7)))); cB = R.cmp_ge(sub(nB[1], cst(NINE(7))))
        if cA and cB: md = 'AB'
        elif cA: md = 'Ab'
        elif cB: md = 'aB'
        else: md = 'hedge' if R.is_le(nA[0], cst(0)) else 'late'
        ok = md + ';' + ';'.join(fkey(f) for f in (nA[0], nA[1], nB[0], nB[1]))
        outs[ok] = (md, nA, nB)
        stats['runs'] += 1; nruns += 1
        if nruns > MAXRUNS: return 'more than %d evaluation runs at one leaf' % MAXRUNS
        for b in reversed(R.newb): stack.append(b)
    for ok, (md, nA, nB) in sorted(outs.items()):
        stats['outcomes'] += 1
        alts = [[[gt0(sub(b, cst(1)))], [leq(zm2, a), leq(a, zs2)]] for a, b in (nA, nB)]
        for i, j in itertools.product(range(2), range(2)):
            subr = region + alts[0][i] + alts[1][j]
            base = 'O|' + ok + '|%d%d' % (i, j)
            if L.has(base + '|X', subr): stats['subempty'] += 1; continue
            if md == 'AB':
                for k, f in enumerate((add(nA[1], nB[1]), add(nA[1], cst(2), scl(nB[1], -1)),
                                       add(cst(2), scl(nA[1], -1), nB[1]), add(cst(4), scl(nA[1], -1), scl(nB[1], -1)))):
                    if not L.has(base + '|E|%d' % k, subr + [gt0(sub(f, cst(NINE(22))))]):
                        return 'missing ' + base + '|E|%d' % k
                    stats['targets'] += 1
            else:
                for di, disj in enumerate(invariant(md, zV2, zm2, zs2, nA[0], nB[0])):
                    for combo in itertools.product(*[[negate(r) for r in alt] for alt in disj]):
                        key = base + '|T|%d|' % di + '|'.join(rkey(q) for q in combo)
                        if not L.has(key, subr + list(combo)): return 'missing ' + key[:160]
                        stats['targets'] += 1
    return None

def main():
    src = sys.argv[1]; fn = sys.argv[2]
    start = json.loads(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else []
    if len(sys.argv) > 4 and sys.argv[4] != '-':
        for d in sys.argv[4].split(','):
            md, i = d.split(':')
            if int(i) < 15 or (md in ('hedge', 'late') and int(i) < 16): print('refusing to drop', d); sys.exit(1)
            DROP.add(d)
    print('dropped conditions of R:', sorted(DROP))
    kind = {}; certs = {}; ncert = 0
    with open(fn) as f:
        for line in f:
            r = json.loads(line); key = json.dumps(r['n'])
            if 't' in r:
                if key in kind: print('DUPLICATE node record', key); sys.exit(1)
                kind[key] = r
            else:
                certs.setdefault(key, {}).setdefault(r['k'], []).append(([tuple(c) for c in r['c']], r['y'])); ncert += 1
    base, H = hypotheses(src)
    cons = list(base); path0 = []
    for hi, ai in start:
        cons += H[hi][ai]; path0.append('h%d=%d' % (hi, ai))
    stats = dict(nodes=0, leaves=0, empty=0, hsplit=0, csplit=0, decided=0, runs=0, outcomes=0, subempty=0, targets=0,
                 bad=0)
    stack = [(path0, cons)]
    seen = set()
    while stack:
        path, region = stack.pop()
        key = json.dumps(path); seen.add(key); stats['nodes'] += 1
        rec = kind.get(key)
        if rec is None:
            stats['bad'] += 1; print('NO RECORD for node', key); continue
        t = rec['t']
        if t == 'hsplit':
            hi = rec['h']; stats['hsplit'] += 1
            for ai in range(len(H[hi])): stack.append((path + ['h%d=%d' % (hi, ai)], region + H[hi][ai]))
        elif t == 'csplit':
            row = tuple(rec['f']); stats['csplit'] += 1
            if len(row) != 10 or row[9] not in (0, 1): stats['bad'] += 1; print('BAD ROW', key); continue
            stack.append((path + ['c0'], region + [row])); stack.append((path + ['c1'], region + [negate(row)]))
        elif t == 'empty':
            c = certs.get(key, {})
            if any(check_cert(region, cc, yy) for cc, yy in c.get('EMPTY', ())): stats['empty'] += 1
            else: stats['bad'] += 1; print('EMPTY without certificate', key)
        elif t == 'leaf':
            msg = check_leaf(region, certs.get(key, {}), stats)
            if msg is None: stats['leaves'] += 1
            else: stats['bad'] += 1; print('LEAF FAIL', key, msg)
        else:
            stats['bad'] += 1; print('UNRESOLVED node', key, t)
    ok = stats['bad'] == 0
    print('ltcheck', src, 'start', start, 'file', fn, 'certificate records', ncert, stats, 'RESULT', 'PASS' if ok else 'FAIL')

if __name__ == '__main__':
    main()
