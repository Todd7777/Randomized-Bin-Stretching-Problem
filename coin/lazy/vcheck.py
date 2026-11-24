# A second checker of the lazy case trees, written from the definitions.
# python3 vcheck.py hedge|late|aB|Ab TREE.jsonl
import sys, json
from fractions import Fraction as Fr
from math import gcd
from itertools import product

NV = 8
def var(i):
    t = [Fr(0)] * 9; t[i] = Fr(1); return tuple(t)
def const(c):
    t = [Fr(0)] * 9; t[8] = Fr(c); return tuple(t)
def A(*fs):
    return tuple(sum((f[i] for f in fs), Fr(0)) for i in range(9))
def M(k, f): return tuple(Fr(k) * v for v in f)
def D(f, g): return A(f, M(-1, g))
V, m, s, aA, aB, x, m2, s2 = (var(i) for i in range(8))
ONE = const(1); N9 = lambda k: const(Fr(k, 9))

def canon(f, strict):
    L = 1
    for v in f: L = L * v.denominator // gcd(L, v.denominator)
    iv = [int(v * L) for v in f]
    g = 0
    for v in iv: g = gcd(g, abs(v))
    if g > 1: iv = [v // g for v in iv]
    return tuple(iv) + (1 if strict else 0,)
def GE(f): return canon(f, False)
def GT(f): return canon(f, True)
def LE(f, g): return GE(D(g, f))
def LT(f, g): return GT(D(g, f))
def NEG(r): return tuple(-v for v in r[:9]) + (1 - r[9],)

def cert_valid(rows, ys):
    if len(rows) != len(ys) or not rows: return False
    tot = [0] * 9; strict = False
    for r, y in zip(rows, ys):
        if len(r) != 10 or r[9] not in (0, 1): return False
        y = Fr(y)
        if y < 0: return False
        if y == 0: continue
        for i in range(9): tot[i] += y * r[i]
        if r[9]: strict = True
    if any(t != 0 for t in tot[:8]): return False
    return tot[8] < 0 or (tot[8] == 0 and strict)

class Sys:
    def __init__(self, certs): self.certs = certs
    def empty(self, S):
        S = set(S)
        for r in S:
            if all(v == 0 for v in r[:8]) and (r[8] < 0 or (r[8] == 0 and r[9])): return True
            if NEG(r) in S: return True
        return any(c <= S for c in self.certs)

def R(mode, V, m, s, a1, a2):
    b1, b2 = D(V, a1), D(V, a2); Y = D(ONE, m)
    C = []
    one = lambda n, r: C.append((n, [[r]]))
    one('v', GE(V)); one('v', LE(V, const(2))); one('v', GE(m)); one('v', GE(D(m, D(V, ONE)))); one('v', LE(m, s))
    one('v', LE(M(2, s), V))
    for a in (a1, a2): one('v', GE(a)); one('v', LE(M(2, a), V))
    for a, b in ((a1, b1), (a2, b2)): C.append(('v', [[GT(D(b, ONE))], [LE(m, a), LE(a, s)]]))
    one('pay', LE(A(b1, b2), N9(22)))
    if mode == 'hedge':
        one('mode', LE(a1, const(0))); one('mode', LT(b1, N9(7))); one('mode', LT(b2, N9(7)))
        C.append(('H1', [[GT(D(V, N9(4)))], [LE(a2, const(0))]]))
        C.append(('H2', [[LE(D(b2, a2), N9(4))], [LE(s, a2)]]))
        C.append(('H3', [[LE(b2, N9(4))], [LT(D(b2, a2), D(V, N9(4)))], [LE(s, a2)]]))
    elif mode == 'late':
        one('mode', GT(a1)); one('mode', LT(b1, N9(7))); one('mode', LT(b2, N9(7)))
        C.append(('L1', [[GT(D(V, N9(11)))]])); C.append(('L2', [[GT(D(m, N9(4)))]]))
        C.append(('L3', [[GE(D(m, a1))], [GE(D(m, D(N9(11), b1))), GE(D(m, D(M(2, a1), N9(7))))]]))
    elif mode == 'Ab':
        one('mode', GE(D(b1, N9(7)))); one('mode', LT(b2, N9(7)))
        C.append(('A1', [[LE(b1, N9(11))]])); C.append(('A2', [[LE(A(a1, a2, M(2, Y)), N9(22))]]))
        C.append(('A3', [[LE(A(b1, a2, Y), N9(22))]]))
        C.append(('A4', [[GT(D(V, ONE))], [LE(a1, const(0))]]))
        C.append(('A5', [[GT(D(V, ONE))], [LE(s, A(a2, N9(2)))], [GE(D(a2, const(Fr(1, 6))))],
                         [LE(a2, D(M(2, V), N9(14)))]]))
        C.append(('A6', [[LE(a1, const(0))], [LT(Y, b1)]]))
        C.append(('A7', [[LE(V, ONE)], [LE(s, A(a2, N9(2)))], [GE(D(A(b1, b2), N9(14)))], [LE(D(b2, a2), N9(4))]]))
    elif mode == 'aB':
        one('mode', LT(b1, N9(7))); one('mode', GE(D(b2, N9(7))))
        C.append(('B1', [[GT(D(V, N9(11)))]])); C.append(('B2', [[LE(b2, N9(11))]]))
        C.append(('B3a', [[LE(A(a1, Y, b2), N9(22))]])); C.append(('B3b', [[LE(A(a1, Y, const(2), M(-1, b2)), N9(22))]]))
    else: raise ValueError(mode)
    return [(n, d) for n, d in C if n not in DROP]
DROP = set()

def hyps(src):
    base, H = [], []
    for n, d in R(src, V, m, s, aA, aB):
        if len(d) == 1: base += d[0]
        else: H.append(d)
    V2 = A(V, x)
    base += [GT(x), LE(x, D(ONE, m)), LE(m2, s2), LE(M(2, s2), V2)]
    iv = [(m, s), (D(V, s), D(V, m)), (A(m, x), A(s, x)), (A(D(V, s), x), A(D(V, m), x))]
    for w in (m2, s2):
        base += [GE(w), GE(D(w, D(V2, ONE))), LE(w, ONE)]
        H.append([[GE(D(w, lo)), LE(w, hi)] for lo, hi in iv])
    if src == 'Ab':
        for a in (aA, aB):
            b = D(V, a); e = A(a, x); bl = LE(b, ONE)
            H.append([[GT(D(b, ONE))], [bl, LT(e, D(V2, ONE))], [bl, GT(D(e, ONE))],
                      [bl, LE(m2, e), LE(e, s2)], [bl, LE(m2, e), LE(D(V2, e), s2)]])
    return base, H

class Need(Exception):
    def __init__(self, k): self.k = k
class Ev:
    def __init__(self, sysm, region, ans):
        self.sm = sysm; self.region = region; self.ans = ans
    def rows(self):
        return [k if v else NEG(k) for k, v in self.ans.items()]
    def ge(self, f):
        k = GE(f)
        if all(v == 0 for v in k[:8]): return k[8] >= 0
        if k in self.ans: return self.ans[k]
        S = self.region + self.rows()
        if self.sm.empty(S + [NEG(k)]): return True
        if self.sm.empty(S + [k]): return False
        raise Need(k)
    def gt(self, f): return not self.ge(M(-1, f))
    def le(self, f, g): return self.ge(D(g, f))
    def lt(self, f, g): return self.gt(D(g, f))
    def mx(self, f, g): return f if self.ge(D(f, g)) else g
    def mn(self, f, g): return f if self.le(f, g) else g

def c14b(E):
    V2 = A(V, x); Y = D(ONE, m2); h = A(ONE, M(-1, V2), s2)
    def la(a, b, strict):
        tK = E.mx(A(b, x), A(a, Y))
        tS = E.mx(E.mx(A(a, x), b), A(E.mn(A(a, x), b), Y))
        return E.lt(tK, tS) if strict else E.le(tK, tS)
    def win(L): return E.ge(D(L, N9(7))) and E.le(L, N9(11))
    def ruleA(a, b):
        if E.ge(D(b, N9(7))): return la(a, b, False)
        if E.le(A(b, x), N9(11)): return True
        return la(a, b, True)
    def place(a, b, st):
        if st: return (a, A(b, x))
        if E.le(A(a, x), b): return (A(a, x), b)
        return (b, A(a, x))
    def ruleB(a, b, a1):
        if E.ge(D(b, N9(7))): return la(a, b, False)
        if E.le(A(b, x), N9(4)): return True
        wb = win(A(b, x)); wa = win(A(a, x))
        if wb and wa: return la(a, b, False)
        if wb: return True
        if wa: return False
        if E.lt(A(b, x), N9(7)):
            if E.le(E.mn(A(a, x), b), N9(4)): return False
            stA = ruleA(a1, D(V, a1))
            pA = place(a1, D(V, a1), stA)
            def J(stB):
                pB = place(a, b, stB)
                t = E.mx(A(pA[1], pB[1]), A(E.mx(pA[1], A(pA[0], Y)), E.mx(pB[1], A(pB[0], Y))))
                if E.gt(h):
                    cE = lambda p: E.mn(E.mx(p[1], A(p[0], M(2, h))), A(p[1], h))
                    t = E.mx(t, A(cE(pA), cE(pB)))
                return t
            jK = J(True); jS = J(False)
            return E.le(jK, jS)
        return False
    kA = ruleA(aA, D(V, aA)); kB = ruleB(aB, D(V, aB), aA)
    nA = place(aA, D(V, aA), kA); nB = place(aB, D(V, aB), kB)
    cA = E.ge(D(nA[1], N9(7))); cB = E.ge(D(nB[1], N9(7)))
    if cA and cB: md = 'AB'
    elif cA: md = 'Ab'
    elif cB: md = 'aB'
    else: md = 'hedge' if E.le(nA[0], const(0)) else 'late'
    return md, nA, nB

def leaf_ok(region, sm, st):
    work = [dict()]; nout = 0
    while work:
        ans = work.pop()
        E = Ev(sm, region, ans)
        try:
            md, nA, nB = c14b(E)
        except Need as e:
            a1 = dict(ans); a1[e.k] = True; a2 = dict(ans); a2[e.k] = False
            work += [a1, a2]; st['branch'] += 1
            if st['branch'] > 10 ** 7: return 'too many branches'
            continue
        nout += 1; st['outcomes'] += 1
        S0 = region + E.rows()
        V2 = A(V, x)
        valt = [[[GT(D(b, ONE))], [LE(m2, a), LE(a, s2)]] for a, b in (nA, nB)]
        for i, j in product(range(2), range(2)):
            S = S0 + valt[0][i] + valt[1][j]
            if sm.empty(S): st['subempty'] += 1; continue
            if md == 'AB':
                bA, bB = nA[1], nB[1]
                for f in (A(bA, bB), A(bA, const(2), M(-1, bB)), A(const(2), M(-1, bA), bB), A(const(4), M(-1, bA), M(-1, bB))):
                    if not sm.empty(S + [GT(D(f, N9(22)))]): return 'AB entry bound not certified %s' % md
                    st['targets'] += 1
            else:
                for name, disj in R(md, V2, m2, s2, nA[0], nB[0]):
                    for combo in product(*[[NEG(r) for r in alt] for alt in disj]):
                        if not sm.empty(S + list(combo)): return 'target %s of %s not certified' % (name, md)
                        st['targets'] += 1
    return None

def main():
    src, fn = sys.argv[1], sys.argv[2]
    if len(sys.argv) > 3 and sys.argv[3] != '-':
        for d in sys.argv[3].split(','): DROP.add(d)
    for d in DROP:
        if d in ('v', 'pay', 'mode'): sys.exit('refusing to drop ' + d)
    nodes = {}; certs = {}; ncert = 0; ninv = 0; dup = 0
    for line in open(fn):
        r = json.loads(line); k = tuple(r['n'])
        if 't' in r:
            if k in nodes: dup += 1
            nodes[k] = r
        else:
            rows = [tuple(c) for c in r['c']]; ncert += 1
            if cert_valid(rows, r['y']): certs.setdefault(k, []).append(frozenset(rows))
            else: ninv += 1
    base, H = hyps(src)
    st = dict(nodes=0, leaves=0, empty=0, hsplit=0, csplit=0, branch=0, outcomes=0, subempty=0, targets=0, bad=0)
    if dup: st['bad'] += dup; print('duplicate node records', dup)
    stack = [((), base)]
    while stack:
        path, region = stack.pop(); st['nodes'] += 1
        r = nodes.get(path)
        if r is None: st['bad'] += 1; print('missing node', path); continue
        t = r['t']; sm = Sys(certs.get(path, []))
        if t == 'hsplit':
            st['hsplit'] += 1
            for ai, alt in enumerate(H[r['h']]): stack.append((path + ('h%d=%d' % (r['h'], ai),), region + alt))
        elif t == 'csplit':
            row = tuple(r['f']); st['csplit'] += 1
            if len(row) != 10 or row[9] not in (0, 1): st['bad'] += 1; print('bad row', path); continue
            stack.append((path + ('c0',), region + [row])); stack.append((path + ('c1',), region + [NEG(row)]))
        elif t == 'empty':
            if sm.empty(region): st['empty'] += 1
            else: st['bad'] += 1; print('empty node not certified', path)
        elif t == 'leaf':
            msg = leaf_ok(region, sm, st)
            if msg: st['bad'] += 1; print('LEAF FAIL', path, msg)
            else: st['leaves'] += 1
        else: st['bad'] += 1; print('unknown node type', path, t)
    print('vcheck', src, fn, 'drop', sorted(DROP), 'certs', ncert, 'invalid certs', ninv, st,
          'RESULT', 'PASS' if st['bad'] == 0 else 'FAIL')

if __name__ == '__main__':
    main()
