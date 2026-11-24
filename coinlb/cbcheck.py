#!/usr/bin/env python3
# cbcheck.py: checks certificates written by coinlb3.cpp.
# python3 -I cbcheck.py CERT...
import sys
import re
from itertools import product
from collections import Counter

INT = re.compile(r'^(0|[1-9][0-9]*)$')

class Fail(Exception):
    pass

def pint(tok, what):
    if not INT.match(tok):
        raise Fail('bad integer %r in %s' % (tok, what))
    return int(tok)

def fits_completion(items, m, g):
    cnt = Counter(items)
    sizes = sorted(cnt, reverse=True)
    mult = [cnt[s] for s in sizes]

    memo = {}

    def rec(mult, bins):
        mult = tuple(mult)
        tot = sum(s * c for s, c in zip(sizes, mult))
        if tot == 0:
            return True
        if bins == 0 or tot > bins * g:
            return False
        key = (mult, bins)
        if key in memo:
            return memo[key]
        first = next(i for i, c in enumerate(mult) if c > 0)
        base = list(mult)
        base[first] -= 1
        room = g - sizes[first]
        ok = False
        chosen = [0] * len(sizes)

        def enum(i, room):
            nonlocal ok
            if ok:
                return
            if i == len(sizes):
                rest = [base[j] - chosen[j] for j in range(len(sizes))]
                if rec(rest, bins - 1):
                    ok = True
                return
            maxc = min(base[i], room // sizes[i]) if i >= first else 0
            for c in range(maxc, -1, -1):
                chosen[i] = c
                enum(i + 1, room - c * sizes[i])
                if ok:
                    break
            chosen[i] = 0

        enum(0, room)
        memo[key] = ok
        return ok

    return rec(mult, m)

def fits_dp(items, m, g):
    if sum(items) > m * g:
        return False
    states = {tuple([0] * m)}
    for s in sorted(items, reverse=True):
        nxt = set()
        for v in states:
            for i in range(m):
                if v[i] + s <= g and (i == 0 or v[i] != v[i - 1]):
                    w = list(v)
                    w[i] += s
                    nxt.add(tuple(sorted(w, reverse=True)))
        if not nxt:
            return False
        states = nxt
    return True

_fitcache = {}

def feasible(items, m, g):
    key = (tuple(sorted(items, reverse=True)), m, g)
    if key in _fitcache:
        return _fitcache[key]
    if any(s < 1 or s > g for s in items):
        r = False
        _fitcache[key] = r
        return r
    a = fits_completion(list(items), m, g)
    b = fits_dp(list(items), m, g)
    if a != b:
        raise RuntimeError('packability methods disagree on %r m=%d g=%d' % (key[0], m, g))
    _fitcache[key] = a
    return a

def canon(L, w):
    L = [tuple(sorted(x, reverse=True)) for x in L]
    out = list(L)
    for wt in set(w):
        pos = [j for j in range(len(w)) if w[j] == wt]
        vecs = sorted((L[j] for j in pos), reverse=True)
        for j, v in zip(pos, vecs):
            out[j] = v
    return tuple(out)

def check(path, verbose=True):
    info = {}
    with open(path, 'rb') as f:
        raw = f.read()
    try:
        text = raw.decode('ascii')
    except UnicodeDecodeError:
        raise Fail('C1: file is not ASCII')
    if '\r' in text:
        raise Fail('C1: carriage return in file')
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    lines = [ln for ln in lines if not ln.startswith('#')]
    if len(lines) < 5:
        raise Fail('C1: fewer than 5 header lines')
    if lines[0] != 'COINLB 1':
        raise Fail('C1: line 1 is %r' % lines[0])
    t = lines[1].split(' ')
    if len(t) != 3:
        raise Fail('C1: line 2 must be "m K g"')
    m, K, g = (pint(x, 'line 2') for x in t)
    if m < 2 or K < 1 or g < 1:
        raise Fail('C1: m>=2, K>=1, g>=1 violated')
    t = lines[2].split(' ')
    if len(t) != K:
        raise Fail('C1: line 3 must list K weights')
    w = [pint(x, 'line 3') for x in t]
    if min(w) < 1:
        raise Fail('C1: weight < 1')
    W = sum(w)
    t = lines[3].split(' ')
    if len(t) != 3 or t[0] != 'T':
        raise Fail('C1: line 4 must be "T a b"')
    a, b = pint(t[1], 'T'), pint(t[2], 'T')
    if a < 1 or b < 1:
        raise Fail('C1: a>=1, b>=1 violated')
    t = lines[4].split(' ')
    if len(t) != 2 or t[0] != 'N':
        raise Fail('C1: line 5 must be "N n"')
    n = pint(t[1], 'N')
    body = lines[5:]
    if len(body) < n:
        raise Fail('C1: %d state lines announced, %d present' % (n, len(body)))
    tail = body[n:]
    if not (tail == [] or tail == ['END']):
        raise Fail('C1: unexpected content after the %d state lines: %r' % (n, tail[:2]))
    info.update(m=m, K=K, g=g, w=w, a=a, b=b, n=n)

    def is_stop(L):
        P = sum(wj * max(Lj) for wj, Lj in zip(w, L))
        return b * P >= a * W * g

    states = {}
    order = []
    for k, ln in enumerate(body[:n]):
        where = 'state line %d' % (k + 1)
        f = ln.split(' | ')
        if len(f) != K + 2:
            raise Fail('C2: %s has %d fields, need %d' % (where, len(f), K + 2))
        if f[0] == '-':
            H = ()
        else:
            H = tuple(pint(x, where) for x in f[0].split(','))
            if any(x < 1 or x > g for x in H):
                raise Fail('C2: %s size outside 1..g' % where)
            if list(H) != sorted(H, reverse=True):
                raise Fail('C2: %s H not non-increasing' % where)
        tot = sum(H)
        L = []
        for j in range(K):
            v = tuple(pint(x, where) for x in f[1 + j].split(','))
            if len(v) != m:
                raise Fail('C2: %s L_%d has %d entries' % (where, j + 1, len(v)))
            if sum(v) != tot:
                raise Fail('C2: %s L_%d sums to %d, H totals %d' % (where, j + 1, sum(v), tot))
            L.append(v)
        L = tuple(L)
        if canon(list(L), w) != L:
            raise Fail('C2: %s not canonical' % where)
        s = pint(f[K + 1], where)
        key = (H, L)
        if key in states:
            raise Fail('C2: %s duplicates an earlier state' % where)
        states[key] = s
        order.append(key)

    root = ((), tuple(tuple([0] * m) for _ in range(K)))
    if root not in states:
        raise Fail('C3: root not listed')

    nstop = 0
    nHinf = 0
    nchild = 0
    succ = {}
    for key in order:
        H, L = key
        s = states[key]
        if is_stop(L):
            nstop += 1
        if not feasible(H, m, g):
            nHinf += 1
        if s < 1 or s > g:
            raise Fail('C4: move %d outside 1..g at %r' % (s, key))
        H2 = tuple(sorted(H + (s,), reverse=True))
        if not feasible(H2, m, g):
            raise Fail('C4: H+{%d} infeasible at %r' % (s, key))
        kids = set()
        for resp in product(range(m), repeat=K):
            L2 = []
            for j in range(K):
                v = list(L[j])
                v[resp[j]] += s
                L2.append(tuple(v))
            c = canon(L2, w)
            nchild += 1
            if is_stop(c):
                continue
            ck = (H2, c)
            if ck not in states:
                raise Fail('C5: child %r of %r under response %r is neither stop nor listed'
                           % (ck, key, tuple(r + 1 for r in resp)))
            kids.add(ck)
        succ[key] = kids

    seen = {root: 0}
    stack = [root]
    while stack:
        x = stack.pop()
        for y in succ[x]:
            if y not in seen:
                seen[y] = seen[x] + 1
                stack.append(y)
    info.update(listed_stops=nstop, listed_H_infeasible=nHinf, child_checks=nchild,
                reachable=len(seen), unreachable=n - len(seen),
                root_move=states[root],
                max_jobs=max(sum(1 for _ in H) for (H, _) in order) + 1,
                stop_threshold_P='b*P >= %d' % (a * W * g))
    return info

def main(argv):
    allok = True
    npass = nfail = 0
    for p in argv[1:]:
        try:
            info = check(p)
            npass += 1
            print('PASS', p, ' '.join('%s=%s' % kv for kv in info.items()))
        except Fail as e:
            nfail += 1
            allok = False
            print('FAIL', p, str(e)[:400])
    print('TOTAL pass=%d fail=%d' % (npass, nfail))
    return 0 if allok else 1

if __name__ == '__main__':
    sys.exit(main(sys.argv))
