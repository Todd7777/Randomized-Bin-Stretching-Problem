#!/usr/bin/env python
"""rgcheck.py CERT [slice=i/n]: exact checker of a potential certificate for the
rounded two-bin game G(k, r, w, x2) (paper, App. E).  Integers only; shares no code with the solver (rg2.cpp).

Certificate: header line with k, r, x2, weights, root; then one line per state
    N T | coarse classes of H (or -) | u,v per policy
meaning the abstract state (H, N, ((u_1,v_1),...,(u_K,v_K))) with potential T.
Checked (paper, Definition E.2 and Theorem E.3):
  (a) the root state (H empty, N = 0, all loads 0) is listed, with T = the header's root value;
  (b) every listed state is well formed and has payoff sum_j w_j v_j <= T;
  (c) for every listed state and EVERY legal adversary move (item class c, volume bit nu, overflow bits of every
      policy) there is a joint response (one bin per policy) whose successor is listed with potential <= T.
Then E[cost] <= T(root) / (W k r) for every real packable input (Theorem E.3).
slice=i/n checks only the states with (line index mod n) == i (all states are loaded); run all n slices.
"""
import sys
import time
from fractions import Fraction
from itertools import product


def packable(H, cap):
    """H: tuple of positive ints.  True iff H splits into two parts, each of sum <= cap."""
    tot = sum(H)
    sums = {0}
    for c in H:
        sums |= {s + c for s in sums if s + c <= cap}
    return any(tot - s <= cap for s in sums)


def main():
    path = sys.argv[1]
    si, sn = 0, 1
    for a in sys.argv[2:]:
        if a.startswith('slice='):
            si, sn = [int(x) for x in a[6:].split('/')]
    t0 = time.time()
    D = {}
    order = []
    with open(path) as f:
        head = f.readline().split()
        # "# rounded-game potential certificate: k K r R x2 X weights W mode M root T"
        k = int(head[head.index('k') + 1])
        r = int(head[head.index('r') + 1])
        x2 = int(head[head.index('x2') + 1])
        w = [int(x) for x in head[head.index('weights') + 1].split(',')]
        mode = head[head.index('mode') + 1]
        root_claim = int(head[head.index('root') + 1])
        assert mode == 'rounded', 'this checker handles the rounded game only'
        for line in f:
            if line.startswith('#'):
                continue
            a, b, c = line.split('|')
            N, T = [int(x) for x in a.split()]
            H = tuple(sorted(int(x) for x in b.split())) if b.strip() != '-' else ()
            P = tuple(tuple(int(x) for x in q.split(',')) for q in c.split())
            key = (H, N, P)
            if key in D:
                print('FAIL: duplicate state', key)
                return 1
            D[key] = T
            order.append(key)
    K = len(w)
    W = sum(w)
    kf = k * r
    NMAX = 2 * kf
    rootkey = ((), 0, ((0, 0),) * K)
    if rootkey not in D or D[rootkey] != root_claim:
        print('FAIL: root state missing or root value differs from the header')
        return 1
    print('certificate %s: k %d r %d x2 %d weights %s, %d states, root T = %d (loaded in %.0fs); slice %d/%d' % (
        path, k, r, x2, w, len(D), root_claim, time.time() - t0, si, sn), flush=True)
    pk_cache = {}
    nmoves = 0
    ncombos = 0
    nstates = 0
    for idx, key in enumerate(order):
        if idx % sn != si:
            continue
        nstates += 1
        H, N, P = key
        T = D[key]
        # (b) well-formedness and payoff
        if len(P) != K or not (0 <= N <= NMAX) or any(not (1 <= c <= k - 1) for c in H):
            print('FAIL: malformed state', key)
            return 1
        es = []
        for (u, v) in P:
            e = u + v - N
            if not (0 <= u <= v) or e not in (0, 1) or (e == 1 and u < 1):
                print('FAIL: malformed policy state', key)
                return 1
            es.append(e)
        if sum(wj * v for wj, (u, v) in zip(w, P)) > T:
            print('FAIL: payoff exceeds potential', key, T)
            return 1
        # (c) every adversary move
        for c in range(kf):
            for nu in (0, 1):
                if N == 0 and nu == 0:
                    continue
                N2 = N + c + nu
                if N2 > NMAX:
                    continue
                C = c // r
                if C >= 1:
                    H2 = tuple(sorted(H + (C,)))
                    pk = pk_cache.get(H2)
                    if pk is None:
                        pk = packable(H2, k - 1)
                        pk_cache[H2] = pk
                    if not pk:
                        continue
                else:
                    H2 = H
                nmoves += 1
                pats = []   # per policy: list of (o_small, o_big)
                free = []
                for (u, v), e in zip(P, es):
                    if u == 0:
                        pats.append([(1, nu)])
                        free.append(False)
                    elif e == 0 and nu == 1:
                        pats.append([(1, 1)])
                        free.append(False)
                    elif e == 1 and nu == 0:
                        pats.append([(0, 0)])
                        free.append(False)
                    else:
                        pats.append([(0, 0), (0, 1), (1, 0), (1, 1)])
                        free.append(True)
                for combo in product(*pats):
                    if x2:
                        fp = [p for p, fr in zip(combo, free) if fr]
                        if (0, 0) in fp and (1, 1) in fp:
                            continue
                    ncombos += 1
                    opts = []
                    for (u, v), (os_, ob) in zip(P, combo):
                        a1 = u + c + os_
                        s_small = (a1, v) if a1 <= v else (v, a1)
                        s_big = (u, v + c + ob)
                        opts.append((s_small, s_big))
                    ok = False
                    for resp in product(*opts):
                        t2 = D.get((H2, N2, resp))
                        if t2 is not None and t2 <= T:
                            ok = True
                            break
                    if not ok:
                        print('FAIL: no response.  state', key, 'T', T, 'move c', c, 'nu', nu, 'bits', combo)
                        return 1
        if nstates % 20000 == 0:
            print('  %d states checked (%.0fs)' % (nstates, time.time() - t0), flush=True)
    u = Fraction(root_claim, W * kf)
    print('CHECK PASS slice %d/%d: %d states checked (of %d), %d item moves, %d bit patterns, all answered.  '
          'T(root) = %d, W = %d, capacity %d fine units => bound u = %s = %.10f  (%.0fs)' % (
              si, sn, nstates, len(D), nmoves, ncombos, root_claim, W, kf, u, float(u), time.time() - t0), flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
