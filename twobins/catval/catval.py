#!/usr/bin/env python3
# Value of a two-bin catalog against every randomized algorithm, with exact lower and upper bounds.
# python3 catval.py CATALOG.json [--exact] [--out VAL.json] [--strategy-out ALGO.json]
import argparse
import json
import sys
import time
from fractions import Fraction
from math import gcd

def lcm(a, b):
    return a * b // gcd(a, b)

def read_catalog(path):
    with open(path) as f:
        raw = json.load(f)
    return [tuple(Fraction(x) for x in s) for s in raw]

def feasible_int(seq, cap):
    total = sum(seq)
    sums = {0}
    for x in seq:
        sums |= {s + x for s in sums if s + x <= cap}
    return any(total - s <= cap for s in sums)

class Catalog:

    def __init__(self, streams):
        L = 1
        for s in streams:
            for x in s:
                if x <= 0:
                    raise ValueError("job sizes must be positive")
                L = lcm(L, x.denominator)
        self.L = L
        ints = sorted(set(tuple(int(x * L) for x in s) for s in streams))
        if any(len(s) == 0 for s in ints):
            raise ValueError("empty stream")
        self.streams = ints
        self.infeasible = [s for s in ints if not feasible_int(s, L)]
        parent, job, total, children, term = [-1], [0], [0], [{}], [-1]
        for k, s in enumerate(ints):
            node = 0
            for x in s:
                ch = children[node]
                if x not in ch:
                    ch[x] = len(parent)
                    parent.append(node)
                    job.append(x)
                    total.append(total[node] + x)
                    children.append({})
                    term.append(-1)
                node = ch[x]
            term[node] = k
        self.parent, self.job, self.total, self.children, self.term = parent, job, total, children, term
        n = len(parent)
        self.sbase = [0] * n
        self.sloads = [None] * n
        self.sindex = [None] * n
        self.sloads[0] = [0]
        self.sindex[0] = {0: 0}
        nstates = 1
        self.groups = []
        for q in range(n):
            if self.sloads[q] is None:
                raise RuntimeError("trie order")
            Tq = total[q]
            for x, c in children[q].items():
                opts_all = []
                for a in self.sloads[q]:
                    b = Tq - a
                    o1 = min(a + x, b)
                    o2 = a
                    opts_all.append((a, (o1, o2) if o1 != o2 else (o1,)))
                la = sorted({o for _, os in opts_all for o in os})
                self.sloads[c] = la
                self.sbase[c] = nstates
                self.sindex[c] = {a: nstates + i for i, a in enumerate(la)}
                nstates += len(la)
                for a, os in opts_all:
                    self.groups.append((self.sindex[q][a], c, [self.sindex[c][o] for o in os]))
        self.nstates = nstates
        self.snode = [0] * nstates
        self.sload = [0] * nstates
        for q in range(n):
            for a, i in self.sindex[q].items():
                self.snode[i] = q
                self.sload[i] = a
        self.terminals = [q for q in range(n) if term[q] >= 0]

    def cost_int(self, s):
        q = self.snode[s]
        a = self.sload[s]
        return max(a, self.total[q] - a)

    def best_response(self, w):
        n = len(self.parent)
        F = [None] * n
        wnode = [0] * n
        for q in self.terminals:
            wnode[q] = w.get(self.term[q], 0)
        for q in range(n - 1, -1, -1):
            Tq = self.total[q]
            vals = {}
            for a in self.sloads[q]:
                v = wnode[q] * max(a, Tq - a)
                b = Tq - a
                for x, c in self.children[q].items():
                    Fc = F[c]
                    o1 = min(a + x, b)
                    v1 = Fc[o1]
                    v2 = Fc[a]
                    v += v1 if v1 < v2 else v2
                vals[a] = v
            F[q] = vals
            for c in self.children[q].values():
                F[c] = None
        return F[0][0]

    def best_response_policy(self, w):
        n = len(self.parent)
        F = [None] * n
        choice = [None] * n
        wnode = [0] * n
        for q in self.terminals:
            wnode[q] = w.get(self.term[q], 0)
        for q in range(n - 1, -1, -1):
            Tq = self.total[q]
            vals = {}
            ch = {}
            for a in self.sloads[q]:
                v = wnode[q] * max(a, Tq - a)
                b = Tq - a
                for x, c in self.children[q].items():
                    o1 = min(a + x, b)
                    v1 = F[c][o1]
                    v2 = F[c][a]
                    if v1 <= v2:
                        v += v1
                        ch[(a, c)] = o1
                    else:
                        v += v2
                        ch[(a, c)] = a
                vals[a] = v
            F[q] = vals
            choice[q] = ch
        state = {0: 0}
        costs = {}
        stack = [0]
        while stack:
            q = stack.pop()
            a = state[q]
            if self.term[q] >= 0:
                costs[self.term[q]] = max(a, self.total[q] - a)
            for x, c in self.children[q].items():
                state[c] = choice[q][(a, c)]
                stack.append(c)
        return F[0][0], costs

    def expected_costs(self, pnum, Q):
        n = len(self.parent)
        depth = [0] * n
        for q in range(1, n):
            depth[q] = depth[self.parent[q]] + 1
        y = [0] * self.nstates
        y[0] = 1
        for g, (ps, c, cs) in enumerate(self.groups):
            yp = y[ps]
            if yp == 0:
                continue
            for k, cst in enumerate(cs):
                y[cst] += yp * pnum[g][k]
        out = {}
        for q in self.terminals:
            num = 0
            base = self.sbase[q]
            for i, a in enumerate(self.sloads[q]):
                num += y[base + i] * max(a, self.total[q] - a)
            out[self.term[q]] = Fraction(num, Q ** depth[q] * self.L)
        return out

def build_lp(cat):
    import numpy as np
    from scipy.sparse import coo_matrix
    S = cat.nstates
    groups = cat.groups
    E = sum(len(cs) for _, _, cs in groups)
    nv = S + E + 1
    vcol = S + E
    rows, cols, vals = [], [], []
    r = 0
    rows.append(r); cols.append(0); vals.append(1.0)
    r += 1
    inflow = [[] for _ in range(S)]
    e = S
    egroup = []
    for g, (ps, c, cs) in enumerate(groups):
        rows.append(r); cols.append(ps); vals.append(-1.0)
        for cst in cs:
            rows.append(r); cols.append(e); vals.append(1.0)
            inflow[cst].append(e)
            egroup.append(g)
            e += 1
        r += 1
    for s in range(1, S):
        rows.append(r); cols.append(s); vals.append(1.0)
        for ee in inflow[s]:
            rows.append(r); cols.append(ee); vals.append(-1.0)
        r += 1
    neq = r
    A_eq = coo_matrix((vals, (rows, cols)), shape=(neq, nv)).tocsr()
    b_eq = np.zeros(neq)
    b_eq[0] = 1.0
    rows, cols, vals = [], [], []
    L = float(cat.L)
    for i, q in enumerate(cat.terminals):
        base = cat.sbase[q]
        for k, a in enumerate(cat.sloads[q]):
            rows.append(i); cols.append(base + k); vals.append(max(a, cat.total[q] - a) / L)
        rows.append(i); cols.append(vcol); vals.append(-1.0)
    A_ub = coo_matrix((vals, (rows, cols)), shape=(len(cat.terminals), nv)).tocsr()
    b_ub = np.zeros(len(cat.terminals))
    c = np.zeros(nv)
    c[vcol] = 1.0
    return c, A_ub, b_ub, A_eq, b_eq, E

def round_prior(mu, den):
    tot = sum(mu.values())
    w = {}
    for k, m in mu.items():
        v = int(round(m / tot * den))
        if v > 0:
            w[k] = v
    return w

def solve(cat, method="highs", den=10 ** 9, Q=2 ** 40, upper=True, want_res=False):
    from scipy.optimize import linprog
    c, A_ub, b_ub, A_eq, b_eq, E = build_lp(cat)
    bounds = [(0, None)] * (A_eq.shape[1] - 1) + [(None, None)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method=method)
    if res.status != 0:
        raise RuntimeError(res.message)
    marg = -res.ineqlin.marginals
    mu = {cat.term[q]: float(marg[i]) for i, q in enumerate(cat.terminals) if marg[i] > 1e-12}
    w = round_prior(mu, den)
    lower = Fraction(cat.best_response(w), sum(w.values()) * cat.L)
    up = None
    pnum = None
    if upper:
        S = cat.nstates
        pnum = []
        e = S
        for g, (ps, cnode, cs) in enumerate(cat.groups):
            zz = [max(0.0, float(res.x[e + k])) for k in range(len(cs))]
            e += len(cs)
            tz = sum(zz)
            if tz <= 0:
                nums = [Q] + [0] * (len(cs) - 1)
            else:
                nums = [int(round(v / tz * Q)) for v in zz]
                nums[-1] = Q - sum(nums[:-1])
                if nums[-1] < 0:
                    nums[0] += nums[-1]
                    nums[-1] = 0
            pnum.append(nums)
        up = max(cat.expected_costs(pnum, Q).values())
    if want_res:
        return res.fun, lower, up, w, res, pnum
    return res.fun, lower, up, w

def solve_linear_exact(rows, nvar, init):
    piv = {}
    order = []
    for coef, rhs in rows:
        coef = dict(coef)
        for pv in order:
            if pv in coef:
                f = coef.pop(pv)
                pc, pr = piv[pv]
                for k, v in pc.items():
                    if k != pv:
                        nv = coef.get(k, 0) - f * v
                        if nv:
                            coef[k] = nv
                        else:
                            coef.pop(k, None)
                rhs -= f * pr
        coef = {k: v for k, v in coef.items() if v}
        if not coef:
            if rhs != 0:
                return None
            continue
        pv = max(coef, key=lambda k: abs(coef[k]))
        f = coef[pv]
        coef = {k: v / f for k, v in coef.items()}
        rhs = rhs / f
        for qv in order:
            qc, qr = piv[qv]
            if pv in qc:
                g = qc.pop(pv)
                for k, v in coef.items():
                    if k != pv:
                        nv = qc.get(k, 0) - g * v
                        if nv:
                            qc[k] = nv
                        else:
                            qc.pop(k, None)
                piv[qv] = (qc, qr - g * rhs)
        piv[pv] = (coef, rhs)
        order.append(pv)
    x = list(init)
    for pv in order:
        coef, rhs = piv[pv]
        x[pv] = rhs - sum(v * x[k] for k, v in coef.items() if k != pv)
    return x

def exact_upper(cat, res, tol_z=1e-10, tol_tight=1e-9, pden=10 ** 6):
    S = cat.nstates
    x = res.x
    ng = len(cat.groups)
    eoff = [0] * (ng + 1)
    e = S
    for g, (ps, c, cs) in enumerate(cat.groups):
        eoff[g] = e
        e += len(cs)
    vfloat = float(x[e])
    gidx = {}
    for g, (ps, c, cs) in enumerate(cat.groups):
        gidx[(ps, c)] = g
    param = {}
    sup = [None] * ng
    for g, (ps, c, cs) in enumerate(cat.groups):
        zz = [float(x[eoff[g] + k]) for k in range(len(cs))]
        s_ = [k for k in range(len(cs)) if zz[k] > tol_z]
        sup[g] = s_
        if len(s_) == 2:
            param[g] = len(param)
    npar = len(param)
    VAR_V = npar
    slack = {}
    for i, q in enumerate(cat.terminals):
        base = cat.sbase[q]
        ec = sum(float(x[base + k]) * max(a, cat.total[q] - a) for k, a in enumerate(cat.sloads[q])) / cat.L
        slack[q] = vfloat - ec
    tight = [q for q in cat.terminals if slack[q] < tol_tight]
    rows = []
    for q in tight:
        path = []
        n = q
        while n != 0:
            path.append(n)
            n = cat.parent[n]
        path.reverse()
        forms = {0: {-1: Fraction(1)}}
        prev = 0
        for n in path:
            new = {}
            for s, f in forms.items():
                g = gidx[(s, n)]
                ps, c, cs = cat.groups[g]
                sp = sup[g]
                if len(sp) == 0:
                    sp = [0]
                if len(sp) == 1:
                    tgt = cs[sp[0]]
                    d = new.setdefault(tgt, {})
                    for k, v in f.items():
                        d[k] = d.get(k, 0) + v
                else:
                    pi = param[g]
                    t1, t2 = cs[sp[0]], cs[sp[1]]
                    d1 = new.setdefault(t1, {})
                    d1[pi] = d1.get(pi, 0) + 1
                    d2 = new.setdefault(t2, {})
                    for k, v in f.items():
                        d2[k] = d2.get(k, 0) + v
                    d2[pi] = d2.get(pi, 0) - 1
            forms = new
            prev = n
        coef = {}
        for s, f in forms.items():
            cst = Fraction(cat.cost_int(s), cat.L)
            for k, v in f.items():
                if v:
                    coef[k] = coef.get(k, 0) + v * cst
        rhs = -coef.pop(-1, 0)
        coef[VAR_V] = Fraction(-1)
        rows.append(({k: v for k, v in coef.items() if v}, rhs))
    init = [Fraction(0)] * (npar + 1)
    for g, pi in param.items():
        init[pi] = Fraction(float(x[eoff[g] + sup[g][0]])).limit_denominator(pden)
    init[VAR_V] = Fraction(vfloat).limit_denominator(pden)
    sol = solve_linear_exact(rows, npar + 1, init)
    if sol is None:
        return None
    v = sol[VAR_V]
    y = [Fraction(0)] * S
    y[0] = Fraction(1)
    probs = [None] * ng
    bad = 0
    for g, (ps, c, cs) in enumerate(cat.groups):
        yp = y[ps]
        sp = sup[g] if sup[g] else [0]
        pr = [Fraction(0)] * len(cs)
        if yp == 0:
            pr[sp[0]] = Fraction(1)
        elif len(sp) == 1:
            pr[sp[0]] = Fraction(1)
        else:
            t = sol[param[g]]
            p0 = t / yp
            if not (0 <= p0 <= 1):
                bad += 1
                p0 = min(max(p0, Fraction(0)), Fraction(1))
            pr[sp[0]] = p0
            pr[sp[1]] = 1 - p0
        probs[g] = pr
        for k, cst in enumerate(cs):
            if pr[k]:
                y[cst] += yp * pr[k]
    worst = Fraction(0)
    for q in cat.terminals:
        base = cat.sbase[q]
        ec = sum(y[base + k] * max(a, cat.total[q] - a) for k, a in enumerate(cat.sloads[q])) / cat.L
        worst = max(worst, ec)
    return worst, v, probs, bad, len(tight), npar

def strategy_records(cat, probs):
    y = [Fraction(0)] * cat.nstates
    y[0] = Fraction(1)
    pref = {0: ()}
    out = []
    for g, (ps, c, cs) in enumerate(cat.groups):
        if c not in pref:
            pref[c] = pref[cat.parent[c]] + (Fraction(cat.job[c], cat.L),)
        yp = y[ps]
        pr = probs[g]
        for k, cst in enumerate(cs):
            if pr[k]:
                y[cst] += yp * pr[k]
        if yp > 0:
            a = cat.sload[ps]
            out.append([[str(v) for v in pref[c]], str(Fraction(a, cat.L)), str(pr[0])])
    return out

def group_key(s):
    return tuple(s[:2])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("catalogs", nargs="+", help="one or more catalogs; several are joined (union)")
    ap.add_argument("--whole", action="store_true", help="also solve the whole catalog as one LP")
    ap.add_argument("--out")
    ap.add_argument("--method", default="highs-ds")
    ap.add_argument("--den", type=int, default=10 ** 9, help="common denominator of the rounded prior")
    ap.add_argument("--pden", type=int, default=2 ** 40, help="denominator Q of the rounded behavioral probabilities")
    ap.add_argument("--strategy-out", help="write the algorithm behind UPPER (behavioral probabilities)")
    ap.add_argument("--exact", action="store_true",
                    help="for groups whose rounded UPPER is not below 7/6, solve the vertex exactly")
    args = ap.parse_args()
    t0 = time.time()
    streams = []
    for path in args.catalogs:
        streams += read_catalog(path)
    print(f"catalogs {args.catalogs}: {len(streams)} streams, {len(set(streams))} distinct", flush=True)
    sev = Fraction(7, 6)
    if args.whole:
        cat = Catalog(streams)
        print(f"whole: L = {cat.L}, prefix nodes {len(cat.parent)}, states {cat.nstates}, groups "
              f"{len(cat.groups)}, infeasible {len(cat.infeasible)}", flush=True)
        t1 = time.time()
        fv, lo, up, w = solve(cat, args.method, args.den, args.pden)
        print(f"WHOLE: LP {fv!r}, LOWER {lo} = {float(lo)!r}, UPPER {float(up)!r} (UPPER - 7/6 = "
              f"{float(up - sev):.3e}), prior support {len(w)} [{time.time()-t1:.1f}s]", flush=True)
    groups = {}
    for s in sorted(set(streams)):
        groups.setdefault(group_key(s), []).append(s)
    rows = []
    strat_records = []
    for key, gs in sorted(groups.items()):
        t1 = time.time()
        if len(key) == 1:
            if not 0 < key[0] <= 1:
                print("ERROR: bad stream", key)
                sys.exit(2)
            rows.append((key, 1, float(key[0]), key[0], key[0], {}, None))
            continue
        gc = Catalog(gs)
        if gc.infeasible:
            print("ERROR: infeasible streams, e.g.", gc.infeasible[0])
            sys.exit(2)
        fv, lo, up, w, res, pnum = solve(gc, args.method, args.den, args.pden, True, True)
        probs = [[Fraction(v, args.pden) for v in nums] for nums in pnum]
        note = ""
        if args.exact and up >= sev:
            r = exact_upper(gc, res)
            if r is None:
                note = " EXACT: inconsistent tight system"
            else:
                worst, v, probs, bad, ntight, npar = r
                note = f" EXACT: v = {v}, max expected cost {worst} ({'<=' if worst <= sev else '>'} 7/6), " \
                       f"tight {ntight}, params {npar}, clipped {bad}"
                if worst < up:
                    up = worst
                    probs = r[2]
        prior = {tuple(Fraction(v, gc.L) for v in gc.streams[k]): wk for k, wk in w.items()}
        if args.strategy_out:
            strat_records.extend(strategy_records(gc, probs))
        rows.append((key, len(gc.streams), fv, lo, up, prior, gc.L))
        print(f"GROUP {tuple(str(a) for a in key)}: {len(gc.streams)} streams, states {gc.nstates}, LP {fv:.12f}, "
              f"LOWER {lo} ({float(lo):.12f}), UPPER - 7/6 = {float(up - sev):.3e}, prior support {len(w)}"
              f"{note} [{time.time()-t1:.1f}s]", flush=True)
    best = max(rows, key=lambda r: r[2])
    lo_all = max(r[3] for r in rows)
    up_all = max(r[4] for r in rows)
    print(f"SUMMARY: {len(rows)} groups (first two jobs); val(C) LP = {best[2]!r} at group "
          f"{tuple(str(a) for a in best[0])}; LOWER = {lo_all} = {float(lo_all)!r}; UPPER = {float(up_all)!r}; "
          f"UPPER <= 7/6: {up_all <= sev}; LOWER > 7/6: {lo_all > sev}; groups with LP > 7/6 - 1e-9: "
          f"{sum(1 for r in rows if r[2] > 7 / 6 - 1e-9)}; groups with exact UPPER < 7/6: "
          f"{sum(1 for r in rows if r[4] < sev)}", flush=True)
    srt = sorted(rows, key=lambda r: -r[2])
    print("top groups by LP value: " + "; ".join(f"{tuple(str(a) for a in r[0])} n={r[1]} {r[2]:.9f}"
                                                 for r in srt[:8]))
    if args.out:
        with open(args.out, "w") as f:
            json.dump({"catalogs": args.catalogs, "lower": str(lo_all), "upper": str(up_all),
                       "groups": [{"key": [str(a) for a in r[0]], "n": r[1], "lp": r[2], "lower": str(r[3]),
                                   "upper": str(r[4]), "L": r[6],
                                   "prior": [{"stream": [str(a) for a in st], "w": wk}
                                             for st, wk in sorted(r[5].items(), key=lambda t: -t[1])]}
                                  for r in rows]}, f)
    if args.strategy_out:
        with open(args.strategy_out, "w") as f:
            json.dump({"catalogs": args.catalogs, "upper": str(up_all),
                       "format": "[prefix including the job being placed, smaller load before it, "
                                 "probability of putting the job on the smaller bin]",
                       "records": strat_records}, f)
        print(f"strategy: {len(strat_records)} records -> {args.strategy_out}")
    print(f"total {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
