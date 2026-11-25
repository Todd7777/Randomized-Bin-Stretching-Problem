# A third check of an algorithm: expected cost at most 7/6 on every stream of the catalog.
# python3 unioncheck.py ALGO.json CATALOG.json
import json, signal
from fractions import Fraction as F
signal.alarm(90)
import sys
R=None
d=json.load(open(sys.argv[1]))
P={}; dup=[]; conflict=[]
for pre,a,p in d['records']:
    k=(tuple(F(x) for x in pre),F(a)); p=F(p); assert 0<=p<=1;
    if k in P:
        dup.append((k,P[k],p))
        if P[k]!=p: conflict.append(k)
    P[k]=p
U=[tuple(F(x) for x in s) for s in json.load(open(sys.argv[2]))]
assert len(set(U))==len(U)
def feasible(s):
    S=sum(s); sums={F(0)}
    for x in s: sums|={a+x for a in sums}
    return S<=2 and any(S-1<=a<=1 for a in sums)
assert all(feasible(s) for s in U)
memo={(): {F(0):F(1)}}
missing=set()
def dist(pre):
    if pre in memo: return memo[pre]
    D=dist(pre[:-1]); S=sum(pre[:-1]); x=pre[-1]; nd={}
    for a,q in D.items():
        if (pre,a) not in P: missing.add((pre,a)); p=None
        else: p=P[(pre,a)]
        b=S-a
        for (lo,hi),w in (((a+x,b),p),((a,b+x),None if p is None else 1-p)):
            if w is None or w==0: continue
            k=min(lo,hi); nd[k]=nd.get(k,0)+q*w
    memo[pre]=nd; return nd
worst=F(0); tight=0
for s in U:
    D=dist(s); S=sum(s)
    c=sum(q*max(a,S-a) for a,q in D.items())
    if sum(D.values())!=1: print('mass',s);
    worst=max(worst,c); tight+= (c==F(7,6))
print('dups',len(dup),'conflicting',len(conflict), dup[:2])
print('streams',len(U),'records',len(P),'missing reached records',len(missing),'worst',worst,'<=7/6',worst<=F(7,6),'tight',tight)
massbad=sum(1 for s in U if sum(dist(s).values())!=1)
sys.exit(0 if not missing and not massbad and worst<=F(7,6) else 1)
