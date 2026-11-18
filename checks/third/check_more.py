import sys, json, time
from cat_solver import *
from fractions import Fraction as F
CATS = sys.argv[1]
r=(6,4,4,4,4,2)
S12=[r+(22,22,22), r+(3,1,2,30,30), r+(3,1,2,20,20,20), r+(3,1,5,29,28), r+(3,1,5,19,19,19),
     r+(3,1,14,30,18), r+(3,1,14,16,16,16), r+(3,1,14,24,24), r+(6,30,30), r+(6,20,20,20), r+(12,30,24), r+(12,18,18,18)]
print('12: feasible', all(feasible(s,3,30) for s in S12), set(sum(s) for s in S12))
w12=(315,379,179,180,122,36,45,3,60,30,298,300)
t=time.time(); mw=min_weighted(S12,3,w12); v12=F(mw,sum(w12))
print('12: prior bound (sizes)', v12, v12==F(23400,649), ' capacity', v12/30, float(v12/30), '%.1fs'%(time.time()-t))
d=json.load(open(CATS+'/r3_k12_cap30.json'))
print('12: file streams equal printed:', sorted(map(tuple,d['streams']))==sorted(S12), ' file value', d.get('value'))
d=json.load(open(CATS+'/r3_k6_cap51.json'))
print('6: keys', list(d.keys()))
S6=[tuple(s) for s in d['streams']]; print('6: streams', S6)
print('6: feasible', all(feasible(s,3,51) for s in S6))
pr=[F(x) for x in d['prior']]; den=1
import math
for q in pr: den=den*q.denominator//math.gcd(den,q.denominator)
w6=tuple(int(q*den) for q in pr)
v6=F(min_weighted(S6,3,w6),sum(w6))
print('6: prior bound', v6/51, v6/51==F(13666,11373), float(v6/51), ' file value', d.get('value'))
S7=[(1,1,2,2,3,4,4,4),(1,1,2,2,5,5,5),(1,1,2,2,7,1,7),(1,1,2,2,3,6,6),(1,1,2,2,6,7,2),(1,1,2,2,3,3,7,2)]
print('g7: feasible', all(feasible(s,3,7) for s in S7))
w7=(15,11,10,7,3,2)
v7=F(min_weighted(S7,3,w7),48)
fr7=frontier(S7,3)
print('g7: prior bound', v7/7, v7/7==F(403,336), ' Pareto', len(fr7))
tight=[v for v in fr7 if F(sum(a*b for a,b in zip(w7,v)),48)==v7]
print('g7: tight', tight)
