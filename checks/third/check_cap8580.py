from cat_solver import *
from fractions import Fraction as F
from itertools import combinations
g=8580
r=(1325,1325,1186,1186,1047,1047)
A=r+(6208,6208,6208); B=r+(8580,8580,1464); C=r+(3558,7533,7533); D=r+(3558,8580,6486); E=r+(3558,5022,5022,5022)
S=[A,B,C,D,E]
print('feasible', [feasible(s,3,g) for s in S], [sum(s) for s in S])
w=(151718320467,176258792429,76869864428,52329577698,228588156539)
print('prior sum', sum(w), sum(w)==685764711561)
mw=min_weighted(S,3,w)
val=F(mw,sum(w)); print('prior lower bound (sizes)', val, val==F(2356712165002156,228588237187))
print('of capacity', val/g, val/g==F(45321387788503,37717059135855), float(val/g))
fr=frontier(S,3)
print('Pareto-minimal', len(fr))
tight=[v for v in fr if F(sum(a*b for a,b in zip(w,v)),sum(w))==val]
print('tight', len(tight))
def solve(Am, b):
    n=len(Am); M=[[F(x) for x in row]+[F(y)] for row,y in zip(Am,b)]
    for c in range(n):
        p=next((i for i in range(c,n) if M[i][c]!=0),None)
        if p is None: return None
        M[c],M[p]=M[p],M[c]; M[c]=[x/M[c][c] for x in M[c]]
        for i in range(n):
            if i!=c and M[i][c]!=0: M[i]=[x-M[i][c]*y for x,y in zip(M[i],M[c])]
    return [M[i][n] for i in range(n)]
cnt=0
for sub in combinations(tight,5):
    Am=[[1]*5]+[[v[j] for v in sub] for j in range(4)]
    x=solve(Am,[1]+[val]*4)
    if x and min(x)>=0 and all(sum(xx*v[j] for xx,v in zip(x,sub))<=val for j in range(5)):
        cnt+=1
        if cnt<=2: print('lottery', sub, x)
print('lotteries found', cnt)
print('best single', min(max(v) for v in fr), float(F(min(max(v) for v in fr),g)))
