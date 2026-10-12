# 1) Checks the type recursion (Lean `step`, `F`) against Hardin's b-file for A246479.
# 2) Checks numerically that row n satisfies the order-(2n+5) recurrence with characteristic
#    polynomial (1-x)^(n+4) (1+x)^(n+1) for n = 1..40 (conjectured for all n; proved in Lean for n <= 7).
# Usage: curl -sO https://oeis.org/A246479/b246479.txt && python3 check_bfile.py
from math import comb
b=[int(l.split()[1]) for l in open('b246479.txt') if l.strip() and not l.startswith('#')]
pos=[];d=1
while len(pos)<len(b):
    for n in range(1,d+1): pos.append((n,d+1-n))
    d+=1
def S(s,k,e):
    A,B,Bm,C,Cm,D,Dm,E,E1,E2,E3=s
    return A+e*Bm+(k-1-e)*B, C+D+e*E3+(k-3-e)*E, Dm+(k-1-e)*E1, Cm+(k-1-e)*E2
def step(s,k,e):
    A,B,Bm,C,Cm,D,Dm,E,E1,E2,E3=s; Sxx,Snm,Sxm,Sym=S(s,k,e)
    return (Sxx,Snm,Sym,Snm,Sxm,Sxx-B,Sxx-Bm,Snm-E,Snm-E3,Sxm-E1,Sym-E2)
def F(s,k,e):
    Sxx,Snm,Sxm,Sym=S(s,k,e)
    return e*(k+1-e)*Sxm+(k+1-e)*(Sxx+e*Sym+(k-1-e)*Snm)
def T(n,k):
    e=1-k%2; s=(1,)*11
    for _ in range(n): s=step(s,k,e)
    return F(s,k,e)
bad=[(n,k) for (n,k),x in zip(pos,b) if T(n,k)!=x]
print(len(b),'b-file terms checked; mismatches:',len(bad))
ok=True
for n in range(1,41):
    a=[1]
    for c in [(-1)**i*comb(n+4,i) for i in range(1,n+5)]: pass
    # coefficients of (1-x)^(n+4)(1+x)^(n+1)
    p=[0]*(2*n+6)
    for i in range(n+5):
        for j in range(n+2): p[i+j]+=(-1)**i*comb(n+4,i)*comb(n+1,j)
    d=2*n+5
    vals=[T(n,k) for k in range(0,d+25)]
    for j in range(d,len(vals)):
        if sum(p[i]*vals[j-i] for i in range(d+1))!=0: ok=False; print('fail',n,j)
print('row recurrences n=1..40 (k up to 2n+29):','OK' if ok else 'FAIL')
