"""Exact certificates for the outer-automorphism cases (H3, H4, F4):
for each witness w found numerically, exhibit exactly a nonzero vector v in U with
  (rho(w) pi) v = eps v          (stable case), or
  (rho(w) pi)^2 v = eps v        (swapped case, F4),
where U = ker(X - lam I) is the certified constituent."""
import numpy as np, sys
from sympy.polys.matrices import DomainMatrix
from sympy import QQ, ZZ
from eig import outer_check, constituents
from analyze import orbitals
def nullity(Mi):
    D=DomainMatrix([[ZZ(int(x)) for x in row] for row in Mi],(Mi.shape[0],Mi.shape[1]),ZZ).convert_to(QQ)
    return D.nullspace().shape[0]
def pm(p):
    N=len(p); P=np.zeros((N,N),dtype=np.int64); P[p,np.arange(N)]=1; return P
for name in sys.argv[1:]:
    C,G,good,res=outer_check(name)
    lab,k=orbitals(C); A=[(lab==i).astype(np.int64) for i in range(k)]
    rng=np.random.default_rng(7); c=rng.integers(1,50,size=k)
    X=sum(int(ci)*a for ci,a in zip(c,A)); X=X+X.T
    lam_of=[]
    for B in good:
        Y=B.T@X@B; lam_of.append(int(round(Y[0,0])))
    pi=res['pi']; N=C.N; I=np.eye(N,dtype=np.int64)
    for kind,a,eps,x in res['wit']:
        Q=G.E[x][pi]
        if kind=='swap': Q=Q[Q]
        Mi=np.vstack([X-lam_of[a]*I, pm(Q)-eps*I])
        print(f'EXACT {name}: {kind} constituent {a} (dim {good[a].shape[1]}, X-eigenvalue {lam_of[a]}), eps={eps}: '
              f'dim ker(X-lam) = {nullity(X-lam_of[a]*I)}, common kernel dim = {nullity(Mi)}',flush=True)
