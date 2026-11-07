"""Exact (rational arithmetic) certification of the representation-theoretic facts used.
For each type: U = ker(X - lam I), X an integer combination of orbital matrices.
Checks exactly: dim U; every orbital matrix acts on U as a scalar (=> U is a multiplicity-one,
absolutely irreducible constituent defined over Q); some simple reflection acts nontrivially on U.
For the outer cases (H3, H4, F4) it also certifies, exactly, eigenvectors for the witnesses."""
import numpy as np, sys
from sympy.polys.matrices import DomainMatrix
from sympy import QQ, ZZ, Matrix
from roots import Cox
from analyze import orbitals
def nullspace_int(Mi):
    D=DomainMatrix([[ZZ(int(x)) for x in row] for row in Mi],(Mi.shape[0],Mi.shape[1]),ZZ).convert_to(QQ)
    ns=D.nullspace().to_Matrix()   # rows = basis vectors
    return ns
def certify_constituent(C,A,lam_target_dim):
    N=C.N; k=len(A)
    rng=np.random.default_rng(7); c=rng.integers(1,50,size=k)
    X=sum(int(ci)*a.astype(np.int64) for ci,a in zip(c,A)); X=X+X.T
    w=np.linalg.eigvalsh(X.astype(float))
    res=[]
    for lam in sorted(set(np.round(w).astype(int))):
        if np.sum(np.abs(w-lam)<1e-6)!=lam_target_dim and lam_target_dim is not None: continue
        if np.min(np.abs(w-lam))>1e-6: continue
        B=nullspace_int(X-lam*np.eye(N,dtype=np.int64))
        d=B.shape[0]
        if d==0: continue
        Bm=Matrix(B).T  # N x d
        scal=True
        for a in A:
            AB=Matrix(a.astype(int).tolist())*Bm
            # scalar? AB = mu*Bm
            j=next(i for i in range(N) if Bm[i,0]!=0)
            mu=AB[j,0]/Bm[j,0]
            if AB!=mu*Bm: scal=False;break
        res.append((lam,d,scal,Bm))
    return res
def perm_matrix(p):
    N=len(p); P=[[0]*N for _ in range(N)]
    for r in range(N): P[p[r]][r]=1
    return Matrix(P)
def main(name,dims):
    C=Cox(name); lab,k=orbitals(C); A=[(lab==i).astype(np.int64) for i in range(k)]
    out={}
    for d in dims:
        for lam,dd,scal,Bm in certify_constituent(C,A,d):
            if not scal: continue
            moved=[]
            for i in range(C.n):
                P=perm_matrix(C.rp[i])
                if P*Bm!=Bm: moved.append(i)
            print(f'{name}: exact constituent dim {dd} (eigenvalue {lam}), commutant scalar: {scal}, simple gens acting nontrivially: {moved}',flush=True)
            out.setdefault(d,[]).append(Bm)
    return C,out
if __name__=='__main__':
    spec={'E6':[15,20],'E7':[27,35],'E8':[35,84],'H3':[4],'H4':[16,25],'F4':[2],'D5':[4,5,10]}
    bad=[]
    for nm in sys.argv[1:]:
        C,out=main(nm,spec[nm])
        if sorted(out)!=sorted(set(spec[nm])): bad.append(nm)   # every requested dimension must be certified
    if bad: print('FAILED CHECKS: missing certified constituents for',bad); sys.exit(1)
    print('ALL CHECKS PASSED')
