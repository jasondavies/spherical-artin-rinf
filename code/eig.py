"""For each type: find multiplicity-one rational constituents U of Q^R, and check the
eigenvalue conditions needed in the proof (inner and outer cases)."""
import numpy as np, sys, itertools
from roots import Cox
from pgrp import PermGroup, classes, center_size
from analyze import orbitals

def constituents(C):
    lab,k=orbitals(C)
    A=[(lab==i).astype(float) for i in range(k)]
    rng=np.random.default_rng(7); c=rng.integers(1,10**4,size=k).astype(float)
    X=sum(ci*a for ci,a in zip(c,A)); X=X+X.T
    w,V=np.linalg.eigh(X)
    out=[]; i=0; N=C.N
    while i<N:
        j=i
        while j<N and abs(w[j]-w[i])<1e-6*max(1,abs(w[i])): j+=1
        out.append((w[i],V[:,i:j])); i=j
    return A,out
def restrict(B,perm):
    P=np.zeros((len(perm),len(perm))); P[perm,np.arange(len(perm))]=1   # e_r -> e_{perm[r]}
    return B.T@P@B, np.linalg.norm(P@B-B@(B.T@P@B))
def has_eig(Mx,lam,tol=1e-7): return np.min(np.abs(np.linalg.eigvals(Mx)-lam))<tol
def main(name, do_outer):
    C=Cox(name); G=PermGroup(C.rp) if do_outer else None
    A,cons=constituents(C)
    # an irreducible constituent U is multiplicity one & rational iff eigenvalue of generic symmetric elt integral-ish and
    # the commutant acts on it by scalars: check each orbital matrix maps U into U and acts as scalar
    good=[]
    for ev,B in cons:
        d=B.shape[1]; scal=True; rat=True
        for a in A:
            Y=B.T@a@B
            if np.linalg.norm(a@B-B@Y)>1e-6 or np.linalg.norm(Y-Y[0,0]*np.eye(d))>1e-6: scal=False;break
            if abs(Y[0,0]-round(Y[0,0]))>1e-6: rat=False
        triv = d==1 and np.allclose(np.abs(B[:,0]),np.abs(B[0,0]))
        # support in which reflection classes
        supp=np.where(np.abs(B).sum(1)>1e-8)[0]
        print(f'  constituent dim {d}: commutant acts by scalars={scal}, rational eigenvalues={rat}, trivial={triv}, support size {len(supp)}')
        if scal and rat and not triv: good.append(B)
    print(' multiplicity-one rational nontrivial constituents: dims',[B.shape[1] for B in good])
    # inner case: need some simple s with rho_U(s) != id
    for B in good:
        moved=[i for i in range(C.n) if not np.allclose(restrict(B,C.rp[i])[0],np.eye(B.shape[1]))]
        print('   U dim',B.shape[1],': simple generators acting nontrivially on U:',moved)
    return C,G,good
def outer_check(name):
    from pgrp import aut_count
    C,G,good=main(name,True)
    _,_,tuples=aut_count(name)
    gidx=[G.index(g) for g in C.rp]
    E=G.E
    # find an outer tuple: not conjugate to the standard generators
    def is_inner(t):
        for x in range(G.order):
            P=E[x]; Pi=np.argsort(P)
            if all(np.array_equal(P[C.rp[i]][Pi], E[t[i]]) for i in range(C.n)): return True
        return False
    outer=None
    for t in tuples:
        if not is_inner(t): outer=t; break
    print(' outer automorphism images of simple gens (indices):',outer)
    th=G.extend([E[c] for c in outer])
    # theta as map on group indices; build reflection point -> group element of that reflection
    refl_el={}
    for x in range(G.order):
        P=E[x]; Pi=np.argsort(P)
        for i in range(C.n):
            p=P[C.sidx[i]]
            if p not in refl_el: refl_el[p]=G.index(P[C.rp[i]][Pi])
    el_refl={v:k for k,v in refl_el.items()}
    pi=np.array([el_refl[th[refl_el[p]]] for p in range(C.N)])
    # check pi realizes theta: pi rho(s) pi^-1 = theta(rho(s))
    pinv=np.argsort(pi)
    ok=all(np.array_equal(pi[C.rp[i]][pinv], E[th[gidx[i]]]) for i in range(C.n))
    print(' permutation pi of R realizing outer theta found, check:',ok)
    # which constituents does pi map to which
    for a,B in enumerate(good):
        for b,B2 in enumerate(good):
            P=np.zeros((C.N,C.N)); P[pi,np.arange(C.N)]=1
            if B.shape==B2.shape and np.linalg.norm(P@B-B2@(B2.T@P@B))<1e-6:
                print(f'   pi maps constituent {a} (dim {B.shape[1]}) onto constituent {b}')
    res={'pi':pi,'wit':[]}
    for a,B in enumerate(good):
        P=np.zeros((C.N,C.N)); P[pi,np.arange(C.N)]=1
        if np.linalg.norm(P@B-B@(B.T@P@B))<1e-6:
            # stable: need w with (rho(w) pi)|U having eig +1 and some with eig -1
            fp=fm=False
            for x in range(G.order):
                Mx,err=restrict(B,E[x][pi])
                if not fp and has_eig(Mx,1): fp=True; res['wit'].append(('stable',a,1,x))
                if not fm and has_eig(Mx,-1): fm=True; res['wit'].append(('stable',a,-1,x))
                if fp and fm: break
            print(f'   stable constituent {a} dim {B.shape[1]}: exists w with eig +1: {fp}, with eig -1: {fm}')
        else:
            # swapped: need for eps=+-1 a w with eps*(rho(w)pi)^2|U having eig 1
            fp=fm=False
            for x in range(G.order):
                Q=E[x][pi]; Q2=Q[Q]
                Mx,err=restrict(B,Q2); assert err<1e-6
                if not fp and has_eig(Mx,1): fp=True; res['wit'].append(('swap',a,1,x))
                if not fm and has_eig(Mx,-1): fm=True; res['wit'].append(('swap',a,-1,x))
                if fp and fm: break
            print(f'   swapped constituent {a} dim {B.shape[1]}: exists w with (rho(w)pi)^2|U eig +1: {fp}, eig -1: {fm}')
    return C,G,good,res
if __name__=='__main__':
    for nm in sys.argv[1:]:
        print('=====',nm)
        if nm in ('H3','H4','F4','D5','A3','D4x'): outer_check(nm)
        else: main(nm,False)
