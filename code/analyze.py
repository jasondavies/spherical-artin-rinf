import numpy as np, sys
from roots import Cox
def orbitals(C):
    N=C.N; lab=-np.ones((N,N),int); k=0
    for a in range(N):
        for b in range(N):
            if lab[a,b]<0:
                stack=[(a,b)]; lab[a,b]=k
                while stack:
                    x,y=stack.pop()
                    for p in C.rp:
                        u,v=p[x],p[y]
                        if lab[u,v]<0: lab[u,v]=k; stack.append((u,v))
                k+=1
    return lab,k
def run(name):
    C=Cox(name); lab,k=orbitals(C)
    A=[(lab==i).astype(float) for i in range(k)]
    comm=all(np.allclose(X@Y,Y@X) for X in A for Y in A)
    rng=np.random.default_rng(0); c=rng.integers(1,1000,size=k)
    Mx=sum(ci*X for ci,X in zip(c,A))
    ev=np.linalg.eigvals(Mx)
    vals,counts=np.unique(np.round(ev.real,4),return_counts=True)
    print(name,'|R|=',C.N,'rank(orbitals)=',k,'commutant commutative:',comm)
    print('   eigenvalue multiplicities of generic commutant elt:',list(zip(vals,counts)))
    # integrality of eigenvalues of each orbital matrix
    for i,X in enumerate(A):
        e=np.unique(np.round(np.linalg.eigvals(X).real,4))
        print('   orbital',i,'valency',int(X[0].sum()),'eigs',e)
if __name__=="__main__":
    for nm in sys.argv[1:]: run(nm)
