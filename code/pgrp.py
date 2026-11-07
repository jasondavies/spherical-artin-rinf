"""Enumerate rho(W) (action of W on its reflections by conjugation, = W/Z(W)) and compute
Aut(rho(W)) / Inn by brute force over generating tuples."""
import numpy as np, sys, time
from roots import Cox
def compose(p,q):  # first q then p? we use x*y = x[y]  (apply y then x) ; acts on points
    return p[q]
class PermGroup:
    def __init__(self,gens):
        d=len(gens[0]); self.d=d; self.gens=[np.asarray(g) for g in gens]
        e=np.arange(d); idx={e.tobytes():0}; els=[e]; parent=[-1]; pgen=[-1]
        i=0
        while i<len(els):
            x=els[i]
            for j,g in enumerate(self.gens):
                y=x[g]            # y = x * g  (right multiplication)
                k=y.tobytes()
                if k not in idx: idx[k]=len(els); els.append(y); parent.append(i); pgen.append(j)
            i+=1
        self.E=np.array(els); self.idx=idx; self.parent=np.array(parent); self.pgen=np.array(pgen)
        self.order=len(els)
        self.RM=np.array([[idx[self.E[x][g].tobytes()] for g in self.gens] for x in range(self.order)])
    def index(self,p): return self.idx[np.asarray(p).tobytes()]
    def ordr(self,p):
        e=np.arange(self.d); q=p.copy(); k=1
        while not np.array_equal(q,e): q=q[p]; k+=1
        return k
    def extend(self,imgs):
        """try to extend s_i -> imgs[i] (as perms in this group) to a homomorphism; return image index array or None"""
        n=self.order; F=np.zeros((n,self.d),dtype=self.E.dtype); F[0]=np.arange(self.d)
        for x in range(1,n): F[x]=F[self.parent[x]][imgs[self.pgen[x]]]
        for j,h in enumerate(imgs):
            if not np.array_equal(F[self.RM[:,j]], F[:,h]): return None
        keys=[F[x].tobytes() for x in range(n)]
        try: im=np.array([self.idx[k] for k in keys])
        except KeyError: return None
        if len(set(im.tolist()))!=n: return None
        return im
def classes(G):
    # conjugacy classes by orbit of conjugation under generators
    n=G.order; cl=-np.ones(n,int); reps=[]; k=0
    inv=lambda p: np.argsort(p)
    ginv=[inv(g) for g in G.gens]
    for x in range(n):
        if cl[x]<0:
            cl[x]=k; reps.append(x); st=[x]
            while st:
                y=st.pop(); P=G.E[y]
                for g,gi in zip(G.gens,ginv):
                    z=G.index(gi[P[g]] if False else g[P[gi]])  # conj
                    if cl[z]<0: cl[z]=k; st.append(z)
            k+=1
    return cl,reps
def center_size(G):
    E=G.E; c=0
    for x in range(G.order):
        P=E[x]
        if all(np.array_equal(P[g],g[P]) for g in G.gens): c+=1
    return c
def aut_count(name, maxtime=3000):
    C=Cox(name); G=PermGroup(C.rp); n=C.n
    t0=time.time()
    print(name,"|rho(W)|=",G.order,"|Z(rho(W))|=",center_size(G),flush=True)
    cl,reps=classes(G); csize=np.bincount(cl)
    ords=np.array([G.ordr(G.E[x]) for x in range(G.order)])
    gidx=[G.index(g) for g in C.rp]
    # invariants of generator images: order 2 and class size equal to that of s_i's class (automorphisms preserve class sizes)
    target=[csize[cl[g]] for g in gidx]
    cand=[np.where((ords==2)&(csize[cl]==target[i]))[0] for i in range(n)]
    M=C.M
    def ordprod(a,b): return ords[G.index(G.E[a][G.E[b]])]
    total=0; outer_examples=[]
    # h1 ranges over class reps with right invariants
    for r in reps:
        if ords[r]!=2 or csize[cl[r]]!=target[0]: continue
        cnt=0
        def bt(i,cur):
            nonlocal cnt
            if i==n:
                im=G.extend([G.E[c] for c in cur])
                if im is not None:
                    cnt+=1
                    if cl[cur[0]]!=cl[gidx[0]] or True: outer_examples.append(list(cur))
                return
            for c in cand[i]:
                ok=True
                for j in range(i):
                    if ordprod(cur[j],c)!=M[j,i]: ok=False;break
                if ok: bt(i+1,cur+[c])
        bt(1,[r])
        total+=cnt*csize[cl[r]]
        print('  h1 class rep',r,'class size',csize[cl[r]],'#autos with s1->rep:',cnt,flush=True)
    print('  |Aut(rho(W))| =',total,' |Inn| =',G.order,' |Out| =',total//G.order, 'time',round(time.time()-t0,1))
    return C,G,outer_examples
if __name__=='__main__':
    for nm in sys.argv[1:]: aut_count(nm)
