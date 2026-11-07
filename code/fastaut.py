"""Faster brute-force |Aut(rho(W))| with vectorised homomorphism extension (BFS layers)."""
import numpy as np, sys, time
import pgrp
from pgrp import PermGroup, classes, center_size
from roots import Cox
def layers(G):
    depth=np.zeros(G.order,int)
    for x in range(1,G.order): depth[x]=depth[G.parent[x]]+1
    L=[]
    for d in range(1,depth.max()+1):
        for j in range(len(G.gens)):
            idx=np.where((depth==d)&(G.pgen==j))[0]
            if len(idx): L.append((idx,G.parent[idx],j))
    return L
def extend_fast(G,L,imgs,keyarr):
    n=G.order; F=np.empty((n,G.d),dtype=G.E.dtype); F[0]=np.arange(G.d)
    for idx,par,j in L: F[idx]=F[par][:,imgs[j]]
    for j,h in enumerate(imgs):
        if not np.array_equal(F[G.RM[:,j]], F[:,h]): return False
    # bijectivity: rows distinct and all in G (n distinct rows of a group closed set suffices: image is subgroup of size n)
    v=np.unique(F,axis=0)
    return len(v)==n
def run(name):
    t0=time.time(); C=Cox(name); G=PermGroup(C.rp); n=C.n

    L=layers(G)
    print(name,'|rho(W)|=',G.order,'|Z|=',center_size(G),flush=True)
    cl,reps=classes(G); csize=np.bincount(cl)
    ords=np.array([G.ordr(G.E[x]) for x in range(G.order)])
    gidx=[G.index(g) for g in C.rp]
    target=[csize[cl[g]] for g in gidx]
    cand=[np.where((ords==2)&(csize[cl]==target[i]))[0] for i in range(n)]
    M=C.M; total=0
    def ordprod(a,b): return ords[G.index(G.E[a][G.E[b]])]
    for r in reps:
        if ords[r]!=2 or csize[cl[r]]!=target[0]: continue
        cnt=0; tested=0
        def bt(i,cur):
            nonlocal cnt,tested
            if i==n:
                tested+=1
                if extend_fast(G,L,[G.E[c] for c in cur],None): cnt+=1
                return
            for c in cand[i]:
                if all(ordprod(cur[j],c)==M[j,i] for j in range(i)): bt(i+1,cur+[c])
        bt(1,[r]); total+=cnt*csize[cl[r]]
        print('  rep',r,'class size',csize[cl[r]],'tuples tested',tested,'automorphisms',cnt,flush=True)
    print('  |Aut|=',total,'|Inn|=',G.order//center_size(G),'|Out|=',total*center_size(G)//G.order,'time',round(time.time()-t0,1),flush=True)
for nm in sys.argv[1:]: run(nm)
