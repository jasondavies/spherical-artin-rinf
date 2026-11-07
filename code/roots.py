"""Root systems and permutation data for finite Coxeter groups (numerical, exact enough)."""
import numpy as np
phi=(1+5**.5)/2
def gram_cholesky(G): return [list(r) for r in np.linalg.cholesky(np.array(G,float))]
def E8simple():
    s=[[.5,-.5,-.5,-.5,-.5,-.5,-.5,.5],[1,1,0,0,0,0,0,0]]
    for i in range(6):
        v=[0]*8; v[i]=-1; v[i+1]=1; s.append(v)
    return s
def simple_roots(name):
    c=np.cos(np.pi/5)
    if name=='E8': return E8simple()
    if name=='E7': return E8simple()[:7]
    if name=='E6': return E8simple()[:6]
    if name=='F4': return [[0,1,-1,0],[0,0,1,-1],[0,0,0,1],[.5,-.5,-.5,-.5]]
    if name=='H3': return gram_cholesky([[1,-.5,0],[-.5,1,-c],[0,-c,1]])
    if name=='H4': return gram_cholesky([[1,-.5,0,0],[-.5,1,-.5,0],[0,-.5,1,-c],[0,0,-c,1]])
    if name[0]=='A':
        n=int(name[1:]); s=[]
        for i in range(n):
            v=[0]*(n+1); v[i]=1; v[i+1]=-1; s.append(v)
        return s
    if name[0]=='D':
        n=int(name[1:]); s=[]
        for i in range(n-1):
            v=[0]*n; v[i]=1; v[i+1]=-1; s.append(v)
        v=[0]*n; v[n-2]=1; v[n-1]=1; s.append(v); return s
    raise ValueError
def key(v): return tuple(np.round(v,5))
class Cox:
    def __init__(self,name):
        self.name=name
        S=[np.array(a,float) for a in simple_roots(name)]
        S=[a/np.linalg.norm(a)*np.sqrt(2) if name[0] in 'EAD' else a for a in S]
        self.S=S; n=self.n=len(S)
        def refl(a,v): return v-2*np.dot(a,v)/np.dot(a,a)*a
        roots=[s.copy() for s in S]; idx={key(r):i for i,r in enumerate(roots)}
        i=0
        while i<len(roots):
            for a in S:
                r=refl(a,roots[i]); k=key(r)
                if k not in idx: idx[k]=len(roots); roots.append(r)
            i+=1
        self.roots=roots; self.ridx=idx
        # permutations on roots
        self.gp=[np.array([idx[key(refl(a,r))] for r in roots]) for a in S]
        # reflections: pair root with its negative
        neg=np.array([idx[key(-r)] for r in roots])
        rid=-np.ones(len(roots),int); R=[]
        for i in range(len(roots)):
            if rid[i]<0: rid[i]=rid[neg[i]]=len(R); R.append(i)
        self.rid=rid; self.Rroot=R; self.N=len(R)
        self.rp=[np.array([rid[g[R[j]]] for j in range(self.N)]) for g in self.gp]  # rho(s_i) on R
        self.sidx=[rid[i] for i in range(n)]
        M=np.ones((n,n),int)
        for i in range(n):
            for j in range(n):
                if i!=j:
                    cc=-np.dot(S[i],S[j])/np.sqrt(np.dot(S[i],S[i])*np.dot(S[j],S[j]))
                    M[i,j]=int(round(np.pi/np.arccos(max(-1,min(1,cc)))))
        self.M=M
