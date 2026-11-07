"""Sanity checks for the R_infinity argument for spherical Artin groups.
Builds W as a permutation group on reflections, the homomorphism
  f : A -> Z^R x| W,  f(s) = (e_s, s),
checks the braid relations, and checks the twisted-class invariant for
psi = conj_s o iota on random elements.  Also checks Delta^2 maps to 2*sum e_r,
and that in rho(s) some reflection is moved (2-cycle)."""
import numpy as np, itertools, random, sys
phi=(1+5**.5)/2
def cartan_roots(simple, gram):
    # generate root system by closure under simple reflections
    n=len(simple); S=[np.array(a,float) for a in simple]
    def refl(a,v): return v-2*np.dot(a,v)/np.dot(a,a)*a
    roots=[s.copy() for s in S]; seen={tuple(np.round(r,6)) for r in roots}
    i=0
    while i<len(roots):
        for a in S:
            r=refl(a,roots[i]); k=tuple(np.round(r,6))
            if k not in seen: seen.add(k); roots.append(r)
        i+=1
    return S,roots
def coxeter_from(simple):
    n=len(simple); S=[np.array(a,float) for a in simple]; M=np.ones((n,n),int)
    for i in range(n):
        for j in range(n):
            if i!=j:
                c=-np.dot(S[i],S[j])/np.sqrt(np.dot(S[i],S[i])*np.dot(S[j],S[j]))
                m=int(round(np.pi/np.arccos(max(-1,min(1,c))))); M[i,j]=m
    return M
def E8simple():
    s=[]
    s.append([.5,-.5,-.5,-.5,-.5,-.5,-.5,.5])
    s.append([1,1,0,0,0,0,0,0])
    for i in range(6): v=[0]*8; v[i]=-1; v[i+1]=1; s.append(v)
    # order: Bourbaki a1..a8 : a1=(.5,-.5..,.5), a2=e1+e2, a3=e2-e1, a4=e3-e2,...
    return s
types={}
e8=E8simple(); types['E8']=e8; types['E7']=e8[:7]; types['E6']=e8[:6]
types['F4']=[[0,1,-1,0],[0,0,1,-1],[0,0,0,1],[.5,-.5,-.5,-.5]]
types['H3']=[[2,0,0],[-phi,1,-1/phi],[0,-1,0]]  # check via coxeter matrix
types['H4']=[[(1+phi)/2*0+ .5*(1), -.5*phi, .5/phi*0 -.5/phi*0, 0]]
# standard H4 simple roots (Humphreys-like)
a=.5
types['H4']=[[a*phi, -a, -a/phi*0+a*(1/phi)*(-1)*(-1)*0, 0]]
del types['H4']
H4=[[ (phi)/2, -0.5, 0, (1/phi)/2*(-1)*-1 ]]
del H4
types['H4']=[[1,-1,0,0],[0,1,-1,0],[0,0,1,0],[-0.5,-0.5,-0.5,-0.5]]  # placeholder, fixed below
def h4():
    # simple roots for H4 from e.g. Coxeter: a1=(-1/2)(1,1,1,1)?? we search: use icosian construction
    # use known: a1=(0,0,0,2)? We'll construct by finding roots with the right Gram matrix numerically.
    c=np.cos(np.pi/5)
    G=np.array([[1,-.5,0,0],[-.5,1,-.5,0],[0,-.5,1,-c],[0,0,-c,1]])
    L=np.linalg.cholesky(G); return [list(r) for r in L]
def h3():
    c=np.cos(np.pi/5)
    G=np.array([[1,-.5,0],[-.5,1,-c],[0,-c,1]]); L=np.linalg.cholesky(G); return [list(r) for r in L]
types['H4']=h4(); types['H3']=h3()
def run(name):
    S,roots=cartan_roots(types[name],None)
    M=coxeter_from(S); n=len(S)
    # reflections = roots up to sign
    def key(r):
        r=r/np.linalg.norm(r)
        for x in r:
            if abs(x)>1e-7:
                if x<0: r=-r
                break
        return tuple(np.round(r,5))
    refl={}; Rlist=[]
    for r in roots:
        k=key(r)
        if k not in refl: refl[k]=len(Rlist); Rlist.append(r/np.linalg.norm(r))
    N=len(Rlist)
    def rmat(a): a=a/np.linalg.norm(a); return np.eye(len(a))-2*np.outer(a,a)
    Smat=[rmat(np.array(a,float)) for a in S]
    # permutation of reflections induced by simple reflection i: r -> s r s
    perm=[]
    for i in range(n):
        p=[refl[key(Smat[i]@r)] for r in Rlist]; perm.append(p)
    sidx=[refl[key(np.array(a,float))] for a in S]
    # group elements as permutations of R (faithful mod centre) plus matrix for W-part
    def mul(x,y): # (v,w)(v',w') with w as matrix, action on R via permutation from matrix
        v,w=x; v2,w2=y
        pw=permof(w)
        return (v+ v2[np.argsort(pw)] , w@w2)
    cache={}
    def permof(w):
        k=tuple(np.round(w,5).flatten())
        if k not in cache: cache[k]=np.array([refl[key(w@r)] for r in Rlist])
        return cache[k]
    # (w.v)_{w r w^-1} = v_r  => new[p[r]] = v[r] ; implement correctly:
    def act(w,v):
        p=permof(w); out=np.zeros_like(v); out[p]=v; return out
    def mul(x,y):
        v,w=x; v2,w2=y; return (v+act(w,v2), w@w2)
    def gen(i,eps=1):
        e=np.zeros(N,int); e[sidx[i]]=1
        if eps==1: return (e, Smat[i])
        return (-e, Smat[i])   # inverse of (e_s,s) is (-s.e_s, s) = (-e_s, s)
    D=len(S[0]); one=(np.zeros(N,int), np.eye(D))
    def word(w):
        x=one
        for (i,e) in w: x=mul(x,gen(i,e))
        return x
    ok=True
    for i in range(n):
        for j in range(i+1,n):
            m=M[i,j]
            w1=[((i,j)[k%2],1) for k in range(m)]; w2=[((j,i)[k%2],1) for k in range(m)]
            a,b=word(w1),word(w2)
            if not (np.array_equal(a[0],b[0]) and np.allclose(a[1],b[1])): ok=False
    # Delta^2 : full twist = (product of simple gens in Coxeter order)^h
    h=2*N//n
    c=word([(i,1) for i in range(n)])
    x=one
    for _ in range(h): x=mul(x,c)
    d2ok = np.allclose(x[1],np.eye(D)) and np.array_equal(x[0],2*np.ones(N,int))
    # ensure s=0, t neighbour
    s=0; t=[j for j in range(n) if M[0,j]>=3][0]
    sts=perm[s][sidx[t]]
    # psi = conj_s o iota ; f(iota(x)) = tau(f(x)), tau(v,w)=(-v,w)
    def fpsi(x):
        v,w=x; y=(-v,w); gs=gen(s,1); gsi=gen(s,-1); return mul(mul(gs,y),gsi)
    def inv(x):
        v,w=x; wi=np.linalg.inv(w); return (-act(wi,v), wi)
    random.seed(1); bad=0; tested=0
    for trial in range(3000):
        L=random.randint(0,12)
        xw=[(random.randrange(n),random.choice([1,-1])) for _ in range(L)]
        X=word(xw)
        k=random.randint(1,5)
        tk=word([(t,1)]*(2*k))
        y=mul(mul(X,tk),inv(fpsi(X)))
        if np.allclose(y[1],np.eye(D)):
            tested+=1
            F=y[0][sidx[t]]-y[0][sts]
            if F not in (0,2*k,-2*k): bad+=1
    print(name,'rank',n,'#refl',N,'braid rels ok',ok,'Delta^2->2*sum e_r',d2ok,
          'rho(s) moves t:',sts!=sidx[t],'random psi-tests',tested,'violations',bad)
for nm in ['H3','H4','F4','E6','E7','E8']: run(nm)
