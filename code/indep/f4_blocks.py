import sys; sys.argv=['x']
exec(open('small_holonomy.py').read().split("if __name__")[0])
n,C,M,pos=roots('F4'); N=len(pos); idx={v:i for i,v in enumerate(pos)}
line=lambda v: idx[v] if v in idx else idx[neg(v)]
gens=[tuple(line(refl(i,v,C)) for v in pos) for i in range(n)]
# classes = orbits on R
orbs=[];seen=set()
for r in range(N):
    if r in seen: continue
    o={r};fr=[r]
    while fr:
        nf=[]
        for x in fr:
            for s in gens:
                if s[x] not in o:o.add(s[x]);nf.append(s[x])
        fr=nf
    orbs.append(sorted(o)); seen|=o
cls={r:k for k,o in enumerate(orbs) for r in o}
oid={};k=0
for a in range(N):
  for b in range(N):
    if (a,b) in oid: continue
    oid[(a,b)]=k;fr=[(a,b)]
    while fr:
      nf=[]
      for x,y in fr:
        for s in gens:
          z=(s[x],s[y])
          if z not in oid: oid[z]=k;nf.append(z)
      fr=nf
    k+=1
from collections import Counter
print("orbit sizes",[len(o) for o in orbs])
print("orbitals per block", Counter((cls[a],cls[b]) for (a,b),w in {v:k for k,v in {w:p for p,w in oid.items()}.items()}.items()))
