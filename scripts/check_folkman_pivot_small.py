#!/usr/bin/env python3
"""Exact finite regression for the Folkman atom-grid pivot formula.

Includes zero rings, empty common bases, and atoms outside the base.
All source pairing evaluations are checked, not just basis entries.
"""
from itertools import product

def diagrams():
    for a in (0, 1):
        for b in (0, 1, 2):
            for c in (0, 1, 2):
                for f in product(range(-1, a), repeat=b):
                    for g in product(range(-1, a), repeat=c):
                        if all(i in f and i in g for i in range(a)):
                            yield (a, b, c, f, g)

def diagram(d):
    a, b, c, f, g = d
    omega = [('grid',i,j) for i in range(b) for j in range(c)
             if f[i] >= 0 and f[i] == g[j]]
    omega += [('B',i) for i in range(b) if f[i] == -1]
    omega += [('C',j) for j in range(c) if g[j] == -1]
    pb = {i: (('grid',i,g.index(f[i])) if f[i]>=0 else ('B',i))
          for i in range(b)}
    pc = {j: (('grid',f.index(g[j]),j) if g[j]>=0 else ('C',j))
          for j in range(c)}
    pa = {i: ('grid',f.index(i),g.index(i)) for i in range(a)}
    def embedding(side,x):
        if side=='B':
            return frozenset(t for t in omega if
                 (t[0]=='grid' and (x>>t[1])&1) or
                 (t[0]=='B' and (x>>t[1])&1))
        return frozenset(t for t in omega if
                 (t[0]=='grid' and (x>>t[2])&1) or
                 (t[0]=='C' and (x>>t[1])&1))
    def retract(side,X):
        return sum(1<<i for i,t in {'A':pa,'B':pb,'C':pc}[side].items() if t in X)
    def base(side,z):
        owner=f if side=='B' else g
        return sum(1<<i for i,v in enumerate(owner)
                   if v>=0 and (z>>v)&1)
    for side in ('B','C'):
        for x in range(1 << (b if side=='B' else c)):
            X=embedding(side,x)
            assert retract(side,X)==x
            opposite='C' if side=='B' else 'B'
            assert retract(opposite,X)==base(opposite,retract('A',X))
    return a,b,c,embedding,retract,base

def pairing(M,x,y,n,m):
    z=0
    for i in range(n):
        for j in range(m):
            if (x>>i)&1 and (y>>j)&1:
                z ^= (M>>(i*m+j))&1
    return z

def main():
    one=list(diagrams())
    assert len(one)==25
    total=compatible=incompatible=checked_b=checked_c=0
    for dl in one:
        al,bl,cl,il,rl,jl=diagram(dl)
        for dr in one:
            ar,br,cr,ir,rr,jr=diagram(dr)
            for mb in range(1 << (bl*br)):
                pb = tuple(tuple(pairing(mb,jl('B',1<<i),jr('B',1<<j),bl,br)
                         for j in range(ar)) for i in range(al))
                for mc in range(1 << (cl*cr)):
                    total+=1
                    pc = tuple(tuple(pairing(mc,jl('C',1<<i),jr('C',1<<j),cl,cr)
                         for j in range(ar)) for i in range(al))
                    if pb!=pc:
                        incompatible+=1
                        continue
                    compatible+=1
                    def extension(X,Y):
                        correction=0
                        for i in range(al):
                            for j in range(ar):
                                if rl('A',X)>>i&1 and rr('A',Y)>>j&1:
                                    correction ^= pb[i][j]
                        return (pairing(mb,rl('B',X),rr('B',Y),bl,br)
                             ^ pairing(mc,rl('C',X),rr('C',Y),cl,cr)
                             ^ correction)
                    for x in range(1<<bl):
                        for y in range(1<<br):
                            assert extension(il('B',x),ir('B',y)) == pairing(mb,x,y,bl,br)
                            checked_b+=1
                    for x in range(1<<cl):
                        for y in range(1<<cr):
                            assert extension(il('C',x),ir('C',y)) == pairing(mc,x,y,cl,cr)
                            checked_c+=1
    assert (total,compatible,incompatible,checked_b,checked_c)==(39661,25211,14450,351931,351931)
    print('Folkman pivot regressions passed: 625 diagrams, 39661 pairings,'
          ' 25211 compatible, 351931 source evaluations on each side')
if __name__=='__main__':
    main()
