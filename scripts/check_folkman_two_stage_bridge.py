#!/usr/bin/env python3
"""Adversarial two-stage Folkman bridge semantics; not a Lean proof.

Stage 0 is a genuinely smaller non-unital Boolean ring presentation
embedded through partial atom owners; stage 1 is the full finite ambient
pairing. A global pairing-automorphism permutes the target copy.
The source and target diagrams must commute on every element and
each stage must reconstruct its exact finite pairing matrix.
"""
from itertools import permutations, product
from random import Random

if not __debug__:
    raise SystemExit('Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.')

rng=Random(20261108)

def image(x, owners):
    return sum(1 << j for j,i in enumerate(owners) if i>=0 and x & (1<<i))

def permute(x,p):
    return sum(1 << p[i] for i in range(len(p)) if x & (1<<i))

def pair(bits,nr,x,y):
    return sum((bits >> (i*nr+j))&1 for i in range(x.bit_length()) if x&(1<<i)
               for j in range(y.bit_length()) if y&(1<<j))%2

def owners(n,m):
    return [o for o in product(range(-1,n),repeat=m)
            if all(i in o for i in range(n))]

stats={'permutations':0,'two_stage_diagrams':0,'pairing':0,'ring_op':0,
       'zero_stage_sorts':0,'unowned':0}
for nl in range(4):
  for nr in range(4):
    for bits in range(1<<(nl*nr)):
      for pl in permutations(range(nl)):
        for pr in permutations(range(nr)):
          if any(pair(bits,nr,1<<i,1<<j)!=pair(bits,nr,1<<pl[i],1<<pr[j])
                 for i in range(nl) for j in range(nr)):
            continue
          stats['permutations']+=1
          ql=rng.randrange(nl+1)
          qr=rng.randrange(nr+1)
          ol=rng.choice(owners(ql,nl))
          or_=rng.choice(owners(qr,nr))
          stats['two_stage_diagrams']+=1
          stats['zero_stage_sorts']+=int(ql==0 or qr==0)
          stats['unowned']+=int(-1 in ol or -1 in or_)
          for x in range(1<<ql):
            sx=image(x,ol)
            tx=permute(sx,pl)
            for z in range(1<<ql):
              assert image(x^z,ol)==sx^image(z,ol)
              assert image(x&z,ol)==sx&image(z,ol)
              assert permute(image(x^z,ol),pl)==tx^permute(image(z,ol),pl)
              assert permute(image(x&z,ol),pl)==tx&permute(image(z,ol),pl)
              stats['ring_op']+=4
            for y in range(1<<qr):
              sy=image(y,or_)
              ty=permute(sy,pr)
              edge0=sum(pair(bits,nr,image(1<<i,ol),image(1<<j,or_))<<(i*qr+j)
                        for i in range(ql) for j in range(qr))
              assert pair(edge0,qr,x,y)==pair(bits,nr,sx,sy)
              assert pair(edge0,qr,x,y)==pair(bits,nr,tx,ty)
              stats['pairing']+=2
          for y in range(1<<qr):
            sy=image(y,or_)
            ty=permute(sy,pr)
            for z in range(1<<qr):
              assert image(y^z,or_)==sy^image(z,or_)
              assert image(y&z,or_)==sy&image(z,or_)
              assert permute(image(y^z,or_),pr)==ty^permute(image(z,or_),pr)
              assert permute(image(y&z,or_),pr)==ty&permute(image(z,or_),pr)
              stats['ring_op']+=4
assert stats['permutations']==1717
assert stats['pairing']>0 and stats['ring_op']>0
print(stats)
print('PASS two-stage finite bridge consistency; NOT Lean kernel certification')
