"""Replay the post-enumeration proof of f(14)=780 using Python's exact integers."""
import argparse
import json
from pathlib import Path
from collections import Counter
from itertools import combinations
from check import check,targets

def turn(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def chain(seq):
    h=[]
    for p in seq:
        while len(h)>1 and turn(h[-2],h[-1],p)<=0:
            h.pop()
        h.append(p)
    return len(h)-1

def profile(pts):
    assert len(pts)==len(set(pts))==14
    assert all(turn(*t)!=0 for t in combinations(pts,3))
    pts=sorted(pts)
    return [sum(chain(S)+chain(reversed(S))==k for S in combinations(pts,k)) for k in range(3,15)]

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('enumeration',type=Path)
    parser.add_argument('--certificates',type=Path,default=Path('exclusions-below780.jsonl'))
    args=parser.parse_args()
    lines=args.enumeration.read_text().splitlines()
    final=[l.split() for l in lines if l.startswith('14 ')]
    assert len(final)==1 and final[0][1:3]==['1','1'] and int(final[0][3])>=415
    assert lines[-1].startswith('Q+P ')
    d=targets(args.enumeration)
    lows={s for s,v in d.items() if v<780}
    seen=set()
    for l in args.certificates.read_text().splitlines():
        s,rr=json.loads(l)
        assert s in lows and s not in seen
        seen.add(s)
        check(s,rr)
    assert lows==seen
    pts=[tuple(map(int,l.split())) for l in Path('witness780-small.txt').read_text().splitlines()]
    v=profile(pts)
    assert sum(v)==780
    print('Excluded candidates:',sorted(Counter(d[s] for s in lows).items()))
    print('Exact witness profile:',v)
    print('Minimum: 780')
