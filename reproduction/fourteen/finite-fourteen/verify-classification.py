"""Recount the unique minimizing witness and verify that all competing signs are impossible."""
from pathlib import Path
import argparse
from itertools import combinations
from importlib import util
from check import targets, verified
src=util.spec_from_file_location("result",Path(__file__).with_name('verify-result.py'))
result=util.module_from_spec(src)
src.loader.exec_module(result)
parser=argparse.ArgumentParser()
parser.add_argument("enumeration",type=Path)
parser.add_argument('--certificates',type=Path,default=Path('exclusions-through780.jsonl'))
args=parser.parse_args()
lines=args.enumeration.read_text().splitlines()
assert lines[-1].startswith('Q+P ')
header=next(line.split() for line in lines if line.startswith('14 '))
assert header[1:3]==['1','1'] and int(header[3])>=416
d=targets(args.enumeration)
seen=verified(args.certificates,d)
assert all(d[s]<=780 for s in seen)
pts=[tuple(map(int,l.split())) for l in Path('witness780-small.txt').read_text().splitlines()]
v=result.profile(pts)
assert v==[364,350,64,2]+[0]*8
s=''.join('1' if result.turn(*t)>0 else '0' for t in combinations(pts,3))
assert d[s]==780 and {s}=={k for k,n in d.items() if n<=780}-seen
print('Strictly smaller candidates excluded:',sum(d[x]<780 for x in seen))
print('Equality candidates excluded:',sum(d[x]==780 for x in seen))
print('Unique optimal order type, profile:',v)
# Count each convex polygon once toward each deletion that retains all its points.
survivors=[0]*14
for k in range(3,15):
    for ss in combinations(range(14),k):
        p=sorted(pts[i] for i in ss)
        if result.chain(p)+result.chain(reversed(p))==k:
            for i in range(14):
                if i not in ss:survivors[i]+=1
assert sorted(survivors)==[574,574,574,575,575,575,576,578,578,580,581,582,586,588]
print('One-point deletion totals:',sorted(survivors))
