"""Search for a planar point set of N points with Q+P at most the supplied bound."""
from functools import cmp_to_key, lru_cache
from itertools import combinations

@lru_cache(None)
def tuples(n,r):
    return tuple(combinations(range(n),r))

def canonical(n,s):
    """Read the signed triples after radial sorting around each hull edge endpoint."""
    def sign(i,j,k):
        return s[tuple(sorted((i,j,k)))] ^ (((i>j)+(i>k)+(j>k))%2)
    candidates=[]
    for i in range(n):
        rest=[j for j in range(n) if j!=i]
        if not any(len({sign(i,j,k) for k in rest if k!=j})==1 for j in rest):
            continue
        rest.sort(key=cmp_to_key(lambda a,b: 1 if sign(i,a,b) else -1))
        for order in ([i]+rest,[i]+rest[::-1]):
            bits=''.join(str(sign(order[a],order[b],order[c])) for a,b,c in tuples(n,3))
            candidates.extend((bits,bits.translate(str.maketrans('01','10'))))
    return min(candidates) if candidates else ''.join(str(s[t]) for t in tuples(n,3))

def one_more(n,bits,q,p,A,B,max_cost):
    s=dict(zip(tuples(n,3),map(int,bits)))
    def sign(i,j,k):
        return s[tuple(sorted((i,j,k)))] ^ (((i>j)+(i>k)+(j>k))%2)
    rows=[]
    for i in range(n):
        patterns=set()
        for j in range(n):
            if i==j: continue
            mask=sum(sign(i,k,j)<<k for k in range(n) if k not in (i,j))
            rev=((1<<n)-1)^(1<<i)^(1<<j)
            patterns.update((mask,mask^(1<<j),mask^rev,mask^rev^(1<<j)))
        rows.append(sorted(patterns))
    quads=[u for u in tuples(n,4) if sum(s[t] for t in combinations(u,3))%2==0]
    assert len(quads)==q
    # A bit in each domain indexes one possible ray sector at that point.
    domains=[(1<<len(row))-1 for row in rows]
    zeros=[[sum(1<<v for v,row in enumerate(rows[j]) if not (row>>i&1)) for j in range(n)] for i in range(n)]
    choice=[]
    def visit(i,allowed):
        if i<n:
            options=allowed[i]
            while options:
                low=options&-options
                options-=low
                row=rows[i][low.bit_length()-1]
                new=allowed[:]
                for j in range(i+1,n):
                    valid=zeros[i][j] if (row>>j&1) else ~zeros[i][j]
                    new[j]&=valid
                    if not new[j]: break
                else:
                    choice.append(row)
                    yield from visit(i+1,new)
                    choice.pop()
            return
        new_quads=set()
        for t in tuples(n,3):
            a,b,c=t
            coeff=(choice[b]>>c&1)+(1^(choice[a]>>c&1))+(choice[a]>>b&1)+(1^s[t])
            if coeff in (0,4): return
            if coeff==2: new_quads.add(t)
        Q=q+len(new_quads)
        if A*Q+B*p>max_cost: return
        P=p+sum(all(t in new_quads for t in combinations(u,3)) for u in quads)
        if A*Q+B*P>max_cost: return
        signs=s.copy()
        for a,b in tuples(n,2):
            signs[a,b,n]=choice[a]>>b&1
        yield canonical(n+1,signs),(Q,P)
    yield from visit(0,domains)

import sys
from math import gcd
N=int(sys.argv[1])
bound=int(sys.argv[2])
A=B=1
rules={N:(A,B,bound)}
for m in range(N,5,-1):
    a,b=A*(m-5),B*(m-4)
    g=gcd(a,b)
    bound=bound*(m-5)*(m-4)//(m*g)
    A,B=a//g,b//g
    rules[m-1]=(A,B,bound)
A,B,T=rules[5]
rules[4]=(1,0,T//(5*A))
print(rules,flush=True)
seeds={'0':(0,0)}
for m in range(4,N+1):
    A,B,T=rules[m]
    out={}
    for bits,(q,p) in seeds.items():
        for signature,counts in one_more(m-1,bits,q,p,A,B,T):
            assert signature not in out or out[signature]==counts
            out[signature]=counts
    seeds=out
    print(m,'points,',len(seeds),'types passing',A,B,T,flush=True)
if seeds:
    print('minimum Q+P among candidates:',min(q+p for q,p in seeds.values()))
