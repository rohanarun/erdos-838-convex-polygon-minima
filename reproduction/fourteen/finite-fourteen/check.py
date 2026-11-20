"""Check exact GP contradictions attached to full 14-point sign signatures."""
import argparse
import json
from collections import Counter
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parent
INPUT = ROOT / "lower417.log"


def targets(path):
    counts = {}
    for line in path.read_text().splitlines():
        if line.startswith("TARGET "):
            _, q, p, larger, signature = line.split()
            assert len(signature) == 364 and set(signature) <= {"0", "1"}
            assert signature not in counts
            counts[signature] = 364 + int(q) + int(p) + int(larger)
    return counts


def check(bits, rows):
    assert rows
    signs = dict(zip(combinations(range(14), 3), (1 if x == "1" else -1 for x in bits)))
    balance = Counter()
    for a,b,c,d,e,major,minor,multiplicity in rows:
        assert len({a,b,c,d,e}) == 5
        assert all(isinstance(j,int) and 0 <= j < 14 for j in (a,b,c,d,e))
        assert major in range(3) and minor in range(3) and major != minor
        assert isinstance(multiplicity,int) and multiplicity > 0
        terms = (((a,b,c),(a,d,e)), ((a,b,d),(a,c,e)), ((a,b,e),(a,c,d)))
        products = [1,-1,1]
        for i, term in enumerate(terms):
            for t in term:
                products[i] *= signs[tuple(sorted(t))] * (-1)**sum(x>y for x,y in combinations(t,2))
        assert all(products[j] == -products[major] for j in range(3) if j != major)
        for i,m in ((major,multiplicity),(minor,-multiplicity)):
            for t in terms[i]:
                balance[tuple(sorted(t))] += m
    assert not any(balance.values())


def verified(path, expected):
    out = set()
    if path.exists():
        for line in path.read_text().splitlines():
            bits, rows = json.loads(line)
            assert bits in expected and bits not in out
            check(bits,rows)
            out.add(bits)
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=INPUT)
    parser.add_argument("--certificates",type=Path,default=ROOT/"proofs.jsonl")
    args = parser.parse_args()
    data = targets(args.input)
    seen = verified(args.certificates,data)
    print("polygon total / candidate types / excluded by certificates")
    for total in sorted(set(data.values())):
        print(total, sum(v==total for v in data.values()), sum(data[s]==total for s in seen))
