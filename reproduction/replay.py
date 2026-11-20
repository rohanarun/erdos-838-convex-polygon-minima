"""Reproduce the exact minima for 10 through 13 points, including all 13-point minimizers."""
import argparse
from collections import Counter
from functools import cmp_to_key
from itertools import combinations
import json
from math import comb
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent
MINIMUM = {10: 189, 11: 283, 12: 408, 13: 570}


def records(filename):
    return [json.loads(line) for line in (ROOT / filename).read_text().splitlines()]


def determinant(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def hull(points):
    def half(ordered):
        chain = []
        for p in ordered:
            while len(chain) >= 2 and determinant(chain[-2], chain[-1], p) <= 0:
                chain.pop()
            chain.append(p)
        return chain[:-1]

    points = sorted(points)
    return half(points) + half(reversed(points))


def signature(points):
    areas = [determinant(*t) for t in combinations(points, 3)]
    assert 0 not in areas, "Three input points are collinear"
    return ''.join('1' if area > 0 else '0' for area in areas)


def canonical(points):
    keys = []
    for pivot in hull(points):
        rest = [p for p in points if p != pivot]
        rest.sort(key=cmp_to_key(lambda q, r: determinant(pivot, q, r)))
        for rays in (rest, rest[::-1]):
            bits = signature([pivot] + rays)
            keys.extend((bits, bits.translate(str.maketrans('01', '10'))))
    return min(keys)


def profile(n, points):
    assert len(points) == n and len({tuple(p) for p in points}) == n
    assert all(len(p) == 2 and all(type(x) == int for x in p) for p in points)
    signature(points)
    counts = [sum(len(hull(sub)) == k for sub in combinations(points, k)) for k in range(3, n+1)]
    assert sum(counts) == MINIMUM[n], (n, counts)
    print(f"{n} points: {counts} (total {sum(counts)})", flush=True)
    return counts


def check_certificate(n, bits, rows):
    assert len(bits) == comb(n, 3) and set(bits) <= {'0', '1'} and rows
    signs = dict(zip(combinations(range(n), 3), (1 if x == '1' else -1 for x in bits)))
    balance = Counter()
    for a, b, c, d, e, major, minor, weight in rows:
        assert len({a,b,c,d,e}) == 5 and all(type(j) == int and 0 <= j < n for j in (a,b,c,d,e))
        assert major in range(3) and minor in range(3) and major != minor
        assert type(weight) == int and weight > 0
        terms = (((a,b,c),(a,d,e)), ((a,b,d),(a,c,e)), ((a,b,e),(a,c,d)))
        products = [1, -1, 1]
        for j, pair in enumerate(terms):
            for t in pair:
                parity = sum(x > y for x,y in combinations(t, 2)) % 2
                products[j] *= (-1)**parity * signs[tuple(sorted(t))]
        assert all(products[j] == -products[major] for j in range(3) if j != major)
        for j, exponent in ((major, weight), (minor, -weight)):
            for t in terms[j]:
                balance[tuple(sorted(t))] += exponent
    assert not any(balance.values()), "The exponents do not cancel"


def finite_checks():
    for n in (10, 11, 12):
        p = [list(map(int, line.split())) for line in (ROOT / f'witness{n}.txt').read_text().splitlines()]
        profile(n, p)
    real = {}
    for bits, points in records('real13.jsonl'):
        assert bits not in real and signature(points) == canonical(points) == bits
        counts = profile(13, points)
        real[bits] = sum(counts)
    assert len(real) == 5
    impossible = {}
    for n in (12, 13):
        impossible[n] = set()
        for bits, rows in records(f'impossible{n}.jsonl'):
            assert bits not in impossible[n]
            impossible[n].add(bits)
            check_certificate(n, bits, rows)
        assert len(impossible[n]) == 6
        print(f"{n} points: checked six product contradictions", flush=True)
    assert not real.keys() & impossible[13]
    return real, impossible


def generated(exe, n, bound, env):
    output = subprocess.check_output([str(exe), str(n), str(bound)], env=env, text=True)
    candidates = {}
    stages = {}
    profiles = Counter()
    for row in output.splitlines():
        cells = row.split()
        if cells[0].isdigit():
            m, a, b, maximum, retained = map(int, cells)
            assert m not in stages
            stages[m] = (a,b,maximum,retained)
        elif cells[0] == 'TARGET':
            _, q, p, bigger, bits = cells
            assert len(bits) == comb(n, 3) and set(bits) <= {'0', '1'} and bits not in candidates
            total = comb(n, 3) + int(q) + int(p) + int(bigger)
            assert total <= comb(n, 3) + bound
            candidates[bits] = total
        else:
            assert cells[0::2] == ['Q+P','larger','types']
            q_plus_p, bigger, multiplicity = map(int, cells[1::2])
            profiles[comb(n, 3) + q_plus_p + bigger] += multiplicity
    assert set(stages) == set(range(4,n+1))
    assert stages[n][:3] == (1,1,bound)
    assert sum(profiles.values()) == stages[n][-1]
    assert {t:k for t,k in profiles.items() if t <= comb(n,3)+bound} == Counter(candidates.values())
    print(f"{n} points: retained {stages[n][-1]} signatures, candidate totals {dict(Counter(candidates.values()))}", flush=True)
    return candidates


def main():
    if not __debug__:
        raise SystemExit("Run Python without -O so every certificate assertion is active.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='check coordinates and sign certificates only')
    args = parser.parse_args()
    real, impossible = finite_checks()
    if args.quick:
        print("Quick checks passed. Exhaustive lower-bound generation skipped.")
        return
    compiler = shlex.split(os.environ.get('CXX','c++'))
    if not compiler or not shutil.which(compiler[0]):
        raise SystemExit("Install a GCC or Clang C++17 compiler, or set CXX to its command.")
    with TemporaryDirectory(dir=ROOT) as tmp:
        env = dict(os.environ, TMPDIR=tmp, TEMP=tmp, TMP=tmp, CLANG_MODULE_CACHE_PATH=tmp)
        exe = Path(tmp) / ('enumerate.exe' if os.name == 'nt' else 'enumerate')
        subprocess.run([*compiler, '-O3', '-std=c++17', str(ROOT/'enumerate.cpp'), '-o', str(exe)], env=env, check=True)
        for n, bound in ((10,68),(11,117)):
            assert generated(exe,n,bound,env) == {}
            output = subprocess.check_output([sys.executable,'-B',str(ROOT/'enumerate-small.py'),str(n),str(bound)],env=env,text=True)
            assert output.splitlines()[-1] == f'{n} points, 0 types passing 1 1 {bound}'
        c12 = generated(exe,12,187,env)
        assert set(c12) == impossible[12] and set(c12.values()) == {407}
        c13 = generated(exe,13,284,env)
        assert set(c13) == set(real) | impossible[13]
        assert Counter(c13.values()) == {569:1, 570:10}
        assert all(c13[s] == total for s,total in real.items())
    print("Full replay passed. Minima: 189, 283, 408, 570. Five 13-point minimizing order types up to relabeling and reflection.")


if __name__ == '__main__':
    main()
