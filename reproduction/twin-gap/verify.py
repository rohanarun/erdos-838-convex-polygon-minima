"""Exact finite tests of the inward move in proof.txt. Run with Python 3."""
from fractions import Fraction
from itertools import combinations
from random import Random


def orient(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def hull_vertex_count(points):
    ordered = sorted(points)
    if len(ordered) < 3:
        return len(ordered)

    def chain_size(seq):
        chain = []
        for p in seq:
            while len(chain) > 1 and orient(chain[-2], chain[-1], p) <= 0:
                chain.pop()
            chain.append(p)
        return len(chain)

    return chain_size(ordered) + chain_size(reversed(ordered)) - 2


def configurations(n, rng):
    origin = (0, 0)
    body = []
    while len(body) < n - 2:
        p = (rng.randrange(1, 70), rng.randrange(-35, 36))
        if p in body or any(orient(a, b, p) == 0
                            for a, b in combinations([origin] + body, 2)):
            continue
        body.append(p)
    slopes = sorted(Fraction(y, x) for x, y in body)
    mid = len(slopes) // 2
    direction = (slopes[mid - 1] + slopes[mid]) / 2
    scale = 1
    while True:
        points = [(x * scale, y * scale) for x, y in body]
        old = [origin, (0, 1)] + points
        new = [origin, (direction.denominator, direction.numerator)] + points
        if all(orient(a, b, center) * orient(a, b, origin) > 0
               for center in [old[1], new[1]] for a, b in combinations(points, 2)):
            return old, new
        scale *= 2


def verify(old, new):
    n = len(old)
    assert all(orient(a, b, c) for s in [old, new] for a, b, c in combinations(s, 3))
    quad_loss = 0
    for size in range(3, n + 1):
        for labels in combinations(range(n), size):
            was_convex = hull_vertex_count([old[i] for i in labels]) == size
            is_convex = hull_vertex_count([new[i] for i in labels]) == size
            assert not is_convex or was_convex
            if was_convex != is_convex:
                assert 0 in labels and 1 in labels
                if size == 4:
                    quad_loss += 1
    assert quad_loss == (n - 2) ** 2 // 4


if __name__ == '__main__':
    rng = Random(838)
    for n in range(4, 11):
        for _ in range(9):
            verify(*configurations(n, rng))
    print('63 exact point-set tests passed for n = 4 through 10')
