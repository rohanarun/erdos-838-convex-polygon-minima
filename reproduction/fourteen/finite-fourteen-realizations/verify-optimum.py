"""Independent integer check of the 14-point upper bound and its deletion deck."""
from collections import Counter
from itertools import combinations
from pathlib import Path


def area(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def profile_and_deck(points):
    n = len(points)
    orient = {t: area(*(points[i] for i in t)) for t in combinations(range(n), 3)}
    assert all(orient.values())
    # Four affine circuit coefficients have signs +,-,+,- times the
    # opposite areas. A two-and-two split characterizes a convex four-set.
    forbidden = []
    for quad in combinations(range(n), 4):
        signs = [(-1)**i * orient[quad[:i] + quad[i+1:]] for i in range(4)]
        if sum(s>0 for s in signs) != 2:
            forbidden.append(sum(1<<i for i in quad))
    profile, deck = Counter(), [0]*n
    hexagons = []
    for mask in range(1<<n):
        size = bin(mask).count("1")
        if size<3 or any(mask & q == q for q in forbidden):
            continue
        profile[size] += 1
        if size == 6:
            hexagons.append(tuple(i for i in range(n) if mask >> i & 1))
        for i in range(n):
            if not (mask >> i & 1):
                deck[i] += 1
    return profile, sorted(deck), hexagons


if __name__ == "__main__":
    source = Path(__file__).resolve().parents[1] / "finite-fourteen" / "witness780-small.txt"
    points = [tuple(map(int,line.split())) for line in source.read_text().splitlines()]
    profile, deck, hexagons = profile_and_deck(points)
    assert profile == {3:364,4:350,5:64,6:2}
    assert deck == [574,574,574,575,575,575,576,578,578,580,581,582,586,588]
    print("Polygon profile:", sorted(profile.items()))
    print("Total polygons:", sum(profile.values()))
    print("Two hexagons (labels start at zero):", hexagons)
    print("Single-deletion totals:", deck)
