# Exact minima for convex subsets of planar point sets

The count includes polygons with at least three vertices. Points are in general position. The minimum counts for 10, 11, 12 and 13 points are 189, 283, 408 and 570. Nikol Savova posted the ten- and eleven-point values on September 24, 2026. This code independently reproduces both and extends the computation to twelve and thirteen. [Savova’s earlier results](https://github.com/NikolSavova/erdos-838-convex-subsets)

## Replay

Extract the archive in a writable directory. From the extracted root run

```sh
python3 replay.py
```

Use Python 3.8 or newer and a C++17 compiler compatible with GCC or Clang. The command compiles the enumerator from source, checks the integer witnesses, regenerates every candidate list and compares the exact signatures against the certificates. It also checks the two smaller lower bounds with a separate Python implementation. No packages, network access, cached enumeration outputs or order-type databases are required. The full enumeration may take several minutes. Temporary compilation output is contained in the extracted directory and cleaned up afterward. Set CXX to choose a compiler.

For the quick witness and contradiction checks alone, run `python3 replay.py --quick`. A quick run omits the exhaustive lower bounds. The complete verification is the default.

## Why the enumeration covers realizable configurations

Write Q and P for the counts of convex quadrilaterals and pentagons. Summing Q after each single-point deletion counts each quadrilateral m−4 times. Likewise each pentagon occurs m−5 times. Thus a constraint A Q + B P ≤ T at size m guarantees at least one deletion satisfying a new weighted bound. For m≥6 the new weights before cancellation are A(m−5) and B(m−4), and the bound before cancellation is T(m−4)(m−5)/m. Divide by the greatest common divisor and round the bound down. At size five, average just Q to obtain the size-four bound. Growing all allowable chains back from a triangle therefore includes every realizable final counterexample up to relabeling and reflection.

At each old point i the direction to the new point lies between two successive lines through i and its old neighbors, treated as rays in both directions. Immediately on either side of ray ij only the sign involving ij can change. At the opposite direction the other signs reverse. The code includes all four cases and enforces sign reversal upon swapping i and j. For four planar points, the four affine-dependence coefficients sum to zero, ruling out identical signs. A two-positive/two-negative split means the four points are convex. A larger set is in convex position exactly when all its four-subsets are, by planar Carathéodory. These tests may retain nonrealizable patterns. The canonicalization only relabels points and optionally reverses all signs. For realizable patterns the angular order of the other vertices about each hull vertex, tested in both directions, is intrinsic; testing all hull pivots gives a full invariant up to relabeling and reflection.

The final twelve-point bound Q+P≤187 retains 92 signatures, six with total 407. The thirteen-point bound Q+P≤284 retains 625 signatures, one with total 569 and ten with total 570. The program regenerates the signatures before checking their exclusion or realization.

## The compact certificates

In each JSON Lines record the first entry encodes the determinant signs of all triples in ascending lexicographic order. Bit 1 means a positive determinant. Realization records append a list of labeled integer points. Each excluded-signature record appends rows [a,b,c,d,e,major,minor,weight], using zero-based labels and positive integer weights.

With bracket [abc] denoting the signed triangle determinant, the three products [abc][ade], −[abd][ace], [abe][acd] sum to zero. The row gives the index of the product with isolated sign and the index of one of the other two. Its magnitude is strictly larger. Multiplying the inequalities to their recorded powers gives an impossible strict inequality because every determinant's total exponent is identical on the two sides. The checker derives the signs and the exponent balance from each row. At thirteen points the six exclusions and five exactly realized signatures partition every candidate returned. The five witnesses have pairwise distinct canonical signatures.

The software and accompanying documentation are licensed under the included MIT license. All arithmetic used to decide the claims is integral.
