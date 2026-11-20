# Finite planar polygon minima: Lean companion

Use Lean 4.32.0 and mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`. With elan, Git, and an internet connection on a fresh checkout, run these commands in the extracted directory:

    lake exe cache get
    sh replay.sh

The first command obtains the pinned dependencies and mathlib objects. Alternatively, when the pinned dependencies have already been built, put the matching Lean binary on PATH, set MATHLIB_LEAN_PATH to their Lean module search path, and run the second command. The replay compiles every included Lean module from source into .replay within the extracted directory. The direct kernel computation of the thirteen-point profile can require several minutes and substantial memory. Each module prints its theorem axioms.

## Coverage

- FiniteWitnesses.lean and Witness13.lean check all triple determinants and the complete profiles for the stated integer witnesses of sizes 10, 11, 12 and 13. The count uses the forbidden concave-quadruple criterion. The witness totals for subsets of size at least three are 189, 283, 408 and 570.
- DeletionCount.lean proves the single-vertex deletion double count for subsets of fixed size.
- CompactCertificates.lean verifies, by finite evaluation, six strict signed-product certificates for the supplied twelve-point signatures. AreaIdentity.lean proves the area identity and the strict dominance of the isolated summand. ProductContradiction.lean proves the abstract contradiction for balanced positive products. These are separate checks at twelve points.
- Exclude569.lean and OtherExclusions.lean prove the nonrealizability over the reals of six explicit thirteen-point signatures, one with count 569 and five with count 570.

The exhaustive deletion search, signature enumeration and complete global minimum theorems are outside the Lean development. Those parts are covered separately in the manuscript and its computational reproduction archive.

## License

The original companion code is distributed under the MIT license in LICENSE. Lean, mathlib, and their dependencies are distributed separately under their own licenses.
