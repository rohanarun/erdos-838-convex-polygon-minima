# Minimum numbers of convex polygons on twelve through fourteen points

**Rohan Arun · Super Powers AI**

The minimum number of convex polygons among planar points with no three collinear is **408** for twelve points, **570** for thirteen points, and **780** for fourteen points. Up to relabeling and reflection, five order types attain the thirteen-point minimum and one attains the fourteen-point minimum. A polygon is counted whenever its vertices are in convex position, regardless of other points inside it. [Paper (PDF)](minima.pdf) · [LaTeX source](minima.tex)

| Points | Minimum | Result |
| ---: | ---: | --- |
| 10 | 189 | Independent verification of Savova’s result |
| 11 | 283 | Independent verification of Savova’s result |
| 12 | 408 | Exact minimum |
| 13 | 570 | Five minimizing order types |
| 14 | 780 | One minimizing order type |

Nikol Savova obtained the ten-point minimum from the Graz order-type database and the eleven-point minimum by an extension argument. Her counting convention includes singletons and pairs, giving 244 and 349. The corresponding values for twelve, thirteen, and fourteen points are 486, 661, and 885. The asymptotic limit asked for in Erdős problem #838 remains open. [Savova’s paper and code](https://github.com/NikolSavova/erdos-838-convex-subsets) · [Erdős problem #838](https://www.erdosproblems.com/838)

## An obstruction at every size

An exterior twin pair consists of consecutive hull vertices that no line through two other points separates. For every $n\ge4$, such a pair forces at least $\lfloor(n-2)^2/4\rfloor$ polygons above the minimum. At fourteen points this gives a lower bound of **816** for configurations with a twin pair. Section 5 of the paper gives the proof. Savova previously checked the exclusion for six through eleven points. The general asymptotic limit remains open.

[Proof and relative bounds](reproduction/twin-gap/proof.txt) · [Exact-arithmetic verification script](reproduction/twin-gap/verify.py)

## Video explainer

The version 1.0.0 narrated animation shows how the point sets determine convex polygons and illustrates the twelve- and thirteen-point minima. [Watch or download the MP4](https://github.com/rohanarun/erdos-838-convex-polygon-minima/releases/download/v1.0.0/erdos-838-explained.mp4) · [Animation source and rendering instructions](explainer/README.md) · [Release downloads](https://github.com/rohanarun/erdos-838-convex-polygon-minima/releases/tag/v1.0.0)

## Citation

To cite the finite minima and the exterior-twin theorem, use version 1.2.0. The earlier Zenodo deposit covers the twelve- and thirteen-point results. [Version 1.2.0 release](https://github.com/rohanarun/erdos-838-convex-polygon-minima/releases/tag/v1.2.0) · [Citation metadata](CITATION.cff) · [Version 1.0.0 DOI](https://doi.org/10.5281/zenodo.24388070)

## Reproduce the results

For the results through thirteen points, run the following commands from the repository root with Python 3.8 or later and a GCC or Clang C++17 compiler.

```sh
cd reproduction
python3 replay.py
```

The program compiles the enumerator, regenerates every candidate, verifies the exact nonrealizability certificates, and recomputes the convex hull of every subset of each integer-coordinate witness. The thirteen-point search retains 625 signatures after the quadrilateral and pentagon bounds. One has a candidate total of 569 and ten have a candidate total of 570. Six exact product contradictions and five realizations account for all eleven. [Reproduction guide](reproduction/README.md)

For fourteen points, verify the archived enumeration and the integer-coordinate minimizer from the repository root.

```sh
cd reproduction/fourteen/finite-fourteen
python3 -B verify-classification.py parallel417.log --certificates compact-through780.jsonl
python3 -B verify-result.py threshold415.log --certificates compact-below780.jsonl
cd ..
python3 -B finite-fourteen-realizations/verify-optimum.py
```

Two C++17 implementations produced identical candidate lists. Four candidates had totals below 780 and thirteen had total 780. Sixteen determinant certificates exclude every candidate except the realized order type, which has 364 triangles, 350 quadrilaterals, 64 pentagons, and two hexagons. Removing any point leaves at least 574 convex polygons. The reproduction guide includes the commands to regenerate the enumeration. [Fourteen-point reproduction guide](reproduction/fourteen/README.txt) · [Proof and enumeration details](reproduction/fourteen/finite-fourteen/result.txt)

The Lean companion checks the deletion counting identity, selected witnesses, determinant inequalities, and finite certificate data. For fourteen points, it also checks the coordinate witness and all sixteen exclusions. The written geometric completeness argument and executable enumeration supply the exhaustive lower bounds. [Lean instructions through thirteen points](lean-sources/README.md) · [Fourteen-point Lean replay script](reproduction/fourteen/lean-sources/replay.sh)

OpenAI Codex assisted with mathematical derivations, code, certificate generation, verification, and manuscript preparation. The included software uses the MIT license. [License](LICENSE)
