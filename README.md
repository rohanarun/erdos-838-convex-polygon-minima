# Minimum numbers of convex polygons on twelve and thirteen points

**Rohan Arun · Super Powers AI**

Among twelve planar points with no three collinear, the minimum number of convex polygons is **408**. For thirteen points, the minimum is **570**, and exactly five order types attain it up to relabeling and reflection. A polygon is counted whenever its vertices are in convex position, regardless of other points inside it. [Paper (PDF)](minima.pdf) · [LaTeX source](minima.tex)

| Points | Minimum | Result |
| ---: | ---: | --- |
| 10 | 189 | Independent verification of Savova’s result |
| 11 | 283 | Independent verification of Savova’s result |
| 12 | 408 | Exact minimum |
| 13 | 570 | Exact minimum and classification of minimizers |

Nikol Savova obtained the ten-point minimum from the Graz order-type database and the eleven-point minimum by an extension argument. Her counting convention includes singletons and pairs, giving 244 and 349. The twelve- and thirteen-point values under that convention are 486 and 661. The asymptotic limit asked for in Erdős problem #838 remains open. [Savova’s paper and code](https://github.com/NikolSavova/erdos-838-convex-subsets) · [Erdős problem #838](https://www.erdosproblems.com/838)

## Video explainer

The narrated animation shows how the point sets determine convex polygons and illustrates the twelve- and thirteen-point minima. [Watch or download the MP4](https://github.com/rohanarun/erdos-838-convex-polygon-minima/releases/download/v1.0.0/erdos-838-explained.mp4) · [Animation source and rendering instructions](explainer/README.md) · [Release downloads](https://github.com/rohanarun/erdos-838-convex-polygon-minima/releases/tag/v1.0.0)

## Citation

Version 1.0.0 is archived under **10.5281/zenodo.24388070**. [Version DOI](https://doi.org/10.5281/zenodo.24388070) · [Citation metadata](CITATION.cff)

## Reproduce the results

Run the following commands with Python 3.8 or later and a GCC or Clang C++17 compiler.

```sh
cd reproduction
python3 replay.py
```

The program compiles the enumerator, regenerates every candidate, verifies the exact nonrealizability certificates, and recomputes the convex hull of every subset of each integer-coordinate witness. The thirteen-point search retains 625 signatures after the quadrilateral and pentagon bounds. One has a candidate total of 569 and ten have a candidate total of 570. Six exact product contradictions and five realizations account for all eleven. [Reproduction guide](reproduction/README.md)

The Lean companion checks the deletion counting identity, selected witnesses, determinant inequalities, and the finite certificate data. The written geometric completeness argument and executable enumeration supply the exhaustive lower bounds. [Lean replay instructions](lean-sources/README.md)

OpenAI Codex assisted with mathematical derivations, code, certificate generation, verification, and manuscript preparation. The included software uses the MIT license. [License](LICENSE)
