The 14-point case of Erdős–Hammer problem 838
Rohan Arun, Super Powers AI

There are at least 780 convex polygons, attained by one order type up to relabeling and reflection. The proof and counting conventions are in finite-fourteen/result.txt. No optimizer is needed for verification.

Quick exact checks using the archived enumeration, from the unpacked root:
  cd finite-fourteen
  python3 -B verify-classification.py parallel417.log --certificates compact-through780.jsonl
  python3 -B verify-result.py threshold415.log --certificates compact-below780.jsonl
  cd ..
  python3 -B finite-fourteen-realizations/verify-optimum.py

To regenerate the larger enumeration from a triangle, use a C++17 compiler with threads. From finite-fourteen:
  c++ -O3 -std=c++17 -pthread packed-parallel.cpp -o enumerate
  ./enumerate 14 417 > fresh.log
  cmp fresh.log parallel417.log
  python3 -B verify-classification.py fresh.log --certificates compact-through780.jsonl

The slower reference entry point is certificate.cpp. The search is exhaustive by deletion, radial-sector extension, and the support criterion described in result.txt. The Lean components were checked separately. The complete enumeration is an external C++ computation.

The earlier 12- and 13-point paper and code are at https://doi.org/10.5281/zenodo.24388070 .
