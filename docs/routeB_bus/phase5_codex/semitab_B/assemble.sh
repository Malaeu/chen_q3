#!/bin/bash
set -e
cd "$(dirname "$0")"
{
  cat table_head.md
  cat table_valid.md
  echo "## 5. S5 — the sign table"
  echo
  echo "### 5.1 REFERENCE: S = {infinity, 2}, lambda = 1 (T = W = 1, ell = 0), N = 8192"
  echo
  python3 mk_final.py main
  echo
  echo "### 5.2 Archimedean control S = {infinity}, lambda = 1, N = 8192"
  echo "(here L = D(v) - c_A ||v||^2; no prime term. This pair is EXACT in the model.)"
  echo
  python3 mk_final.py arch
  echo
  echo "### 5.3 S = {infinity, 2} at lambda = sqrt2 and lambda = 2, N = 8192"
  echo
  python3 mk_final.py lam
  echo
  echo "## 6. THEOREM_CONTROL_CC20"
  echo
  cat thm_head.md
  python3 mk_final.py thm
  echo
  echo "## 7. Convergence of the identity residual |N_S - E_S - L_S|"
  echo
  echo "Semilocal (S = {infinity, 2}), lambda = 1:"
  echo
  python3 mk_final.py conv
  echo
  echo "Archimedean control (S = {infinity}), lambda = 1 — the EXACT pair:"
  echo
  python3 mk_final.py conva
  echo
  echo "Read this pair of tables together: the archimedean residual falls by a factor ~0.62 per"
  echo "doubling of N (i.e. like delta^{1.4}, delta = 1/sqrt(2N)), so the identity"
  echo "L = N - E is confirmed as a converging numerical statement for the exact pair."
  echo "The semilocal residual falls only by ~0.85 and on several tests not at all: it is"
  echo "approaching a nonzero floor set by the 20-octave model defect of section 0."
  echo
  cat table_tail_draft.md
  cat table_concl.md
  cat sec10_head.md
  python3 mk_sec10.py
  cat sec10_tail.md
} > TABLE.md
echo "TABLE.md written: $(wc -l < TABLE.md) lines"
