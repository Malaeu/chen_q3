#!/bin/bash
# Reproduction of the parity-complete Legendre packet floor certificate
# (see LEGENDRE_PACKET_FLOOR_CERTIFICATE_REPORT_2026-09-07.md).
set -e
PY=/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/.venv/bin/python
cd "$(dirname "$0")"

$PY legarb.py            | tee out/profiles.txt   # rank, Gram, tails, exact identities
$PY legbudget.py 4000    | tee out/budget.txt     # eps_J, Tstar, analytic tail matrix

# main run, two bands (the second is the extension that buys the frequency tail)
$PY legcert.py    0 4000 0.5 36 3.0 22 out/main_0_4000.txt
$PY legcert.py 4000 6000 0.5 36 3.0 22 out/main_4000_6000.txt

# second quadrature on [0,1000] with an entirely different rule
$PY legcert.py    0 1000 0.4 28 2.8 22 out/xcheck.txt

# post-hoc rho-optimized Bernstein bound over the whole band [0,6000]
$PY legequad.py 0 6000 0.5 36 22 3.0 3.4 3.6 3.8 3.9 4.0 | tee out/equad.txt

$PY legassemble.py 6000 90 out/main_0_4000.txt out/main_4000_6000.txt | tee out/assemble.txt
$PY legverify.py 6000 out/xcheck.txt out/main_0_4000.txt out/main_4000_6000.txt \
    | tee out/verify.txt
