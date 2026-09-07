#!/bin/bash
# Reproduction of the packet floor certificate (see H4_PACKET_FLOOR_CERTIFICATE_REPORT_2026-09-07.md).
PY=/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/.venv/bin/python
cd "$(dirname "$0")"
$PY packarb.py                                   # profiles, Gram, tails, exact identities
$PY packbudget.py 4000                           # eps_J, Tstar, normalized tail matrix vs X
$PY packcert.py 4000 0.5 36 3.0 22 out/main.txt      # ~73 min, 22 processes
$PY packequad.py 4000 0.5 36 22 3.0 3.4 3.6 3.8 3.9 4.0   # post-hoc rho-optimized E_quad
$PY packcert.py 1000 0.4 28 2.8 22 out/xcheck.txt    # second quadrature on [0,1000]
$PY packassemble.py out/main.txt 4000 90 | tee out/assemble.txt
$PY packverify.py  out/main.txt out/xcheck.txt   | tee out/verify.txt
