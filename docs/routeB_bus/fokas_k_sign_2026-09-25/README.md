# Reproduce this mathematical checkpoint

Read REPORT.md and REVIEW.md for scope. The accepted cofinal sign remains OPEN.

From the repository root, using the existing numerical environment:

```sh
.venv/bin/python docs/routeB_bus/fokas_k_sign_2026-09-25/divided_difference_check.py
.venv/bin/python docs/routeB_bus/fokas_k_sign_2026-09-25/arb_m2_certificate.py
.venv/bin/python docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py --m 13 --dps 140
```

Observed versions: Python 3.13.0, mpmath 1.3.0, python-flint 0.8.0. No dependency was installed for this checkpoint.

Only arb_m2_certificate.py uses rigorous outward ball arithmetic; full_center_probe.py and rectangle_probe.py remain diagnostics. The Arb script overwrites its own JSON result beside the script. The command is a PAPER/computer-assisted calculation, not Lean kernel admission.

The source pin is ee99aacc for the mathematical verdict; b29b53e1 subsequently records the seventh already-sent Proshka request. That request was not duplicated here; c56ec1d9 subsequently recorded its completed RAW_R6 response, reconciled in REPORT.md. source_hashes.txt binds the consulted canonical definitions; FILE_SHA256SUMS binds this checkpoint's files.
