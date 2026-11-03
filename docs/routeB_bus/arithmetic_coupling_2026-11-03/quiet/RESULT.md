Route B = CHALLENGER / NOT_RH. DIAGNOSTIC_NEVER_A_PROOF.

All570 literal-even kappa1 quiet frames are available for m16..300 in zeta and DH. Each frames/{world}_m{m}.npz contains Q spanning J and U spanning Jperp. INDEX.csv supplies q,r,strict cutoff T, method, zero-input hash and NPZ hash. No source matrix or new eigenproblem enters this construction.

Frames use768-bit MPFR orthogonalization and float64 storage. Maximum orthogonality errors are U:2.894e-15, Q:3.224e-15; maximum cross overlap is1.288e-15. Independent row/null pilots16,80,248,300 in both worlds agree within2.359e-15; normalized actual evaluation residual norm(EQ)/norm(E) is at most7.807e-16.

DH uses the complete900-height numerical census, including all off-line orbits strictly below each T. double2 uses the same saved zeta frames with label REFERENCE_Jζ; no matching altered-source zero census is asserted. See DEFINITION.md and aliases.json.

Reproduce pilots with `python build.py --m 16 80 248 300 --validate`, then `python build.py --all`, `python pilot_checks.py`, `python inventory.py`. QUIET_ZETA and QUIET_DH override zero-input paths; QUIET_DEPS overrides the trusted gmpy2 dependency directory. gcc,MPFR/GMP,numpy and scipy are required; no download or package installation occurs.

The570 compressed NPZ frames total141137827bytes. They are numerical intermediates with reproducible source and per-file hashes, not interval-certified projectors or ranks. Only complete-orbit counts determine q; no float SVD rank truncation is used.
