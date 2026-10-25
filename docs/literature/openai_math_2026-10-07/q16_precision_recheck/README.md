# Q16 precision recheck, 2026-10-25

Finite diagnostic only, not interval proof or full CCM spectrum. The two original general-P cells are (m,M)=(16,2),(64,3); they are not the production small-epsilon schedule. All 10/27 nonzero von Mangoldt terms, proper powers, both times in Q_n, and every complex matrix entry are retained. Original projected seed is recomputed rather than promoting rounded float64 coefficients.

mpmath 1.3.0 at 80 and160 decimal digits gives respectively -0.5615919682926353073801519856641 and -0.6760833504086246251197418409862. Differences from saved float64 decimal values are about 2.07e-16 and6.25e-16. Precision drift is below5e-81. Root checked complete term recombination and contact residual below1e-150 at160digits; no interval enclosure is claimed. These two direct values show no catastrophic cancellation at the displayed accuracy. This does NOT audit all historical panels or certify packet quadrature; packet contacts are separately computed analytically by the script.

Run with /Users/emalam/GitHub/riemannn/riemann_env/bin/python ccm_q16_precision_recheck.py. Script retains its original absolute source and /tmp output paths for reproducibility; original Q16 files are unchanged. Tester q16_precision_recheck performed the run, root inspected formulas and checked saved output. No arithmetic exponent improved; Q24 is still pending and untouched.
