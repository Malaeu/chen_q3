# Q2: simple-even, numerical quickcheck

**ζ: INCONCLUSIVE_RESOLUTION on the complete requested grid.** At the
resolvable smaller sizes the finite-matrix minimum is simple and even.
For m=30,40,47,55, the ζ minima/gaps reach the arithmetic floor at one or
both resolutions, so the apparent computed parity there is not scored.
This does not contradict or reproduce Botha's continuum assertion.

**DH: VIOLATED_AT m=55 in both finite resolutions.** At N=55,
(even0,odd0)=(-0.6639206460810498,-0.7129338188715162).
At N=110 the pair is (-0.7429143800841891,-0.7696188420487396).
The odd minimum is lower by 0.0490131727904664 and 0.0267044619645505,
respectively. Thus simple-even is not shared by every fake-world matrix.
At m=47 the doubled-resolution DH matrix also has an odd minimum, but the
N=47 matrix is positive and even: that case is resolution-sensitive.

**Planted: VIOLATED_AT m=5**, also at m=10,20,40, with odd minima at both
resolutions. For m=5, N=5 gives even0=-0.0212116279655747 and
odd0=-0.0265474486549359. Other requested sizes and both even gaps are
retained in `spectra.csv`; no eigenvalue is silently dropped.

The source is the full physical cosine/sine source form, including every
arithmetic atom within the window, the ζ pole with opposite even/odd signs,
and the DH odd-gamma factor without a pole. The planted definition is
exactly the pinned innovation scan:
`g_plant=g_zeta+4 Re[(cos(wt)-1)/w^2]`,
`w=2 pi/log(2)+i/4`. Differentiating gives the physical source-kernel
addition `-g_plant''+g_zeta''=4 Re cos(w(x-y))`; its parity matrices are
`4 Re(C C^T)` and `4 Re(S S^T)` for the cosine/sine transforms at w.
This fixes the odd-sector sign without borrowing an external formula.

Every requested m=3,5,7,10,15,20,30,40,47,55 is run at N=m and N=2m.
The low resolution uses 70 decimal digits and composite Gauss–Legendre
48 nodes ×8 panels; the high uses 90 digits and 80 nodes ×12 panels.
`spectra.csv` records even0, even1, odd0, both gaps and the arithmetic
precision guard. `resolution_comparison.csv` records the changes.
The guard is a numerical screening rule, not a quadrature error bound.
Finite eigenvalues can drift substantially as N doubles; no continuum
simplicity or spectral enclosure follows from these calculations.

Normalization: physical support is [-log(m)/2,log(m)/2], with orthonormal
real cosine/sine bases in L2. Botha's L is our log(m)/2. Thus m=47 has
halfwidth≈1.9251, near the registered-grid hole; m=55 has halfwidth≈2.0037,
slightly outside the externally claimed range L≤2. The fake-world tests
are discriminators, not counterexamples to a ζ-only external statement.

The external GitHub README is reachable and saved as `BOTHA_README.md`
(blob f18fa5e422e0488e82ef636e88480edd339dd2a4, accessed 2026-11-03).
It explicitly asserts L∈(0,2] for version2.0.0/DOI23852617 and discloses
the registered failure at L=1.92364501953125 plus post-hoc rule E. Its
code/certificates were not executed or trusted here. This is an independent
finite-source check, not an audit of their proof or a priority finding.

Run `python parity.py --factor 1 --dps 70 --order 48 --panels 8`, then
`python parity.py --factor 2 --dps 90 --order 80 --panels 12`, followed by
`python summarize.py` (mpmath required).

DIAGNOSTIC_NEVER_A_PROOF. Route B=CHALLENGER/NOT_RH. No route-state export.
