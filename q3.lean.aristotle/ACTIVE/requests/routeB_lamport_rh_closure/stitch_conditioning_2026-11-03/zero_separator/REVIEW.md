# Independent bounded diagnostic review

Reviewed scan_separator.py, aggregate.py, summary.json, the source method,
three shared-q saved residuals, and dimension/prefix bookkeeping across all
21,153 sectors. No blocking defect found in the main nontrivial-sector scan.

- Strict inclusion gamma<T gives exactly (gamma_last/Omega,
  gamma_next/Omega] for each prefix. The upper endpoint intersects kappa>=1
  when it is >=1. Quartet events add two real rows atomically, preserving
  skipped ranks. The dimensions q+r=m+1 and strictly increasing q check out
  for every recorded sector; all recorded sectors have 0<r<d.
- For critical-line rows, omitting the common nonzero Fourier scalar gives
  the same row span via the rational Cauchy row. The complex quartet scalar
  is retained before realification, and both real/imaginary rows are added.
  This is valid for the supplied nodes, assuming no exact carrier-frequency
  collision; it is not a claim about raw singular-value normalization.
- Twice-reorthogonalized MP row frames, then ordered full QR, preserve the
  cutoff prefixes. The reported largest float-frame orthogonality errors
  are about1.12e-15. The delta comparison is the full ||AQ||, not ||Q^T A Q||.
- Matching q against the older conditioning cells gives delta differences
  -4.86e-17 for zeta m40,q20; -2.78e-16 for plant m55,q31; and -7.53e-16
  for DH m80,q76. The last residual is at the float floor, as labeled.
- lambda_r uses zero-based r=dimJ, with the preferred frozen MP spectrum
  selected consistently with the count table. The rejection based on a
  nonpositive lambda_r or lambda_r<-lambda_0 is a valid necessary-condition
  rejection. It does not assume the false unconditional bound
  ||AQ||>=|lambda_0|. Conditional on ||AQ||<lambda_r, every negative
  magnitude must fit below lambda_r by singular-value minmax.
- Eigenvalues in (0,2) remain positive directions. The aggregation keeps
  this category separate from inertia at zero and from delta<2.

The supplied summary is internally consistent: kappa>=1 yields zeta105
YES, plant105 NO, DH m16–52 and54 YES,53 unresolved,55–120 NO.
For unrestricted positive kappa, zeta/DH105 YES each and plant43 YES.
These quantify only nontrivial sectors. q=0 has r=d and no lambda_r;
q>=d has J=0 and a vacuous residual, and is deliberately excluded.

The DH53 replay script initially used mpmath matrix index ev[-1], which
returns zero in this environment. The owner corrected it before the final
replay to ev[len(ev)-1]; the current script uses the valid last index.
The supplemental point-arithmetic residuals at q50/51/52 are respectively
1.24645e-11,4.04358e-14,7.44375e-17, substantially above the corresponding
lambda_r values. Its original MP matrix cache was not retrievable; this
is a recipe replay using the pinned unchanged dh_matrix.py, not a
byte-identical replay of the original cached MP A. Consequently baseline
DH53 remains unresolved, with supplemental NO_REPLAY_SUPPORTED evidence.
The source/order agreement is numerical, not an interval error bound.

All classifications remain finite numerical diagnostics, not certified
source signs, interval eigenvalue enclosures or route-state conclusions.
