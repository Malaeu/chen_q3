# Linear convolution alias return, 2026-10-07

Obstruction: after exact parity return, the complete signed residual on
(v,J_r v) has unestimated weighted even-prime correlations. The next linear
rewrite is Heath-Brown k3 on b<=m/U; long total product need not have a long
unweighted factor. Target and exact formula: PARITY_PRIME_AUDIT_2026-10-06.md,
Own next attempt, and Q10(13),(14),(26) in the source_observability bus.

Dictionaries searched: Heath-Brown identity; multilinear logarithmic phase;
Type III Dirichlet polynomial. All three shelf queries returned
ASK_STATUS: INCOMPLETE because semantic-index freshness validation failed.
This does not establish shelf absence. The bounded primary lookup below
checks the free-factor mechanism; it supplies no signed CCM closure.

## Verified partial mechanism, already covered by the accepted Arias bound

Olivier Robert, On van der Corput's k-th derivative test for exponential sums,
author-hosted PDF, https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf
Local: robert-vdc-2015.pdf
SHA-256: 755f6002a7daa97b6bf7531be69fcc6a69f8701a30c994ce9f57d101ed9acdea
§3.1 Theorem1, printed p5; proof mechanism §3.2, p6.
Quote (Remarks after theorem): "The result is trivial for λ2 ≥ 1."
The theorem assumes a real C2 phase, lambda2<=|f''|<=alpha lambda2,
and gives |sum e(f(n))|<=C(alpha)(M sqrt(lambda2)+lambda2^-1/2).

Exact map: on a free factor x in[R,2R], f(x)=-t log(x)/(2pi), t!=0,
 lambda2=|t|/(8pi R²), alpha=4, integer sum length M<=R+1.
Its unweighted bound is O(sqrt(|t|)+R/sqrt(|t|)), plus endpoint constants.
Multiplying by x^-1/2 log x is handled by Abel summation on each clipped
subinterval, retaining endpoints and log loss; it does not admit arbitrary
Möbius coefficients for free. Nor does it directly bound F_(v,J_rv).
At |t| comparable to Omega~m/U and R<=z~(m/U)^(1/3), sqrt(|t|)>>R:
the second-derivative envelope is trivial. This is an envelope limitation,
not proof of absence of cancellation. At t=0 use a separate elementary
sum-minus-integral estimate; this theorem has lambda2>0.

Negative control outside the unit-amplitude class: weights c_n=e(-f(n))
make the weighted sum equal its length. Thus a C2 phase alone cannot pay
arbitrary weights. Actual Möbius weights are NOT arbitrary; this control
does not kill their cancellation. Their arithmetic must be used explicitly.
PROVED: phase derivative hypotheses and exact finite convolution identity.
PARTIAL: free-factor estimate in its nontrivial parameter range.
OPEN: all-free-short sectors, signed compensator and original-norm Schur bound.

This is source-verified discovery evidence (root independently reread the
stated theorem and proof sketch), not a new theorem beyond our existing
Arias de Reyna Lemma5. No new claim about RH/SP follows.

## Excluded lead

Van der Corput, Verschärfung der Abschätzung beim Teilerproblem,
Math. Ann.87 (1922),39–65, original volume PDF:
https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0087/PPN235181684_0087.pdf
SHA-256 45a828889ba0c690026a9cd7e7f3e9290ef1739205202c92bfc5a11429665e70.
Researcher inspected printed pp42–43 (Satz1). Root has not independently
reread the scanned theorem; excluded as an admitted supplier. The B-transform
would require full stationary-phase/endpoint and coefficient transfer.
No assertion that it controls the weighted CCM convolution is made.

Next single test: explicit free-factor-sector decomposition plus actual
coefficient-weighted remainder in the linear consumer. Stop the test when
its full signed budget or a precise unsupplied estimate is established.
