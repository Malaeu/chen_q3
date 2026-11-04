# Pre-registration: Gate 0 and literal even CCM commutants

Route B = CHALLENGER / NOT_RH. DIAGNOSTIC_NEVER_A_PROOF.
Base: rh_clean@5bc0c57099ce7da2fd51126b67b7e01d044c7434.
Registered from the owner brief before numerical source-identity or commutant runs.

- R1 (P=0.85): r(A)>=1e-3 at every m in {16,40,100,300,1000}; no low-order near-commutant for the full window.
- R2 (P=0.35): r(H)<=1e-6 at some m; the Gamma part alone has a prolate-type near-commutant.
- R6 (P=0.70): if any D gives r(A)<=1e-6, the same D gives r(A+Q)<=1e-6; the commutant is blind to the planted quartet.
- G0 (P=0.90): source identity Gate 0 passes with absolute difference<=1e-40 at all m in {16,80,300}.

Gate 0 comes first. At >=50 mpmath decimal digits, compare the unchanged pinned source A00=H00+P00-B00 with 2*Psi(log m)/log m from Suzuki Theorem1.1(1.1), reporting all pieces. The required pole identity is P00=8*(exp(L/2)+exp(-L/2)-2)/L. A failure stops the commutant scan without source repair.

Conditional scan: D=(a f')'+b f, even polynomial a,b of degree<=4, Galerkin on the stated even cosine carrier. All literal short circuits, including scalar identities or projection/domain issues, must be reported. The metric in the brief is retained unless a separate explicitly labelled quotient is justified; no silent removal of directions. Mandatory Slepian positive and random symmetric negative controls precede interpretation. Positive-control failure voids the scan. Any r<1e-10 requires >=50dps confirmation.

Publication procedure: preserve this exact blob in an immutable pre-registration commit object before any numerical run; publish one final commit directly on the requested base/head, carrying this blob and the pre-registration receipt. The registration object is not a second branch update.
