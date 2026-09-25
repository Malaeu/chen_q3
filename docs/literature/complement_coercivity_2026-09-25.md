# Literature: proving the full orthogonal-complement floor

2026-09-25, source baseline 04df81d0. Discovery evidence, not source admission.

Target: K=K*, ||q||=1, a=q*Kq. For all y⊥q, prove y*(K-aI)y>=delta||y||²,
delta>0. Equivalently B=U*(K-aI)U>=delta I for an EXACT orthonormal basis U
of q-perp. Source: PROSHKA_VERDICT_GOAL058_CELLWISE_COMPLEMENT_SIGN §4 (9)-(12).
The scalar tau>0 is only necessary. Current m8 CENTER diagnostics have three
negative eigenvalues of B; no interval or selected-cofinal conclusion follows.

Negative control: K=diag(0,1,10000), q=(sqrt(2499)/50,0,1/50) has a=4 and
sine-angle 1/50 from the exact ground, but y=(0,1,0)⊥q gives energy -3.
Thus even close alignment cannot itself supply this shifted floor.
Initial UNVERIFIED search dictionaries: constrained coercivity, verified
positive definiteness, spectral clusters. ask.sh returned conditional receivers
but ASK_STATUS INCOMPLETE (semantic-index freshness); no absence claim.

## Comparison of forms: verified conditional mechanism

Gerald Teschl, Mathematical Methods in Quantum Mechanics, 2009 manuscript,
§4.3, Theorem 4.10/Corollary 4.11, pp.118-119.
https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf
PDF SHA256 8dc8de0b58aa0a3fedfe594a345f9b5875322e5526ea581cb640a98d55b82818.
Quote, Corollary 4.11: "Suppose A and B are self-adjoint operators with A ≥ B";
its conclusion orders the corresponding eigenvalues.

Our elementary application: on the SAME q-perp independently establish
B0>=gI, write B=B0+E and prove ||E||<=epsilon<g. For EVERY x,
x*Bx >= (g-epsilon)||x||². The input controls the whole quadratic form,
not only its value at one trial vector. Source B0 and error budget OPEN.
If B is indefinite, these sufficient hypotheses cannot all hold.
The text explicitly distinguishes complements of exact and approximate
first eigenvectors; they do not give the same lower spectral bound.

## Rump: verified finite-matrix certificate

S.M. Rump, Verification of Positive Definiteness, BIT 46 (2006), 433-452,
DOI 10.1007/s10543-006-0056-1.
https://www.tuhh.de/ti3/paper/rump/Ru06c.pdf
PDF SHA256 68cc0e5fc9ed984f28d6ec8ead8c39dfbe4041f7afae5a80bb8bddcd26764b8e.
Quote, Corollary 2.4, PDF p.5: "runs to completion, then A is positive definite."

Essential hypotheses: c rigorously bounds the error matrix norm Delta(A),
and Cholesky is applied to a matrix with the same off-diagonal entries but
diagonals at most A_ii-c. A bare successful chol(A) is not the certificate.
Apply to A=B-delta I. Certified success proves the floor for all vectors.
Section 4 also brackets lambda_min by shifted positive/negative certificates.
Input errors in K, q and the basis must be enclosed, too; approximate
orthogonality is not exact by declaration. The paper discusses interval inputs.
Algorithm verified as a discovery; NOT RUN on our CCM inputs. A finite cell
certificate does not provide the selected infinite-family quantifier.

## Nakatsukasa: treat the whole low cluster

Yuji Nakatsukasa, Sharp error bounds for Ritz vectors and approximate singular
vectors, Mathematics of Computation 89 (2020), 1843-1866,
DOI 10.1090/mcom/3519. Theorem 5.1, formula (5.2).
https://arxiv.org/html/1810.02532
Archived PDF SHA256 879cde7acdeba2d5406b299da8928e4074ea8941da20f23e02c5a84f9311a8c4.
Quote, §5: "Here is the extension of the previous bounds to invariant subspaces."

Map A to K and the whole trial block to an approximate LOW spectral cluster.
When all Ritz vectors in the block are targeted, R2 is empty and internal
cluster spacings do not enter the subspace-angle estimate. A positive EXTERNAL
Gap to the complementary compression and a residual bound are still required,
along with identification of the desired bottom cluster. The theorem supplies
neither the external gap nor q's individual ground alignment inside the cluster.
Verified partial mechanism; these source hypotheses remain OPEN.
At m8 four K eigenvalues are numerically below a: one orthogonality constraint
cannot remove all their directions. This is a diagnostic, not a family proof.

## Bounded next test

Certify the odd negative witness with source/arithmetic uncertainty. If it
survives, the Rayleigh-shifted one-vector floor fails at that cell; investigate
the full low cluster and its external gap. Do not try to cure a genuinely
negative form with a different identity. Stop any proposed bridge that assumes
the positivity/separation it is meant to supply. No Goal058/RH closure.

Primary PDFs/text were read in /tmp/q3-coercivity-lit-20260925 and
/tmp/q3-literature-cluster-20260925; exact hashes and URLs are recorded above.

Luna researcher independently checked Rump Theorem 2.3 and Corollaries 2.4/2.7.
Failure of ordinary Cholesky is only failure to certify; a negative certificate
is a separate result. Root checked the quoted primary passages and mappings.

Follow-up executed: ../routeB_bus/fokas_k_sign_2026-09-25/INDEPENDENT_ENERGY_SHIFT.md
records the strict reference-cell witness, a certified low cluster and a
finite ground-tracking certificate with an independent energy cut.
