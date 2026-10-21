# Q07 — phase moments: bounded acceptance, no full CCM gain

2026-10-21. Natural completion observed12:03UTC in the same living chat.
Original86778bytes,1185LF, SHA256
 afeb5f8391138c8d09305e2333a0a33ee13eb4175adb4fea842f5394aa0a2fe2.
Downloaded original read completely. No resend/interruption. Request and all14
source bodies are preserved in PROSHKA_CCM_FIXED_CELL_BACKTRACK_Q07_2026-10-21.txt.

## Reproduction and independent audit

Root reproduced242 exact controls and3 mpmath60-decimal diagnostics; both JSONs
match the embedded results identically, including script/registration hashes.
See ccm_phase_q07_checks/. Exact rational matrices are controls, NOT actual
CCM matrices. Numerical transforms are not intervals. No prime sums, full CCM
spectra, Lean or Arb runs. Original independent_review=NOT_RUN is preserved
as author provenance; it does not describe the subsequent independent audit.
Read-only q07_phase_audit read the complete original and returned bounded
PAPER PASS, bound to the original hash. No material defect found in §§2–4,
6–8 or the full return. Root checked the same signs, Fourier tail and scope.
PNT input is the unconditional asymptotic psi(x)~x, DLMF27.12.5;
no RH-sized error, effective onset or finite verification of that limit claimed.

## What is proved within this scope

All original prime powers and intermediate projections survive the finite
multiplicative lift S(z). S(1) is the original source; other phases are
auxiliary sources. Haar mean zero and covariance
Gamma=sum a_n²(C_n C_n* + C_n* C_n) <=6L(1+L)P are exact.
Fourth phase moment gives some good PHASE, not the identity phase and not
an unbounded subsequence of original m. Point return pays2*n_m, yielding
||S(1)||<=sqrt(96m(1+L)); direct Chebyshev gives ||S(z)||<=12sqrt(m).
Neither improves the inherited CONDITIONAL3/8 bound or yields eta->0.

For fixed tau=1/10 and every fixed0<epsilon<1/32, the SAME projector and full
prime-power sum with auxiliary coefficients n^(i*tau) have eventually
lambda_max(S_tau)>=6478241/23092593750000 * sqrt(m).
The compact profile g=h''-h/4, h=(t-1)^4(2-t)^4 on[1,2], has both original
exponential contacts zero. Its shifted Laplace transform is nonzero. The
phase-aligned endpoint pair and PNT give a positive full sqrt(m) contribution.
Original Fourier truncation and three-constraint projection cost
O(L^(3/2)M^(-3/2))=o(1). The full12sqrt(m) norm pays all newly activated
atoms and mixed terms as o(sqrt(m)); nothing is discarded after projection.
At tau=0 the leading coefficient vanishes exactly: H_g(1/2)=0.
Therefore this is NOT an original CCM lower bound or a counterexample to RH.

This rules out a sub-half-power upper bound UNIFORM over the full auxiliary
phase family. It also rules out a free generic passage from phase-invariant
moments to the distinguished source phase. Positive absolutely continuous
coefficient-exact averaging cannot reproduce even z_2=1; this narrower fact
does not exclude a one-sided comparison using additional source relations.

## Full return and decision

Scalar T return pays the short term once. Direct K return pays arch50L+8,
without charging the short term a second time. Q02 fee applies only to V.
No full exponent, cofinal result, original-source failure, SP or RH follows.
CF22/PySR remain PARKED_REOPENABLE; native goal ACTIVE.

Stop the phase-uniform/moment-only transfer as a proposed source supplier.
No automatic Q08: changing the name of the missing identity-phase estimate
would repeat the debt. Deliberate next rollback: inspect whether the exact
annihilation of the real exponential source can be used BEFORE phase
averaging, and test the cheapest concrete signed comparison against the
already-known Q03 primitive-cone obstruction. If it only restates the prime
remainder or requires an RH-sized PNT error, record that and do not dispatch
it as a new mechanism. No claim that such a comparison exists is made.
