# Independent log3 SOS audit

**FIRST_STEP_LOG3_SOS_PAPER_AUDIT_PASS**

Verdict: CONFIRMED, fixed-support computer-assisted PAPER certificate.
Route B remains CHALLENGER / NOT_RH. No global(P), RH or novelty claim.

Source: e4390b8, PROSHKA_VERDICT_FIRST_STEP_LOG3_SOS_2026-11-03.md,
SHA256 `4daedf962be48ffa858f00afba6977654843cfcc099569b2b0bcd4a454d8aa01`.
The full [independent audit and line-by-line analysis](../first_step_log3_sos_audit_2026-11-03/RESULT.md)
and all executed artifacts are committed alongside this summary.

Both prescribed runs, iv70/Q40 and iv90/Q48, complete. Their dyadic matrices
are byte-identical with canonical SHA256
`8b7fb1900093eb47e663ae352e0b52a2ad18043bd5d654e0f1a71aacec5ddcc0`.
Integer Bareiss checks all exact divisions and positive principal minors.
A separately written rational SymPy LDL checker reconstructs both parity
blocks exactly and reproduces both determinant hashes.

The independently recomputed source-to-operator error is <1.783523e-18
at Q40 and <1.740902e-18 at Q48, both <2^-40. Reviewed bounds include
the infinite Legendre tail, both pole tails, Binet/Bessel remainders,
analytic operator-norm Gauss remainder and source-to-dyadic rounding.
The exact SOS expansion and convergent binomial square-root construction
have no circular positivity assumption. No invalid step was found.

Accepted local scope: W[f]>=2^-30||f||_2^2 for complex finite-form-energy
inputs supported on an interval of length<=log3. The all-node pullback
uses the physical min(s,t) norm, not a uniform Euclidean Gram eigenvalue
gap. Arbitrary short intervals require reanchoring; a fixed anchor0 claim
requires the interval to contain0. Remote old histories are not covered.

Native Arb and Lean were not used. Acceptance rests on elementary directed
interval arithmetic, separately audited analytic remainder bounds and exact
rational signs. Diagnostic normalization controls and the doubled-prime
negative test agree with the same source. Canon and mirror are byte-identical.
