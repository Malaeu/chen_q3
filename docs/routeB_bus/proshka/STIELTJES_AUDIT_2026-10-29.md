# STIELTJES audit — observer, 2026-10-29

Verdict: [`PROSHKA_VERDICT_STIELTJES_2026-10-29.md`](PROSHKA_VERDICT_STIELTJES_2026-10-29.md), 940 lines, 58592 bytes,
SHA-256 `0055688df2c9e18220f6ca297391562fa7b6fab381930942972217cd510de367`. Status `TRY_STIELTJES_UNREDUCED_COFACTOR_POSITIVITY`,
route score 4, progress class FALSIFICATION + REPRESENTATION. Q1 `G1A_REDUCED_TO_POSITIVE_SIGN` (coefficient cone, not one sign),
Q2 `ALTERNATION_PARTIAL`, Q3 `THETA_UNDECIDED`. No cofinal G1a sign.

## What Proshka established (PAPER)
- (1.4) unreduced cofactor chi(t) = h^T adj(E - tI) e0 = det(O - tI) for all t, every cell.
- (3.1) G1a <=> lambda_min(E) < lambda_min(O); simplicity and eta-pairing follow.
- (4.2) G1a <=> all coefficients of P(x) = det(O - lambda I + x I) positive (exact, multiplicity-safe).
- (4.6)-(4.7) root-free bracket: tau with p_E(tau) < 0 and det(O - tau I + x I) with positive coefficients gives G1a.
- Our Abel condition N4(c) is sufficient (needs a simple even bottom), not necessary. w0 > 0 alone is insufficient.
- Killed theorem shapes (synthetic structured plants, not the arithmetic family): w0>0 => G1a (5.1);
  G1a => all W_k > 0 (5.4); W_k > 0 => G1a without simplicity (5.8); Jacobi commutation => G1a (7.3).
- Directive: source supplier for the endpoint cofactor chi_m(lambda_m) = det(O_m - lambda_m I) > 0
  (report as ENDPOINT_COFACTOR_SIGN_ONLY, never as G1a).

## Observer checks (`thetagrade_2026-10-28/stieltjes_verdict_checks.py`)
- (1.4) on literal m = 3, 6, 9 at t = lambda, lambda - 1, 0.37: relative error <= 7.6e-97 (dps 120). PASS.
- Coefficient cone on the same cells: min c_k = c_0 = det(O - lambda I) (1.9e-5, 9.8e-25, 1.3e-52). The endpoint
  coefficient is the smallest one, so Proshka's directive targets the binding coefficient. PASS.
- Plant 5.1 rebuilt from (A, b) through our own parity_bases: E matches (5.1) to 3.7e-17; G1a False with w0 = 0.0236 > 0.
  Note: W_1 = -0.562 < 0, so our Abel test correctly rejects it; only "w0 alone" is killed. PASS.
- Plant 5.4: G1a True, W_1 = -0.0271 < 0. PASS. Plant 5.8: degenerate bottom, W = (1, 1, 1). PASS.
- Plant 7.3: K equals the structured matrix from (A0=4, A1=0, b1=1), [T, K] = 0 exactly, odd ground -1. PASS.

## Observer finding after the verdict (diagnostic)
mu/lambda (odd bottom over even bottom), both positive on every cell:
diagonal m = 2..16: 41, 116, 178, 288, 362, 379, 326, 568, 640, 644, 611, 810, 988, 1112, 1256 (`residue_dps170.jsonl`);
off-diagonal 72 cells: min 6.97 (N = 16, lambda^2 = 1.5), max 1714 (`offdiag_dps100.jsonl`).
Reading: G1a is a multiplicative separation, not a near-tie. Proshka's bracket (4.6)-(4.7) then only needs two
crude one-sided bounds: lambda <= U from an explicit even trial vector (Rayleigh) and mu >= Lo from a lower bound
on the odd block, with U < Lo; each may be off by a factor ~sqrt(mu/lambda). This is rule 18 (sign as two one-sided
bounds). Candidate for the next step, probability 0.35 that an explicit even trial vector gives U within a factor 5
of lambda on m = 2..16. DIAGNOSTIC_NEVER_A_PROOF.

## Predictions
- Observer 0.55 "Proshka reduces G1a to one positive sign": qualified. Q1 code matches, but the sign is a cone of
  m + 1 coefficients and Proshka scores it as re-representation (§9.3), not cofinal progress.
- P1b (0.50) "first unpaid term concerns only the bottom even level": not confirmed (plant 5.1).
