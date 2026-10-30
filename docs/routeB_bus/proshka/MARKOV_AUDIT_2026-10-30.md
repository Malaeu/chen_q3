# MARKOV audit — observer, 2026-10-30

Verdict: [`PROSHKA_VERDICT_MARKOV_2026-10-29.md`](PROSHKA_VERDICT_MARKOV_2026-10-29.md), 1163 lines, 69513 bytes,
SHA-256 `64a67ac8ccfdcf35eb8e0918136e4ae75c322198817fe5fbd749fc5118f98512` (Downloads copy and repo copy identical).
File time 2026-10-30 07:27; request sent 2026-10-29 15:19. Status `TRY_MARKOV_BULK_WITH_INDEX_GUARD`, route score 5,
progress class PROOF_PROGRESS (PAPER). Q1 `MARKOV_PROVED` (continuum window), finite Fourier compression `MARKOV_PARTIAL`;
Q2a `REDUCTION_CORRECTED`; Q2b `INDEX_RH_GRADED`; Q2c exact secular description; Q3 `REDUCED_TO_FIRST_UNPAID`.
G1a for K: not proved. Secular signs and index bounds: not proved cofinally. PX_RH_CLAIM: NOT_MADE.

## What Proshka established (PAPER)

- (2.1)-(2.2) pole-free bulk = killed symmetric jump Dirichlet form (Levy measure j(|s|) ds + prime atoms at ±log n)
  minus the constant (c* + 2 S_L), S_L = sum_{n <= e^L} Lambda(n)/sqrt(n), c* = gamma + log(8 pi) + pi/2.
- (2.5)-(2.7) every window: semigroup positivity improving; bottom simple, positive a.e., even, <p, phi> > 0.
  Continuum only. Fourier compression does not inherit it automatically (exact plant (2.8)).
- (2.9) full K is not positivity preserving at m = 2 (pole kernel 2 cosh beats j). Does not touch G1a.
- (3.1) constant mode: bulk energy < 1 - gamma - log(4 pi tanh(L/2)) < 0, so n_-(G_E) >= 1 for every m >= 2.
- (3.2)-(3.5) complete rank-one inertia classification with kernel guards and Moore-Penrose inverses.
- (4.19) RH <=> n_-(G_{m,m,E}) <= 1 on an unbounded set of m <=> G_{m,m,O} >= 0 on an unbounded set of m.
  Witness: theta function h with h-hat = 4 xi (radical vector, g(h,h) = -8) plus two pole-annihilating tests f_E, f_O
  built from an assumed off-line zero quartet; each has Weil value -4r; return to N = m with error (4.17).
- (5.4) sufficient G1a bracket: tau with alpha0 < tau < min(alpha1, beta0), Phi_E(tau) > 0, Phi_O(tau) > 0.
- (6.8) k[hF] = E_h[F] - 8 (Var_mu F + |int tanh(x/2) F dmu|^2), dmu = cosh(x/2) h dx / 2 (probability measure).
  Missing: the sharp weighted jump Poincare inequality (6.9) with constant 8.
- Kills (theorem shapes, synthetic plants): PF bulk => secular signs (7.1); automatic Fourier Markov inheritance (2.8);
  PF for full K on every window (2.9).

## Observer checks

| Claim | Check | Result |
|---|---|---|
| (3.1) constant-mode energy | G00 = K[m,m] - kappa u_0^2 vs bound, m = 2..12, dps 40 | PASS: G00 from -1.217 (m=2) to -5.604 (m=12), always below the bound; final constant -1.0096 |
| (4.3)-(4.5) theta function h | series at dps 30: evenness, h-hat(0), h-hat(2.7), mu mass | PASS: h-hat = 4 xi to 12 digits; mass 1.0; h(-3) = -2.9e-30 is series cancellation (Poisson gives 4e-543) |
| (4.9) pole annihilation | paper: <p,f> ~ f-hat(i/2) + f-hat(-i/2), <q,f> ~ f-hat(i/2) - f-hat(-i/2), factor z^2 + 1/4 kills both | PASS (paper, two lines) |
| (4.10) quartet signs | Proshka sympy block §11.4 | PASS (algebra only) |
| (4.6)-(4.8) H_0 entire, strip decay, f_E, f_O in S_exp | not checked from here | PAPER, not verified |
| (4.12)-(4.17) return to N = m | observer read the exponents (L^{7/2} m^{-7/2}, prime norm 4 sqrt(m) log m, pole 4 sinh(L/2)); no independent proof | PAPER, not verified |
| (6.8) theta jump identity, constant 8 | `thetagrade_2026-10-28/theta_jump_identity_check.py`, float64 quadrature, two smooth F with odd part | PASS: diff 9.7e-10 (r = 0.4) and 1.9e-10 (r = 0.9); second F nearly saturates (E_h = 0.01960, 8(Var+odd^2) = 0.01958) |
| normalization of (1.2)-(1.4) vs our matrix K | same code on psi_0 - (psi_1 + psi_-1)/2 vs c^T K c | PASS: diff 1.4e-9 (m = 3), 1.5e-9 (m = 5) |
| (7.1) three-state plant | numpy | PASS: all four sign combinations; P = 9/4 even bottom, P = 11/4 odd bottom |
| (2.9) numeric bound | 1/(1 - e^{-24/25}) = 1.620 < 1513/888 = 1.704 < 2 | PASS |
| §2.5 defect in our pf_probe.py | code read: `mp.re` of a synthesized function | CONFIRMED and FIXED (below) |

## Defect fixed: pf_probe.py odd phase (verdict §2.5)

`pf_probe.py` took `mp.re` of the synthesized bottom function. Real odd coefficients synthesize a purely imaginary
function, so an odd bottom would read as zero. Fix: divide by a common phase (value of largest modulus), assert the
imaginary rest is below 10^(-dps/2), then take the real part. Regression: planted odd bottom e_1 - e_-1 now reports
sector O, one sign change, min/max -1.414/+1.414. Rerun m = 2..12 at dps 120 (`pf_probe_dps120_fixed.jsonl`): all old
rows identical byte for byte; new cells m = 7, 9, 11 also even, no sign change. Old even conclusions stand.
The grid with 2% margin stays a diagnostic, not a global function-sign certificate (Proshka's second point, accepted).

## Bracket (5.4) probe: same wall

`thetagrade_2026-10-28/bracket_probe.py`, dps 120, m = 2..12, tau = sqrt(lam0(K_E) lam0(K_O)).
Both Phi are positive between the two roots by construction (Phi_E increases from its root at lam0(K_E), Phi_O
decreases to its root at lam0(K_O)), so existence of the bracket only repeats the known G1a numerics.
The informative number is the size: Phi_E(tau) ~ 0.6 tau, Phi_O(tau) ~ 500 tau.

| m | lam0(K_E) | lam0(K_O) | Phi_E(tau) | Phi_O(tau) | s_E | s_O |
|---|---|---|---|---|---|---|
| 2 | 3.06e-3 | 0.126 | 1.49e-2 | 0.915 | -2.79e-3 | 0.927 |
| 6 | 8.00e-15 | 2.90e-12 | 9.26e-14 | 7.36e-11 | -5.13e-15 | 7.76e-11 |
| 12 | 6.79e-29 | 4.15e-26 | 9.78e-28 | 9.03e-25 | -4.12e-29 | 9.41e-25 |

Reading: Phi = 1 + kappa <u, (A - tau)^-1 u>; a margin of 1e-27 means the same 28-digit cancellation of 1 against the
resolvent term as s_E, s_O. The bracket re-expresses G1a; it does not give it a healthy margin.
Root check: Phi_E(0) = -4.12e-29, slope (Phi_E(tau) - Phi_E(0))/tau = 0.607, linear root 6.79e-29 = lam0(K_E).
So lam0(K_E) is a root of Phi_E, not an untouched G_E level (Proshka's invisible-level guard), at m = 12.

## Pole-free odd sector (recorded when seen)

(4.19) line 3: RH <=> G_O >= 0 on an unbounded set of m. G_O has no pole term at all: archimedean jumps and primes only.
Our rerun: lam0(G_O) = 0.135 (m = 2), 3.7e-13 (m = 8), 1.6e-21 (m = 12). Removing the pole buys no margin:
the pole-free odd bottom is as close to zero as the full K. The pole is not where the difficulty sits.

## Consequences for the atlas shortlist (`docs/PRIME_PROPERTIES_ATLAS_2026-10-29.md` §4)

- Candidate 2 (index 1 on the complement of the pole, Hodge-index analogue): RH-graded by (4.19). It is the roof, not a
  pillar. Not a shortcut.
- Candidate 1 (partial sums of Lambda^{*k}, rule 18): by (2.1) the prime comb enters as sum c_n ||f(.+a_n) - f||^2
  (positive) MINUS 2 S_L ||f||^2 (S_L ~ 2 sqrt(m)). "Prime squares without the diagonal compensation change the object"
  (§11.2). Any rule-18 decomposition must name its B0. If B0 carries -2 S_L ||f||^2, partial sums start near -4 sqrt(m)
  and must climb to 1e-29: sign as a difference again. Not re-offered in its old form.
- New object for the Williams method: (6.9) is a Poincare (spectral-gap) inequality for an explicit symmetric jump
  Markov process with reference probability measure mu, required constant exactly 8. Foreign tool families to check:
  spectral-gap lower bounds for jump processes (Chen Mu-Fa variational formulas, Lyapunov / Barta-type test-function
  bounds, Cheeger for jump kernels). Risk: the constant must be sharp (second test F above is within 0.1% of saturation).

## Predictions (observer, frozen in the request)

| Prediction | Outcome | Note |
|---|---|---|
| P1 MARKOV_PROVED 0.55 / PARTIAL 0.30 / REFUTED 0.15 | qualified PROVED (continuum), PARTIAL (Fourier) | modal branch hit, with scope cut |
| P1c finite compression needs its own argument 0.65 | confirmed | |
| P2 reduction confirmed/corrected 0.85 | confirmed with correction | kernel guards added |
| P2b UNCONDITIONAL 0.25 / RH_GRADED 0.20 / UNDECIDED 0.55 | RH_GRADED | MISS of the modal guess. I put 0.55 on "undecided"; Proshka proved the index bounds are exactly RH. Error: I treated the observed index pattern as background data, not as a zero-content statement. — observer |
| P3 SIGN_REPRESENTATION 0.07 / FIRST_UNPAID 0.63 / NONE 0.30 | FIRST_UNPAID | modal branch hit |

## Open and next

1. Proshka's directive: independent PAPER audit of §4 (H_0 analyticity and decay, f_E/f_O in S_exp, return (4.12)-(4.17)).
   This is the only check that would lift (4.19) above PAPER. Channel: Codex (read-only paper audit) or a second Proshka
   chat. Owner decision.
2. (6.9) Poincare inequality: literature pass on sharp spectral-gap bounds for symmetric jump processes (Williams method).
3. pf_probe.py fix and the two new scripts are diagnostics only. DIAGNOSTIC_NEVER_A_PROOF.

## Update 2026-10-30: literature pass on (6.9)
`docs/literature/POINCARE_JUMP_PASS_2026-10-30.md`: no sharp foreign tool; agent's A_abs / Barta candidate killed by
`crossing_prime_probe.py` (crossing prime couplings exceed the odd margin by 3e3 .. 2e25 on m = 3..12).
