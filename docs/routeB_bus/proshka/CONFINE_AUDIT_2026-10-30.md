# CONFINE audit — observer, 2026-10-30

Verdict: [`PROSHKA_VERDICT_CONFINE_2026-10-30.md`](PROSHKA_VERDICT_CONFINE_2026-10-30.md), 1266 lines, 73080 bytes,
SHA-256 `57088a914942b0dd1c3d1835edaca2f223a59831d78350c0a092356024852ddb` (Downloads copy and repo copy identical).
File time 2026-10-30 13:37; request sent about 10:53. Status `TRY_CONFINE_FIXED_JET_OVERLAP_AUDIT`, route score 5,
PROOF_PROGRESS (PAPER), independent review not performed. Request hash check: all four values match.
RH, G1a, G3: not proved. PX_RH_CLAIM: NOT_MADE.

## 1. What Proshka established (PAPER, not independently audited)

- (2.1)-(2.3) The L²-closed span of the even (odd) derivatives of h is all of L²_E (L²_O). On every finite carrier
  V_m the projected derivatives span the whole sector. So "the bottom lies in the xi-radical family" with unbounded
  derivative order is true for every vector, including bottoms of perturbed (Beurling) matrices. Content survives
  only for a FIXED finite jet, for example span{h, h'', h''''}.
- (3.8)-(3.9) For every fixed derivative r = h^(k), u_m = P_m(chi(x/b) r) is a superalgebraic quasimode on the
  original schedule N = m, L = log m: ||u_m - r|| + ||K_m u_m|| = O(m^-A) for every A. Endpoint jumps and the
  infinite exterior prime tail are paid in the bound.
- (4.1)-(4.6) An off-critical zero gives a fixed negative compact test in each parity separately (two independent
  interpolations, not a parity twin), hence lambda_min(K_{m,sigma}) <= -nu_sigma/2 for m >= m0(rho).
- (4.7)-(4.9) NEW: an off-critical zero forces every unit sector bottom to converge weakly to zero and to lose its
  overlap with every fixed finite jet: ||P_J f_m|| = O(m^-A). Contrapositive: a persistent overlap
  ||P_J f_{m,sigma}|| >= eps on an unbounded set of m implies RH. No G1a or G3 is needed for this direction.
- (5.1) Exact selection functional inside a fixed jet: H_m(i,j) = k(e_i, e_j) (signed leakage), not the L² tail.
- (5.4)-(5.7), (7.5) Every heat-smoothed h_s is radical for every s >= 0. Global balance cannot select s = 0.0031.
  Least-squares coefficients on a non-orthogonal 3-jet are not heat-Taylor coefficients (5.6).
- (6.1) The pole pair is a difference kernel: p(x)p(y) - q(x)q(y) = 2 cosh((x-y)/2). The window breaks translation,
  not the pole.
- (6.3) [K_m, D] = i omega (eta beta^T - beta eta^T), beta_n = n K_m(n,0); rank two, indefinite (6.13).
- (6.6)-(6.11) Derivative trial v = X xi / ||X xi||: (K_O - lambda_E) v = -(alpha/d) beta; exact Schur criterion
  K_O - lambda_E > 0 <=> C > 0 and a - r* C^-1 r > 0. First unpaid G1a term: the signed Q beta response.
- (7.6) Archived 2025 Paper I, tail integral: substitution x = e^y loses the Jacobian factor e^{y/2}.
- §7.3 Paper I's unrestricted-cone claim fails on a narrow even bump at an isolated prime node.

## 2. Observer checks

| Item | Check | Result | Locator |
|---|---|---|---|
| (6.3) displacement K(n,k) = (beta_n - beta_k)/(n-k) | literal K_m, dps 100, m = 4, 8, 12, 16 | max error 2.1e-101 | `thetagrade_2026-10-28/confine_schur_probe_dps100.txt` |
| (6.6) residual of the derivative trial | same | 7.9e-101 | same |
| (7.6) missing e^{y/2} in Paper I | read source | confirmed: lines 532-534 integrate y e^{-ty²}, the correct integrand is y e^{y/2-ty²} | `full/archive_latex_2026_01_29/paper1_fejer_heat/main.tex:532` |
| (6.1) pole pair is a difference kernel | algebra | confirmed: 2cosh(x/2)cosh(y/2) - 2sinh(x/2)sinh(y/2) = 2cosh((x-y)/2) | — |
| §6.5 angle vs vector error | arithmetic | confirmed: 1 - cos = 1.5e-6 means vector error sqrt(3e-6) = 1.73e-3 | — |
| (6.12) crude Schur criterion a > ‖r‖²/min C | literal K_m | FAILS by 47 (m = 4), 2.1e10 (8), 2.8e18 (12), 8.9e26 (16) | `confine_schur_probe_dps100.txt` |
| (3.9) quasimode norm ‖K_m P_m h‖/‖P_m h‖ falls faster than every power | literal K_m, dps 50, m = 8..20 | consistent: 4.5e-7, 6.4e-10, 1.2e-10, 1.7e-12 = (0.12 ... 0.49) x the Xi Fourier tail beyond t_m = 2 pi m / log m, which decays like exp(-pi² m / (2 log m)); the slow step 12 -> 16 is the modulation of abs(Xi) near t_m | `thetagrade_2026-10-28/quasimode_norm_probe_dps50.txt`, `quasimode_xi_tail.txt` |

NOT checked: the analytic estimates (3.2)-(3.8), (4.5), the quartet interpolation (4.1)-(4.3), the strip-density
proof (2.1)-(2.2), the fixed-Gram projection step (4.9). They stay PAPER. Proshka's own directive (§14) asks for an
independent paper audit of exactly these.

## 3. Schur margin = the gap itself; the ladder is the Schur response

Measured at dps 100 (`confine_schur_probe.py`):

| m | a / gap | ladder C_m (3fc421b5) | s/a = r*C^-1 r / a | Delta / gap | 1/(v* A^-1 v) vs Delta |
|---|---|---|---|---|---|
| 4 | 1.9304 | 1.93 | 0.48189 | 1.000186 | equal |
| 8 | 4.5831 | 4.57 | 0.78180 | 1.000039 | equal |
| 12 | 5.4956 | 5.49 | 0.81803 | 1.000009 | equal |
| 16 | 6.2926 | 6.29 | 0.84108 | 1.000003 | equal |

Here gap = lambda0(K_O) - lambda0(K_E), A = K_O - lambda_E.

1. Delta = a - r*C^-1 r = 1/(v* A^-1 v) is an identity (inverse of a 2x2 block). With v almost on the odd bottom,
   Delta = gap to 3e-6. Proshka's (9.2) is therefore not a cheaper object than the gap. It is the gap written
   through the weights of the trial vector.
2. a / gap is the ladder constant C_m. The equipartition ladder and the Schur response are one finding, not two.
3. s/a = 1 - 1/C_m. The cancellation is polynomial (about 2/m), not exponential. But a = -alpha beta^T X xi / d²
   still needs the bottom xi. By rule 11 the question is not yet on the source inputs.
4. min C / gap = 3.8e3 ... 3.0e5: the complement is well separated. The crude bound (6.12) still fails by 1e10-1e27
   because r carries weight on the high odd levels (equipartition |r_i|² ~ lambda0 lambda_i).

### 3b. Strange thing recorded on sight (quasimode decay)

The step m = 12 -> 16 fell only by 5.3 (effective power 5.8, against 16 for 8 -> 12). Two readings: (A) (3.9) is
false as written; (B) the residual follows abs(Xi(2 pi n / L)) at the cutoff, which oscillates. Discriminator: the
predicted tail eps0 = sqrt(sum_{|n|>m} L^-1 abs(4 Xi(2 pi n/L))²). Outcome: measured/eps0 = 0.22, 0.12, 0.49, 0.40
for m = 8, 12, 16, 20. Reading B. Side fact: the crude trial vectors of 5db6d539 miss lambda0(K_E) because
eps0² (1e-20 at m = 16) is far above lambda0(K_E) (5e-38): the bottom is h corrected at order eps0, not P_m h.

## 4. Observer retractions and prediction misses (signed: observer)

1. Request Q2 said the pole kernel cosh breaks translation. False: (6.1). The window breaks it.
2. "1 - cos = 1.5e-6" was presented as closeness of the odd bottom to f_E'. The vector error is 1.73e-3.
3. "The bottom lies in the xi-radical family" without a fixed order is empty by (2.1)-(2.3). Only the fixed 3-jet
   statement has content.
4. `weights_normalised` in `pingeom_fit.py` ignore the Gram matrix; they are not spectral masses.
5. "Odd bottom = derivative of even bottom" is an L² statement only; no derivative control.
6. `pingeom_limit.py` uses 8/pi instead of 16/pi (amplitude only; root unchanged; already noted in RESULT).
7. Predictions: P1 modal "reduced" .45 missed, outcome RH-graded (.20). P1b heat profile .30 unresolved.
   P2 exact commutator .70 hit. P2 zero-free lower gap .12 not obtained. P3 does not reduce to one outcome
   (fixed jet RH-graded, unrestricted closure zero-free but vacuous). P4 closed form for a* .45: partial (implicit
   equation (7.2) only).

## 5. Consequences for the map

- Geometry line (owner 30.10: "geometry is the exit"): the observation is precise and deserves a theorem, but it is
  RH-graded. Proving that the overlap with {h, h'', h''''} stays >= eps for unbounded m proves RH. It is the wall in
  new coordinates, with a new object: ||P_J f_m||² is positive by construction and computable without zeros.
- Finite tables cannot distinguish the two worlds. Under an off-critical zero at height T the escape starts only at
  m >= m0(rho), astronomically large. Our cos(f_E, h) = 0.9986 ... 0.9999 for m <= 16 is the measured form of (9.1),
  not its proof.
- G1a line: equipartition batch is postponed. After §3 it equals a lower bound for the gap and needs xi.
- 2025 Paper I has two confirmed defects (Jacobian (7.6), unrestricted cone §7.3). Not used as input anywhere.

## 6. Next (observer's choice)

1. Codex read-only PAPER audit of §§1-4 per Proshka §14 (one transaction, cost zero for us). Success code
   `FIXED_JET_ESCAPE_CONFIRMED_PAPER`, else `FIXED_JET_ESCAPE_FIRST_UNPAID_TERM`. Channel needs the owner's word.
   Probability that the proof survives as written: 0.6.
2. IF_A (confirmed): fixed-jet overlap becomes a legitimate rule-15 coordinate. Next question: replace f_m by source
   inputs (rule 11) in ||P_J f_m||.
3. IF_B (first unpaid term found): repair or bury this proof only. The geometry family stays alive.

## 7. Codex audit (2026-10-30 14:11)

Codex (gpt-6.1-sol, high, read-only, session `01a18ce8-7bd0-71a0-b7a4-2c6902262512`) audited §§1-4:
`FIXED_JET_ESCAPE_CONFIRMED_PAPER`, all eight steps OK, no findings. File:
[`CODEX_AUDIT_CONFINE_2026-10-30.md`](CODEX_AUDIT_CONFINE_2026-10-30.md). Codex ran no numeric checks.
Observer re-checked three of its constants: J_1 = sum (2l+1/2)^-2 = 4.29933 < 5; int_0^inf (e^{s/2}-1)/sinh s ds =
log 2 + pi/2 to 30 digits; 4 sinh(log m / 2) <= 2 sqrt(m). The theorem is now PAPER with two independent readers.
It is conditional: it proves "persistent fixed-jet overlap => RH", not the overlap itself.
