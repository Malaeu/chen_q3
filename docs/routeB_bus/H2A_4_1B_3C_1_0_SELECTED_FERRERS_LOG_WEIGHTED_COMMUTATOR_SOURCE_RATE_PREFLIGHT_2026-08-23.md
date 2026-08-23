# H2A.4.1B.3C.1.0 — selected Ferrers log-weighted commutator source-rate preflight (READ-ONLY)

```yaml
PRIMARY: H2A_4_1B_3C_1_0_SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_SOURCE_RATE_PREFLIGHT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict 9e1c5b61 — CODEX DIRECTIVE (REQ-2026-08-22-V, NEXT_AUTHORIZATION)
MODE: READ_ONLY
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: 9e1c5b61357178ceec79920afed76445a63cfde7
BASE_HEAD_PARENT: 03ed411e94fbf80d6462295a25d724274470a76a   # matches verdict expectation

OUTCOME_CODE: HMODE_HCHI_INSUFFICIENT_FOR_GAMMA_SOURCE_RATE

PREFLIGHT_ASK:
  - "./ask.sh \"selected Ferrers log weighted commutator energy\" — exit 0; no source-rate theorem; nearest hits are the 3B/3C receiver chain itself"
  - "./ask.sh \"mode weighted finite Riesz defect\" — exit 0; no mode-weighted defect theorem; CCMModeFinite machinery only"
  - "./ask.sh \"selected source prime oscillation bound\" — exit 0; no oscillatory prime-sum estimate; only opNorm-type prime form bounds"
  - "./ask.sh \"selected source arch graph derivative bound\" — exit 0; no derivative-type arch bound; only the C0 log-domination of the symbol"

FILES_INSPECTED:
  - Q3/Proofs/RouteB/G6N1SelectedFerrersCommutatorResidualDefect.lean      # Gamma def, Gamma = D*r, Loewner structured_all
  - Q3/Proofs/RouteB/G6N1SelectedFerrersCenterCoefficientFloor.lean        # 3C.0 receiver chain, global target cap
  - Q3/Proofs/RouteB/G6N1SelectedFerrersOddMassDecay.lean                  # eta_k <= C*L_k/sqrt(m_k) chain
  - Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean                    # finite Riesz = synthesis conjugation (171 lines; NO ambient compression)
  - Q3/Proofs/RouteB/D0PstarSourceWeilSesquilinearForm.lean                # W02/prime split; norm_sourcePrimeSesquilinearForm_apply_le (opNorm only)
  - Q3/Proofs/RouteB/D0PstarShiftedArchSesquilinearForm.lean               # shifted arch form on the dense domain
  - Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean              # |symbol(t)| <= (|log pi|+log 4+7)*(1+log(2+|t|)) — C0, not derivative
  - Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean                        # Fourier mode localization: far 1/|t−n/L| tail + resonanceSafe 1/(1+|t|)
  - Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean                    # prime entry = sum_{k<=m} Λ(k)/√k * cos-pairing; identity to ccmPrimeEntryN1
  - Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean                    # tau structured offdiag, commutator identity
  - Q3/Proofs/RouteB/CCMFiniteWeilShiftedRankOne.lean                      # shifted rank-one, beta oddness
  - Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean                        # ccmWeilMatFinite, modeDiag, eta

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## TEST 1 — RATE THRESHOLD (re-derivation, no prose shortcuts)

Known odd-mass rate (H2A.3, kernel-checked):

```text
eta_k <= C1 * L_k / sqrt(m_k)          eventually,  C1 = 4*(C1'+C2')^2/||Xi0||^2.
```

Required consumer (3C.0 receiver input):

```text
L_k * eta_k * GammaEnergy_k -> 0.
```

Substitution of the known rate:

```text
L_k * eta_k * GammaEnergy_k <= C1 * (L_k^2 / sqrt(m_k)) * GammaEnergy_k.
```

Sufficient source envelope, exactly as the verdict states:

```text
GammaEnergy_k = o( sqrt(m_k) / L_k^2 ).
```

Polynomial-log ledger.  For a proposed envelope `GammaEnergy <= C * m^alpha * L^beta`
the consumer sequence is bounded by `C*C1 * m^(alpha - 1/2) * L^(beta + 2)`.  Hence:

| envelope (alpha, beta) | consumer exponent | verdict |
|---|---|---|
| alpha < 1/2, any beta | m^(alpha−1/2) * L^(beta+2) -> 0 | STRICTLY SUBCRITICAL |
| alpha = 1/2, beta < −2 | L^(beta+2) -> 0 | SUBCRITICAL (boundary) |
| alpha = 1/2, beta >= −2 | does not tend to 0 | NOT subcritical |
| alpha > 1/2 | diverges | SUPERCRITICAL |

Concrete candidate envelopes measured against this ledger (details in Tests 3–5;
`sinh^2(L/4) ~ sqrt(m)/4` since `L = log m` drives the W02 scale):

| candidate | exponent pair (alpha, beta) | subcritical? |
|---|---|---|
| trivial cap `N^2 * opNorm^2` | (3, 0) class | NO |
| W02 rank-two, absolute CS | (1, 2) class | NO |
| W02 rank-two + odd-mass cancellation | (1/2, 3) class | NO (beta = 3 > −2) |
| prime absolute von-Mangoldt (Chebyshev scale) | >= (2, 0) class | NO (kill bound only) |
| arch via C0 symbol domination | circular: reduces to mode-weighted energy of `q` itself | NOT DERIVABLE |
| target-only smooth heuristic `C*L^2` | (0, 2) — would be subcritical | NOT PROVED for `q` (error part uncontrolled) |

No candidate assembled from disk facts is strictly subcritical.

## TEST 2 — EXACT OBJECT

`Gamma_k` is kept as the literal combined vector of
`G6N1SelectedFerrersCommutatorResidualDefect.lean`:

```text
Gamma = S*(D q) + A*beta − B*1,   proved componentwise equal to D*r  (r = M q − a q).
```

Every estimate in this report that bounds a component (W02 / arch / prime) is
labeled KILL BOUND and is never substituted for the combined object.  The ratified
plants of 3B stand: the combined defect can vanish by cancellation while both
separated action terms remain large; conversely the norm-sum of components is not
the consumer.

## TEST 3 — R1 LOG-COORDINATE ROUTE

Three levels, kept strictly apart:

1. **Coefficient identity — AVAILABLE (theorem-sized, not on disk).**
   The modes are `V_n(u) ~ L^(-1/2) * exp(2*pi*i*n*log(u)/L)` on the log window.
   Termwise differentiation of the finite synthesis gives

   ```text
   synthesis(D q) = (L / (2*pi*i)) * d/dt [ synthesis(q) ]   (t = log-coordinate).
   ```

   This is a finite Fourier sum derivative; a Lean proof is routine.  Consequence:

   ```text
   GammaEnergy_k = ||D r||^2 = (L/(2*pi))^2 * || d/dt synthesis(r) ||^2_{L2(window)}.
   ```

   The Gamma energy IS the log-Sobolev seminorm of the literal finite Riesz
   defect.  This confirms the R1 framing of the verdict.

2. **Finite Riesz source-form identity — PARTIALLY AVAILABLE, does not close.**
   `sourceCCMFiniteRieszOperator` is defined by synthesis conjugation
   (`D0PstarCCMFiniteRieszOperator.lean`), so `synthesis(r)` is the literal defect
   function on the window.  Its `d/dt` splits along the source ledger:
   - arch part: a Fourier multiplier; differentiation multiplies the symbol by
     `2*pi*i*t`.  The disk supplies only the C0 domination
     `|symbol(t)| <= (|log pi| + log 4 + 7)*(1 + log(2+|t|))`
     (`D0PstarExactArchSymbolLogDomination.lean`).  Weighting by `t` and pairing
     against the mode localization
     (`norm_fourier_logWindowZeroExtendedMode_le_far/resonanceSafe`) concentrates
     at the resonance `t ~ n/L`, giving a factor `~ (n/L)*log(2+n/L)` per mode —
     i.e. the arch contribution to the Gamma energy is controlled by
     `C * L^2/L^2 * sum_n n^2*(1+log)^2*|q_n|^2`, which is the **mode-weighted
     energy of `q` itself**.  That quantity is exactly as unknown as the target:
     the route is CIRCULAR at the current contract level.
   - W02 part: rank-two endpoint functionals
     (`sourceW02ModePairing_eq_rankTwoEndpointModeValues`); differentiation turns
     endpoint mode values into endpoint values of the derivative of the synthesis
     — again the same unknown derivative object.
   - prime part: see Test 4.

3. **Ambient associated-operator / compression identity — ABSENT.**
   `D0PstarCCMFiniteRieszOperator.lean` (171 lines) contains no theorem of the
   form `finite Riesz = compression of an ambient operator`.  Per the verdict
   this may not be inferred from levels 1–2 and is not used anywhere in this
   report.

R1 conclusion: the reduction `GammaEnergy = log-Sobolev(defect)` is real and
cheap, but closing it requires a **derivative-level source contract** for the
normalized selected row `q` (equivalently: a gradient version of the L73/hmode
proximity).  The existing `hmode`/`hchi` are C0/Hilbert contracts and do not
supply it (Test 6, falsifier).

## TEST 4 — R2 LOEWNER / PRIME ROUTE

The Loewner law is on disk and exact
(`ccmWeilTau_structured_offdiag`: `(n_j − n_l)*tau_{jl} = beta_j − beta_l`;
3B `structured_all`).  Expanding the prime block through the literal pairing
(`D0PstarSourcePrimeModePairing.lean`):

```text
PrimeEntry(n, r) = sum_{k <= m} Λ(k)/sqrt(k) * 2 * ∫ conj(F V_n)(t) * cos(2*pi*t*log k) * (F V_r)(t) dt.
```

The mode-difference weight transfers by partial integration:
`(n − r)` pairs with `d/dt cos(2*pi*t*log k) = −2*pi*log(k) * sin(...)`, moving
the weight onto the von-Mangoldt side as `Λ(k)*log(k)/sqrt(k)` with a
sign-oscillating `sin`-pairing.  Cancellation is preserved (no norms taken before
the transfer).

- **Absolute version (kill bound only, as mandated):** Chebyshev-scale
  `sum_{k<=m} Λ(k)*log(k)/sqrt(k) ~ sqrt(m)*L` gives a Gamma prime-block energy
  at the `(>=1, >=2)` exponent class after squaring — SUPERCRITICAL.  As the
  verdict anticipates, the absolute von-Mangoldt sum misses the threshold and is
  recorded only as a kill bound, not a positive route.
- **Oscillatory version:** subcriticality would require genuine cancellation in
  `sum_k Λ(k)*k^(-1/2)*e(±t*log k)`-type sums paired against window modes — an
  explicit-formula-grade oscillation statement.  `./ask.sh "selected source
  prime oscillation bound"` — nothing on disk; no Abel/generating identity for
  this pairing exists in the tree.  This input is OPEN.

R2 conclusion: structurally sound, cancellation-preserving, but the decisive
oscillatory prime input does not exist on disk and is not implied by
`hmode`/`hchi`.

## TEST 5 — COMPONENT LEDGER (honest, kill-bound status; NOT the consumer)

| component | best disk-derivable envelope for its Gamma-energy share | (alpha, beta) | subcritical? | note |
|---|---|---|---|---|
| W02 (rank-two endpoint) | absolute CS with `psi*n`-weight; `sinh^2(L/4) ~ sqrt(m)/4` scale | (1, 2) | NO | odd-cancellation improves to (1/2, 3): still NO (beta > −2) |
| shifted arch | C0 symbol log-domination + resonance localization → `C * (mode-weighted energy of q)` | not closed | CIRCULAR | needs derivative contract on `q`; with `sum n^2|q_n|^2 <= Q_k` it becomes `C*L^0*Q_k` — subcritical iff `Q_k = o(sqrt(m)/L^2)` |
| prime (retained von Mangoldt) | absolute Chebyshev | >= (2, 0) | NO | kill bound only; oscillatory identity OPEN |

None of the three rows is treated as the exact consumer; the combined `Gamma`
keeps its cancellation (Test 2).  The ledger shows that even *with* full
componentwise optimism no existing fact closes any single row, so the combined
cancellation is currently the only conceivable rescue — and no disk theorem
quantifies it.

## TEST 6 — INPUT SUFFICIENCY

The exact `hmode`/`hchi` contracts supply: Hilbert (C0-level) proximity of the
selected trial to the factor-four target, chi-limit at the shell, and through
the ratified chain: `eta`-rate, center floor, conditional receivers.  They do
NOT supply, and cannot logically supply (see falsifier), any of:

```text
OPEN-1: mode-weighted (log-Sobolev) control of the normalized selected row:
        sum_n n^2 * |q_{n,k}|^2 <= Q_k with subcritical Q_k
        (equivalently: derivative-level L73 proximity of kTrial to the target
        in the log coordinate);
OPEN-2: oscillatory prime-sum estimate for Λ(k)/sqrt(k)-pairings against
        window modes (explicit-formula-grade cancellation);
OPEN-3: derivative-level decay of the factor-four target itself
        (theorem-sized from the explicit E* formulas, but NEW analysis —
        the current E* chain bounds values, not derivatives).
```

Any one of these is a new analytic input beyond the ratified contracts.
Therefore the source-rate contract is NOT green.

Judge prediction check: P_H2A41B3C1_0_1 = 0.95 — CONFIRMED (no existing theorem
proves the subcritical envelope).  P_H2A41B3C1_0_2 = 0.78 (W02 and shifted-arch
admit subcritical envelopes once exact source units are retained) — NOT
CONFIRMED on disk facts: both rows reduce to the unresolved mode-weighted energy
of `q` (W02 through endpoint derivative values, arch through the resonance
ledger).  They plausibly become subcritical AFTER OPEN-1/OPEN-3 are supplied,
but they are not subcritical from the current contracts alone.
P_H2A41B3C1_0_3 = 0.82 — PARTIALLY: the prime row is a load-bearing gap
(OPEN-2), but it is not the *sole* one; OPEN-1 blocks all three rows first.

## MANDATORY FALSIFIER

Family on the selected carrier (dimension `N = m`), guarding against reusing the
L73 `L2` estimate as a derivative estimate:

```text
x^{(m)} := m^(-1/2) * e_N        (e_N = top-mode unit coordinate vector)

Hilbert norm:        ||x^{(m)}|| = m^(-1/2)  -> 0   (even at the L73 speed);
mode-weighted energy: sum_n n^2 |x_n|^2 = N^2 * m^(-1) = m.
```

Comparison with the critical scale: `m / (sqrt(m)/L^2) = m^(1/2) * L^2 -> ∞`.
A finite Fourier family with Hilbert norm tending to zero carries mode-weighted
energy arbitrarily far ABOVE the critical `sqrt(m)/L^2` scale.  Hence no
Hilbert-norm contract (hmode, L73, chi) can imply any Gamma source rate; the
implication is falsified structurally, not merely unproved.

## IF NOT GREEN — minimal missing identity and updated representations

**Minimal missing identity (single smallest input):** OPEN-1, the
derivative-level source contract

```text
SELECTED_ROW_MODE_WEIGHTED_ENERGY_CONTRACT:
    sum_n n^2 * |q_{n,k}|^2 <= Q_k,   Q_k subcritical for the ledger of Test 1
```

— equivalently a log-coordinate gradient version of the L73 proximity (target
derivative decay + error derivative smallness).  With OPEN-1 in hand the R1
reduction turns the arch row into a closed subcritical estimate and reframes the
prime row as the remaining oscillation question (OPEN-2).

**Candidate representations, updated:**

```yaml
R1_COMBINED_LOG_COORDINATE_SOURCE_DEFECT:
  STATUS: reduction real (coefficient identity theorem-sized; GammaEnergy =
    (L/2pi)^2 * log-Sobolev seminorm of the literal finite Riesz defect);
    closure blocked by OPEN-1 (+ OPEN-3 for the target side)
  KILL_POWER: 10/10
  COST: 7/10        # was 5/10; raised: needs a NEW derivative-level production
                    # contract, possibly a paper-source question (L73 gradient)
R2_LOEWNER_ABEL_VON_MANGOLDT_COMBINED_ACTION:
  STATUS: structurally sound, cancellation preserved through partial summation
    (mode weight -> log p weight); decisive oscillatory prime input OPEN-2 has
    no disk instance and is explicit-formula-adjacent
  KILL_POWER: 9/10
  COST: 8/10        # was 6/10; raised: the oscillation estimate is the
                    # hardest object in the entire H2A wall
```

No Lean was written (MODE: READ_ONLY honored).

## FORBIDDEN CHECK

```yaml
new_rate_hypothesis: none introduced
row_sum_or_ambient_opNorm_relabeled: no (opNorm facts cited only as kill bounds)
finite_riesz_ambient_compression: not assumed (absence verified in file)
termwise_replacement_of_Gamma: no (Test 2)
fitted_constants: none
numerics_in_cofinal_quantifier: none (NUMERICS false)
edits_H2A3_3B_3C0: none (read-only)
sector_floors_ground_510_RH_bundling: none
```

SUCCESS_CODE_RETURNED: HMODE_HCHI_INSUFFICIENT_FOR_GAMMA_SOURCE_RATE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
