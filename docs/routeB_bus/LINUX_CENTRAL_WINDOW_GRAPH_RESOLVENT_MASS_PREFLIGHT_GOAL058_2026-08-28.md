---
TASK_ID: GOAL058_SELECTED_FERRERS_CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: 5405b7ed
DISCRIMINATOR: HOLD
RESULT_CODE: CENTRAL_WINDOW_SAMPLING_EXACT_BUT_GRAPH_RESOLVENT_MASS_UNCONTROLLED
LEAN_EDIT: false
NUMERICS: none
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - CENTRAL_WINDOW_SAMPLING_INEQUALITY
OPENS: []
STOP_RULE_TRIGGERED: on_hold — returning to the owner for representation rerank
---

# Central-window sampling is exact; the graph resolvent is not controlled, and a plant shows it need not be

## 1. Source-locked pole evaluation

`proposition59PoleKernel_at_pole` (`Proposition59EntireTransform.lean:48`,
kernel-green) gives, for `L != 0`,

    proposition59PoleKernel L j (proposition59Pole L j) = L * cos(j pi) = (-1)^j L.

For `k != j` the numerator `2 sin(z L/2)` vanishes at `z = p_j = 2 pi j/L`
(`proposition59Numerator_at_pole`, line 20) while the denominator `p_j - p_k` does
not, so the entry is `0`. Hence, with sign and scalar fixed by the source,

    kappa_m(p_j) = (-1)^j L e_j.                                          (1)

## 2. The fixed-compact sampling inequality

Fix once a compact `K0` in the tracking strip containing the real interval
`[-delta, delta]` and having nonempty interior; this choice is made before any
`m`, so the compact quantifier is respected. The poles `p_j = 2 pi j/L` lie in
`[-delta, delta]` exactly for `|j| <= J_m = floor(delta L/(2 pi))`. By (1),

    T_{m,p_j}(a) = < kappa_m(p_j), u_{m,rho} > = (-1)^j L * conj( u_{m,rho}(j) ),

so `|T_{m,p_j}| = L |u_{m,rho}(j)|` and therefore

    sup_{z in K0} |T_{m,z}(a_rho)|  >=  L * max_{|j| <= J_m} |u_{m,rho}(j)|
                                    >=  L / sqrt(2 J_m + 1) * || P_{J_m} u_{m,rho} ||_2.   (2)

This is the verdict's target, now derived rather than precommitted. It uses only
(1) and `max >= RMS`.

## 3. The exact object and its threshold

    u_{m,rho} = C_m^{-1} Q_m Phi_m(a_rho),   Phi_m(a) = ([S_a, H_m] + C_a) q_m.

With `2 J_m + 1 ~ delta L/pi`, inequality (2) reads
`sup |T| >= sqrt(pi L/delta) * || P_{J_m} u ||_2`. The kill threshold
`sup |T| >~ m^{-sigma} (log m)^{-3/2}` therefore becomes

    || P_{J_m} u_{m,rho} ||_2  >~  sqrt(delta/pi) * m^{-sigma} * (log m)^{-2},   (3)

required infinitely often along the schedule. The whole arithmetic question is now
a statement about the mass of one explicit vector in the central `O(log m)`
coordinates.

## 4. Shelf audit, stated as an audit and not as evidence

Asked this session for suppliers bounding `C^{-1}` applied to a vector. What the
catalogue returns concerns the **spectrum**: `H2a_SimpleEvenGround_FromPenaltyCoercivity`,
`gap_clause`, `simplicity_clause`, `sectorIsolationRadius_certificate` and its
companion. These bound eigenvalue separation and eigenspace dimension. Schur
machinery exists — `mode4HermitianSchurMatrix_negativeCount_eq_classicalHeadCount`,
`sourceWeilOddTargetFloorSchurComplement_isPositive_iff_ccm_corrected_energy` and
their receivers — but their targets are negative counts, boundary flux and an odd
target floor, not the coordinate distribution of a resolvent image.

Per correction 13 section 7 this is a statement about our citation base only: the
item `CENTRAL_WINDOW_GRAPH_RESOLVENT_MASS_LOWER_ENVELOPE` is **unsupplied**, which
is not evidence that it is false.

## 5. Plant: central localization need not survive the resolvent

The verdict asked for this and it is easy to supply, which is itself informative.

On `q^perp` choose the Hermitian block of `K_m - eps_m I` to be
`diag(c_n)` with `c_n = m^{A}` for `|n| <= J_m` and `c_n = 1` otherwise, `A > 0`
arbitrary. Then `C = Q diag(c) Q + q q^*` is Hermitian, positive definite, and
preserves `q^perp`; all hypotheses of `trialGraphOperator_posDef` hold with floor
`beta = 1`. But

    || P_{J_m} C^{-1} Q Phi ||_2 = m^{-A} || P_{J_m} Q Phi ||_2,

so however well `Phi` is centrally localized, its resolvent image can be
suppressed below any prescribed power. **Central localization of `Phi` is
therefore not transferable to `u` without a statement about `C` on the central
block.** My previous report's appeal to the localization of `Phi` is accordingly
insufficient, independently of the separate object-mismatch correction about odd
mass.

## 6. Source-adapted Schur/Feshbach candidate, with its ledger

Split the carrier into the central block `B = { |n| <= J_m }` and its complement
`B'`. Writing `C` in blocks on `q^perp` and solving,

    P_B u = ( C_BB - C_{BB'} C_{B'B'}^{-1} C_{B'B} )^{-1}
            ( P_B Q Phi - C_{BB'} C_{B'B'}^{-1} P_{B'} Q Phi ).

So (3) reduces to two inputs and no others:

- an **upper** envelope for the norm of the central Schur complement
  `C_BB - C_{BB'} C_{B'B'}^{-1} C_{B'B}`, which is a statement about the literal
  CCM matrix restricted to `O(log m)` central modes plus its coupling;
- a **lower** envelope for the effective central source
  `P_B Q Phi - C_{BB'} C_{B'B'}^{-1} P_{B'} Q Phi`.

This ledger is strictly smaller than the previous one: it drops the complement
floor, the kernel compact rate, the mode-energy adapter and the energy contract,
replacing all four by two statements about one `O(log m)`-dimensional block.
Whether it is *achievable* is not claimed; only that it is smaller.

The plant of section 5 lives entirely in the first input — there the central Schur
complement is `m^A I` — so the two inputs are exactly where the difficulty was
relocated, not where it was hidden.

## 7. Guards observed

- `selectedFerrersFiniteCCMOddMass` is not used as a mode-localization statement
  anywhere above; the verdict's object-mismatch correction is accepted.
- No quartet and no cross-zero conclusion appears in this transaction.
- No "no supplier" argument is used as mathematical evidence; section 4 is scoped
  as an audit.
- The compact `K0` is fixed before `m` and never varies with the cell.

## 8. Stop rule

The discriminator is HOLD, so the verdict's stop rule applies: no further
Cauchy, Volterra or observability wrapper is to be launched, and the front returns
to the owner for representation rerank — unless the Schur/Feshbach candidate of
section 6 is judged to have a strictly smaller input ledger, which by the count
above it does. That judgement is the judge's, not mine; I record both the
candidate and the stop.

## 9. Next load-bearing gap

    CENTRAL_SCHUR_COMPLEMENT_ENVELOPE_AND_EFFECTIVE_CENTRAL_SOURCE

with threshold (3). Two objects, both on an `O(log m)`-dimensional block of the
literal CCM matrix.
