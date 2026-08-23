# LINUX SOURCE RECORD — REQ V_H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION

DATE: 2026-08-23
EXECUTOR: Claude (Linux body), standing NIGHT_GRANT
VERDICT: PROSHKA_VERDICT_REQ_2026_08_22_V_H2A_4_1B_3C_1_10_SEMANTIC_ADMISSION_AND_W2_VARIATION_AUTHORIZATION_2026-08-23.md (commit ea6f3109)
TASK: H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE_LEAN (W2)

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
ARISTOTLE: false

BASE_HEAD (pasted verbatim from `git rev-parse HEAD` before commit):
460b017a4effe3755b4b8b99f45689575dd46564

## Deliverable

LEAN_PATH: `q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean`

Public surface (exactly the verdict's mandated surface):

```lean
noncomputable def selectedFerrersLemma73SourcePacket (k : ℕ) : ℝ → ℂ :=
  fun x => selectedFerrersLemma73SourceScale k *
    prolateCombination (selectedFerrersPreAnchorPair k) x

theorem selectedFerrersLemma73SourcePacket_boundedVariationOn (k : ℕ) :
    BoundedVariationOn (selectedFerrersLemma73SourcePacket k) Set.univ
```

DIRECT IMPORTS (as mandated): `Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate`,
`Mathlib.Analysis.BoundedVariation`.

## Proof route executed (matches the verdict's PROOF ROUTE 1-6)

1. **Closed-interval Legendre derivative majorant, polynomial in degree.**
   `mode4OrdinaryLegendrePolynomial_derivative_abs_le_closed`:
   `|P_n'(x)| ≤ n(n+1)` on `[-1,1]`.  Obtained by integrating the exact flux
   identity `((1-x²)P_n')' = -n(n+1)·P_n` (a rearrangement of the
   kernel-checked `mode4OrdinaryLegendrePolynomial_differentialEquation`)
   from the right endpoint (`legendre_flux_derivative`, `legendre_flux_at_one`,
   `legendre_flux_abs_le` via FTC + the kernel-checked closed bound
   `mode4OrdinaryLegendre_abs_le_one`), then dividing by `(1-t)(1+t)` with
   `1+t ≥ 1` on `[0,1)`, extending to `x = 1` by closedness of the sublevel
   set (`closure_Ico`), and reflecting to `[-1,0]` by the kernel-checked
   parity `mode4OrdinaryLegendrePolynomial_derivative_eval_neg`.
   The interior `(1-r²)⁻¹` majorant was NOT used.
2. **Weighted coefficient summability.** `selected_weighted_summable`:
   `Summable ((q+1)² |a_q|)` from the structure field `tail_splice` through
   the kernel-checked
   `mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice`
   at weight `r = 2`, with `hsep = selectedFerrersPreAnchorSeparation k` and
   `Λ ≤ 20` from `mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three`.
   Term bound: `|(-1)^q a_q P_{2q}'(x)| ≤ (2q)(2q+1)|a_q| ≤ 4(q+1)²|a_q|`
   (`firstDerivativeTerm_abs_le_closed`, `firstDerivativeSeries_abs_le_closed`).
3. **Closed-interval Lipschitz bound.** MVT on the open interval
   (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` with the structure
   field `ferrersSeries_hasDerivAt_firstDerivativeSeries`), extended to the
   closed interval through `continuousOn_closed` along the contraction
   family `z_n(t) = t·(n+1)/(n+2)` (`lipschitz_pairs_closed_of_open`,
   `ferrersSeries_lipschitz_closed`).
4. **Transport to the production packet.**
   `normalizedPhysicalMode_lipschitz_on_window` pays the physical scale
   `√m`, the nonnegative `L²` normalization (degenerate normalization handled
   exactly, not assumed away) and the window indicator on the closed window;
   `selectedPacket_lipschitz_on_window` combines both modes through the exact
   integrals `I0, I4`, the exact normalizing denominator and the exact
   complex source scale `selectedFerrersLemma73SourceScale k`.
5. **Global bounded variation with two explicit endpoint jumps.**
   `Set.univ = Iic(-λ) ∪ (Icc(-λ,λ) ∪ Ici λ)` with two applications of
   `eVariationOn.union` at the boundary points `-λ, λ`.  The two tails pay
   exactly one jump each: `eVariationOn_Iic_le_edist_of_zero_on_Iio` /
   `eVariationOn_Ici_le_edist_of_zero_on_Ioi` (a monotone card crosses the
   boundary at most once — Finset card ≤ 1 argument).  The middle window is
   `LipschitzOnWith.comp_boundedVariationOn` over `id`, whose variation is
   closed by `MonotoneOn.eVariationOn_le`.  Packet vanishing outside the
   window comes from the pair's support fields (`selectedPacket_zero_outside`).
6. **Axiom audit.** Both `#print axioms` in-file:
   `selectedFerrersLemma73SourcePacket_boundedVariationOn` and the mandatory
   plant depend on `[propext, Classical.choice, Quot.sound]` only.

## Mandatory plant

`strict_compact_derivative_bound_does_not_supply_closed_endpoint_bound_plant`:
the interior factor `4/(1-r²)+1` tends to `atTop` along `r_k = 1-(k+2)⁻¹`
(lower bound `2(k+2)+1`, `tendsto_atTop_mono`).  Records
STRICT_COMPACT_DERIVATIVE_BOUND_DOES_NOT_SUPPLY_CLOSED_ENDPOINT_BOUND.

## Forbidden-list compliance

- No interior-analyticity-plus-endpoint-continuity BV inference.
- No unweighted `coefficients_abs_summable` in the derivative bound.
- No zero-endpoint-value assumption: full production endpoint values; the
  two jumps are paid explicitly through `eVariationOn.union`.
- No midpoint regularization; the packet is the exact full-endpoint object.
- No differentiation of a C⁰-rate; no Dirichlet–Jordan / Abel imports.
- No cofinal-rate substitute.
- No sorry / admit / native_decide; no axioms beyond the standard three.

## Gates

1. `lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean`
   → exit 0, zero warnings, axiom prints as above.
2. `lake build` → Build completed successfully (7817 jobs), exit 0.
3. `./scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean`
   from repo root → `q3_check ok`, exit 0 (kernel pass + hole-marker scan +
   new-axiom diff scan).
   Environment note: the script's no-argument legacy default (three PSD
   files) currently fails on stale oleans outside the root import graph
   (`PSD_CenteredCoeffAnalyticP0Import.olean` missing); unrelated to this
   task's file, recorded as an observed environment symptom.

OUTCOME: W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE_KERNEL_GREEN
NEXT (per verdict): NEXT_AFTER_SEMANTIC_ADMISSION_ONLY — W3 Abel L² lock
awaits the judge's semantic admission of this W2 certificate.
