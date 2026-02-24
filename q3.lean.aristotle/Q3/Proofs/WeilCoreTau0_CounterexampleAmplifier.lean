import Q3.Proofs.WeilCoreTau0_CriterionTau0

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.Proofs.WeilCoreTau0

/-!
Counterexample-amplifier layer for the τ=0 criterion route.

The goal is to expose a minimal, reusable contract:
- from `¬ RH`, build a τ=0 test witness with `Q < 0`.
- this contract is exactly `Tau0Separation`, packaged in a structured way
  so it can be implemented independently (manual proof / Aristotle / numerics).
-/

/-- Structured contract for constructing a τ=0 negative witness from `¬ RH`. -/
structure Tau0CounterexampleAmplifier (t0 B_min B_max : ℝ) where
  witness : (¬ Q3.RH) → (ℝ → ℝ)
  witness_mem :
    ∀ hNotRH, witness hNotRH ∈ TestClass t0 B_min B_max
  witness_neg :
    ∀ hNotRH, Q3.Q (witness hNotRH) < 0

/-- Any `Tau0CounterexampleAmplifier` discharges the separation obligation. -/
theorem Tau0CounterexampleAmplifier.to_tau0_separation
    (t0 B_min B_max : ℝ)
    (hAmp : Tau0CounterexampleAmplifier t0 B_min B_max) :
    Tau0Separation t0 B_min B_max := by
  intro hNotRH
  exact ⟨hAmp.witness hNotRH, hAmp.witness_mem hNotRH, hAmp.witness_neg hNotRH⟩

/-- Main criterion route through global nonnegativity + a concrete amplifier. -/
theorem criterion_of_global_weil_and_amplifier
    (t0 B_min B_max : ℝ)
    (hAmp : Tau0CounterexampleAmplifier t0 B_min B_max) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact
    criterion_of_global_nonneg_and_separation t0 B_min B_max
      (hAmp.to_tau0_separation t0 B_min B_max)

/-- Non-axiomatic adapter: quantitative bridge already implies an amplifier
via the global Weil route (`Weil_criterion` + witness bridge from q-approx). -/
noncomputable def amplifier_of_qapprox
    (t0 B_min B_max : ℝ)
    (hApprox : Tau0QApproxBridge t0 B_min B_max) :
    Tau0CounterexampleAmplifier t0 B_min B_max := by
  classical
  let hSep : Tau0Separation t0 B_min B_max :=
    tau0_separation_of_global_weil t0 B_min B_max
      (tau0_witness_bridge_of_qapprox t0 B_min B_max hApprox)
  refine
    { witness := fun hNotRH => Classical.choose (hSep hNotRH)
      witness_mem := ?_
      witness_neg := ?_ }
  · intro hNotRH
    exact (Classical.choose_spec (hSep hNotRH)).1
  · intro hNotRH
    exact (Classical.choose_spec (hSep hNotRH)).2

/-- Legacy name kept for compatibility.
Constructive implementation: build the amplifier from the quantitative bridge,
without using `Weil_criterion_tau0`. -/
noncomputable def amplifier_via_tau0_axiom
    (t0 B_min B_max : ℝ)
    (hApprox : Tau0QApproxBridge t0 B_min B_max) :
    Tau0CounterexampleAmplifier t0 B_min B_max :=
  amplifier_of_qapprox t0 B_min B_max hApprox

/-- Temporary criterion theorem through the amplifier API.
This route is now constructive modulo `Tau0QApproxBridge`. -/
theorem criterion_via_axiomatic_amplifier
    (t0 B_min B_max : ℝ)
    (hApprox : Tau0QApproxBridge t0 B_min B_max) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact criterion_of_global_weil_and_amplifier t0 B_min B_max
    (amplifier_via_tau0_axiom t0 B_min B_max hApprox)

/-- Compact-approximation route to the amplifier criterion. -/
theorem criterion_via_compact_approx_amplifier
    (t0 B_min B_max : ℝ)
    (hApproxWK : Tau0CompactApproxOnWK t0 B_min B_max) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact criterion_via_axiomatic_amplifier t0 B_min B_max
    (tau0_qapprox_of_compact_approx_global t0 B_min B_max hApproxWK)

end Q3.Proofs.WeilCoreTau0
