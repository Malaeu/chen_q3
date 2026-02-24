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

/-- Temporary amplifier obtained from the current τ=0 criterion axiom route.
Keeps the API stable while we replace this construction with a proof. -/
noncomputable def amplifier_via_tau0_axiom
    (t0 B_min B_max : ℝ) :
    Tau0CounterexampleAmplifier t0 B_min B_max := by
  classical
  refine
    { witness := fun hNotRH => Classical.choose (tau0_separation_via_axiom t0 B_min B_max hNotRH)
      witness_mem := ?_
      witness_neg := ?_ }
  · intro hNotRH
    exact (Classical.choose_spec (tau0_separation_via_axiom t0 B_min B_max hNotRH)).1
  · intro hNotRH
    exact (Classical.choose_spec (tau0_separation_via_axiom t0 B_min B_max hNotRH)).2

/-- Temporary criterion theorem through the amplifier API.
This is equivalent in strength to the current axiom-backed path, but isolates
the replacement point to `amplifier_via_tau0_axiom`. -/
theorem criterion_via_axiomatic_amplifier
    (t0 B_min B_max : ℝ) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact criterion_of_global_weil_and_amplifier t0 B_min B_max
    (amplifier_via_tau0_axiom t0 B_min B_max)

end Q3.Proofs.WeilCoreTau0
