import Q3.Proofs.RouteB.D0ScaledJacobiForcedReceiver

/-!
# The resonant Jacobi receiver compatibility discriminator

At a resonant spectral value, a polynomial-growth forced receiver can exist only when the forcing
has zero projection onto the rapidly decaying homogeneous mode.  This file proves that abstract
necessary condition and its direct nonexistence contrapositive.  It does not evaluate any
source-specific projection.
-/

open Filter Topology
open scoped BigOperators

/-- A polynomial-growth receiver at resonance forces the forcing projection onto the rapidly
decaying kernel mode to vanish. -/
theorem forcingProjection_eq_zero_of_polynomialGrowth_receiver
    (p d r ω b4 Y A : ℕ → ℝ)
    (hω : ∀ q, ω q ≠ 0)
    (hsym :
      ∀ q, ω q * r q =
        ω (q + 1) * p (q + 1))
    (hb4 :
      ∀ q, jacobiOp p d r b4 q = 0)
    (hreceiver :
      ∀ q, jacobiOp p d r Y q = A q / ω q)
    (hresponse :
      Summable (fun q ↦ b4 q * A q))
    (hωr :
      SequencePolynomialGrowth
        (fun q ↦ ω q * r q))
    (hY : SequencePolynomialGrowth Y)
    (hb4rapid : SequenceRapidDecay b4) :
    ∑' q, b4 q * A q = 0 := by
  have hterminal :
      Tendsto (jacobiTerminal ω r Y b4) atTop (nhds 0) :=
    jacobiTerminal_tendsto_zero_of_growth_decay ω r Y b4 hωr hY hb4rapid
  have hcore :=
    scaledSampledResponse_eq_gap_mul_receiverPair
      p d r ω b4 Y (fun _ ↦ 0) A 0 hω hsym
      (fun q ↦ by simp [hb4 q])
      hreceiver hresponse
      (by simpa using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ))))
      hterminal
  simpa using hcore

/-- A nonzero forcing projection rules out every polynomial-growth resonant receiver. -/
theorem no_polynomialGrowth_receiver_of_forcingProjection_ne_zero
    (p d r ω b4 A : ℕ → ℝ)
    (hω : ∀ q, ω q ≠ 0)
    (hsym :
      ∀ q, ω q * r q =
        ω (q + 1) * p (q + 1))
    (hb4 :
      ∀ q, jacobiOp p d r b4 q = 0)
    (hresponse :
      Summable (fun q ↦ b4 q * A q))
    (hωr :
      SequencePolynomialGrowth
        (fun q ↦ ω q * r q))
    (hb4rapid : SequenceRapidDecay b4)
    (hproj : ∑' q, b4 q * A q ≠ 0) :
    ¬ ∃ Y : ℕ → ℝ,
      SequencePolynomialGrowth Y ∧
      ∀ q, jacobiOp p d r Y q = A q / ω q := by
  rintro ⟨Y, hY, hreceiver⟩
  exact hproj <|
    forcingProjection_eq_zero_of_polynomialGrowth_receiver
      p d r ω b4 Y A hω hsym hb4 hreceiver hresponse hωr hY hb4rapid

/-!
Mutation plants for the discriminator boundary:

* P-JC-1: zero forcing has zero projection and is compatible with the zero receiver.
* P-JC-2: a nonzero `b4` forcing projection forbids every polynomial-growth receiver by the second
  theorem.
* P-JC-3: without rapid decay of `b4`, the terminal can retain the compatibility defect.
* P-JC-4: without polynomial growth of `Y`, a dominant receiver can retain a nonzero terminal.
* P-JC-5: neither theorem makes a sign claim; the discriminator is equality versus nonzero.
* P-JC-6: the statements are sequence-generic and contain no distinguished finite calibration.
-/

example : (∑' _q : ℕ, (0 : ℝ)) = 0 := by simp
