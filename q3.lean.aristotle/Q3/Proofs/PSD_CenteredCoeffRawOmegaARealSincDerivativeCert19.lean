import Q3.Proofs.PSD_CenteredCoeffRawOmegaARealSincDerivativePayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Fin19 `realSinc` derivative certificate surface for the RawProduct18 source.

The existing coarse certificate covers rows `0, ..., 17`.  The RawProduct18
Leibniz receiver needs the ShapeSq factor through row `18`, so this file keeps
the same proof-grade rational checker and extends only the row-index surface to
`Fin 19`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- Finite rational certificate surface for `realSinc` derivative rows
`k = 0, ..., 18`. -/
structure Step33Sub0RealSincDerivativeMajorantCert19 where
  prefixN : Fin 19 -> Nat
  tailAbs : Fin 19 -> Rat
  baseAbs : Fin 19 -> Rat

namespace Step33Sub0RealSincDerivativeMajorantCert19

/-- Rational checker obligations for a Fin19 `realSinc` derivative majorant
certificate. -/
structure Valid (data : Step33Sub0RealSincDerivativeMajorantCert19) : Prop where
  tailBudget :
    ∀ k : Fin 19,
      step33Sub0RealSincDerivMajorantTerm k.1 (data.prefixN k) /
          (1 - ((1 : Rat) / 400) ^ 2) <=
        data.tailAbs k
  totalBudget :
    ∀ k : Fin 19,
      (∑ m ∈ Finset.range (data.prefixN k),
          step33Sub0RealSincDerivMajorantTerm k.1 m) +
          data.tailAbs k <=
        data.baseAbs k

/-- Analytic majorant supplied by a Fin19 rational certificate. -/
def ProvidesAnalyticMajorant
    (data : Step33Sub0RealSincDerivativeMajorantCert19) : Prop :=
  ∀ u ∈ Set.Icc (0 : Real) ((1 : Real) / 400),
    ∀ k : Fin 19,
      ‖iteratedDeriv k.1 realSinc u‖ <= (data.baseAbs k : Real)

/-- A valid Fin19 rational prefix/tail certificate provides analytic
`realSinc` derivative majorants for rows `0, ..., 18`. -/
theorem providesAnalyticMajorant_of_valid
    {data : Step33Sub0RealSincDerivativeMajorantCert19}
    (hdata : Valid data) :
    ProvidesAnalyticMajorant data := by
  intro u hu k
  have hAnalytic :=
    realSinc_iteratedDeriv_norm_le_tsum_majorant hu k.1
  let f : Nat -> Real := fun m : Nat =>
    (step33Sub0RealSincDerivMajorantTerm k.1 m : Real)
  let N : Nat := data.prefixN k
  have hf : Summable f := by
    simpa [f] using
      step33Sub0RealSincDerivMajorantTerm_real_shift_summable k.1 0
  have hsplit :
      (Finset.range N).sum f + (∑' m : Nat, f (m + N)) =
        ∑' m : Nat, f m := by
    simpa using (hf.sum_add_tsum_nat_add N)
  have htailGeom :
      (∑' m : Nat, f (m + N)) <=
        (step33Sub0RealSincDerivMajorantTerm k.1 N : Real) /
          (1 - (((1 : Real) / 400) ^ 2)) := by
    simpa [f, N, Nat.add_comm] using
      step33Sub0RealSincDerivMajorantTerm_real_tsum_tail_le k.1 N
  have htailBudget :
      (step33Sub0RealSincDerivMajorantTerm k.1 N : Real) /
          (1 - (((1 : Real) / 400) ^ 2)) <=
        (data.tailAbs k : Real) := by
    have htailBudget' :
        (step33Sub0RealSincDerivMajorantTerm k.1 (data.prefixN k) : Real) /
            (1 - (((1 : Real) / 400) ^ 2)) <=
          (data.tailAbs k : Real) := by
      have htailBudgetRat := hdata.tailBudget k
      norm_num at htailBudgetRat ⊢
      have hcast :
          ((step33Sub0RealSincDerivMajorantTerm k.1 (data.prefixN k) /
              ((159999 : Rat) / 160000) : Rat) : Real) <=
            (data.tailAbs k : Real) := by
        exact_mod_cast htailBudgetRat
      norm_num at hcast
      exact hcast
    simpa [N] using htailBudget'
  have htotal :
      (Finset.range N).sum f + (data.tailAbs k : Real) <=
        (data.baseAbs k : Real) := by
    have htotal' :
        (∑ m ∈ Finset.range (data.prefixN k),
            (step33Sub0RealSincDerivMajorantTerm k.1 m : Real)) +
            (data.tailAbs k : Real) <=
          (data.baseAbs k : Real) := by
      exact_mod_cast hdata.totalBudget k
    simpa [f, N] using htotal'
  have hrow :
      (∑' m : Nat,
        (step33Sub0RealSincDerivMajorantTerm k.1 m : Real)) <=
        (data.baseAbs k : Real) := by
    rw [← hsplit]
    calc
      (Finset.range N).sum f + (∑' m : Nat, f (m + N))
          <= (Finset.range N).sum f + (data.tailAbs k : Real) := by
            exact add_le_add le_rfl (htailGeom.trans htailBudget)
      _ <= (data.baseAbs k : Real) := htotal
  exact hAnalytic.trans hrow

/-- Coarse exact row budget for all `realSinc` derivative rows `0, ..., 18`. -/
def coarseTwoBaseAbs : Step33Sub0RealSincDerivativeMajorantCert19 where
  prefixN := fun _ => 0
  tailAbs := fun _ => 2
  baseAbs := fun _ => 2

/-- The coarse `2` row budget satisfies the Fin19 rational checker. -/
theorem coarseTwoBaseAbs_valid : Valid coarseTwoBaseAbs := by
  constructor
  · intro k
    fin_cases k <;> native_decide
  · intro k
    fin_cases k <;> native_decide

/-- The coarse Fin19 payload supplies analytic `realSinc` majorants through
row `18`. -/
theorem coarseTwoBaseAbs_providesAnalyticMajorant :
    ProvidesAnalyticMajorant coarseTwoBaseAbs :=
  providesAnalyticMajorant_of_valid coarseTwoBaseAbs_valid

end Step33Sub0RealSincDerivativeMajorantCert19
end Step33
end PSDpd
end Q3
