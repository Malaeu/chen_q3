import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NormalForm

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Raw-product order-18 bridge for the Step33A.1-A sub0 degree-0 preflight.

The checked degree-0 receiver for the active-actual order-16 row still needs a
proof-grade uniform bound for
`D^17(ComponentProductActual)` on the active cell.  The normal-form file already
proves that `ComponentProductActual` is the derivative of the raw product
`OmegaActual * ShapeSqActual`.  This file records the exact index shift needed
by the current route:

`D^17(ComponentProductActual) = D^18(RawProductActual)`.

It does not provide the missing order-18 raw-product majorant.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

private theorem iteratedDeriv_deriv_eq_succ
    (n : Nat) (f : Real -> Real) (eta : Real) :
    iteratedDeriv n (fun x : Real => deriv f x) eta =
      iteratedDeriv (n + 1) f eta := by
  induction n generalizing eta with
  | zero =>
      rw [iteratedDeriv_succ]
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv n (fun x : Real => deriv f x) =
            iteratedDeriv (n + 1) f := by
        funext x
        exact ih x
      rw [hfun]
      rw [← iteratedDeriv_succ]

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18
    (eta : Real) :
    iteratedDeriv 17
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta =
      iteratedDeriv 18
        primaryFiniteRow0Parent0Split100Sub0RawProductActual eta := by
  have hfun :
      primaryFiniteRow0Parent0Split100Sub0ComponentProductActual =
        fun x : Real =>
          deriv primaryFiniteRow0Parent0Split100Sub0RawProductActual x := by
    funext x
    exact
      primaryFiniteRow0Parent0Split100Sub0_componentProductActual_eq_rawProductDeriv
        x
  rw [hfun]
  simpa using
    iteratedDeriv_deriv_eq_succ 17
      primaryFiniteRow0Parent0Split100Sub0RawProductActual eta

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_abs
    (raw18Abs : Real)
    (hRaw18 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 18
            primaryFiniteRow0Parent0Split100Sub0RawProductActual eta‖ <=
          raw18Abs) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
        raw18Abs := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18]
  exact hRaw18 eta hEta

end Step33
end PSDpd
end Q3
