/-
Production port source: ACTIVE/requests/routeB_lamport_rh_closure/muntz_v3/RequestProject/MellinConvergentSqrtTail.lean
Source SHA-256: dc91214ad1b7b09a37e0c90eae8891ddf8d1d743550d70380ad77cc6e31c9b04
Body copied byte-for-byte; import path rewritten only.
Port date: 2026-08-06
-/

import Q3.Proofs.RouteB.MuntzV3.Core

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace EStarMuntzZeroMassContinuation

/-- A local square-root estimate at zero together with eventual vanishing is
enough for Mellin convergence throughout the half-plane `-1 / 2 < re s`. -/
theorem mellinConvergent_of_sqrtBound_eventuallyZero
    (f : ℝ → ℂ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (C B : ℝ)
    (hsqrt :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        ‖f u‖ ≤ C * Real.sqrt u)
    (htail : ∀ u, B < u → f u = 0)
    (s : ℂ) (hs : (-1 : ℝ) / 2 < s.re) :
    MellinConvergent f s := by
  have htop :
      f =O[atTop] (fun x : ℝ => x ^ (-(s.re + 1))) := by
    apply (isBigO_zero (fun x : ℝ => x ^ (-(s.re + 1))) atTop).congr'
    · filter_upwards [eventually_gt_atTop B] with x hx
      exact (htail x hx).symm
    · rfl
  have hbot :
      f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(-(1 : ℝ) / 2))) := by
    rw [isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (Iio_mem_nhds (show 0 < (1 : ℝ) by norm_num))]
      with u hu hu1
    have hsqrt_u := hsqrt u ⟨hu, hu1⟩
    rw [Real.sqrt_eq_rpow] at hsqrt_u
    have hexp : (1 / 2 : ℝ) = -(-(1 : ℝ) / 2) := by norm_num
    rw [hexp] at hsqrt_u
    have hrpow_nonneg : 0 ≤ u ^ (-(-(1 : ℝ) / 2)) :=
      Real.rpow_nonneg hu.le _
    rw [Real.norm_eq_abs, abs_of_nonneg hrpow_nonneg]
    exact hsqrt_u
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith) hbot hs

#print axioms mellinConvergent_of_sqrtBound_eventuallyZero

end EStarMuntzZeroMassContinuation
