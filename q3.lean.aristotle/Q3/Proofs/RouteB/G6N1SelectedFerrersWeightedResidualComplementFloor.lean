import Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

open Complex Matrix Filter
open scoped BigOperators Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# H2a.4.1b.2 — weighted residual to eventual complement floor

Floor `H2A_4_1B_2_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR` of
verdict `b3e0e6ea`.

The exact downstream consequence of the ratified weighted-residual
consumer: with a fixed positive floor `β0` on both exact reflection
sectors, odd-mass decay together with the weighted residual contract

`√(oddMass_k) · √(residualEnergy_k) → 0`

forces the H2A.1 effective floor to tend to `β0`, hence the literal
complement-floor predicate holds **eventually with the fixed constant
`β0/2`**.  Plain residual decay `ρ_k → 0` is never assumed — the second
plant records that it was never the consumer, and the first plant records
that the weighted contract is load-bearing.

This theorem proves no source rate: the weighted residual source rate
remains open (`H2A_4_1B_3`).  The source-action split is deliberately NOT
imported here.

Deliberately NOT here: sector-floor suppliers, source-action analysis,
simple ground, Theorem 5.10, real zeros.

LEDGER:
  CLOSES: [SELECTED_FERRERS_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR,
           RESIDUAL_DECAY_NOT_REQUIRED_FOR_H2A_EFFECTIVE_FLOOR]
  OPENS:  []
-/

/-! ## The two mandatory plants -/

/-- **Plant 1.**  The weighted residual contract is load-bearing: with
`η_n = (n+2)⁻²` and `ρ_n = (n+2)²`, the odd mass tends to zero, yet
`√η_n · ρ_n = n+2` does not tend to zero, and the H2A.1 effective floor
with sector floor `1` is negative for every `n`.  Odd-mass decay alone
does not keep the floor positive. -/
private theorem weighted_residual_is_load_bearing_plant :
    ∃ (η ρ : ℕ → ℝ),
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
      ¬ Filter.Tendsto (fun n => Real.sqrt (η n) * ρ n)
          Filter.atTop (nhds 0) ∧
      ∀ n, 1 * (1 - η n) -
        (2 * Real.sqrt (η n) + η n) / Real.sqrt (1 - η n) * ρ n < 0 := by
  classical
  refine ⟨fun n => (((n:ℝ) + 2)⁻¹) ^ 2, fun n => ((n:ℝ) + 2) ^ 2,
    ?_, ?_, ?_⟩
  · have hbase : Filter.Tendsto (fun n : ℕ => ((n:ℝ) + 2)⁻¹)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((n:ℝ) + 2))
          Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact h1.inv_tendsto_atTop
    have := hbase.mul hbase
    simpa [sq] using this
  · intro hcontra
    have hval : ∀ n : ℕ,
        Real.sqrt ((((n:ℝ) + 2)⁻¹) ^ 2) * ((n:ℝ) + 2) ^ 2 =
          (n:ℝ) + 2 := by
      intro n
      have hpos : (0:ℝ) < (n:ℝ) + 2 := by positivity
      rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ ((n:ℝ) + 2)⁻¹)]
      field_simp
    have hlt := hcontra.eventually_lt_const
      (by norm_num : (0:ℝ) < 1)
    rw [Filter.eventually_atTop] at hlt
    obtain ⟨N0, hN0⟩ := hlt
    have h := hN0 N0 (le_refl N0)
    rw [hval N0] at h
    have : (0:ℝ) ≤ (N0 : ℝ) := Nat.cast_nonneg _
    linarith
  · intro n
    have hpos : (0:ℝ) < (n:ℝ) + 2 := by positivity
    set c : ℝ := ((n:ℝ) + 2)⁻¹ with hc
    have hc0 : 0 < c := by positivity
    have hchalf : c ≤ 1/2 := by
      rw [hc]
      have h2 : (2:ℝ) ≤ (n:ℝ) + 2 := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      calc ((n:ℝ) + 2)⁻¹ ≤ (2:ℝ)⁻¹ :=
            (inv_le_inv₀ (by linarith) (by norm_num)).mpr h2
        _ = 1/2 := by norm_num
    have hsqrtc : Real.sqrt (c ^ 2) = c := Real.sqrt_sq hc0.le
    have hcsq : c ^ 2 ≤ 1/4 := by nlinarith
    have h1c : (0:ℝ) < 1 - c ^ 2 := by nlinarith
    have hsqrt1 : Real.sqrt (1 - c ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith [sq_nonneg c]
    have hsqrt1pos : 0 < Real.sqrt (1 - c ^ 2) :=
      Real.sqrt_pos.mpr h1c
    have hcinv : c * ((n:ℝ) + 2) ^ 2 = (n:ℝ) + 2 := by
      rw [hc]
      field_simp
    have hquot : 2 * c ≤
        (2 * Real.sqrt (c ^ 2) + c ^ 2) / Real.sqrt (1 - c ^ 2) := by
      rw [hsqrtc]
      rw [le_div_iff₀ hsqrt1pos]
      nlinarith [hc0.le, sq_nonneg c]
    have hcont : 2 * ((n:ℝ) + 2) ≤
        (2 * Real.sqrt (c ^ 2) + c ^ 2) / Real.sqrt (1 - c ^ 2) *
          ((n:ℝ) + 2) ^ 2 := by
      calc 2 * ((n:ℝ) + 2) = 2 * c * ((n:ℝ) + 2) ^ 2 := by
            rw [mul_assoc, hcinv]
        _ ≤ (2 * Real.sqrt (c ^ 2) + c ^ 2) / Real.sqrt (1 - c ^ 2) *
              ((n:ℝ) + 2) ^ 2 :=
            mul_le_mul_of_nonneg_right hquot (by positivity)
    have hn4 : (4:ℝ) ≤ 2 * ((n:ℝ) + 2) := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    nlinarith [hcont, hn4, sq_nonneg c]

/-- **Plant 2.**  Residual decay was never the consumer: with exactly even
rows (`η_n = 0`) and arbitrary unbounded `ρ_n = n`, the H2A.1 effective
floor with sector floor `1` equals exactly `1` for every `n`. -/
private theorem residual_decay_is_not_necessary_plant :
    ∃ (η ρ : ℕ → ℝ),
      (∀ n, η n = 0) ∧ (∀ n, ρ n = (n:ℝ)) ∧
      ∀ n, 1 * (1 - η n) -
        (2 * Real.sqrt (η n) + η n) / Real.sqrt (1 - η n) * ρ n = 1 := by
  refine ⟨fun _ => 0, fun n => (n:ℝ), fun _ => rfl, fun _ => rfl, ?_⟩
  intro n
  simp

/-! ## Local groundwork -/

private lemma selected_oddMass_nonneg
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    0 ≤ selectedFerrersFiniteCCMOddMass P k := by
  unfold selectedFerrersFiniteCCMOddMass
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

private lemma dot_star_self_re_nonneg
    {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    0 ≤ (star v ⬝ᵥ v).re := by
  classical
  unfold dotProduct
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [Pi.star_apply, show star (v j) * v j =
    ((Complex.normSq (v j) : ℝ) : ℂ) by
      rw [show star (v j) = (starRingEnd ℂ) (v j) from rfl, mul_comm,
        Complex.mul_conj]]
  rw [Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-! ## The public theorem -/

/-- **H2A.4.1B.2.**  The weighted residual contract closes the eventual
complement floor: with a fixed positive sector floor `β0` on both exact
reflection sectors, odd-mass decay and `√η_k·ρ_k → 0` force the literal
H2A.1 complement-floor predicate with the fixed constant `β0/2`,
eventually along the selected schedule.  Plain residual decay is not
assumed anywhere. -/
theorem selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (β0 : ℝ) (hβ0 : 0 < β0)
    (hη : Filter.Tendsto
      (fun k => selectedFerrersFiniteCCMOddMass P k)
      Filter.atTop (nhds 0))
    (hweighted : Filter.Tendsto
      (fun k =>
        Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
          Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k))
      Filter.atTop (nhds 0))
    (heven : ∀ᶠ k in Filter.atTop,
      ∀ x,
        ccmComplexReflectionMatrix
            ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = x →
        star ((2⁻¹ : ℂ) •
          (selectedFerrersFiniteCCMRow P k +
            ccmComplexReflectionMatrix
              ((selectedFerrersCofinalSourceData P).index k).N *ᵥ
                selectedFerrersFiniteCCMRow P k)) ⬝ᵥ x = 0 →
        β0 * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((sourceCCMFiniteMatrix
                ((selectedFerrersCofinalSourceData P).index k) -
              ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
                (1 : Matrix _ _ ℂ)) *ᵥ x)).re)
    (hodd : ∀ᶠ k in Filter.atTop,
      ∀ x,
        ccmComplexReflectionMatrix
            ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = -x →
        β0 * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((sourceCCMFiniteMatrix
                ((selectedFerrersCofinalSourceData P).index k) -
              ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
                (1 : Matrix _ _ ℂ)) *ᵥ x)).re) :
    ∀ᶠ k in Filter.atTop,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix
          ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ)
        (β0 / 2) := by
  classical
  -- the exact H2A.1 effective floor sequence
  set F : ℕ → ℝ := fun k =>
    β0 * (1 - selectedFerrersFiniteCCMOddMass P k) -
      (2 * Real.sqrt (selectedFerrersFiniteCCMOddMass P k) +
        selectedFerrersFiniteCCMOddMass P k) /
        Real.sqrt (1 - selectedFerrersFiniteCCMOddMass P k) *
        Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k) with hF
  -- limit machinery
  have hsqrtη : Filter.Tendsto
      (fun k => Real.sqrt (selectedFerrersFiniteCCMOddMass P k))
      Filter.atTop (nhds 0) := by
    have := hη.sqrt
    simpa using this
  have h1mη : Filter.Tendsto
      (fun k => 1 - selectedFerrersFiniteCCMOddMass P k)
      Filter.atTop (nhds 1) := by
    have h := Filter.Tendsto.sub
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (1:ℝ)) Filter.atTop (nhds 1)) hη
    simpa using h
  have hsqrt1m : Filter.Tendsto
      (fun k => Real.sqrt (1 - selectedFerrersFiniteCCMOddMass P k))
      Filter.atTop (nhds 1) := by
    have := h1mη.sqrt
    simpa using this
  have hnum : Filter.Tendsto
      (fun k => 2 + Real.sqrt (selectedFerrersFiniteCCMOddMass P k))
      Filter.atTop (nhds 2) := by
    have h := Filter.Tendsto.add
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (2:ℝ)) Filter.atTop (nhds 2)) hsqrtη
    simpa using h
  have hcoeff : Filter.Tendsto
      (fun k => (2 + Real.sqrt (selectedFerrersFiniteCCMOddMass P k)) /
        Real.sqrt (1 - selectedFerrersFiniteCCMOddMass P k))
      Filter.atTop (nhds 2) := by
    have := hnum.div hsqrt1m one_ne_zero
    simpa using this
  have hcont : Filter.Tendsto
      (fun k => (2 + Real.sqrt (selectedFerrersFiniteCCMOddMass P k)) /
        Real.sqrt (1 - selectedFerrersFiniteCCMOddMass P k) *
        (Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
          Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k)))
      Filter.atTop (nhds 0) := by
    have := hcoeff.mul hweighted
    simpa using this
  have hmain : Filter.Tendsto
      (fun k => β0 * (1 - selectedFerrersFiniteCCMOddMass P k))
      Filter.atTop (nhds β0) := by
    have h := Filter.Tendsto.mul
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => β0) Filter.atTop (nhds β0)) h1mη
    simpa using h
  -- the algebraic identity splitting the contamination term
  have halg : ∀ k, F k =
      β0 * (1 - selectedFerrersFiniteCCMOddMass P k) -
        (2 + Real.sqrt (selectedFerrersFiniteCCMOddMass P k)) /
          Real.sqrt (1 - selectedFerrersFiniteCCMOddMass P k) *
          (Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
            Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k)) := by
    intro k
    have hid : 2 * Real.sqrt (selectedFerrersFiniteCCMOddMass P k) +
        selectedFerrersFiniteCCMOddMass P k =
        (2 + Real.sqrt (selectedFerrersFiniteCCMOddMass P k)) *
          Real.sqrt (selectedFerrersFiniteCCMOddMass P k) := by
      have h := Real.mul_self_sqrt (selected_oddMass_nonneg P k)
      calc 2 * Real.sqrt (selectedFerrersFiniteCCMOddMass P k) +
          selectedFerrersFiniteCCMOddMass P k =
          2 * Real.sqrt (selectedFerrersFiniteCCMOddMass P k) +
            Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
              Real.sqrt (selectedFerrersFiniteCCMOddMass P k) := by
            rw [h]
        _ = (2 + Real.sqrt (selectedFerrersFiniteCCMOddMass P k)) *
            Real.sqrt (selectedFerrersFiniteCCMOddMass P k) := by ring
    show β0 * (1 - selectedFerrersFiniteCCMOddMass P k) -
        (2 * Real.sqrt (selectedFerrersFiniteCCMOddMass P k) +
          selectedFerrersFiniteCCMOddMass P k) /
          Real.sqrt (1 - selectedFerrersFiniteCCMOddMass P k) *
          Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k) = _
    rw [hid]
    ring
  have hFlim : Filter.Tendsto F Filter.atTop (nhds β0) := by
    have hcomb := hmain.sub hcont
    rw [sub_zero] at hcomb
    exact hcomb.congr fun k => (halg k).symm
  -- eventual facts
  have hev_half : ∀ᶠ k in Filter.atTop, β0 / 2 ≤ F k :=
    hFlim.eventually_const_le (half_lt_self hβ0)
  have hev_η1 : ∀ᶠ k in Filter.atTop,
      selectedFerrersFiniteCCMOddMass P k < 1 :=
    hη.eventually_lt_const (by norm_num : (0:ℝ) < 1)
  filter_upwards [hev_half, hev_η1, heven, hodd] with k hFk hη1 hevenk hoddk
  -- receiver at the exact effective floor
  have hρ0 : (0:ℝ) ≤
      Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k) :=
    Real.sqrt_nonneg _
  have hρsq : (star (selectedFerrersFiniteCCMResidual P k) ⬝ᵥ
      selectedFerrersFiniteCCMResidual P k).re ≤
      Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k) ^ 2 := by
    rw [Real.sq_sqrt (selectedFerrersFiniteCCMResidualEnergy_nonneg P k)]
    exact le_of_eq rfl
  have hbeta : F k = min β0 β0 *
      (1 - selectedFerrersFiniteCCMOddMass P k) -
      (2 * Real.sqrt (selectedFerrersFiniteCCMOddMass P k) +
        selectedFerrersFiniteCCMOddMass P k) /
        Real.sqrt (1 - selectedFerrersFiniteCCMOddMass P k) *
        Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k) := by
    rw [min_self]
  have hbeta0 : 0 < F k :=
    lt_of_lt_of_le (half_pos hβ0) hFk
  have hfloor :=
    selectedFerrersFiniteCCMComplementFloor_of_sectorFloors_oddMass_residual
      P k β0 β0
      (Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k))
      (F k) hη1 hevenk hoddk hρ0 hρsq hbeta hbeta0
  -- downgrade the varying effective floor to the fixed constant β0/2
  obtain ⟨hFpos, hbound⟩ := hfloor
  refine ⟨half_pos hβ0, ?_⟩
  intro x
  calc β0 / 2 *
      ((star (complexTrialLineComplement
          (selectedFerrersFiniteCCMRow P k) *ᵥ x)) ⬝ᵥ
        (complexTrialLineComplement
          (selectedFerrersFiniteCCMRow P k) *ᵥ x)).re
      ≤ F k *
        ((star (complexTrialLineComplement
            (selectedFerrersFiniteCCMRow P k) *ᵥ x)) ⬝ᵥ
          (complexTrialLineComplement
            (selectedFerrersFiniteCCMRow P k) *ᵥ x)).re :=
        mul_le_mul_of_nonneg_right hFk
          (dot_star_self_re_nonneg _)
    _ ≤ _ := hbound x

#print axioms selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
#print axioms weighted_residual_is_load_bearing_plant
#print axioms residual_decay_is_not_necessary_plant

end Q3.RouteB.D0Pstar

end
