import Q3.Proofs.RouteB.CCMFiniteWeilCell13N2PrimeKernelNormalForm

/-!
# Nonintegral constant normal form for the CCM cell `(13, 2)`

This file combines the exact `W02` and Prime normal forms with the exact
archimedean constant.  Every literal archimedean integral remains symbolic.
-/

namespace Q3.RouteB

/- P-NIC-1: diagonal and off-diagonal classes select different constants. -/
private theorem ccmNIC_plant_qkernel_zero_selector :
    let L := ccmL 13
    ccmQKernel L (-2) (-2) 0 = 2 ∧
      ccmQKernel L (-2) (-1) 0 = 0 ∧
      ccmQKernel L (-2) 0 0 = 0 ∧
      ccmQKernel L (-2) 1 0 = 0 ∧
      ccmQKernel L (-1) (-1) 0 = 2 ∧
      ccmQKernel L (-1) 0 0 = 0 ∧
      ccmQKernel L 0 0 0 = 2 := by
  dsimp only
  have hL : ccmL 13 ≠ 0 := ne_of_gt (ccmL_pos 13 (by norm_num))
  unfold ccmQKernel
  norm_num
  simp [hL]

/- P-NIC-2: the source logarithm argument at `L = log 13`. -/
private theorem ccmNIC_plant_exact_exp_constant :
    4 * Real.pi *
        ((Real.exp (ccmL 13) - 1) /
          (Real.exp (ccmL 13) + 1)) =
      ((24 : ℝ) * Real.pi) / 7 := by
  rw [ccm_exp_L 13 (by norm_num)]
  ring

/- P-NIC-3: the source factor `q(0) / 2` is load-bearing. -/
private theorem ccmNIC_plant_qzero_half_factor (C I : ℝ) :
    (2 : ℝ) / 2 * (C + I) = C + I := by
  ring

/- P-NIC-4: the source subtraction orientation is load-bearing. -/
private theorem ccmNIC_plant_subtraction_orientation
    (W C I P : ℝ) :
    W - (C + I) - P = W - C - I - P := by
  ring

/- P-NIC-5: the two asymmetric representative labels are distinct. -/
private theorem ccmNIC_plant_representative_label_integrity :
    let L : ℝ := 1
    let x : ℝ := 1 / 4
    (Real.sin (2 * Real.pi * x / L) -
        Real.sin (4 * Real.pi * x / L)) / Real.pi ≠
      -(Real.sin (2 * Real.pi * x / L) +
        Real.sin (4 * Real.pi * x / L)) / (3 * Real.pi) := by
  dsimp only
  rw [show 2 * Real.pi * (1 / 4 : ℝ) / 1 = Real.pi / 2 by ring,
    show 4 * Real.pi * (1 / 4 : ℝ) / 1 = Real.pi by ring,
    Real.sin_pi_div_two, Real.sin_pi]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  intro h
  field_simp [hpi] at h
  norm_num at h

/--
Exact seven-representative normal form of the literal finite CCM Weil entry
for the cell `(13,2)`.  The `W02`, WR-constant, and Prime terms are assembled
without separately enclosing any component; all seven WR integrals remain
literal.
-/
theorem ccmWeilTauN1_13_seven_class_nonintegral_constant_normal_form :
    let L := ccmL 13
    let S := Real.sinh (L / 4) ^ 2
    let C13 : ℝ :=
      Real.eulerMascheroniConstant +
        Real.log (((24 : ℝ) * Real.pi) / 7)
    let primeFunctional : (ℝ → ℝ) → ℝ := fun K =>
      Real.log 2 *
          ((Real.sqrt 2)⁻¹ * K (Real.log 2) +
            (2 : ℝ)⁻¹ * K (2 * Real.log 2) +
            (2 * Real.sqrt 2)⁻¹ * K (3 * Real.log 2)) +
        Real.log 3 *
          ((Real.sqrt 3)⁻¹ * K (Real.log 3) +
            (3 : ℝ)⁻¹ * K (2 * Real.log 3)) +
        Real.log 5 * (Real.sqrt 5)⁻¹ * K (Real.log 5) +
        Real.log 7 * (Real.sqrt 7)⁻¹ * K (Real.log 7) +
        Real.log 11 * (Real.sqrt 11)⁻¹ * K (Real.log 11)
    let K22 : ℝ → ℝ := fun x =>
      2 * (L - x) / L * Real.cos (4 * Real.pi * x / L)
    let K2m1 : ℝ → ℝ := fun x =>
      (Real.sin (2 * Real.pi * x / L) -
          Real.sin (4 * Real.pi * x / L)) / Real.pi
    let K20 : ℝ → ℝ := fun x =>
      -Real.sin (4 * Real.pi * x / L) / (2 * Real.pi)
    let K21 : ℝ → ℝ := fun x =>
      -(Real.sin (2 * Real.pi * x / L) +
          Real.sin (4 * Real.pi * x / L)) / (3 * Real.pi)
    let K11 : ℝ → ℝ := fun x =>
      2 * (L - x) / L * Real.cos (2 * Real.pi * x / L)
    let K10 : ℝ → ℝ := fun x =>
      -Real.sin (2 * Real.pi * x / L) / Real.pi
    let K00 : ℝ → ℝ := fun x =>
      2 * (L - x) / L

    ccmWeilTauN1 13 (-2) (-2) =
        32 * L * S * (L ^ 2 - 64 * Real.pi ^ 2) /
            (L ^ 2 + 64 * Real.pi ^ 2) ^ 2 -
          (C13 +
            (∫ x in Set.Ioc 0 L,
              ccmWRIntegrand L (-2) (-2) x)) -
          primeFunctional K22 ∧

    ccmWeilTauN1 13 (-2) (-1) =
        32 * L * S * (L ^ 2 - 32 * Real.pi ^ 2) /
            ((L ^ 2 + 64 * Real.pi ^ 2) *
              (L ^ 2 + 16 * Real.pi ^ 2)) -
          (∫ x in Set.Ioc 0 L,
            ccmWRIntegrand L (-2) (-1) x) -
          primeFunctional K2m1 ∧

    ccmWeilTauN1 13 (-2) 0 =
        32 * L * S / (L ^ 2 + 64 * Real.pi ^ 2) -
          (∫ x in Set.Ioc 0 L,
            ccmWRIntegrand L (-2) 0 x) -
          primeFunctional K20 ∧

    ccmWeilTauN1 13 (-2) 1 =
        32 * L * S * (L ^ 2 + 32 * Real.pi ^ 2) /
            ((L ^ 2 + 64 * Real.pi ^ 2) *
              (L ^ 2 + 16 * Real.pi ^ 2)) -
          (∫ x in Set.Ioc 0 L,
            ccmWRIntegrand L (-2) 1 x) -
          primeFunctional K21 ∧

    ccmWeilTauN1 13 (-1) (-1) =
        32 * L * S * (L ^ 2 - 16 * Real.pi ^ 2) /
            (L ^ 2 + 16 * Real.pi ^ 2) ^ 2 -
          (C13 +
            (∫ x in Set.Ioc 0 L,
              ccmWRIntegrand L (-1) (-1) x)) -
          primeFunctional K11 ∧

    ccmWeilTauN1 13 (-1) 0 =
        32 * L * S / (L ^ 2 + 16 * Real.pi ^ 2) -
          (∫ x in Set.Ioc 0 L,
            ccmWRIntegrand L (-1) 0 x) -
          primeFunctional K10 ∧

    ccmWeilTauN1 13 0 0 =
        32 * S / L -
          (C13 +
            (∫ x in Set.Ioc 0 L,
              ccmWRIntegrand L 0 0 x)) -
          primeFunctional K00 := by
  dsimp only
  rcases ccmW02Entry_13_seven_class_normal_form with
    ⟨hw22, hw2m1, hw20, hw21, hw11, hw10, hw00⟩
  rcases ccmPrimeEntryN1_13_seven_class_exact_normal_form with
    ⟨hp22, hp2m1, hp20, hp21, hp11, hp10, hp00⟩
  rcases ccmNIC_plant_qkernel_zero_selector with
    ⟨hq22, hq2m1, hq20, hq21, hq11, hq10, hq00⟩
  have harg := ccmNIC_plant_exact_exp_constant
  constructor
  · unfold ccmWeilTauN1 ccmWREntry
    rw [hw22, hp22, hq22, harg]
    ring
  constructor
  · unfold ccmWeilTauN1 ccmWREntry
    rw [hw2m1, hp2m1, hq2m1]
    ring
  constructor
  · unfold ccmWeilTauN1 ccmWREntry
    rw [hw20, hp20, hq20]
    ring
  constructor
  · unfold ccmWeilTauN1 ccmWREntry
    rw [hw21, hp21, hq21]
    ring
  constructor
  · unfold ccmWeilTauN1 ccmWREntry
    rw [hw11, hp11, hq11, harg]
    ring
  constructor
  · unfold ccmWeilTauN1 ccmWREntry
    rw [hw10, hp10, hq10]
    ring
  · unfold ccmWeilTauN1 ccmWREntry
    rw [hw00, hp00, hq00, harg]
    ring

#print axioms ccmWeilTauN1_13_seven_class_nonintegral_constant_normal_form

end Q3.RouteB
