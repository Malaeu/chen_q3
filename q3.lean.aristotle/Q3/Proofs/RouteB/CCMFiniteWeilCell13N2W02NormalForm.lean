import Q3.Proofs.RouteB.CCMFiniteWeilCell13N2VonMangoldtNormalForm

/-!
# Exact `W02` normal form for the CCM cell `(13, 2)`

This file rewrites the seven source representatives of the closed `W02`
component.  It keeps `log 13`, `pi`, and `sinh` symbolic and proves no
numerical enclosure.
-/

namespace Q3.RouteB

/--
The seven exact `W02` representatives for the CCM cell `(13, 2)`.
-/
theorem ccmW02Entry_13_seven_class_normal_form :
    let L := ccmL 13
    let S := Real.sinh (L / 4) ^ 2
    ccmW02Entry L (-2) (-2) =
        32 * L * S * (L ^ 2 - 64 * Real.pi ^ 2) /
          (L ^ 2 + 64 * Real.pi ^ 2) ^ 2 ∧
    ccmW02Entry L (-2) (-1) =
        32 * L * S * (L ^ 2 - 32 * Real.pi ^ 2) /
          ((L ^ 2 + 64 * Real.pi ^ 2) *
            (L ^ 2 + 16 * Real.pi ^ 2)) ∧
    ccmW02Entry L (-2) 0 =
        32 * L * S / (L ^ 2 + 64 * Real.pi ^ 2) ∧
    ccmW02Entry L (-2) 1 =
        32 * L * S * (L ^ 2 + 32 * Real.pi ^ 2) /
          ((L ^ 2 + 64 * Real.pi ^ 2) *
            (L ^ 2 + 16 * Real.pi ^ 2)) ∧
    ccmW02Entry L (-1) (-1) =
        32 * L * S * (L ^ 2 - 16 * Real.pi ^ 2) /
          (L ^ 2 + 16 * Real.pi ^ 2) ^ 2 ∧
    ccmW02Entry L (-1) 0 =
        32 * L * S / (L ^ 2 + 16 * Real.pi ^ 2) ∧
    ccmW02Entry L 0 0 =
        32 * S / L := by
  dsimp only
  have hLpos : 0 < ccmL 13 := ccmL_pos 13 (by norm_num)
  have hL : ccmL 13 ≠ 0 := ne_of_gt hLpos
  have h16 : ccmL 13 ^ 2 + 16 * Real.pi ^ 2 ≠ 0 := by positivity
  have h64 : ccmL 13 ^ 2 + 64 * Real.pi ^ 2 ≠ 0 := by positivity
  constructor
  · unfold ccmW02Entry
    norm_num
    ring
  constructor
  · unfold ccmW02Entry
    norm_num
    ring
  constructor
  · unfold ccmW02Entry
    norm_num
    field_simp [hL, h64]
    ring
  constructor
  · unfold ccmW02Entry
    norm_num
    ring
  constructor
  · unfold ccmW02Entry
    norm_num
    ring
  constructor
  · unfold ccmW02Entry
    norm_num
    field_simp [hL, h16]
  · unfold ccmW02Entry
    norm_num
    field_simp [hL]

/- P-W02-1: the sign of the mixed mode product is load-bearing. -/
private theorem ccmW02_plant_mixed_sign :
    let L := ccmL 13
    ccmW02Entry L (-2) 1 - ccmW02Entry L (-2) (-1) =
      2048 * L * Real.sinh (L / 4) ^ 2 * Real.pi ^ 2 /
        ((L ^ 2 + 64 * Real.pi ^ 2) *
          (L ^ 2 + 16 * Real.pi ^ 2)) := by
  dsimp only
  rcases ccmW02Entry_13_seven_class_normal_form with
    ⟨_, hneg, _, hpos, _⟩
  rw [hpos, hneg]
  ring

/- P-W02-2: the absolute mode-one and mode-two denominators stay distinct. -/
private theorem ccmW02_plant_mode_square :
    let L := ccmL 13
    ccmW02Entry L (-1) 0 - ccmW02Entry L (-2) 0 =
      1536 * L * Real.sinh (L / 4) ^ 2 * Real.pi ^ 2 /
        ((L ^ 2 + 16 * Real.pi ^ 2) *
          (L ^ 2 + 64 * Real.pi ^ 2)) := by
  dsimp only
  rcases ccmW02Entry_13_seven_class_normal_form with
    ⟨_, _, htwo, _, _, hone, _⟩
  rw [hone, htwo]
  have h16 : ccmL 13 ^ 2 + 16 * Real.pi ^ 2 ≠ 0 := by positivity
  have h64 : ccmL 13 ^ 2 + 64 * Real.pi ^ 2 ≠ 0 := by positivity
  field_simp [h16, h64]
  ring

/- P-W02-3: the central entry cancels exactly one power of `L`. -/
private theorem ccmW02_plant_central_log_power :
    let L := ccmL 13
    L * ccmW02Entry L 0 0 = 32 * Real.sinh (L / 4) ^ 2 := by
  dsimp only
  rcases ccmW02Entry_13_seven_class_normal_form with
    ⟨_, _, _, _, _, _, hcenter⟩
  rw [hcenter]
  have hL : ccmL 13 ≠ 0 :=
    ne_of_gt (ccmL_pos 13 (by norm_num))
  field_simp [hL]

#print axioms ccmW02Entry_13_seven_class_normal_form

end Q3.RouteB
