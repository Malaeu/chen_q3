import Mathlib

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- Half the smaller of the next-even and bottom-odd gaps above the selected
even ground level. -/
def sectorIsolationRadius
    (epsilonPlus1 epsilonPlus2 epsilonMinus1 : ℝ) : ℝ :=
  min (epsilonPlus2 - epsilonPlus1)
      (epsilonMinus1 - epsilonPlus1) / 2

theorem sectorIsolationRadius_pos
    {epsilonPlus1 epsilonPlus2 epsilonMinus1 : ℝ}
    (hEven : epsilonPlus1 < epsilonPlus2)
    (hOdd : epsilonPlus1 < epsilonMinus1) :
    0 < sectorIsolationRadius epsilonPlus1 epsilonPlus2 epsilonMinus1 := by
  unfold sectorIsolationRadius
  exact div_pos
    (lt_min (sub_pos.mpr hEven) (sub_pos.mpr hOdd))
    (by norm_num)

theorem sectorIsolationRadius_le_even_gap
    {epsilonPlus1 epsilonPlus2 epsilonMinus1 : ℝ}
    (hEven : epsilonPlus1 < epsilonPlus2) :
    sectorIsolationRadius epsilonPlus1 epsilonPlus2 epsilonMinus1 ≤
      epsilonPlus2 - epsilonPlus1 := by
  unfold sectorIsolationRadius
  have hgap : 0 ≤ epsilonPlus2 - epsilonPlus1 := sub_nonneg.mpr hEven.le
  have hmin :
      min (epsilonPlus2 - epsilonPlus1)
          (epsilonMinus1 - epsilonPlus1) ≤
        epsilonPlus2 - epsilonPlus1 := min_le_left _ _
  linarith

theorem sectorIsolationRadius_le_odd_gap
    {epsilonPlus1 epsilonPlus2 epsilonMinus1 : ℝ}
    (hOdd : epsilonPlus1 < epsilonMinus1) :
    sectorIsolationRadius epsilonPlus1 epsilonPlus2 epsilonMinus1 ≤
      epsilonMinus1 - epsilonPlus1 := by
  unfold sectorIsolationRadius
  have hgap : 0 ≤ epsilonMinus1 - epsilonPlus1 := sub_nonneg.mpr hOdd.le
  have hmin :
      min (epsilonPlus2 - epsilonPlus1)
          (epsilonMinus1 - epsilonPlus1) ≤
        epsilonMinus1 - epsilonPlus1 := min_le_right _ _
  linarith

theorem sectorIsolationRadius_isolates
    {epsilonPlus1 epsilonPlus2 epsilonMinus1 mu : ℝ}
    (hEven : epsilonPlus1 < epsilonPlus2)
    (hOdd : epsilonPlus1 < epsilonMinus1)
    (hmu : epsilonPlus2 ≤ mu ∨ epsilonMinus1 ≤ mu) :
    sectorIsolationRadius epsilonPlus1 epsilonPlus2 epsilonMinus1 ≤
      mu - epsilonPlus1 := by
  rcases hmu with hmu | hmu
  · exact (sectorIsolationRadius_le_even_gap hEven).trans
      (sub_le_sub_right hmu epsilonPlus1)
  · exact (sectorIsolationRadius_le_odd_gap hOdd).trans
      (sub_le_sub_right hmu epsilonPlus1)

theorem sectorIsolationRadius_certificate
    {epsilonPlus1 epsilonPlus2 epsilonMinus1 : ℝ}
    (hEven : epsilonPlus1 < epsilonPlus2)
    (hOdd : epsilonPlus1 < epsilonMinus1) :
    0 < sectorIsolationRadius epsilonPlus1 epsilonPlus2 epsilonMinus1 ∧
      sectorIsolationRadius epsilonPlus1 epsilonPlus2 epsilonMinus1 ≤
        epsilonPlus2 - epsilonPlus1 ∧
      sectorIsolationRadius epsilonPlus1 epsilonPlus2 epsilonMinus1 ≤
        epsilonMinus1 - epsilonPlus1 ∧
      ∀ mu : ℝ, epsilonPlus2 ≤ mu ∨ epsilonMinus1 ≤ mu →
        sectorIsolationRadius epsilonPlus1 epsilonPlus2 epsilonMinus1 ≤
          mu - epsilonPlus1 := by
  exact ⟨sectorIsolationRadius_pos hEven hOdd,
    sectorIsolationRadius_le_even_gap hEven,
    sectorIsolationRadius_le_odd_gap hOdd,
    fun _ hmu => sectorIsolationRadius_isolates hEven hOdd hmu⟩

#print axioms sectorIsolationRadius_pos
#print axioms sectorIsolationRadius_le_even_gap
#print axioms sectorIsolationRadius_le_odd_gap
#print axioms sectorIsolationRadius_isolates
#print axioms sectorIsolationRadius_certificate

end Q3.RouteB
