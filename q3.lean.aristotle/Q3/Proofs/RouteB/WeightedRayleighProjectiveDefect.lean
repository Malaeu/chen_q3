import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators

noncomputable section
namespace Q3.RouteB

theorem weighted_projective_defect_mul_gap_le_rayleigh_excess
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ground : ι) (weight level : ι → ℝ) (alpha gap : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight_sum : ∑ i, weight i = 1)
    (hground : level ground = 0)
    (hgap : ∀ i, i ≠ ground → gap ≤ level i)
    (halpha : alpha = ∑ i, weight i * level i) :
    gap * (1 - weight ground) ≤ alpha := by
  have hcomplement :
      Finset.sum (Finset.univ.erase ground) weight = 1 - weight ground := by
    have hsplit := Finset.sum_erase_add (s := Finset.univ)
      (f := weight) (Finset.mem_univ ground)
    rw [hweight_sum] at hsplit
    linarith
  have hbound :
      Finset.sum (Finset.univ.erase ground) (fun i => gap * weight i) ≤
        Finset.sum (Finset.univ.erase ground) (fun i => weight i * level i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hig : i ≠ ground := Finset.ne_of_mem_erase hi
    nlinarith [hweight i, hgap i hig]
  rw [halpha]
  calc
    gap * (1 - weight ground) =
        Finset.sum (Finset.univ.erase ground) (fun i => gap * weight i) := by
      rw [← hcomplement, Finset.mul_sum]
    _ ≤ Finset.sum (Finset.univ.erase ground) (fun i => weight i * level i) := hbound
    _ = ∑ i, weight i * level i := by
      have hsplit := Finset.sum_erase_add (s := Finset.univ)
        (f := fun i => weight i * level i) (Finset.mem_univ ground)
      simpa only [hground, mul_zero, add_zero] using hsplit

theorem weighted_projective_defect_le_rayleigh_excess_div_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ground : ι) (weight level : ι → ℝ) (alpha gap : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight_sum : ∑ i, weight i = 1)
    (hground : level ground = 0)
    (hgap_pos : 0 < gap)
    (hgap : ∀ i, i ≠ ground → gap ≤ level i)
    (halpha : alpha = ∑ i, weight i * level i) :
    1 - weight ground ≤ alpha / gap := by
  apply (le_div_iff₀ hgap_pos).2
  simpa [mul_comm] using
    weighted_projective_defect_mul_gap_le_rayleigh_excess
      ground weight level alpha gap hweight hweight_sum hground hgap halpha

#print axioms weighted_projective_defect_mul_gap_le_rayleigh_excess
#print axioms weighted_projective_defect_le_rayleigh_excess_div_gap

end Q3.RouteB
