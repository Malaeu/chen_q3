import Q3.Proofs.RouteB.Proposition59EntireTransform
import Q3.Proofs.RouteB.Proposition59GroundLagrangeZeroSetBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.NumberTheory.ZetaValues

set_option linter.mathlibStandardSet false

/-!
# Proposition 5.9 explicit-product curvature bridge

Judge directive `926c1865` (`REQ-2026-09-03-CURVBRIDGE`), paper proof at Lean
granularity in `PROSHKA_VERDICT_GOAL058_CURVATURE_BRIDGE_PROOF_AND_HS_REPRESENTATION_2026-09-03.md`
§2.1–2.7.  Everything here is finite-cell: no Hadamard factorization, no
entire-function order predicate, no global cancellation of the sine numerator
against the Cauchy denominator at a removable node.
-/

noncomputable section

open Filter Set Polynomial
open scoped Topology BigOperators

namespace Q3.RouteB

/-! ## Step 1 — the finite Cauchy numerator (`P59_FINITE_CAUCHY_NUMERATOR_IDENTITY`) -/

/-- `D_N(z) = ∏_{k ∈ S} (z - x_k)`, the finite Cauchy denominator of
Proposition 5.9 on the carrier `S`. -/
def proposition59CauchyDenominator (L : ℝ) (S : Finset ℤ) : Polynomial ℂ :=
  ∏ k ∈ S, (X - C (proposition59Pole L k))

/-- `P_N(z) = ∑_{k ∈ S} v_k ∏_{j ≠ k} (z - x_j)`, the finite Cauchy numerator.
It is a genuine polynomial: no infinite-function theorem enters. -/
def proposition59CauchyNumerator (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) :
    Polynomial ℂ :=
  ∑ k ∈ S, C (v k) *
    ∏ j ∈ S.erase k, (X - C (proposition59Pole L j))

@[simp] theorem proposition59CauchyDenominator_eval
    (L : ℝ) (S : Finset ℤ) (z : ℂ) :
    (proposition59CauchyDenominator L S).eval z =
      ∏ k ∈ S, (z - proposition59Pole L k) := by
  simp [proposition59CauchyDenominator, eval_prod]

@[simp] theorem proposition59CauchyNumerator_eval
    (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) (z : ℂ) :
    (proposition59CauchyNumerator L S v).eval z =
      ∑ k ∈ S, v k * ∏ j ∈ S.erase k, (z - proposition59Pole L j) := by
  simp [proposition59CauchyNumerator, eval_finset_sum, eval_prod]

/-- The finite Cauchy denominator is nonzero exactly off the lattice. -/
theorem proposition59CauchyDenominator_eval_ne_zero
    (L : ℝ) (S : Finset ℤ) {z : ℂ}
    (hz : ∀ k ∈ S, z ≠ proposition59Pole L k) :
    (proposition59CauchyDenominator L S).eval z ≠ 0 := by
  rw [proposition59CauchyDenominator_eval]
  exact Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hz k hk)

/-- `P59_FINITE_CAUCHY_NUMERATOR_IDENTITY`: off the finite lattice the Cauchy
sum is the quotient of the two finite polynomials. -/
theorem proposition59_finite_cauchy_numerator_identity
    (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) {z : ℂ}
    (hz : ∀ k ∈ S, z ≠ proposition59Pole L k) :
    ∑ k ∈ S, v k / (z - proposition59Pole L k) =
      (proposition59CauchyNumerator L S v).eval z /
        (proposition59CauchyDenominator L S).eval z := by
  have hD : (proposition59CauchyDenominator L S).eval z ≠ 0 :=
    proposition59CauchyDenominator_eval_ne_zero L S hz
  rw [proposition59CauchyNumerator_eval, proposition59CauchyDenominator_eval,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hsplit :
      ∏ j ∈ S, (z - proposition59Pole L j) =
        (z - proposition59Pole L k) *
          ∏ j ∈ S.erase k, (z - proposition59Pole L j) :=
    (Finset.mul_prod_erase S _ hk).symm
  have hk0 : z - proposition59Pole L k ≠ 0 := sub_ne_zero.mpr (hz k hk)
  have hrest : ∏ j ∈ S.erase k, (z - proposition59Pole L j) ≠ 0 := by
    rw [proposition59CauchyDenominator_eval] at hD
    rw [hsplit] at hD
    exact fun h => hD (by rw [h, mul_zero])
  rw [hsplit]
  field_simp

/-- The exact value of the finite Cauchy numerator at an included lattice
point: `P_N(x_j) = v_j ∏_{k ≠ j} (x_j - x_k)`. -/
theorem proposition59CauchyNumerator_eval_at_lattice
    (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) {j : ℤ} (hj : j ∈ S) :
    (proposition59CauchyNumerator L S v).eval (proposition59Pole L j) =
      v j * ∏ k ∈ S.erase j,
        (proposition59Pole L j - proposition59Pole L k) := by
  rw [proposition59CauchyNumerator_eval]
  refine Finset.sum_eq_single j (fun k hk hkj => ?_) (fun h => absurd hj h)
  have hjmem : j ∈ S.erase k := Finset.mem_erase.mpr ⟨Ne.symm hkj, hj⟩
  have : ∏ i ∈ S.erase k,
      (proposition59Pole L j - proposition59Pole L i) = 0 :=
    Finset.prod_eq_zero hjmem (by ring)
  rw [this, mul_zero]

/-- On the lattice the numerator vanishes exactly where the coefficient does. -/
theorem proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff
    {L : ℝ} (hL : L ≠ 0) (S : Finset ℤ) (v : ℤ → ℂ) {j : ℤ} (hj : j ∈ S) :
    (proposition59CauchyNumerator L S v).eval (proposition59Pole L j) = 0 ↔
      v j = 0 := by
  rw [proposition59CauchyNumerator_eval_at_lattice L S v hj]
  have hprod : ∏ k ∈ S.erase j,
      (proposition59Pole L j - proposition59Pole L k) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr ?_
    exact proposition59Pole_ne hL (Finset.mem_erase.mp hk).1.symm
  exact mul_eq_zero_iff_right hprod

#print axioms proposition59_finite_cauchy_numerator_identity
#print axioms proposition59CauchyNumerator_eval_at_lattice
#print axioms proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff

/-! ## Step 2 — numerator root ⟹ transform root
(`P59_NUMERATOR_ROOT_IMP_TRANSFORM_ROOT`)

The included-lattice branch is mandatory.  The sine numerator is never
cancelled against the Cauchy denominator globally: at an included node the
argument goes through the exact removable sampling value
`F(x_j) = √L (−1)^j v_j` instead. -/

/-- The exact removable-node sampling value of the raw transform. -/
theorem proposition59RawTransform_at_lattice
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℂ) {j : ℤ} (hj : j ∈ S) :
    proposition59RawTransform L S v (proposition59Pole L j) =
      (Real.sqrt L : ℂ) * (j.negOnePow : ℂ) * v j := by
  have hsqrt : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hL
  have hsq : (Real.sqrt L : ℂ) * (Real.sqrt L : ℂ) = (L : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hL.le
  unfold proposition59RawTransform
  rw [proposition59PoleKernel_sum_at_lattice hL.ne' S v hj, ← hsq]
  field_simp

/-- `P59_NUMERATOR_ROOT_IMP_TRANSFORM_ROOT`: every root of the finite Cauchy
numerator, including one that coincides with an included lattice point, is a
root of the raw transform. -/
theorem proposition59_numerator_root_imp_transform_root
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℂ) {z : ℂ}
    (hroot : (proposition59CauchyNumerator L S v).eval z = 0) :
    proposition59RawTransform L S v z = 0 := by
  classical
  by_cases hlat : ∃ j ∈ S, z = proposition59Pole L j
  · obtain ⟨j, hj, rfl⟩ := hlat
    have hvj : v j = 0 :=
      (proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff
        hL.ne' S v hj).mp hroot
    rw [proposition59RawTransform_at_lattice hL S v hj, hvj, mul_zero]
  · have hz : ∀ k ∈ S, z ≠ proposition59Pole L k := by
      intro k hk hkz
      exact hlat ⟨k, hk, hkz⟩
    rw [proposition59RawTransform_eq_paper_formula hL.ne' S v hz,
      proposition59_finite_cauchy_numerator_identity L S v hz, hroot,
      zero_div, mul_zero]

/-- Consequence of `ZerosRealOn`: every complex root of the finite Cauchy
numerator is real. -/
theorem proposition59CauchyNumerator_roots_real
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℂ)
    (hzeros : ZerosRealOn Set.univ (proposition59RawTransform L S v))
    {z : ℂ} (hroot : (proposition59CauchyNumerator L S v).eval z = 0) :
    z.im = 0 :=
  hzeros z (Set.mem_univ _)
    (proposition59_numerator_root_imp_transform_root hL S v hroot)

/-! ### Mandatory plants A and B (judge)

Plant A: `N = 1`, `v 0 = 1`, `v (±1) = 0`.  The two included lattice factors
`(z ∓ x_1)` must be produced by the finite numerator `P_N` itself.

Plant B: `N = 1`, `v (-1) = v 0 = v 1 = 1`.  The included lattice values of the
raw transform are nonzero, so they must not survive as sine zeros. -/

/-- Plant A: the finite numerator of the row `v = δ_0` on `I_1` is exactly the
pair of included lattice factors. -/
example (L : ℝ) (z : ℂ) :
    (proposition59CauchyNumerator L ({-1, 0, 1} : Finset ℤ)
        (fun k => if k = 0 then (1 : ℂ) else 0)).eval z =
      (z - proposition59Pole L (-1)) * (z - proposition59Pole L 1) := by
  have herase : ({-1, 0, 1} : Finset ℤ).erase 0 = {-1, 1} := by decide
  simp [proposition59CauchyNumerator_eval, herase,
    Finset.prod_pair (show (-1 : ℤ) ≠ 1 by decide)]

/-- Plant A, second half: those two included lattice points really are roots of
`P_N`, hence roots of the transform. -/
example {L : ℝ} (hL : 0 < L) :
    proposition59RawTransform L ({-1, 0, 1} : Finset ℤ)
        (fun k => if k = 0 then (1 : ℂ) else 0)
        (proposition59Pole L 1) = 0 := by
  refine proposition59_numerator_root_imp_transform_root hL _ _ ?_
  have herase : ({-1, 0, 1} : Finset ℤ).erase 0 = {-1, 1} := by decide
  simp [proposition59CauchyNumerator_eval, herase,
    Finset.prod_pair (show (-1 : ℤ) ≠ 1 by decide)]

/-- Plant B: on the constant row every included lattice value is nonzero. -/
example {L : ℝ} (hL : 0 < L) {j : ℤ} (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) :
    proposition59RawTransform L ({-1, 0, 1} : Finset ℤ) (fun _ => (1 : ℂ))
        (proposition59Pole L j) ≠ 0 := by
  rw [proposition59RawTransform_at_lattice hL _ _ hj]
  have hsqrt : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hL
  have hsign : ((j.negOnePow : ℂ)) ≠ 0 := by
    rw [Int.cast_negOnePow ℂ j]
    exact zpow_ne_zero _ (by norm_num)
  simpa using mul_ne_zero hsqrt hsign

#print axioms proposition59RawTransform_at_lattice
#print axioms proposition59_numerator_root_imp_transform_root
#print axioms proposition59CauchyNumerator_roots_real

/-! ## Step 3 — even, real-rooted polynomials factor into quadratics
(`P59_EVEN_REAL_ROOTED_POLYNOMIAL_QUADRATIC_PRODUCT`)

Finite polynomial algebra only.  `Polynomial.Splits` over `ℂ` is free, so
`Polynomial.Splits.eval_eq_prod_roots` supplies the finite factorization and no
Hadamard product is involved. -/

/-- For an even polynomial the root multiplicities at `a` and `-a` agree. -/
private theorem rootMultiplicity_neg_of_even {p : ℂ[X]} (hp : p ≠ 0)
    (heven : p.comp (-X) = p) (a : ℂ) :
    p.rootMultiplicity (-a) = p.rootMultiplicity a := by
  have key : ∀ (b : ℂ) (n : ℕ), (X - C b) ^ n ∣ p → (X - C (-b)) ^ n ∣ p := by
    rintro b n ⟨q, hq⟩
    refine ⟨(-1 : ℂ[X]) ^ n * q.comp (-X), ?_⟩
    have h2 : p = (-X - C b) ^ n * q.comp (-X) := by
      conv_lhs => rw [← heven]
      rw [hq]
      simp [mul_comp, pow_comp, sub_comp]
    rw [h2, C_neg, show (X - -C b : ℂ[X]) = X + C b by ring,
      show (-X - C b : ℂ[X]) = -(X + C b) by ring, neg_pow]
    ring
  have le1 : p.rootMultiplicity a ≤ p.rootMultiplicity (-a) := by
    rw [le_rootMultiplicity_iff hp]
    exact key a _ ((le_rootMultiplicity_iff hp).mp le_rfl)
  have le2 : p.rootMultiplicity (-a) ≤ p.rootMultiplicity a := by
    rw [le_rootMultiplicity_iff hp]
    simpa using key (-a) _ ((le_rootMultiplicity_iff hp).mp le_rfl)
  exact le_antisymm le2 le1

/-- The root multiset of an even polynomial is invariant under negation. -/
private theorem roots_map_neg_of_even {p : ℂ[X]} (hp : p ≠ 0)
    (heven : p.comp (-X) = p) :
    p.roots.map (fun r => -r) = p.roots := by
  classical
  refine Multiset.ext.mpr fun a => ?_
  have hcount := Multiset.count_map_eq_count'
    (fun r : ℂ => -r) p.roots neg_injective (-a)
  simp only [neg_neg] at hcount
  rw [hcount, Polynomial.count_roots, Polynomial.count_roots,
    rootMultiplicity_neg_of_even hp heven a]

open scoped Classical in
/-- The multiset of positive roots, with multiplicity, of a complex polynomial
whose roots are all real. -/
noncomputable def positiveRootMultiset (p : ℂ[X]) : Multiset ℝ :=
  (p.roots.filter (fun r => 0 < r.re)).map Complex.re

theorem positiveRootMultiset_pos {p : ℂ[X]} {ρ : ℝ}
    (hρ : ρ ∈ positiveRootMultiset p) : 0 < ρ := by
  classical
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hρ
  exact (Multiset.mem_filter.mp hr).2

/-- `P59_EVEN_REAL_ROOTED_POLYNOMIAL_QUADRATIC_PRODUCT`: an even complex
polynomial with only real roots and nonzero value at the origin is, after
normalization at the origin, the finite product of the paired quadratics
`1 - z²/ρ²` over its positive roots. -/
theorem eval_div_eval_zero_eq_prod_positiveRootMultiset
    {p : ℂ[X]} (hp0 : p.eval 0 ≠ 0) (heven : ∀ z : ℂ, p.eval (-z) = p.eval z)
    (hreal : ∀ z : ℂ, p.eval z = 0 → z.im = 0) (z : ℂ) :
    p.eval z / p.eval 0 =
      ((positiveRootMultiset p).map
        (fun ρ : ℝ => 1 - z ^ 2 / (ρ : ℂ) ^ 2)).prod := by
  classical
  have hp : p ≠ 0 := fun h => hp0 (by simp [h])
  have hcomp : p.comp (-X) = p := by
    refine Polynomial.funext fun w => ?_
    simpa using heven w
  have hsplits : p.Splits := IsAlgClosed.splits p
  -- roots are nonzero real numbers
  have hroot_ne : ∀ r ∈ p.roots, r ≠ 0 := by
    intro r hr hr0
    subst hr0
    exact hp0 ((Polynomial.mem_roots hp).mp hr)
  have hroot_re : ∀ r ∈ p.roots, ((r.re : ℂ)) = r := by
    intro r hr
    have him : r.im = 0 := hreal r ((Polynomial.mem_roots hp).mp hr)
    exact Complex.ext rfl (by simp [him])
  have hroot_re_ne : ∀ r ∈ p.roots, r.re ≠ 0 := by
    intro r hr hre
    exact hroot_ne r hr (by rw [← hroot_re r hr, hre]; simp)
  -- the factorization normalized at the origin
  have hprodroots : p.eval z = p.eval 0 *
      (p.roots.map (fun r => 1 - z / r)).prod := by
    rw [hsplits.eval_eq_prod_roots z, hsplits.eval_eq_prod_roots 0, mul_assoc,
      ← Multiset.prod_map_mul]
    congr 2
    refine Multiset.map_congr rfl fun r hr => ?_
    have hrne : r ≠ 0 := hroot_ne r hr
    field_simp
    ring
  -- split the roots into the positive part and its mirror image
  set Pos : Multiset ℂ := p.roots.filter (fun r => 0 < r.re) with hPos
  set Neg : Multiset ℂ := p.roots.filter (fun r => ¬ 0 < r.re) with hNeg
  have hsplit : Pos + Neg = p.roots := Multiset.filter_add_not _ _
  have hNegMap : Neg = Pos.map (fun r => -r) := by
    have hmapneg := roots_map_neg_of_even hp hcomp
    have h1 : Neg = Multiset.filter (fun r : ℂ => ¬ 0 < r.re)
        (p.roots.map (fun r => -r)) := by rw [hmapneg]
    rw [h1, Multiset.filter_map]
    congr 1
    refine Multiset.filter_congr fun r hr => ?_
    have hre := hroot_re_ne r hr
    simp only [Function.comp_apply, Complex.neg_re]
    constructor
    · intro h
      exact lt_of_le_of_ne (by linarith [not_lt.mp h]) (Ne.symm hre)
    · intro h
      exact not_lt.mpr (by linarith)
  -- assemble the paired quadratic product
  have hpair : (p.roots.map (fun r => 1 - z / r)).prod =
      (Pos.map (fun r => 1 - z ^ 2 / r ^ 2)).prod := by
    rw [← hsplit, Multiset.map_add, Multiset.prod_add, hNegMap,
      Multiset.map_map, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun r hr => ?_)
    have hrne : r ≠ 0 := hroot_ne r (Multiset.mem_of_mem_filter hr)
    simp only [Function.comp_apply]
    field_simp
    ring
  have hposre : (Pos.map (fun r => 1 - z ^ 2 / r ^ 2)) =
      (positiveRootMultiset p).map
        (fun ρ : ℝ => 1 - z ^ 2 / (ρ : ℂ) ^ 2) := by
    rw [positiveRootMultiset, Multiset.map_map]
    refine Multiset.map_congr rfl fun r hr => ?_
    rw [Function.comp_apply, hroot_re r (Multiset.mem_of_mem_filter hr)]
  rw [hprodroots, hpair, hposre, mul_comm, mul_div_assoc, div_self hp0, mul_one]

#print axioms positiveRootMultiset_pos
#print axioms eval_div_eval_zero_eq_prod_positiveRootMultiset

/-! ### The finite numerator on the symmetric window is even -/

theorem proposition59Pole_neg (L : ℝ) (k : ℤ) :
    proposition59Pole L (-k) = -proposition59Pole L k := by
  simp [proposition59Pole]
  ring

theorem card_Icc_symm (N : ℕ) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  omega

/-- `P_N` on a symmetric window with an even coefficient row is an even
polynomial. -/
theorem proposition59CauchyNumerator_eval_neg
    (L : ℝ) (N : ℕ) {v : ℤ → ℂ} (hv : ∀ k : ℤ, v (-k) = v k) (z : ℂ) :
    (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v).eval (-z) =
      (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v).eval z := by
  classical
  set S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hSdef
  have hmemS : ∀ k : ℤ, k ∈ S ↔ -k ∈ S := by
    intro k
    simp [hSdef, Finset.mem_Icc]
    omega
  rw [proposition59CauchyNumerator_eval, proposition59CauchyNumerator_eval]
  refine Finset.sum_equiv (Equiv.neg ℤ) (fun k => ?_) (fun k hk => ?_)
  · simpa using hmemS k
  · have hkS : k ∈ S := hk
    have hcard : (S.erase k).card = 2 * N := by
      rw [Finset.card_erase_of_mem hkS, card_Icc_symm]
      omega
    have hsign : ∏ _j ∈ S.erase k, (-1 : ℂ) = 1 := by
      rw [Finset.prod_const, hcard, pow_mul]
      norm_num
    have hinner :
        ∏ j ∈ S.erase k, (-z - proposition59Pole L j) =
          ∏ j ∈ S.erase (-k), (z - proposition59Pole L j) := by
      have hstep :
          ∏ j ∈ S.erase k, (-z - proposition59Pole L j) =
            ∏ j ∈ S.erase k, (z - proposition59Pole L (-j)) := by
        rw [show (∏ j ∈ S.erase k, (z - proposition59Pole L (-j))) =
            ∏ j ∈ S.erase k,
              ((-1 : ℂ) * (-z - proposition59Pole L j)) from
          Finset.prod_congr rfl fun j _ => by
            rw [proposition59Pole_neg]; ring]
        rw [Finset.prod_mul_distrib, hsign, one_mul]
      rw [hstep]
      refine Finset.prod_equiv (Equiv.neg ℤ) (fun j => ?_) (fun j _ => by simp)
      simp only [Equiv.neg_apply, Finset.mem_erase, ne_eq, neg_inj]
      constructor
      · rintro ⟨hjk, hjS⟩
        exact ⟨hjk, (hmemS j).mp hjS⟩
      · rintro ⟨hjk, hjS⟩
        exact ⟨hjk, (hmemS j).mpr hjS⟩
    rw [hinner]
    simp only [Equiv.neg_apply, hv]

#print axioms proposition59CauchyNumerator_eval_neg

/-! ### Step 3 applied to the Proposition-5.9 numerator -/

theorem proposition59CauchyNumerator_eval_zero_ne_zero
    {L : ℝ} (hL : L ≠ 0) (N : ℕ) (v : ℤ → ℂ) (hv0 : v 0 ≠ 0) :
    (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v).eval 0 ≠ 0 := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by simp
  have hpole : proposition59Pole L 0 = 0 := by simp [proposition59Pole]
  intro h
  refine hv0 ((proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff hL _ v h0).mp ?_)
  rw [hpole]
  exact h

/-- The normalized finite factorization of the Proposition-5.9 Cauchy numerator
under the two source hypotheses `ZerosRealOn` and `v 0 ≠ 0`. -/
theorem proposition59CauchyNumerator_normalized_product
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℂ) (hv : ∀ k : ℤ, v (-k) = v k)
    (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v))
    (z : ℂ) :
    (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v).eval z /
        (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v).eval 0 =
      ((positiveRootMultiset
          (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v)).map
        (fun ρ : ℝ => 1 - z ^ 2 / (ρ : ℂ) ^ 2)).prod :=
  eval_div_eval_zero_eq_prod_positiveRootMultiset
    (proposition59CauchyNumerator_eval_zero_ne_zero hL.ne' N v hv0)
    (proposition59CauchyNumerator_eval_neg L N hv)
    (fun _ hw => proposition59CauchyNumerator_roots_real hL _ v hzeros hw) z

#print axioms proposition59CauchyNumerator_eval_zero_ne_zero
#print axioms proposition59CauchyNumerator_normalized_product

/-! ## Step 4a — the removable-node-safe included-factor identity

The finite included lattice factors are moved to the left-hand side, so no
denominator is cancelled at a node where it vanishes.  The identity is proved
for every `z`: off the lattice by the Cauchy quotient, at the central node by
the exact removable value, and at a nonzero node by the *exact* vanishing of
both sides (the sine numerator is not cancelled globally). -/

/-- `v 0 * D_N(z) = z * P_N(0) * ∏_{k ≠ 0} (1 - z/x_k)`; the finite algebra
that moves the included lattice factors across. -/
theorem proposition59CauchyDenominator_eq_included_factors
    {L : ℝ} (hL : L ≠ 0) (N : ℕ) (v : ℤ → ℂ) (z : ℂ) :
    v 0 * (proposition59CauchyDenominator L (Finset.Icc (-(N : ℤ)) (N : ℤ))).eval z =
      z * (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v).eval 0 *
        ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
          (1 - z / proposition59Pole L k) := by
  classical
  set S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hSdef
  have h0 : (0 : ℤ) ∈ S := by simp [hSdef]
  have hpole0 : proposition59Pole L 0 = 0 := by simp [proposition59Pole]
  have hxk : ∀ k ∈ S.erase 0, proposition59Pole L k ≠ 0 := by
    intro k hk
    rw [← hpole0]
    exact proposition59Pole_ne hL (Finset.mem_erase.mp hk).1
  have hD : (proposition59CauchyDenominator L S).eval z =
      z * ∏ k ∈ S.erase 0, (z - proposition59Pole L k) := by
    rw [proposition59CauchyDenominator_eval, ← Finset.mul_prod_erase S _ h0, hpole0]
    ring
  have hP0 : (proposition59CauchyNumerator L S v).eval 0 =
      v 0 * ∏ k ∈ S.erase 0, (0 - proposition59Pole L k) := by
    have := proposition59CauchyNumerator_eval_at_lattice L S v h0
    rwa [hpole0] at this
  have hfac : ∏ k ∈ S.erase 0, (z - proposition59Pole L k) =
      (∏ k ∈ S.erase 0, (0 - proposition59Pole L k)) *
        ∏ k ∈ S.erase 0, (1 - z / proposition59Pole L k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk0 := hxk k hk
    field_simp
    ring
  rw [hD, hfac, hP0]
  ring

/-- Step 4a (`P59_REMOVABLE_LATTICE_PRODUCT_EXTENSION`, exact form): for every
`z`, including the removable nodes. -/
theorem proposition59_included_factor_product_identity
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℂ) (hv0 : v 0 ≠ 0) (z : ℂ) :
    proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v z *
        ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
          (1 - z / proposition59Pole L k) =
      proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v 0 *
        ((proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v).eval z /
          (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v).eval 0) *
        (proposition59PoleKernel L 0 z / (L : ℂ)) := by
  classical
  set S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hSdef
  have h0 : (0 : ℤ) ∈ S := by simp [hSdef]
  have hpole0 : proposition59Pole L 0 = 0 := by simp [proposition59Pole]
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hP0 : (proposition59CauchyNumerator L S v).eval 0 ≠ 0 :=
    proposition59CauchyNumerator_eval_zero_ne_zero hL.ne' N v hv0
  have hsqrt : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hL
  have hsq : (Real.sqrt L : ℂ) * (Real.sqrt L : ℂ) = (L : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hL.le
  have hF0 : proposition59RawTransform L S v 0 = (Real.sqrt L : ℂ) * v 0 :=
    proposition59RawTransform_at_zero_eq_sqrt hL S v h0
  by_cases hlat : ∃ j ∈ S, z = proposition59Pole L j
  · obtain ⟨j, hj, rfl⟩ := hlat
    by_cases hj0 : j = 0
    · subst j
      rw [hpole0]
      have hone : ∏ k ∈ S.erase 0, (1 - (0 : ℂ) / proposition59Pole L k) = 1 := by
        simp
      have hker : proposition59PoleKernel L 0 0 = (L : ℂ) := by
        rw [← hpole0, proposition59PoleKernel_at_pole hL.ne' 0]
        simp
      rw [hone, hker, div_self hP0, div_self hLC]
      ring
    · have hjerase : j ∈ S.erase 0 := Finset.mem_erase.mpr ⟨hj0, hj⟩
      have hzero : ∏ k ∈ S.erase 0,
          (1 - proposition59Pole L j / proposition59Pole L k) = 0 :=
        Finset.prod_eq_zero hjerase (by
          have : proposition59Pole L j ≠ 0 := by
            rw [← hpole0]; exact proposition59Pole_ne hL.ne' hj0
          field_simp
          ring)
      have hker : proposition59PoleKernel L 0 (proposition59Pole L j) = 0 := by
        rw [proposition59PoleKernel_at_lattice_sign hL.ne' 0 j, if_neg (Ne.symm hj0)]
      rw [hzero, hker, mul_zero, zero_div, mul_zero]
  · have hz : ∀ k ∈ S, z ≠ proposition59Pole L k := fun k hk hkz => hlat ⟨k, hk, hkz⟩
    have hz0 : z ≠ 0 := by
      have := hz 0 h0
      rwa [hpole0] at this
    have hDne : (proposition59CauchyDenominator L S).eval z ≠ 0 :=
      proposition59CauchyDenominator_eval_ne_zero L S hz
    have hFz : proposition59RawTransform L S v z =
        (Real.sqrt L : ℂ)⁻¹ * proposition59Numerator L z *
          ((proposition59CauchyNumerator L S v).eval z /
            (proposition59CauchyDenominator L S).eval z) := by
      rw [proposition59RawTransform_eq_paper_formula hL.ne' S v hz,
        proposition59_finite_cauchy_numerator_identity L S v hz]
    have hker : proposition59PoleKernel L 0 z =
        proposition59Numerator L z / z := by
      rw [proposition59PoleKernel_eq_quotient hL.ne' 0 (by rw [hpole0]; exact hz0),
        hpole0, sub_zero]
    have hDrel := proposition59CauchyDenominator_eq_included_factors hL.ne' N v z
    have hPi : ∏ k ∈ S.erase 0, (1 - z / proposition59Pole L k) =
        v 0 * (proposition59CauchyDenominator L S).eval z /
          (z * (proposition59CauchyNumerator L S v).eval 0) := by
      rw [eq_div_iff (mul_ne_zero hz0 hP0), hDrel]
      ring
    rw [hFz, hker, hF0, hPi, ← hsq]
    field_simp

#print axioms proposition59CauchyDenominator_eq_included_factors
#print axioms proposition59_included_factor_product_identity

/-- Step 4a combined with step 3: the exact, node-safe explicit-product form of
the Proposition-5.9 transform.  The right-hand side carries the finite positive
root product of `P_N` and the entire removable sine factor
`proposition59PoleKernel L 0 z / L = sin(zL/2)/(zL/2)`; the finite included
lattice factors stay on the left, so nothing is cancelled at a removable node. -/
theorem proposition59_explicit_product_identity
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℂ) (hv : ∀ k : ℤ, v (-k) = v k)
    (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v))
    (z : ℂ) :
    proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v z *
        ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
          (1 - z / proposition59Pole L k) =
      proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v 0 *
        ((positiveRootMultiset
            (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v)).map
          (fun ρ : ℝ => 1 - z ^ 2 / (ρ : ℂ) ^ 2)).prod *
        (proposition59PoleKernel L 0 z / (L : ℂ)) := by
  rw [proposition59_included_factor_product_identity hL N v hv0 z,
    proposition59CauchyNumerator_normalized_product hL N v hv hv0 hzeros z]

#print axioms proposition59_explicit_product_identity

/-- Plant D in machine-checkable form: the normalization hypothesis used
throughout, `v 0 ≠ 0`, is literally `F 0 ≠ 0`. -/
theorem proposition59RawTransform_at_zero_ne_zero_iff
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℂ) :
    proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v 0 ≠ 0 ↔
      v 0 ≠ 0 := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by simp
  have hsqrt : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hL
  rw [proposition59RawTransform_at_zero_eq_sqrt hL _ v h0]
  simp [hsqrt]

#print axioms proposition59RawTransform_at_zero_ne_zero_iff

/-! ## Steps 5 and 6 — the exact curvature identity, finite route

The Euler tail limit is never formed.  Instead the node-safe step-4a identity
`F · A = F 0 · Q · s` is differentiated twice at the origin, where `A` and `Q`
are *polynomials* in `z²` and `s = sin(zL/2)/(zL/2)` is the already-formalized
removable kernel, whose exact second jet is
`proposition59PoleKernel_secondDerivative_zero`. -/

/-! ### Calculus and polynomial helpers -/

private theorem iteratedDeriv_two_eq_deriv_deriv (h : ℂ → ℂ) (z : ℂ) :
    iteratedDeriv 2 h z = deriv (deriv h) z := by
  simp [iteratedDeriv_succ]

private theorem iteratedDeriv_two_mul_of_differentiable
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (z : ℂ) :
    iteratedDeriv 2 (fun w => f w * g w) z =
      iteratedDeriv 2 f z * g z + 2 * (deriv f z * deriv g z) +
        f z * iteratedDeriv 2 g z := by
  have hf2 : ContDiff ℂ 2 f := hf.contDiff.of_le le_top
  have hg2 : ContDiff ℂ 2 g := hg.contDiff.of_le le_top
  have hdf : Differentiable ℂ (deriv f) := hf2.differentiable_deriv_two
  have hdg : Differentiable ℂ (deriv g) := hg2.differentiable_deriv_two
  have hstep : deriv (fun w => f w * g w) =
      fun w => deriv f w * g w + f w * deriv g w := by
    funext w
    exact deriv_mul (hf w) (hg w)
  have hA : HasDerivAt (fun w => deriv f w * g w)
      (deriv (deriv f) z * g z + deriv f z * deriv g z) z :=
    (hdf z).hasDerivAt.mul (hg z).hasDerivAt
  have hB : HasDerivAt (fun w => f w * deriv g w)
      (deriv f z * deriv g z + f z * deriv (deriv g) z) z :=
    (hf z).hasDerivAt.mul (hdg z).hasDerivAt
  have hAB : HasDerivAt (fun w => deriv f w * g w + f w * deriv g w)
      (deriv (deriv f) z * g z + deriv f z * deriv g z +
        (deriv f z * deriv g z + f z * deriv (deriv g) z)) z := hA.add hB
  rw [iteratedDeriv_two_eq_deriv_deriv, hstep,
    iteratedDeriv_two_eq_deriv_deriv f, iteratedDeriv_two_eq_deriv_deriv g,
    hAB.deriv]
  ring

private theorem polyEval_deriv_zero (p : Polynomial ℂ) :
    deriv (fun z : ℂ => p.eval z) 0 = p.coeff 1 := by
  rw [Polynomial.deriv]
  simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]

private theorem polyEval_iteratedDeriv_two_zero (p : Polynomial ℂ) :
    iteratedDeriv 2 (fun z : ℂ => p.eval z) 0 = 2 * p.coeff 2 := by
  have hd : deriv (fun z : ℂ => p.eval z) =
      fun z : ℂ => (Polynomial.derivative p).eval z := by
    funext z
    exact Polynomial.deriv p
  rw [iteratedDeriv_two_eq_deriv_deriv, hd, Polynomial.deriv]
  simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  ring

/-- The finite even factor `∏ (1 - c z²)` as a polynomial. -/
noncomputable def quadProductPoly (c : Multiset ℂ) : Polynomial ℂ :=
  (c.map (fun a => 1 - Polynomial.C a * Polynomial.X ^ 2)).prod

@[simp] theorem quadProductPoly_eval (c : Multiset ℂ) (z : ℂ) :
    (quadProductPoly c).eval z = (c.map (fun a => 1 - a * z ^ 2)).prod := by
  simp [quadProductPoly, Polynomial.eval_multiset_prod, Multiset.map_map]

theorem quadProductPoly_coeff_zero (c : Multiset ℂ) :
    (quadProductPoly c).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, quadProductPoly_eval]
  simp

theorem quadProductPoly_coeff_one (c : Multiset ℂ) :
    (quadProductPoly c).coeff 1 = 0 := by
  induction c using Multiset.induction_on with
  | empty => simp [quadProductPoly, Polynomial.coeff_one]
  | cons a c ih =>
      have hfac : quadProductPoly (a ::ₘ c) =
          (1 - Polynomial.C a * Polynomial.X ^ 2) * quadProductPoly c := by
        simp [quadProductPoly]
      rw [hfac, Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [Finset.sum_range_succ, Polynomial.coeff_one,
        quadProductPoly_coeff_zero, ih]

theorem quadProductPoly_coeff_two (c : Multiset ℂ) :
    (quadProductPoly c).coeff 2 = -c.sum := by
  induction c using Multiset.induction_on with
  | empty => simp [quadProductPoly, Polynomial.coeff_one]
  | cons a c ih =>
      have hfac : quadProductPoly (a ::ₘ c) =
          (1 - Polynomial.C a * Polynomial.X ^ 2) * quadProductPoly c := by
        simp [quadProductPoly]
      rw [hfac, Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [Finset.sum_range_succ, Polynomial.coeff_one,
        quadProductPoly_coeff_zero, quadProductPoly_coeff_one, ih]

/-- Pairing of a symmetric integer window with its centre removed. -/
theorem prod_erase_zero_Icc_symm {M : Type*} [CommMonoid M] (N : ℕ) (g : ℤ → M) :
    ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, g k =
      ∏ k ∈ Finset.Icc 1 N, (g (k : ℤ) * g (-(k : ℤ))) := by
  classical
  induction N with
  | zero => simp
  | succ n ih =>
      have hset : (Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)).erase 0 =
          insert ((n : ℤ) + 1)
            (insert (-((n : ℤ) + 1)) ((Finset.Icc (-(n : ℤ)) (n : ℤ)).erase 0)) := by
        ext a
        simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem1 : -((n : ℤ) + 1) ∉ (Finset.Icc (-(n : ℤ)) (n : ℤ)).erase 0 := by
        simp only [Finset.mem_erase, Finset.mem_Icc]
        omega
      have hnotmem2 : ((n : ℤ) + 1) ∉
          insert (-((n : ℤ) + 1)) ((Finset.Icc (-(n : ℤ)) (n : ℤ)).erase 0) := by
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc]
        omega
      have hcast : ((n : ℕ) + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [show (-(((n : ℕ) + 1 : ℕ) : ℤ)) = -((n : ℤ) + 1) by push_cast; ring,
        show ((((n : ℕ) + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 by push_cast; ring,
        hset, Finset.prod_insert hnotmem2, Finset.prod_insert hnotmem1, ih,
        Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
      push_cast
      rw [← mul_assoc, mul_comm]

#print axioms quadProductPoly_coeff_two
#print axioms prod_erase_zero_Icc_symm

/-! ### The two even factor polynomials -/

/-- `c_k = 1/x_k²` for the included lattice modes `1 ≤ k ≤ N`. -/
noncomputable def proposition59IncludedCoefficients (L : ℝ) (N : ℕ) : Multiset ℂ :=
  (Finset.Icc 1 N).val.map (fun k : ℕ => ((proposition59Pole L (k : ℤ)) ^ 2)⁻¹)

/-- `c_ρ = 1/ρ²` over the positive roots of the finite Cauchy numerator. -/
noncomputable def proposition59RootCoefficients
    (L : ℝ) (N : ℕ) (v : ℤ → ℂ) : Multiset ℂ :=
  (positiveRootMultiset
      (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v)).map
    (fun ρ : ℝ => ((ρ : ℂ) ^ 2)⁻¹)

theorem proposition59IncludedFactors_eq_eval
    {L : ℝ} (hL : 0 < L) (N : ℕ) (z : ℂ) :
    ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
        (1 - z / proposition59Pole L k) =
      (quadProductPoly (proposition59IncludedCoefficients L N)).eval z := by
  rw [prod_erase_zero_Icc_symm, quadProductPoly_eval,
    proposition59IncludedCoefficients, Multiset.map_map]
  rw [show ((Finset.Icc 1 N).val.map
      ((fun a : ℂ => 1 - a * z ^ 2) ∘
        fun k : ℕ => ((proposition59Pole L (k : ℤ)) ^ 2)⁻¹)).prod =
      ∏ k ∈ Finset.Icc 1 N,
        (1 - ((proposition59Pole L (k : ℤ)) ^ 2)⁻¹ * z ^ 2) from rfl]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk0 : (k : ℤ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  have hxk : proposition59Pole L (k : ℤ) ≠ 0 := by
    have hp0 : proposition59Pole L 0 = 0 := by simp [proposition59Pole]
    rw [← hp0]
    exact proposition59Pole_ne hL.ne' hk0
  rw [proposition59Pole_neg]
  field_simp
  ring

theorem proposition59RootFactors_eq_eval
    (L : ℝ) (N : ℕ) (v : ℤ → ℂ) (z : ℂ) :
    ((positiveRootMultiset
        (proposition59CauchyNumerator L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v)).map
      (fun ρ : ℝ => 1 - z ^ 2 / (ρ : ℂ) ^ 2)).prod =
      (quadProductPoly (proposition59RootCoefficients L N v)).eval z := by
  rw [quadProductPoly_eval, proposition59RootCoefficients, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun ρ _ => ?_)
  simp [div_eq_inv_mul]

/-! ### The removable sine factor `s(z) = sin(zL/2)/(zL/2)` -/

private theorem proposition59Sinc_at_zero {L : ℝ} (hL : 0 < L) :
    (L : ℂ)⁻¹ * proposition59PoleKernel L 0 0 = 1 := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hp0 : proposition59Pole L 0 = 0 := by simp [proposition59Pole]
  have : proposition59PoleKernel L 0 0 = (L : ℂ) := by
    rw [← hp0, proposition59PoleKernel_at_pole hL.ne' 0]
    simp
  rw [this, inv_mul_cancel₀ hLC]

private theorem proposition59Sinc_secondDeriv {L : ℝ} (hL : 0 < L) :
    iteratedDeriv 2
        (fun z : ℂ => (L : ℂ)⁻¹ * proposition59PoleKernel L 0 z) 0 =
      -((L : ℂ) ^ 2) / 12 := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hcd : ContDiffAt ℂ 2 (proposition59PoleKernel L 0) 0 :=
    ((differentiable_proposition59PoleKernel L 0).contDiff.of_le le_top).contDiffAt
  rw [iteratedDeriv_const_mul hcd,
    proposition59PoleKernel_secondDerivative_zero hL 0]
  simp [proposition59SecondJetCoefficient]
  field_simp

/-! ### Step 5 — the exact second jet of `F` from the explicit product -/

/-- `P59_CURVATURE_SECOND_JET_REAL` (jet half): differentiating the node-safe
step-4a identity twice at the origin.  All first derivatives at the origin
carry a vanishing partner, so no unknown `F'(0)` survives. -/
theorem proposition59_secondDerivative_zero_from_product
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℂ) (hv : ∀ k : ℤ, v (-k) = v k)
    (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v)) :
    iteratedDeriv 2
        (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v) 0 =
      proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v 0 *
        (-2 * (proposition59RootCoefficients L N v).sum - (L : ℂ) ^ 2 / 12
          + 2 * (proposition59IncludedCoefficients L N).sum) := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hSdef
  set Fe : ℂ → ℂ := proposition59RawTransform L S v with hFedef
  set Ap : Polynomial ℂ :=
    quadProductPoly (proposition59IncludedCoefficients L N) with hApdef
  set Qp : Polynomial ℂ :=
    quadProductPoly (proposition59RootCoefficients L N v) with hQpdef
  set sK : ℂ → ℂ :=
    fun z => (L : ℂ)⁻¹ * proposition59PoleKernel L 0 z with hsKdef
  have hFdiff : Differentiable ℂ Fe :=
    differentiable_proposition59RawTransform L S v
  have hAdiff : Differentiable ℂ (fun z : ℂ => Ap.eval z) := Ap.differentiable
  have hQdiff : Differentiable ℂ (fun z : ℂ => Qp.eval z) := Qp.differentiable
  have hsdiff : Differentiable ℂ sK :=
    (differentiable_proposition59PoleKernel L 0).const_mul _
  have hGdiff : Differentiable ℂ (fun z : ℂ => Fe 0 * Qp.eval z) :=
    hQdiff.const_mul _
  have hQcd : ContDiffAt ℂ 2 (fun z : ℂ => Qp.eval z) 0 :=
    (hQdiff.contDiff.of_le le_top).contDiffAt
  -- the step-4a identity, as an equality of functions
  have hid : (fun z : ℂ => Fe z * Ap.eval z) =
      fun z : ℂ => (Fe 0 * Qp.eval z) * sK z := by
    funext z
    rw [hApdef, hQpdef, ← proposition59IncludedFactors_eq_eval hL N z,
      ← proposition59RootFactors_eq_eval L N v z, hsKdef]
    rw [proposition59_explicit_product_identity hL N v hv hv0 hzeros z]
    field_simp
    ring
  have hjet := congrArg (fun h : ℂ → ℂ => iteratedDeriv 2 h 0) hid
  simp only at hjet
  rw [iteratedDeriv_two_mul_of_differentiable hFdiff hAdiff 0,
    iteratedDeriv_two_mul_of_differentiable hGdiff hsdiff 0] at hjet
  have hA0 : Ap.eval 0 = 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hApdef, quadProductPoly_coeff_zero]
  have hA1 : deriv (fun z : ℂ => Ap.eval z) 0 = 0 := by
    rw [polyEval_deriv_zero, hApdef, quadProductPoly_coeff_one]
  have hA2 : iteratedDeriv 2 (fun z : ℂ => Ap.eval z) 0 =
      -2 * (proposition59IncludedCoefficients L N).sum := by
    rw [polyEval_iteratedDeriv_two_zero, hApdef, quadProductPoly_coeff_two]
    ring
  have hQ0 : Qp.eval 0 = 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hQpdef, quadProductPoly_coeff_zero]
  have hQ1 : deriv (fun z : ℂ => Qp.eval z) 0 = 0 := by
    rw [polyEval_deriv_zero, hQpdef, quadProductPoly_coeff_one]
  have hQ2 : iteratedDeriv 2 (fun z : ℂ => Qp.eval z) 0 =
      -2 * (proposition59RootCoefficients L N v).sum := by
    rw [polyEval_iteratedDeriv_two_zero, hQpdef, quadProductPoly_coeff_two]
    ring
  have hG1 : deriv (fun z : ℂ => Fe 0 * Qp.eval z) 0 = 0 := by
    rw [deriv_const_mul _ (hQdiff 0), hQ1, mul_zero]
  have hG2 : iteratedDeriv 2 (fun z : ℂ => Fe 0 * Qp.eval z) 0 =
      Fe 0 * (-2 * (proposition59RootCoefficients L N v).sum) := by
    rw [iteratedDeriv_const_mul hQcd, hQ2]
  have hs0 : sK 0 = 1 := proposition59Sinc_at_zero hL
  have hs2 : iteratedDeriv 2 sK 0 = -((L : ℂ) ^ 2) / 12 :=
    proposition59Sinc_secondDeriv hL
  rw [hA0, hA1, hA2, hQ0, hG1, hG2, hs0, hs2] at hjet
  linear_combination hjet

#print axioms proposition59IncludedFactors_eq_eval
#print axioms proposition59RootFactors_eq_eval
#print axioms proposition59_secondDerivative_zero_from_product

end Q3.RouteB
