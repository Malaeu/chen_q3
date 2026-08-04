import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

set_option linter.mathlibStandardSet false

/-
Source lock:
- Connes–Consani–Moscovici, Zeta Spectral Triples
- arXiv:2511.22755v1, Lemma 5.1
- e-print SHA-256:
  96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a
- scope: general finite structured beta and source commutator only
-/

namespace Q3.RouteB

open Matrix MeasureTheory
open scoped BigOperators

/-- The source beta scalar recovered from the central column. -/
noncomputable def ccmBetaScalar (mProject : ℕ) (n : ℤ) : ℝ :=
  (n : ℝ) * ccmWeilTauN1 mProject n 0

/-- The source beta vector on the ordered finite carrier. -/
noncomputable def ccmBetaFinite
    (mProject N : ℕ) : CCMModeFinite N → ℝ :=
  fun i =>
    (ccmModeFinite N i : ℝ) *
      ccmWeilMatFinite mProject N i (ccmCenterFinite N)

@[simp] theorem ccmModeFinite_center (N : ℕ) :
    ccmModeFinite N (ccmCenterFinite N) = 0 := by
  simp [ccmModeFinite, ccmCenterFinite]

theorem ccmModeFinite_injective (N : ℕ) :
    Function.Injective (ccmModeFinite N) := by
  intro i j hij
  apply Fin.ext
  simpa [ccmModeFinite] using hij

theorem ccmModeFinite_cast_sub_ne
    (N : ℕ) {i j : CCMModeFinite N} (hij : i ≠ j) :
    (ccmModeFinite N i : ℝ) - (ccmModeFinite N j : ℝ) ≠ 0 := by
  intro h
  have hcast : (ccmModeFinite N i : ℝ) = (ccmModeFinite N j : ℝ) :=
    sub_eq_zero.mp h
  have hint : ccmModeFinite N i = ccmModeFinite N j := by
    exact_mod_cast hcast
  exact hij (ccmModeFinite_injective N hint)

private theorem ccmQKernel_structured_mul
    (L : ℝ) {n m : ℤ} (hnm : n ≠ m) (x : ℝ) :
    ((n : ℝ) - (m : ℝ)) * ccmQKernel L n m x =
      (n : ℝ) * ccmQKernel L n 0 x -
        (m : ℝ) * ccmQKernel L m 0 x := by
  by_cases hn0 : n = 0
  · subst n
    have hm0 : m ≠ 0 := by simpa using Ne.symm hnm
    have hm0R : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    simp only [Int.cast_zero, zero_sub, zero_mul]
    rw [ccmQKernel, if_neg hnm, ccmQKernel, if_neg hm0]
    push_cast
    field_simp [hm0R]
    ring
  · by_cases hm0 : m = 0
    · subst m
      simp only [Int.cast_zero, sub_zero, zero_mul, sub_zero]
    · rw [ccmQKernel, if_neg hnm, ccmQKernel, if_neg hn0,
        ccmQKernel, if_neg hm0]
      have hn0R : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
      have hm0R : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
      have hnmR : (n : ℝ) - (m : ℝ) ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast hnm)
      push_cast
      field_simp [hn0R, hm0R, hnmR]
      ring

private theorem ccmW02Entry_structured_mul
    (L : ℝ) (n m : ℤ) :
    ((n : ℝ) - (m : ℝ)) * ccmW02Entry L n m =
      (n : ℝ) * ccmW02Entry L n 0 -
        (m : ℝ) * ccmW02Entry L m 0 := by
  by_cases hL : L = 0
  · subst L
    simp [ccmW02Entry]
  · have hden (k : ℤ) :
        L ^ 2 + 16 * Real.pi ^ 2 * (k : ℝ) ^ 2 ≠ 0 := by
      have hL2 : 0 < L ^ 2 := sq_pos_of_ne_zero hL
      have hk : 0 ≤ 16 * Real.pi ^ 2 * (k : ℝ) ^ 2 := by positivity
      nlinarith
    unfold ccmW02Entry
    push_cast
    field_simp [hden n, hden m, hden 0]
    ring

private theorem ccmPrimeEntry_structured_mul
    (mProject : ℕ) {n m : ℤ} (hnm : n ≠ m) :
    ((n : ℝ) - (m : ℝ)) * ccmPrimeEntryN1 mProject n m =
      (n : ℝ) * ccmPrimeEntryN1 mProject n 0 -
        (m : ℝ) * ccmPrimeEntryN1 mProject m 0 := by
  unfold ccmPrimeEntryN1
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hq := ccmQKernel_structured_mul
    (ccmL mProject) hnm (Real.log (k : ℝ))
  calc
    ((n : ℝ) - (m : ℝ)) *
          (ArithmeticFunction.vonMangoldt k *
            (Real.sqrt (k : ℝ))⁻¹ *
            ccmQKernel (ccmL mProject) n m (Real.log (k : ℝ))) =
        (ArithmeticFunction.vonMangoldt k *
          (Real.sqrt (k : ℝ))⁻¹) *
          (((n : ℝ) - (m : ℝ)) *
            ccmQKernel (ccmL mProject) n m (Real.log (k : ℝ))) := by ring
    _ = (ArithmeticFunction.vonMangoldt k *
          (Real.sqrt (k : ℝ))⁻¹) *
          ((n : ℝ) * ccmQKernel (ccmL mProject) n 0 (Real.log (k : ℝ)) -
            (m : ℝ) * ccmQKernel (ccmL mProject) m 0
              (Real.log (k : ℝ))) := by rw [hq]
    _ = (n : ℝ) *
          (ArithmeticFunction.vonMangoldt k *
            (Real.sqrt (k : ℝ))⁻¹ *
            ccmQKernel (ccmL mProject) n 0 (Real.log (k : ℝ))) -
        (m : ℝ) *
          (ArithmeticFunction.vonMangoldt k *
            (Real.sqrt (k : ℝ))⁻¹ *
            ccmQKernel (ccmL mProject) m 0 (Real.log (k : ℝ))) := by ring

private theorem ccmModeFinite_exists_of_mem_range
    (N : ℕ) (n : ℤ)
    (hlo : -(N : ℤ) ≤ n) (hhi : n ≤ N) :
    ∃ i : CCMModeFinite N, ccmModeFinite N i = n := by
  have hnonneg : 0 ≤ n + (N : ℤ) := by omega
  have hlt : n + (N : ℤ) < (2 * N + 1 : ℕ) := by omega
  have hto : ((n + (N : ℤ)).toNat : ℤ) = n + (N : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  have hltNat : (n + (N : ℤ)).toNat < 2 * N + 1 := by
    exact (Int.toNat_lt_of_ne_zero (by omega)).2 hlt
  let i : CCMModeFinite N := ⟨(n + (N : ℤ)).toNat, hltNat⟩
  refine ⟨i, ?_⟩
  simp only [ccmModeFinite, i]
  rw [hto]
  ring

private theorem ccmWRIntegrand_integer_integrableOn
    (mProject : ℕ) (hm : 2 ≤ mProject) (n m : ℤ) :
    IntegrableOn
      (ccmWRIntegrand (ccmL mProject) n m)
      (Set.Ioc 0 (ccmL mProject)) := by
  let N : ℕ := max n.natAbs m.natAbs + 1
  have hN : 1 ≤ N := by simp [N]
  have hnNat : n.natAbs ≤ N := by
    have h := Nat.le_max_left n.natAbs m.natAbs
    dsimp [N]
    omega
  have hmNat : m.natAbs ≤ N := by
    have h := Nat.le_max_right n.natAbs m.natAbs
    dsimp [N]
    omega
  have hnCast : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hnNat
  have hmCast : (m.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hmNat
  have hnUpper : n ≤ (N : ℤ) :=
    le_trans Int.le_natAbs hnCast
  have hmUpper : m ≤ (N : ℤ) :=
    le_trans Int.le_natAbs hmCast
  have hnNeg : -n ≤ (n.natAbs : ℤ) := by
    simpa using (Int.le_natAbs : -n ≤ ((-n).natAbs : ℤ))
  have hmNeg : -m ≤ (m.natAbs : ℤ) := by
    simpa using (Int.le_natAbs : -m ≤ ((-m).natAbs : ℤ))
  have hnLower : -(N : ℤ) ≤ n := by linarith
  have hmLower : -(N : ℤ) ≤ m := by linarith
  obtain ⟨i, hi⟩ := ccmModeFinite_exists_of_mem_range N n hnLower hnUpper
  obtain ⟨j, hj⟩ := ccmModeFinite_exists_of_mem_range N m hmLower hmUpper
  simpa [hi, hj] using
    (ccmWRIntegrandFinite_integrableOn mProject N hm hN i j)

private theorem ccmWRIntegrand_structured_mul
    (L : ℝ) {n m : ℤ} (hnm : n ≠ m) (x : ℝ) :
    ((n : ℝ) - (m : ℝ)) * ccmWRIntegrand L n m x =
      (n : ℝ) * ccmWRIntegrand L n 0 x -
        (m : ℝ) * ccmWRIntegrand L m 0 x := by
  have hx := ccmQKernel_structured_mul L hnm x
  have h0 := ccmQKernel_structured_mul L hnm 0
  have hnum :
      ((n : ℝ) - (m : ℝ)) *
          (Real.exp (x / 2) * ccmQKernel L n m x - ccmQKernel L n m 0) =
        (n : ℝ) *
            (Real.exp (x / 2) * ccmQKernel L n 0 x - ccmQKernel L n 0 0) -
          (m : ℝ) *
            (Real.exp (x / 2) * ccmQKernel L m 0 x - ccmQKernel L m 0 0) := by
    calc
      ((n : ℝ) - (m : ℝ)) *
          (Real.exp (x / 2) * ccmQKernel L n m x - ccmQKernel L n m 0) =
        Real.exp (x / 2) *
            (((n : ℝ) - (m : ℝ)) * ccmQKernel L n m x) -
          (((n : ℝ) - (m : ℝ)) * ccmQKernel L n m 0) := by ring
      _ = Real.exp (x / 2) *
            ((n : ℝ) * ccmQKernel L n 0 x -
              (m : ℝ) * ccmQKernel L m 0 x) -
          ((n : ℝ) * ccmQKernel L n 0 0 -
            (m : ℝ) * ccmQKernel L m 0 0) := by rw [hx, h0]
      _ = (n : ℝ) *
            (Real.exp (x / 2) * ccmQKernel L n 0 x - ccmQKernel L n 0 0) -
          (m : ℝ) *
            (Real.exp (x / 2) * ccmQKernel L m 0 x - ccmQKernel L m 0 0) := by ring
  unfold ccmWRIntegrand
  calc
    ((n : ℝ) - (m : ℝ)) *
        ((Real.exp (x / 2) * ccmQKernel L n m x - ccmQKernel L n m 0) /
          (Real.exp x - Real.exp (-x))) =
      (((n : ℝ) - (m : ℝ)) *
        (Real.exp (x / 2) * ccmQKernel L n m x - ccmQKernel L n m 0)) /
          (Real.exp x - Real.exp (-x)) := by ring
    _ = ((n : ℝ) *
            (Real.exp (x / 2) * ccmQKernel L n 0 x - ccmQKernel L n 0 0) -
          (m : ℝ) *
            (Real.exp (x / 2) * ccmQKernel L m 0 x - ccmQKernel L m 0 0)) /
          (Real.exp x - Real.exp (-x)) := by rw [hnum]
    _ = (n : ℝ) *
          ((Real.exp (x / 2) * ccmQKernel L n 0 x - ccmQKernel L n 0 0) /
            (Real.exp x - Real.exp (-x))) -
        (m : ℝ) *
          ((Real.exp (x / 2) * ccmQKernel L m 0 x - ccmQKernel L m 0 0) /
            (Real.exp x - Real.exp (-x))) := by ring

private theorem ccmWREntry_structured_mul
    (mProject : ℕ) (hm : 2 ≤ mProject) {n m : ℤ} (hnm : n ≠ m) :
    ((n : ℝ) - (m : ℝ)) * ccmWREntry (ccmL mProject) n m =
      (n : ℝ) * ccmWREntry (ccmL mProject) n 0 -
        (m : ℝ) * ccmWREntry (ccmL mProject) m 0 := by
  let L := ccmL mProject
  let C := Real.eulerMascheroniConstant +
    Real.log (4 * Real.pi * ((Real.exp L - 1) / (Real.exp L + 1)))
  have hq0 := ccmQKernel_structured_mul L hnm 0
  have hconst :
      ((n : ℝ) - (m : ℝ)) * (ccmQKernel L n m 0 / 2 * C) =
        (n : ℝ) * (ccmQKernel L n 0 0 / 2 * C) -
          (m : ℝ) * (ccmQKernel L m 0 0 / 2 * C) := by
    calc
      ((n : ℝ) - (m : ℝ)) * (ccmQKernel L n m 0 / 2 * C) =
        (((n : ℝ) - (m : ℝ)) * ccmQKernel L n m 0) * (C / 2) := by ring
      _ = ((n : ℝ) * ccmQKernel L n 0 0 -
          (m : ℝ) * ccmQKernel L m 0 0) * (C / 2) := by rw [hq0]
      _ = (n : ℝ) * (ccmQKernel L n 0 0 / 2 * C) -
          (m : ℝ) * (ccmQKernel L m 0 0 / 2 * C) := by ring
  have hnmInt := ccmWRIntegrand_integer_integrableOn mProject hm n m
  have hn0Int := ccmWRIntegrand_integer_integrableOn mProject hm n 0
  have hm0Int := ccmWRIntegrand_integer_integrableOn mProject hm m 0
  have hInt :
      ((n : ℝ) - (m : ℝ)) *
          (∫ x in Set.Ioc 0 L, ccmWRIntegrand L n m x) =
        (n : ℝ) * (∫ x in Set.Ioc 0 L, ccmWRIntegrand L n 0 x) -
          (m : ℝ) * (∫ x in Set.Ioc 0 L, ccmWRIntegrand L m 0 x) := by
    calc
      ((n : ℝ) - (m : ℝ)) *
          (∫ x in Set.Ioc 0 L, ccmWRIntegrand L n m x) =
        ∫ x in Set.Ioc 0 L,
          ((n : ℝ) - (m : ℝ)) * ccmWRIntegrand L n m x := by
            rw [integral_const_mul]
      _ = ∫ x in Set.Ioc 0 L,
          ((n : ℝ) * ccmWRIntegrand L n 0 x -
            (m : ℝ) * ccmWRIntegrand L m 0 x) := by
            exact setIntegral_congr_fun measurableSet_Ioc fun x _ =>
              ccmWRIntegrand_structured_mul L hnm x
      _ = (n : ℝ) * (∫ x in Set.Ioc 0 L, ccmWRIntegrand L n 0 x) -
          (m : ℝ) * (∫ x in Set.Ioc 0 L, ccmWRIntegrand L m 0 x) := by
            rw [integral_sub (hn0Int.const_mul _) (hm0Int.const_mul _),
              integral_const_mul, integral_const_mul]
  change ((n : ℝ) - (m : ℝ)) *
      (ccmQKernel L n m 0 / 2 * C +
        ∫ x in Set.Ioc 0 L, ccmWRIntegrand L n m x) =
    (n : ℝ) *
        (ccmQKernel L n 0 0 / 2 * C +
          ∫ x in Set.Ioc 0 L, ccmWRIntegrand L n 0 x) -
      (m : ℝ) *
        (ccmQKernel L m 0 0 / 2 * C +
          ∫ x in Set.Ioc 0 L, ccmWRIntegrand L m 0 x)
  rw [mul_add, hconst, hInt]
  ring

theorem ccmWeilTau_structured_offdiag
    (mProject : ℕ) (hm : 2 ≤ mProject)
    {n m : ℤ} (hnm : n ≠ m) :
    ccmWeilTauN1 mProject n m =
      (ccmBetaScalar mProject n - ccmBetaScalar mProject m) /
        ((n : ℝ) - (m : ℝ)) := by
  have hW02 := ccmW02Entry_structured_mul (ccmL mProject) n m
  have hWR := ccmWREntry_structured_mul mProject hm hnm
  have hPrime := ccmPrimeEntry_structured_mul mProject hnm
  have hmul :
      ((n : ℝ) - (m : ℝ)) * ccmWeilTauN1 mProject n m =
        (n : ℝ) * ccmWeilTauN1 mProject n 0 -
          (m : ℝ) * ccmWeilTauN1 mProject m 0 := by
    unfold ccmWeilTauN1
    calc
      ((n : ℝ) - (m : ℝ)) *
          (ccmW02Entry (ccmL mProject) n m -
            ccmWREntry (ccmL mProject) n m -
            ccmPrimeEntryN1 mProject n m) =
        ((n : ℝ) - (m : ℝ)) * ccmW02Entry (ccmL mProject) n m -
          ((n : ℝ) - (m : ℝ)) * ccmWREntry (ccmL mProject) n m -
          ((n : ℝ) - (m : ℝ)) * ccmPrimeEntryN1 mProject n m := by ring
      _ = ((n : ℝ) * ccmW02Entry (ccmL mProject) n 0 -
            (m : ℝ) * ccmW02Entry (ccmL mProject) m 0) -
          ((n : ℝ) * ccmWREntry (ccmL mProject) n 0 -
            (m : ℝ) * ccmWREntry (ccmL mProject) m 0) -
          ((n : ℝ) * ccmPrimeEntryN1 mProject n 0 -
            (m : ℝ) * ccmPrimeEntryN1 mProject m 0) := by
              rw [hW02, hWR, hPrime]
      _ = (n : ℝ) *
            (ccmW02Entry (ccmL mProject) n 0 -
              ccmWREntry (ccmL mProject) n 0 -
              ccmPrimeEntryN1 mProject n 0) -
          (m : ℝ) *
            (ccmW02Entry (ccmL mProject) m 0 -
              ccmWREntry (ccmL mProject) m 0 -
              ccmPrimeEntryN1 mProject m 0) := by ring
  have hden : (n : ℝ) - (m : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hnm)
  rw [eq_div_iff hden]
  calc
    ccmWeilTauN1 mProject n m * ((n : ℝ) - (m : ℝ)) =
        ((n : ℝ) - (m : ℝ)) * ccmWeilTauN1 mProject n m := by ring
    _ = (n : ℝ) * ccmWeilTauN1 mProject n 0 -
        (m : ℝ) * ccmWeilTauN1 mProject m 0 := hmul
    _ = ccmBetaScalar mProject n - ccmBetaScalar mProject m := by
      rfl

theorem ccmWeilMatFinite_structured_offdiag
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    {i j : CCMModeFinite N} (hij : i ≠ j) :
    ccmWeilMatFinite mProject N i j =
      (ccmBetaFinite mProject N i - ccmBetaFinite mProject N j) /
        ((ccmModeFinite N i : ℝ) - (ccmModeFinite N j : ℝ)) := by
  have hmode : ccmModeFinite N i ≠ ccmModeFinite N j := by
    intro h
    exact hij (ccmModeFinite_injective N h)
  have hs := ccmWeilTau_structured_offdiag mProject hm hmode
  have _hN := hN
  simpa [ccmWeilMatFinite, ccmBetaFinite, ccmBetaScalar] using hs

@[simp] theorem ccmBetaFinite_center (mProject N : ℕ) :
    ccmBetaFinite mProject N (ccmCenterFinite N) = 0 := by
  simp [ccmBetaFinite]

theorem ccmBetaFinite_unique
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (β : CCMModeFinite N → ℝ)
    (hβ0 : β (ccmCenterFinite N) = 0)
    (hstruct : ∀ i j, i ≠ j →
      ccmWeilMatFinite mProject N i j =
        (β i - β j) /
          ((ccmModeFinite N i : ℝ) - (ccmModeFinite N j : ℝ))) :
    β = ccmBetaFinite mProject N := by
  have _hm := hm
  have _hN := hN
  funext i
  by_cases hi : i = ccmCenterFinite N
  · subst i
    simp [hβ0]
  · have hs := hstruct i (ccmCenterFinite N) hi
    have hden := ccmModeFinite_cast_sub_ne N hi
    have hmul := (eq_div_iff hden).mp hs
    rw [hβ0] at hmul
    simp only [ccmModeFinite_center, Int.cast_zero, sub_zero] at hmul
    unfold ccmBetaFinite
    simpa [mul_comm] using hmul.symm

theorem ccmBetaFinite_one_eq (mProject : ℕ) :
    ccmBetaFinite mProject 1 = ccmBetaN1 mProject := by
  rfl

theorem ccmWeilMatFinite_commutator
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    ccmModeDiagFinite N * ccmWeilMatFinite mProject N -
        ccmWeilMatFinite mProject N * ccmModeDiagFinite N =
      Matrix.vecMulVec (ccmBetaFinite mProject N) (ccmEtaFinite N) -
        Matrix.vecMulVec (ccmEtaFinite N) (ccmBetaFinite mProject N) := by
  classical
  ext i j
  have hleft :
      (ccmModeDiagFinite N * ccmWeilMatFinite mProject N -
          ccmWeilMatFinite mProject N * ccmModeDiagFinite N) i j =
        ((ccmModeFinite N i : ℝ) - (ccmModeFinite N j : ℝ)) *
          ccmWeilMatFinite mProject N i j := by
    rw [Matrix.sub_apply]
    simp only [ccmModeDiagFinite, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hright :
      (Matrix.vecMulVec (ccmBetaFinite mProject N) (ccmEtaFinite N) -
          Matrix.vecMulVec (ccmEtaFinite N) (ccmBetaFinite mProject N)) i j =
        ccmBetaFinite mProject N i - ccmBetaFinite mProject N j := by
    simp [Matrix.vecMulVec_apply, ccmEtaFinite]
  rw [hleft, hright]
  by_cases hij : i = j
  · subst j
    ring
  · rw [ccmWeilMatFinite_structured_offdiag mProject N hm hN hij]
    have hden := ccmModeFinite_cast_sub_ne N hij
    field_simp [hden]

#print axioms ccmWeilTau_structured_offdiag
#print axioms ccmWeilMatFinite_structured_offdiag
#print axioms ccmBetaFinite_unique
#print axioms ccmWeilMatFinite_commutator

end Q3.RouteB
