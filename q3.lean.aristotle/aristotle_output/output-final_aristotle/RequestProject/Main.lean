import Mathlib
import RequestProject.H2aPenalty

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Complex Filter Topology

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# A formal skeleton for the RH route

This file is a **skeleton** (no proofs) tracking the proof-obligation ledger of the
paper.  Every result is stated and left as `sorry`; nothing is proved here.

The strategy proves the Riemann Hypothesis through a family of gauge-normalized
approximants
$$ H_j := a_j \, \frac{F_j}{\gamma_j}, \qquad \gamma_j \in \mathcal O(S)^\times,\ a_j\neq 0, $$
of the Riemann `Ξ`-function on the strip `S`.  The logical architecture is:

* **Roof** (`GaugeSoftSubsequenceZeroEscape`, already established): real-zero
  approximants + a locally uniformly convergent subsequence tracking `Ξ` with a
  nonzero limit `⟹` RH, via Hurwitz on the two half-strips `S⁺`, `S⁻`.

* **Six dependency slots**: `H1`, `H2a`, `H2b`, `ANCHOR`, `S1`, `S2`.

* **Three gates**:
  - **RoofGateA** = `H1 + H2a ⟹ SlotH2b` (finite real-zero engine, via the
    real-zero theorem);
  - **RoofGateB** = `H1 + ANCHOR + S1 ⟹ ∃ nonzero cluster H`   (existence via
    Montel + anchor);
  - **RoofGateC** = `S2 ⟹ H = c·Ξ·γ₀`   (cluster identification, the main wall).

The heavy fronts are `H2a`, `S1`, `S2`, with `S2 ≫ H2a ≳ S1`.
-/

namespace RHRoute

/-! ## Section 0. Core objects: the strip, the half-strips, and `Ξ`. -/

/-- The open connected strip `S = { z : |Im z| < 1/2 }`.
Zeros of `ζ` in the critical strip `0 < Re s < 1` correspond, via `s = 1/2 + i z`,
to zeros of `Ξ` inside `S`. -/
def Sset : Set ℂ := {z | |z.im| < 1 / 2}

/-- The upper half-strip `S⁺ = { 0 < Im z < 1/2 }`. -/
def Splus : Set ℂ := {z | 0 < z.im ∧ z.im < 1 / 2}

/-- The lower half-strip `S⁻ = { -1/2 < Im z < 0 }`. -/
def Sminus : Set ℂ := {z | -(1 / 2) < z.im ∧ z.im < 0}

/-- Riemann ξ on the strip: `Xi z = ξ(1/2 + i z)`; zeros of `Xi` in `S` are exactly
the nontrivial zeta zeros.  Entire, even, real on ℝ.

Note (C1): `completedRiemannZeta₀` alone (`Λ₀ = Λ + 1/s + 1/(1−s)`) is *wrong* for
this, since at a zeta zero `ρ` one has `Λ₀(ρ) = 1/(ρ(1−ρ)) ≠ 0`.  We use the entire
ξ via the identity `ξ(s) = ½·s·(s−1)·Λ₀(s) + ½` (check: `ξ(0)=ξ(1)=½`). -/
noncomputable def Xi (z : ℂ) : ℂ :=
  let s : ℂ := 1/2 + Complex.I * z
  (1/2) * s * (s - 1) * completedRiemannZeta₀ s + 1/2

/-- The zero set of `f` inside a region `U`. -/
def zeroSet (f : ℂ → ℂ) (U : Set ℂ) : Set ℂ := {z | z ∈ U ∧ f z = 0}

/-- `f` has only real zeros inside `S`. -/
def RealZerosOn (f : ℂ → ℂ) : Prop := ∀ z ∈ Sset, f z = 0 → z.im = 0

/-- `f` is a unit of `𝒪(S)`, i.e. holomorphic and zero-free on `S`
(`f ∈ 𝒪(S)^×`).  This is the class of admissible construction gauges `γⱼ`. -/
def IsUnitOnS (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f Sset ∧ ∀ z ∈ Sset, f z ≠ 0

/-- A family `g : ℕ → ℂ → ℂ` is **locally bounded** on `U`: uniformly bounded in
`j` on every compact `K ⋐ U`.  This is the Montel input (slot `S1`). -/
def LocBddOn (g : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ j, ∀ z ∈ K, ‖g j z‖ ≤ M

/-- The identification target: `h = c · Ξ · γ₀` with `c ≠ 0` and `γ₀` a fixed unit
of `𝒪(S)`.  This is the conclusion of slot `S2` / `RoofGateC`. -/
def IsXiGaugeMultiple (h : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (g0 : ℂ → ℂ), c ≠ 0 ∧ IsUnitOnS g0 ∧ ∀ z ∈ Sset, h z = c * Xi z * g0 z

/-- Some subsequence of `g` converges locally uniformly on `S` to `h`. -/
def SubseqLU (g : ℕ → ℂ → ℂ) (h : ℂ → ℂ) : Prop :=
  ∃ phi : ℕ → ℕ, StrictMono phi ∧ TendstoLocallyUniformlyOn (fun k => g (phi k)) h atTop Sset

/-- The anchor point `i/4 ∈ S⁺` used to normalize the family and prevent limit
collapse. -/
noncomputable def anchor : ℂ := Complex.I / 4

/-- Link to Mathlib's `completedRiemannZeta` (`Λ`): on the open strip `S`,
`Xi z = ½·s·(s−1)·Λ(s)` with `s = 1/2 + i z`.  (Stated on `Sset` only: at the
boundary points `z = ± i/2` the classical form hits the poles of `Λ`, where
Mathlib assigns junk values and the unguarded identity is false.) -/
theorem Xi_eq_classical (z : ℂ) (hz : z ∈ Sset) :
    Xi z = (1/2) * (1/2 + Complex.I*z) * (1/2 + Complex.I*z - 1)
             * completedRiemannZeta (1/2 + Complex.I*z) := by sorry

/-! ## Section 1. The roof and its complex-analytic tools.

These are the already-established, complex-analytic parts of the argument that do
not need re-proving; they are recorded here for completeness of the skeleton. -/

/-- **Hurwitz zero-escape** (the tool behind the roof).  On an open, connected
region `U`, if analytic functions `g k` are all zero-free on `U`, converge locally
uniformly to `h`, and `h` is not identically zero on `U`, then `h` is zero-free on
`U`.  Applied to `U = S⁺` and `U = S⁻`, where the real-zero approximants are
zero-free (no real points there). -/
theorem hurwitz_zero_escape
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (g : ℕ → ℂ → ℂ) (h : ℂ → ℂ)
    (hg : ∀ k, AnalyticOnNhd ℂ (g k) U)
    (hconv : TendstoLocallyUniformlyOn g h atTop U)
    (hne : ∃ z ∈ U, h z ≠ 0)
    (hzf : ∀ k, ∀ z ∈ U, g k z ≠ 0) :
    ∀ z ∈ U, h z ≠ 0 := by
  sorry

/-- Identity-theorem remark: a function holomorphic on the connected strip `S`
that vanishes on the open subset `S⁺` vanishes on all of `S`.  Hence proving
`h ≢ 0` on a single half-strip already forces `h ≢ 0` globally; the two anchor
points `±i/4` are a convenience, not two extra obligations. -/
theorem identity_from_Splus (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h Sset)
    (h0 : ∀ z ∈ Splus, h z = 0) :
    ∀ z ∈ Sset, h z = 0 := by
  sorry

/-- Bridge to Mathlib's `RiemannHypothesis`: if `Ξ` has no zeros off the real axis
inside `S`, then RH holds. -/
theorem RH_of_Xi_offcritical_zerofree
    (hXi : ∀ z ∈ Sset, z.im ≠ 0 → Xi z ≠ 0) :
    RiemannHypothesis := by
  sorry

/-- **The roof: `GaugeSoftSubsequenceZeroEscape`** (already established).
If the gauge-normalized approximants `g j` have only real zeros in `S`, and some
subsequence converges locally uniformly on `S` to a limit of the form `c·Ξ·γ₀`
with `c ≠ 0` and `γ₀ ∈ 𝒪(S)^×`, then two applications of Hurwitz (on `S⁺` and
`S⁻`) yield the Riemann Hypothesis. -/
theorem GaugeSoftSubsequenceZeroEscape
    (g : ℕ → ℂ → ℂ) (h : ℂ → ℂ)
    (hzeros : ∀ j, RealZerosOn (g j))
    (hconv : SubseqLU g h)
    (hlim : IsXiGaugeMultiple h) :
    RiemannHypothesis := by
  sorry

/-! ## Section 2. The construction data. -/

/-- The construction data: the raw approximants `F j`, the zero-free construction
gauges `γ j ∈ 𝒪(S)^×`, and the nonzero anchor constants `a j`. -/
structure Approx where
  /-- The raw approximants `Fⱼ`. -/
  F : ℕ → ℂ → ℂ
  /-- The construction gauges `γⱼ`. -/
  gamma : ℕ → ℂ → ℂ
  /-- The anchor constants `aⱼ`. -/
  a : ℕ → ℂ
  /-- Each gauge is a unit of `𝒪(S)` (the already-closed background dependency). -/
  gamma_unit : ∀ j, IsUnitOnS (gamma j)
  /-- Each anchor constant is nonzero. -/
  a_ne : ∀ j, a j ≠ 0

/-- The gauge-normalized family `Hⱼ = aⱼ · Fⱼ / γⱼ`.  It is `Hⱼ`, not the raw
`Fⱼ`, that must pass slots `S1` and `S2`. -/
noncomputable def Hfam (P : Approx) (j : ℕ) (z : ℂ) : ℂ :=
  P.a j * P.F j z / P.gamma j z

/-- **Construction-gauge zero-freeness** (already-closed background dependency).
Dividing by a zero-free gauge does not move zeros: `Z(Fⱼ/γⱼ) = Z(Fⱼ)` on `S`. -/
theorem gauge_preserves_zeros (P : Approx) (j : ℕ) :
    zeroSet (fun z => P.F j z / P.gamma j z) Sset = zeroSet (P.F j) Sset := by
  sorry

/-! ### The finite pencil data and the bridge to the route family (H2a bridge layer).

These two structures give the H2a spectral content its real meaning: `PencilData`
bundles the exact finite Hermitian-pencil data of the proved engine
`H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity`, and `PencilBridge` records
(as hypothesis fields) the transport connecting that pencil's ground state to the
approximant `Hfam P j`. -/

section PencilBridgeLayer
open Matrix
open scoped ComplexOrder

/-- The exact finite Hermitian-pencil data feeding the proved engine
`H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity`: a positive-definite `G`,
a Hermitian `K`, an involution `J` commuting with the pencil, a `J`-even,
`G`-normalized vector `q` with Rayleigh value `a`, and the penalty certificate
`K - β G + τ (Gq)(Gq)* ⪰ 0` with `a < β`.  The index type `n` is bundled together
with its `Fintype`/`DecidableEq` instances. -/
structure PencilData where
  /-- The finite index type of the pencil. -/
  n : Type
  [fin : Fintype n]
  [dec : DecidableEq n]
  /-- The positive-definite metric `G`. -/
  G : Matrix n n ℂ
  /-- The Hermitian operator `K`. -/
  K : Matrix n n ℂ
  /-- The parity involution `J`. -/
  J : Matrix n n ℂ
  /-- The `J`-even, `G`-normalized reference vector `q`. -/
  q : n → ℂ
  /-- The Rayleigh value `a = q* K q`. -/
  a : ℝ
  /-- The penalty threshold `β`. -/
  β : ℝ
  /-- The penalty weight `τ`. -/
  τ : ℝ
  hG : G.PosDef
  hK : K.IsHermitian
  hJ : J * J = 1
  hJG : Jᴴ * G * J = G
  hJK : Jᴴ * K * J = K
  hJq : J *ᵥ q = q
  hq : star q ⬝ᵥ (G *ᵥ q) = 1
  ha : star q ⬝ᵥ (K *ᵥ q) = (a : ℂ)
  hab : a < β
  hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef

attribute [instance] PencilData.fin PencilData.dec

/-- The bridge relating the finite `(K, G)`-pencil of `D` to the `j`-th approximant
`Hfam P j`.  The fields are **hypotheses**, not proofs: their construction is the
(source-locked) Layer-B instantiation and is intentionally out of scope here.

Note: the full window operator `T_j` and any compressed/defect relation are OUT OF
SCOPE — `Ran(synthesis)` is not `T`-invariant in this project — so nothing beyond
`transform` is claimed, and no equivalence between the pencil and a full-operator
eigenproblem is assumed.  The pencil IS the compressed object. -/
structure PencilBridge (P : Approx) (j : ℕ) (D : PencilData) where
  /-- The linear transform sending pencil vectors to holomorphic functions on `ℂ`. -/
  transform : (D.n → ℂ) →ₗ[ℂ] (ℂ → ℂ)
  /-- Parity intertwining: the `J`-action corresponds to the reflection `z ↦ -z`. -/
  parity_intertwine : ∀ x, transform (D.J *ᵥ x) = fun z => transform x (-z)
  /-- Ground-state link: the transform of a lowest eigenvector is a nonzero scalar
  multiple of the `j`-th approximant `Hfam P j`. -/
  ground_link : ∀ lam x, H2aPenalty.GEig D.K D.G lam x →
      (∀ μ y, H2aPenalty.GEig D.K D.G μ y → lam ≤ μ) →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z, Hfam P j z = c * transform x z

end PencilBridgeLayer

/-! ## Section 3. The six dependency slots.

The spectral content of `H2a` is packaged in the structure `SpectralData` below
(C3): a lower-bounded self-adjoint object with a simple, isolated, even lowest
eigenvalue whose transform is the approximant.  Stub fields are temporary. -/

/-- Spectral data of the `j`-th finite object (C3): the existence of finite pencil
data `D` (a lower-bounded self-adjoint pencil carrying the penalty certificate)
together with a bridge `PencilBridge P j D` linking its ground state to the
approximant `Hfam P j`.  This replaces the earlier `True`-stub fields with real
mathematical content: the pencil supplied by `PencilData` is exactly the input of
the proved engine `H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity`, and the
bridge carries its simple/isolated/even ground state over to `Hfam P j`. -/
structure SpectralData (P : Approx) (j : ℕ) : Prop where
  content : ∃ D : PencilData, Nonempty (PencilBridge P j D)


/-! ### The Theorem-5.10 determinant bridge and its finite-dimensional witness. -/

section Det510TransformLayer
open Matrix
open scoped ComplexOrder

/-- Theorem-5.10 bridge for the `j`-th approximant.  The two substantive fields
are deliberately hypotheses (Layer-B / paper debts): `factor` is the exact
all-variable regularized-determinant identity on the strip (Theorem 5.10,
p. 41), while `d_zeros_real` is its self-adjoint spectral content.  A
Fredholm/regularized-determinant theory is not presently part of Mathlib. -/
structure Det510Bridge (P : Approx) (j : ℕ) where
  /-- The determinant side. -/
  d : ℂ → ℂ
  /-- The zero-free phase factor (the class of `-i λ^{-iz}`). -/
  unit : ℂ → ℂ
  /-- The phase is nonzero throughout the strip. -/
  unit_ne : ∀ z ∈ Sset, unit z ≠ 0
  /-- Debt A: the exact all-`z` factorization on the strip. -/
  factor : ∀ z ∈ Sset, Hfam P j z = unit z * d z
  /-- Debt B: self-adjoint determinant zeros are real. -/
  d_zeros_real : ∀ z ∈ Sset, d z = 0 → z.im = 0

/-- Transport of Theorem 5.10's two hypothesis fields to real zeros of the
approximant. -/
theorem realZeroTheorem_of_det510 (P : Approx) (j : ℕ) :
    Det510Bridge P j → RealZerosOn (Hfam P j) := by
  intro hb z hzS hz
  have hprod : hb.unit z * hb.d z = 0 := by
    rw [← hb.factor z hzS]
    exact hz
  exact hb.d_zeros_real z hzS ((mul_eq_zero.mp hprod).resolve_left (hb.unit_ne z hzS))

/-- Finite-dimensional kernel lemma: every zero of the characteristic
determinant of a Hermitian complex matrix is real. -/
theorem selfAdjointCharDetRealZeros {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∀ z : ℂ, Matrix.det ((z : ℂ) • (1 : Matrix n n ℂ) - A) = 0 → z.im = 0 := by
  intro z hz
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have heig : A *ᵥ v = z • v := by
    have h : z • v - A *ᵥ v = 0 := by
      simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hker
    exact (sub_eq_zero.mp h).symm
  have him := hA.im_star_dotProduct_mulVec_self v
  rw [heig] at him
  have hsum : (star v ⬝ᵥ z • v) = z * (star v ⬝ᵥ v) := by
    simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at him
  change (z * (star v ⬝ᵥ v)).im = 0 at him
  rw [Complex.mul_im] at him
  have hreal : (star v ⬝ᵥ v).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    simpa using (Matrix.star_dotProduct v v).symm
  rw [hreal, mul_zero, zero_add] at him
  have hnorm : (star v ⬝ᵥ v).re ≠ 0 := by
    intro hzero
    have hcomplex : star v ⬝ᵥ v = 0 := Complex.ext hzero hreal
    exact hv (dotProduct_star_self_eq_zero.mp hcomplex)
  exact (mul_eq_zero.mp him).resolve_right hnorm

/-- A concrete `2 × 2` Hermitian matrix used to witness that the bridge is
inhabited. -/
def det510ToyMatrix : Matrix (Fin 2) (Fin 2) ℂ := 0

/-- The characteristic determinant of `det510ToyMatrix`. -/
noncomputable def det510ToyDet (z : ℂ) : ℂ :=
  Matrix.det (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - det510ToyMatrix)

/-- A toy approximant whose zeroth member is exactly the finite characteristic
determinant and whose gauge and anchor scalar are both one. -/
noncomputable def det510ToyApprox : Approx where
  F := fun _ => det510ToyDet
  gamma := fun _ _ => 1
  a := fun _ => 1
  gamma_unit := by
    intro j
    exact ⟨analyticOnNhd_const, by simp⟩
  a_ne := by simp

/-- **T2b (inhabitability guard).**  The determinant bridge is genuinely
inhabited: in this finite model debt B is discharged exactly by
`selfAdjointCharDetRealZeros`. -/
noncomputable def det510ToyBridge : Det510Bridge det510ToyApprox 0 where
  d := det510ToyDet
  unit := fun _ => 1
  unit_ne := by simp
  factor := by simp [Hfam, det510ToyApprox]
  d_zeros_real := by
    intro z _ hz
    exact selfAdjointCharDetRealZeros det510ToyMatrix (by simp [det510ToyMatrix]) z hz

/-- Data with every bridge field except `unit_ne`: the unit vanishes at `i/4`,
the determinant side has no zeros, and the resulting approximant has a non-real
zero in the strip.  Thus `unit_ne` is load-bearing. -/
theorem PL1_det510_unit_ne_load_bearing :
    ∃ (P : Approx) (d unit : ℂ → ℂ) (z0 : ℂ),
      z0 ∈ Sset ∧ z0.im ≠ 0 ∧ unit z0 = 0 ∧
      (∀ z ∈ Sset, Hfam P 0 z = unit z * d z) ∧
      (∀ z ∈ Sset, d z = 0 → z.im = 0) ∧ Hfam P 0 z0 = 0 := by
  let z0 : ℂ := Complex.I / 4
  let unit : ℂ → ℂ := fun z => z - z0
  let d : ℂ → ℂ := fun _ => 1
  let P : Approx := {
    F := fun _ z => unit z
    gamma := fun _ _ => 1
    a := fun _ => 1
    gamma_unit := by
      intro j
      exact ⟨analyticOnNhd_const, by simp⟩
    a_ne := by simp }
  refine ⟨P, d, unit, z0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [z0, Sset, abs_of_nonneg]
    norm_num
  · simp [z0]
  · simp [unit]
  · intro z _
    simp [P, Hfam, d]
  · intro z _ hz
    simp [d] at hz
  · simp [P, Hfam, unit]

/-- Data with every bridge field except `d_zeros_real`: the unit is constantly
one and `d(z)=z²+1/16`, so the R9-shaped zeros `±i/4` are non-real points of the
strip.  This isolates debt B as load-bearing. -/
theorem PL2_det510_d_zeros_real_load_bearing :
    ∃ (P : Approx) (d unit : ℂ → ℂ) (z0 : ℂ),
      z0 ∈ Sset ∧ z0.im ≠ 0 ∧
      (∀ z ∈ Sset, unit z ≠ 0) ∧
      (∀ z ∈ Sset, Hfam P 0 z = unit z * d z) ∧
      d z0 = 0 ∧ Hfam P 0 z0 = 0 := by
  let z0 : ℂ := Complex.I / 4
  let unit : ℂ → ℂ := fun _ => 1
  let d : ℂ → ℂ := fun z => z ^ 2 + 1 / 16
  let P : Approx := {
    F := fun _ => d
    gamma := fun _ _ => 1
    a := fun _ => 1
    gamma_unit := by
      intro j
      exact ⟨analyticOnNhd_const, by simp⟩
    a_ne := by simp }
  refine ⟨P, d, unit, z0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [z0, Sset, abs_of_nonneg] <;> norm_num
  · simp [z0]
  · simp [unit]
  · intro z _
    simp [P, Hfam, unit]
  · dsimp [d, z0]
    rw [div_pow, Complex.I_sq]
    norm_num
  · simp only [P, Hfam, one_mul, one_div, d, z0]
    rw [div_pow, Complex.I_sq]
    norm_num

end Det510TransformLayer

/-- **Slot H1** — holomorphy of the normalized family `Hⱼ ∈ 𝒪(S)`.
(Open, but technically the lightest of the slots.) -/
def SlotH1 (P : Approx) : Prop := ∀ j, AnalyticOnNhd ℂ (Hfam P j) Sset

/-- **Slot H2a** — the exact ground state is simple, isolated, and even.
(OPEN; the substantive spectral step.)  Packaged via `SpectralData`. -/
def SlotH2a (P : Approx) : Prop := ∀ j, SpectralData P j

/-- **Slot H2b** — output of applying the real-zero theorem: each `Hⱼ` has only
real zeros in `S`.  (The theorem layer exists; the application depends on `H1`
and `H2a`.) -/
def SlotH2b (P : Approx) : Prop := ∀ j, RealZerosOn (Hfam P j)

/-- **Slot ANCHOR** — the family is anchor-normalized at `i/4`:
`Hⱼ(i/4) = Ξ(i/4)` (which is nonzero), guaranteeing a nonzero limit.
Well-defined; controlling the growth of `aⱼ` is folded into `S1`. -/
def SlotAnchor (P : Approx) : Prop := ∀ j, Hfam P j anchor = Xi anchor

/-- **Slot S1** — local boundedness of the *post-anchor* family `Hⱼ` on every
`K ⋐ S`.  (OPEN.)  Stated for `Hⱼ = aⱼ·Fⱼ/γⱼ`, not for the raw `Fⱼ`: local
boundedness of the raw family need not transfer through possibly unbounded `aⱼ`. -/
def SlotS1 (P : Approx) : Prop := LocBddOn (Hfam P) Sset

/-- **Slot S2** — identification of *every* nonzero locally uniform cluster:
any `h` that is a nonzero locally uniform subsequential limit of `Hⱼ` equals
`c·Ξ·γ₀`.  (OPEN, the main wall.)  Frozen in the "for all clusters" form so that
`S2` does not re-absorb the work of `S1` and `ANCHOR`. -/
def SlotS2 (P : Approx) : Prop :=
  ∀ h : ℂ → ℂ, SubseqLU (Hfam P) h → (∃ z ∈ Sset, h z ≠ 0) → IsXiGaugeMultiple h

/-- Basic fact used by the anchor: the anchor value `Ξ(i/4)` is nonzero.
(`ξ(1/4) > 0` unconditionally via the eta-series sign of `ζ` on `(0,1)`.) -/
theorem Xi_anchor_ne : Xi anchor ≠ 0 := by
  sorry

/-- **Supply H1**: holomorphy of the normalized family (open object/holomorphy
lock). -/
theorem supply_H1 (P : Approx) : SlotH1 P := by
  sorry

/-- **Supply H2a**: existence of a simple, isolated, even ground state for each
finite object (OPEN spectral supply). -/
theorem supply_H2a (P : Approx) : SlotH2a P := by
  sorry

/-- **The real-zero theorem** (`H2b` theorem layer): the exact Theorem-5.10
determinant factorization, its zero-free phase, and the reality of the
self-adjoint determinant-side zeros transport to the approximant `Hⱼ`. -/
theorem realZeroTheorem (P : Approx) (j : ℕ)
    (hb : Det510Bridge P j) : RealZerosOn (Hfam P j) := by
  exact realZeroTheorem_of_det510 P j hb

/-- **Supply ANCHOR**: the family can be anchor-normalized at `i/4`. -/
theorem supply_anchor (P : Approx) : SlotAnchor P := by
  sorry

/-- **Supply S1**: local boundedness of the post-anchor family (OPEN). -/
theorem supply_S1 (P : Approx) : SlotS1 P := by
  sorry

/-- **Supply S2**: identification of every nonzero cluster (OPEN, main wall).
This is `CombinedDefectFiniteIdentityAndPlantLock → 3Q.4 → S2`. -/
theorem supply_S2 (P : Approx) : SlotS2 P := by
  sorry

/-! ## Section 4. The three gates. -/

/-- **RoofGateA** — finite real-zero engine: `H1 + H2a` together with the
Theorem-5.10 bridge supply imply `SlotH2b` (`Z(Hⱼ) ∩ S ⊆ ℝ`).  The H1/H2a
arguments remain in the six-slot interface; the determinant transport itself
uses the bridge supply. -/
theorem RoofGateA (P : Approx)
    (hH1 : SlotH1 P) (hH2a : SlotH2a P)
    (hbr : ∀ j, Det510Bridge P j) : SlotH2b P := by
  intro j
  exact realZeroTheorem P j (hbr j)

/-- **RoofGateB** — existence of a nonzero cluster:
`H1 + ANCHOR + S1 ⟹ ∃ Hⱼₖ → H, H ≢ 0`.  Montel (from `S1`, needing analyticity
from `H1`) extracts a locally uniformly convergent subsequence; the anchor keeps
the limit from collapsing to zero (`Xi_anchor_ne`). -/
theorem RoofGateB (P : Approx)
    (hH1 : SlotH1 P) (hanchor : SlotAnchor P) (hS1 : SlotS1 P) :
    ∃ h : ℂ → ℂ, SubseqLU (Hfam P) h ∧ (∃ z ∈ Sset, h z ≠ 0) := by
  sorry

/-- **RoofGateC** — cluster identification: `S2 ⟹ H = c·Ξ·γ₀` for every nonzero
cluster. -/
theorem RoofGateC (P : Approx)
    (hS2 : SlotS2 P) (h : ℂ → ℂ)
    (hconv : SubseqLU (Hfam P) h) (hne : ∃ z ∈ Sset, h z ≠ 0) :
    IsXiGaugeMultiple h := by
  sorry

/-! ## Section 5. Assembly: the six slots yield RH. -/

/-- **Main theorem (design α).** Given the five construction slots `H1`, `H2a`,
`ANCHOR`, `S1`, `S2` and the sixth Theorem-5.10 bridge supply, the Riemann
Hypothesis follows.  There is no assumed `hH2b`: it is derived by `RoofGateA`.
The proof then chains `RoofGateB`, `RoofGateC`, and
`GaugeSoftSubsequenceZeroEscape`. -/
theorem RH_of_slots (P : Approx)
    (hH1 : SlotH1 P)
    (hH2a : SlotH2a P)
    (hanchor : SlotAnchor P)
    (hS1 : SlotS1 P)
    (hS2 : SlotS2 P)
    (hbr : ∀ j, Det510Bridge P j) :
    RiemannHypothesis := by
  obtain ⟨h, hconv, hne⟩ := RoofGateB P hH1 hanchor hS1
  exact GaugeSoftSubsequenceZeroEscape (Hfam P) h
    (RoofGateA P hH1 hH2a hbr) hconv (RoofGateC P hS2 h hconv hne)

end RHRoute
