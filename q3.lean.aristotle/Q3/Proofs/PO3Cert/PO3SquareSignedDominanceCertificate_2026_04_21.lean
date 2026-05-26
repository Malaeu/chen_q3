import Q3.Proofs.HBridge_PO3_Shell

/-!
Certificate feeder for the current live transform-side wall `PO3-square.2d3`.

This file does not solve the real Gamma-tower mathematics.
Its role is narrower: it freezes the exact certificate shape that a future
Q3-side signed rightmost / top-cluster estimate must provide in order to
trigger the already-closed shell:

- one signed main tower;
- one dominant packet inside it;
- one controlled remainder;
- one mirror tower;
- the dominant-packet lower bound;
- the eventual relative remainder control;
- the mirror decay.

Once that data is available, the shell already returns the named
`PO3-square.2d2` contradiction target.
-/

namespace Q3.Proofs.PO3Cert

open Q3.HBridge
open scoped BigOperators

noncomputable section

/-! ## Transform-side landing surface -/

/-- Canonical Gamma-profile ancestor pinned by the current `PO3-square.2d3`
notes:

- the old `PO2` note records the exact profile
  `u_k(x) = (-1)^k Γ(N+1-x) / Γ(k+N+1-x)`;
- the live `PO3` route packages the real wall as a signed main `A_k` tower
  against a suppressed mirror `B_k` tower.

This definition does not solve the analytic wall. It only gives the future
transform-side packet estimate one fixed Lean name for the shared Gamma-profile
building block. -/
def po3_gamma_profile (N : ℕ) (x : ℂ) (k : ℕ) : ℂ :=
  ((-1 : ℂ) ^ k) * Complex.Gamma ((N + 1 : ℂ) - x) /
    Complex.Gamma ((k + N + 1 : ℂ) - x)

theorem po3_gamma_profile_zero (N : ℕ) (x : ℂ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) :
    po3_gamma_profile N x 0 = 1 := by
  have hΓ : Complex.Gamma ((N + 1 : ℂ) - x) ≠ 0 := Complex.Gamma_ne_zero hbase
  simp [po3_gamma_profile, hΓ]

/-- Exact one-step recurrence for the transform-side Gamma profile.

This is the clean algebraic bridge from the Gamma-quotient presentation to the
packet/product presentation used in the old `PO2` direct-receiver notes. -/
theorem po3_gamma_profile_succ (N : ℕ) (x : ℂ) (k : ℕ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) :
    po3_gamma_profile N x (k + 1) =
      (x - (N + k + 1 : ℕ) : ℂ)⁻¹ * po3_gamma_profile N x k := by
  let z : ℂ := (N + k + 1 : ℂ) - x
  have hshift : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    apply hbase (m + k)
    have hm' : z - (k : ℂ) = (-m : ℂ) - k := by
      simpa using congrArg (fun t : ℂ => t - k) hm
    dsimp [z] at hm' ⊢
    ring_nf at hm' ⊢
    norm_num at hm' ⊢
    exact hm'
  have hz0 : z ≠ 0 := by
    intro hz
    exact hshift 0 (by simpa using hz)
  have hGamma :
      (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹ :=
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z
  have hstep : (Complex.Gamma (z + 1))⁻¹ = z⁻¹ * (Complex.Gamma z)⁻¹ := by
    have htmp := congrArg (fun t : ℂ => z⁻¹ * t) hGamma
    simp [hz0] at htmp
    exact htmp.symm
  have hzneg : z⁻¹ = -((x - (N + k + 1 : ℕ) : ℂ)⁻¹) := by
    have hzrepr : z = -(x - (N + k + 1 : ℕ) : ℂ) := by
      dsimp [z]
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hzrepr, inv_neg]
  unfold po3_gamma_profile
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hden1 : Complex.Gamma (((k + 1 : ℕ) : ℂ) + ↑N + 1 - x) = Complex.Gamma (z + 1) := by
    congr 1
    dsimp [z]
    norm_num
    ring
  have hden0 : Complex.Gamma ((↑k : ℂ) + ↑N + 1 - x) = Complex.Gamma z := by
    congr 1
    dsimp [z]
    ring
  rw [hden1, hden0, hstep, hzneg]
  simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Exact finite-product form of the transform-side Gamma profile.

This is the real Lean bridge from the Gamma quotient
`(-1)^k Γ(N+1-x) / Γ(k+N+1-x)` to the packet form
`1 / ∏_{j=1}^k (x - (N+j))`
used in the old `PO2` notes. -/
theorem po3_gamma_profile_eq_prod (N : ℕ) (x : ℂ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) :
    ∀ k,
      po3_gamma_profile N x k =
        Finset.prod (Finset.range k) (fun j => (x - (N + j + 1 : ℕ) : ℂ)⁻¹) := by
  intro k
  induction k with
  | zero =>
      simpa using po3_gamma_profile_zero N x hbase
  | succ k ih =>
      rw [po3_gamma_profile_succ N x k hbase, ih, Finset.prod_range_succ]
      simp [mul_comm]

theorem po3_gamma_profile_factor_ne_zero (N : ℕ) (x : ℂ) (j : ℕ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) :
    (x - (N + j + 1 : ℕ) : ℂ) ≠ 0 := by
  intro hx
  apply hbase j
  have hx' : x = (N + j + 1 : ℕ) := sub_eq_zero.mp hx
  rw [hx']
  norm_num

/-- The reciprocal-product avatar is exact: after multiplying by the matching
finite denominator packet, one gets `1`. -/
theorem po3_gamma_profile_mul_prod_eq_one (N : ℕ) (x : ℂ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) (k : ℕ) :
    po3_gamma_profile N x k *
        Finset.prod (Finset.range k) (fun j => (x - (N + j + 1 : ℕ) : ℂ)) = 1 := by
  rw [po3_gamma_profile_eq_prod N x hbase k]
  calc
    (Finset.prod (Finset.range k) (fun j => (x - (N + j + 1 : ℕ) : ℂ)⁻¹)) *
        Finset.prod (Finset.range k) (fun j => (x - (N + j + 1 : ℕ) : ℂ))
        =
        Finset.prod (Finset.range k)
          (fun j => ((x - (N + j + 1 : ℕ) : ℂ)⁻¹ * (x - (N + j + 1 : ℕ) : ℂ))) := by
            symm
            exact Finset.prod_mul_distrib
    _ = Finset.prod (Finset.range k) (fun _ => (1 : ℂ)) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          exact inv_mul_cancel₀ (po3_gamma_profile_factor_ne_zero N x j hbase)
    _ = 1 := by simp

/-- Finite packet extracted from the transform-side Gamma profile ancestor. -/
def po3_gamma_packet {ι : Type*} (N : ℕ) (packet : Finset ι) (coeff : ι → ℂ)
    (support : ι → ℂ) (k : ℕ) : ℂ :=
  ∑ i ∈ packet, coeff i * po3_gamma_profile N (support i) k

/-- Exact rewrite of a finite Gamma packet into the reciprocal-product avatar.

This is the first honest Lean landing surface for a future top-cluster /
dominant-packet estimate: finite packets of the real transform-side tower can
now be stated directly as finite sums of reciprocal products. -/
theorem po3_gamma_packet_eq_sum_prod {ι : Type*} (N : ℕ) (packet : Finset ι)
    (coeff : ι → ℂ) (support : ι → ℂ)
    (hbase : ∀ i ∈ packet, ∀ m : ℕ, ((N + 1 : ℂ) - support i) ≠ -m) :
    ∀ k,
      po3_gamma_packet N packet coeff support k =
        ∑ i ∈ packet,
          coeff i * Finset.prod (Finset.range k)
            (fun j => (support i - (N + j + 1 : ℕ) : ℂ)⁻¹) := by
  intro k
  unfold po3_gamma_packet
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [po3_gamma_profile_eq_prod N (support i) (hbase i hi) k]

/-- Named transform-side data packet for the live `PO3-square.2d3` wall.

This is the first honest Lean-facing landing surface for the real formula map
already pinned in the repo:

- `Ya` is the one-sided paired support `Y_a = {x_γ, x_γ - 1}`;
- `Ak` is the signed main tower on the real transform side;
- `Bk` is the mirror tower;
- `po3_gamma_profile` is the common Gamma-profile ancestor from the old `PO2`
  direct-receiver notes.

The record stays intentionally weak: it names the real objects and their
support geometry, but it does not pretend that the signed rightmost estimate is
already proved. -/
structure PO3SquareTransformSideData (ι γ : Type*) where
  N : ℕ
  xGamma : γ → ℂ
  Ya : ι → ℂ
  Ak : ℕ → ℂ
  Bk : ℕ → ℂ
  paired_support : ∀ y, ∃ g, Ya y = xGamma g ∨ Ya y = xGamma g - 1

/-! ## Log-loss mirror-row consumer -/

/-- Relative row smallness against a moving nonnegative scale.

This is the Lean-side home for normalized estimates of the form
`row = o(scale)` in the `PO3-square.2d3` endpoint-row audit.  The quantities
are already absolute upper bounds, so no norm is included here. -/
def po3_row_relative_small (row scale : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ K, ∀ k, K ≤ k → row k ≤ ε * scale k

/-- Product smallness for the log-loss mirror route.

This records the analytic condition
`eta_{k,rho} * log(2+xi_k) -> 0` abstractly, without committing this file to a
specific zero-counting model. -/
def po3_product_tends_to_zero (eta logLoss : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ K, ∀ k, K ≤ k → eta k * logLoss k ≤ ε

/-- Real-valued smallness to zero, used for nonnegative error norms. -/
def po3_real_tends_to_zero (error : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ K, ∀ k, K ≤ k → error k < ε

/-- Eventual positive upper bound for a scalar conditioning sequence. -/
def po3_eventually_bounded_above_by_pos (C : ℕ → ℝ) : Prop :=
  ∃ B > 0, ∃ K, ∀ k, K ≤ k → C k ≤ B

/-- A scalar error bounded by a product tending to zero also tends to zero. -/
theorem po3_real_tends_to_zero_of_le_product
    {capture C rowError : ℕ → ℝ}
    (hcapture : ∀ k, capture k ≤ C k * rowError k)
    (hproduct : po3_product_tends_to_zero C rowError) :
    po3_real_tends_to_zero capture := by
  intro ε hεpos
  have hhalf_pos : 0 < ε / 2 := by positivity
  rcases hproduct (ε / 2) hhalf_pos with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  exact lt_of_le_of_lt (le_trans (hcapture k) (hK k hk)) (by linarith)

/-- Bounded conditioning times a real error tending to zero gives product
smallness. -/
theorem po3_product_tends_to_zero_of_bounded_left
    {C rowError : ℕ → ℝ}
    (hrow_nonneg : ∀ k, 0 ≤ rowError k)
    (hC : po3_eventually_bounded_above_by_pos C)
    (hrow : po3_real_tends_to_zero rowError) :
    po3_product_tends_to_zero C rowError := by
  intro ε hεpos
  rcases hC with ⟨B, hBpos, KC, hKC⟩
  have hεB_pos : 0 < ε / B := div_pos hεpos hBpos
  rcases hrow (ε / B) hεB_pos with ⟨Krow, hKrow⟩
  refine ⟨max KC Krow, ?_⟩
  intro k hk
  have hkC : KC ≤ k := le_trans (le_max_left _ _) hk
  have hkrow : Krow ≤ k := le_trans (le_max_right _ _) hk
  have hCk : C k ≤ B := hKC k hkC
  have hrowk : rowError k < ε / B := hKrow k hkrow
  have hmul_le : C k * rowError k ≤ B * rowError k :=
    mul_le_mul_of_nonneg_right hCk (hrow_nonneg k)
  have hBrow_lt : B * rowError k < ε := by
    have htmp : B * rowError k < B * (ε / B) :=
      mul_lt_mul_of_pos_left hrowk hBpos
    rwa [mul_div_cancel₀ ε hBpos.ne'] at htmp
  exact le_of_lt (lt_of_le_of_lt hmul_le hBrow_lt)

/-- Product of eventually bounded scalar sequences is eventually bounded when
the right factor is nonnegative. -/
theorem po3_eventually_bounded_above_by_pos_mul
    {C D : ℕ → ℝ}
    (hD_nonneg : ∀ k, 0 ≤ D k)
    (hC : po3_eventually_bounded_above_by_pos C)
    (hD : po3_eventually_bounded_above_by_pos D) :
    po3_eventually_bounded_above_by_pos (fun k => C k * D k) := by
  rcases hC with ⟨BC, hBCpos, KC, hKC⟩
  rcases hD with ⟨BD, hBDpos, KD, hKD⟩
  refine ⟨BC * BD, mul_pos hBCpos hBDpos, max KC KD, ?_⟩
  intro k hk
  have hkC : KC ≤ k := le_trans (le_max_left _ _) hk
  have hkD : KD ≤ k := le_trans (le_max_right _ _) hk
  have hCk : C k ≤ BC := hKC k hkC
  have hDk : D k ≤ BD := hKD k hkD
  calc
    C k * D k ≤ BC * D k :=
      mul_le_mul_of_nonneg_right hCk (hD_nonneg k)
    _ ≤ BC * BD :=
      mul_le_mul_of_nonneg_left hDk (le_of_lt hBCpos)

/-- Product-smallness transfers through an upper bound on the left factor. -/
theorem po3_product_tends_to_zero_of_le_left
    {eta etaBound logLoss : ℕ → ℝ}
    (hlog_nonneg : ∀ k, 0 ≤ logLoss k)
    (heta_le : ∀ k, eta k ≤ etaBound k)
    (hbound : po3_product_tends_to_zero etaBound logLoss) :
    po3_product_tends_to_zero eta logLoss := by
  intro ε hεpos
  rcases hbound ε hεpos with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  have hle :
      eta k * logLoss k ≤ etaBound k * logLoss k :=
    mul_le_mul_of_nonneg_right (heta_le k) (hlog_nonneg k)
  exact le_trans hle (hK k hk)

/-- Product-smallness transfers through an upper bound on the right factor. -/
theorem po3_product_tends_to_zero_of_le_right
    {eta logLoss logBound : ℕ → ℝ}
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (hlog_le : ∀ k, logLoss k ≤ logBound k)
    (hbound : po3_product_tends_to_zero eta logBound) :
    po3_product_tends_to_zero eta logLoss := by
  intro ε hεpos
  rcases hbound ε hεpos with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  have hle :
      eta k * logLoss k ≤ eta k * logBound k :=
    mul_le_mul_of_nonneg_left (hlog_le k) (heta_nonneg k)
  exact le_trans hle (hK k hk)

/-- Product-smallness transfers through upper bounds on both factors. -/
theorem po3_product_tends_to_zero_of_le_factors
    {eta etaBound countBound logBound : ℕ → ℝ}
    (hlogBound_nonneg : ∀ k, 0 ≤ logBound k)
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (heta_le : ∀ k, eta k ≤ etaBound k)
    (hcount_le : ∀ k, countBound k ≤ logBound k)
    (hbound : po3_product_tends_to_zero etaBound logBound) :
    po3_product_tends_to_zero eta countBound := by
  have hetaLog :
      po3_product_tends_to_zero eta logBound :=
    po3_product_tends_to_zero_of_le_left
      hlogBound_nonneg heta_le hbound
  exact
    po3_product_tends_to_zero_of_le_right
      heta_nonneg hcount_le hetaLog

/-- If `row_k <= factorLeft_k * factorRight_k * scale_k` and the factor
product tends to zero, then `row = o(scale)`. -/
theorem po3_row_relative_small_of_le_product_scale
    {row factorLeft factorRight scale : ℕ → ℝ}
    (hscale_nonneg : ∀ k, 0 ≤ scale k)
    (hrow :
      ∀ k, row k ≤ (factorLeft k * factorRight k) * scale k)
    (hproduct : po3_product_tends_to_zero factorLeft factorRight) :
    po3_row_relative_small row scale := by
  intro ε hεpos
  rcases hproduct ε hεpos with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  exact
    le_trans (hrow k)
      (mul_le_mul_of_nonneg_right (hK k hk) (hscale_nonneg k))

/-- Finite row-mass count bridge.

If every point in a finite row window contributes at most `pointBound * scale`
and `card * pointBound <= countBound`, then the total near-row mass is bounded
by `countBound * scale`.  This is the Lean side of the log-loss row-mass
bookkeeping; zero-counting supplies the `countBound` hypothesis elsewhere. -/
theorem po3_near_row_mass_le_count_mul_scale
    {ι : Type*} [Fintype ι]
    {rowMass : ι → ℝ} {nearAMass pointBound countBound scale : ℝ}
    (hnear : nearAMass ≤ ∑ i, rowMass i)
    (hpoint : ∀ i, rowMass i ≤ pointBound * scale)
    (hcount : (Fintype.card ι : ℝ) * pointBound ≤ countBound)
    (hscale_nonneg : 0 ≤ scale) :
    nearAMass ≤ countBound * scale := by
  have hsum_le : (∑ i, rowMass i) ≤ ∑ _ : ι, pointBound * scale := by
    exact Finset.sum_le_sum (fun i _ => hpoint i)
  have hconst :
      (∑ _ : ι, pointBound * scale)
        = (Fintype.card ι : ℝ) * (pointBound * scale) := by
    simp
  have hcount_scale :
      ((Fintype.card ι : ℝ) * pointBound) * scale ≤ countBound * scale :=
    mul_le_mul_of_nonneg_right hcount hscale_nonneg
  calc
    nearAMass ≤ ∑ i, rowMass i := hnear
    _ ≤ ∑ _ : ι, pointBound * scale := hsum_le
    _ = (Fintype.card ι : ℝ) * (pointBound * scale) := hconst
    _ = ((Fintype.card ι : ℝ) * pointBound) * scale := by ring
    _ ≤ countBound * scale := hcount_scale

/-- Sequence form of the finite row-mass count bridge. -/
theorem po3_endpoint_row_log_mass_bound_of_finite_count
    {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
    (rowMass : ∀ k, ι k → ℝ)
    (nearAMass pointBound countBound scale : ℕ → ℝ)
    (hnear : ∀ k, nearAMass k ≤ ∑ i, rowMass k i)
    (hpoint : ∀ k i, rowMass k i ≤ pointBound k * scale k)
    (hcount : ∀ k, (Fintype.card (ι k) : ℝ) * pointBound k ≤ countBound k)
    (hscale_nonneg : ∀ k, 0 ≤ scale k) :
    ∀ k, nearAMass k ≤ countBound k * scale k := by
  intro k
  exact
    po3_near_row_mass_le_count_mul_scale
      (rowMass := rowMass k)
      (nearAMass := nearAMass k)
      (pointBound := pointBound k)
      (countBound := countBound k)
      (scale := scale k)
      (hnear k)
      (hpoint k)
      (hcount k)
      (hscale_nonneg k)

/-- Threshold-exhaustion omitted-mass bridge.

If all omitted row-effective points are individually at most `delta_k * scale_k`,
the local count is at most `logLoss_k`, and `delta_k * logLoss_k -> 0`, then
the omitted mass is small relative to `scale_k`. -/
theorem po3_threshold_omitted_mass_row_relative_small_of_finite_count
    {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
    (rowMass : ∀ k, ι k → ℝ)
    {omittedAMass delta logLoss scale : ℕ → ℝ}
    (hscale_nonneg : ∀ k, 0 ≤ scale k)
    (hdelta_nonneg : ∀ k, 0 ≤ delta k)
    (hnear : ∀ k, omittedAMass k ≤ ∑ i, rowMass k i)
    (hpoint : ∀ k i, rowMass k i ≤ delta k * scale k)
    (hcount : ∀ k, (Fintype.card (ι k) : ℝ) ≤ logLoss k)
    (hdeltaLog : po3_product_tends_to_zero delta logLoss) :
    po3_row_relative_small omittedAMass scale := by
  have hcount_delta :
      ∀ k, (Fintype.card (ι k) : ℝ) * delta k ≤ delta k * logLoss k := by
    intro k
    have hmul :
        delta k * (Fintype.card (ι k) : ℝ) ≤ delta k * logLoss k :=
      mul_le_mul_of_nonneg_left (hcount k) (hdelta_nonneg k)
    calc
      (Fintype.card (ι k) : ℝ) * delta k
          = delta k * (Fintype.card (ι k) : ℝ) := by ring
      _ ≤ delta k * logLoss k := hmul
  have hmass :
      ∀ k, omittedAMass k ≤ (delta k * logLoss k) * scale k :=
    po3_endpoint_row_log_mass_bound_of_finite_count
      rowMass omittedAMass delta (fun k => delta k * logLoss k) scale
      hnear hpoint hcount_delta hscale_nonneg
  exact
    po3_row_relative_small_of_le_product_scale
      hscale_nonneg hmass hdeltaLog

/-- Threshold-exhaustion omitted-mass bridge fed by a larger log/count envelope.

This is the same finite-count consumer as
`po3_threshold_omitted_mass_row_relative_small_of_finite_count`, but with the
analytic estimates supplied in the more stable form
`deltaBound_k * logBound_k -> 0`, `delta_k <= deltaBound_k`, and
`countBound_k <= logBound_k`. -/
theorem po3_threshold_omitted_mass_row_relative_small_of_finite_count_log_envelope
    {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
    (rowMass : ∀ k, ι k → ℝ)
    {omittedAMass delta deltaBound countBound logBound scale : ℕ → ℝ}
    (hscale_nonneg : ∀ k, 0 ≤ scale k)
    (hdelta_nonneg : ∀ k, 0 ≤ delta k)
    (hlogBound_nonneg : ∀ k, 0 ≤ logBound k)
    (hdelta_le : ∀ k, delta k ≤ deltaBound k)
    (hcount_le : ∀ k, countBound k ≤ logBound k)
    (hnear : ∀ k, omittedAMass k ≤ ∑ i, rowMass k i)
    (hpoint : ∀ k i, rowMass k i ≤ delta k * scale k)
    (hcount : ∀ k, (Fintype.card (ι k) : ℝ) ≤ countBound k)
    (hdeltaBoundLog : po3_product_tends_to_zero deltaBound logBound) :
    po3_row_relative_small omittedAMass scale := by
  have hdeltaCount : po3_product_tends_to_zero delta countBound :=
    po3_product_tends_to_zero_of_le_factors
      hlogBound_nonneg hdelta_nonneg hdelta_le hcount_le hdeltaBoundLog
  exact
    po3_threshold_omitted_mass_row_relative_small_of_finite_count
      rowMass
      (hscale_nonneg := hscale_nonneg)
      (hdelta_nonneg := hdelta_nonneg)
      (hnear := hnear)
      (hpoint := hpoint)
      (hcount := hcount)
      (hdeltaLog := hdeltaCount)

/-- `EndpointRowLogMassMirrorControl`.

If the mirror row is bounded by pointwise mirror suppression times the local
absolute `A`-mass plus a far mirror tail, the local `A`-mass has only a
log-loss bound against the packet scale, the product `eta * logLoss` tends to
zero, and the far mirror tail is already small relative to the same scale, then
the mirror row is small relative to the packet scale.

This is intentionally only a consumer shell.  The real analytic work remains:
prove the zero-counting log-loss bound and the stronger pointwise condition
`eta_{k,rho} log(2+xi_k) -> 0` for the selected endpoint rows. -/
theorem po3_endpoint_row_log_mass_mirror_control
    {mirrorAbs nearAMass farMirror eta logLoss scale : ℕ → ℝ}
    (hscale_nonneg : ∀ k, 0 ≤ scale k)
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (hmirror :
      ∀ k, mirrorAbs k ≤ eta k * nearAMass k + farMirror k)
    (hnear :
      ∀ k, nearAMass k ≤ logLoss k * scale k)
    (hetaLog : po3_product_tends_to_zero eta logLoss)
    (hfar : po3_row_relative_small farMirror scale) :
    po3_row_relative_small mirrorAbs scale := by
  intro ε hεpos
  have hhalf_pos : 0 < ε / 2 := by positivity
  rcases hetaLog (ε / 2) hhalf_pos with ⟨Keta, hKeta⟩
  rcases hfar (ε / 2) hhalf_pos with ⟨Kfar, hKfar⟩
  refine ⟨max Keta Kfar, ?_⟩
  intro k hk
  have hketa : Keta ≤ k := le_trans (le_max_left _ _) hk
  have hkfar : Kfar ≤ k := le_trans (le_max_right _ _) hk
  have hnear_eta :
      eta k * nearAMass k ≤ eta k * (logLoss k * scale k) := by
    exact mul_le_mul_of_nonneg_left (hnear k) (heta_nonneg k)
  have hnear_scale :
      eta k * (logLoss k * scale k) ≤ (ε / 2) * scale k := by
    calc
      eta k * (logLoss k * scale k)
          = (eta k * logLoss k) * scale k := by ring
      _ ≤ (ε / 2) * scale k := by
          exact mul_le_mul_of_nonneg_right (hKeta k hketa) (hscale_nonneg k)
  have hfar_scale : farMirror k ≤ (ε / 2) * scale k := hKfar k hkfar
  calc
    mirrorAbs k ≤ eta k * nearAMass k + farMirror k := hmirror k
    _ ≤ (ε / 2) * scale k + (ε / 2) * scale k := by
        exact add_le_add (le_trans hnear_eta hnear_scale) hfar_scale
    _ = ε * scale k := by ring

/-- Log-loss mirror control where the near `A`-mass bound comes from a finite
local count and pointwise row-mass comparability. -/
theorem po3_endpoint_row_log_mass_mirror_control_of_finite_count
    {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
    (rowMass : ∀ k, ι k → ℝ)
    {mirrorAbs nearAMass farMirror eta pointBound countBound scale : ℕ → ℝ}
    (hscale_nonneg : ∀ k, 0 ≤ scale k)
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (hmirror :
      ∀ k, mirrorAbs k ≤ eta k * nearAMass k + farMirror k)
    (hnear : ∀ k, nearAMass k ≤ ∑ i, rowMass k i)
    (hpoint : ∀ k i, rowMass k i ≤ pointBound k * scale k)
    (hcount : ∀ k, (Fintype.card (ι k) : ℝ) * pointBound k ≤ countBound k)
    (hetaCount : po3_product_tends_to_zero eta countBound)
    (hfar : po3_row_relative_small farMirror scale) :
    po3_row_relative_small mirrorAbs scale := by
  have hnear_log :
      ∀ k, nearAMass k ≤ countBound k * scale k :=
    po3_endpoint_row_log_mass_bound_of_finite_count
      rowMass nearAMass pointBound countBound scale
      hnear hpoint hcount hscale_nonneg
  exact
    po3_endpoint_row_log_mass_mirror_control
      hscale_nonneg heta_nonneg hmirror hnear_log hetaCount hfar

/-- Finite-count mirror control fed by a larger log/count envelope.

This is the form used when the analytic proof first gives product-smallness
for an upper suppression bound `etaBound` against a coarse log envelope, and
only separately compares the finite-count bound to that envelope. -/
theorem po3_endpoint_row_log_mass_mirror_control_of_finite_count_log_envelope
    {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
    (rowMass : ∀ k, ι k → ℝ)
    {mirrorAbs nearAMass farMirror eta etaBound pointBound countBound
      logBound scale : ℕ → ℝ}
    (hscale_nonneg : ∀ k, 0 ≤ scale k)
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (hlogBound_nonneg : ∀ k, 0 ≤ logBound k)
    (heta_le : ∀ k, eta k ≤ etaBound k)
    (hcount_le : ∀ k, countBound k ≤ logBound k)
    (hmirror :
      ∀ k, mirrorAbs k ≤ eta k * nearAMass k + farMirror k)
    (hnear : ∀ k, nearAMass k ≤ ∑ i, rowMass k i)
    (hpoint : ∀ k i, rowMass k i ≤ pointBound k * scale k)
    (hcount : ∀ k, (Fintype.card (ι k) : ℝ) * pointBound k ≤ countBound k)
    (hetaBoundLog : po3_product_tends_to_zero etaBound logBound)
    (hfar : po3_row_relative_small farMirror scale) :
    po3_row_relative_small mirrorAbs scale := by
  have hetaCount : po3_product_tends_to_zero eta countBound :=
    po3_product_tends_to_zero_of_le_factors
      hlogBound_nonneg heta_nonneg heta_le hcount_le hetaBoundLog
  exact
    po3_endpoint_row_log_mass_mirror_control_of_finite_count
      rowMass
      hscale_nonneg
      heta_nonneg
      hmirror
      hnear
      hpoint
      hcount
      hetaCount
      hfar

/-- Sum of two row-small estimates against the same moving scale. -/
theorem po3_row_relative_small_add
    {row₁ row₂ scale : ℕ → ℝ}
    (hrow₁ : po3_row_relative_small row₁ scale)
    (hrow₂ : po3_row_relative_small row₂ scale) :
    po3_row_relative_small (fun k => row₁ k + row₂ k) scale := by
  intro ε hεpos
  have hhalf_pos : 0 < ε / 2 := by positivity
  rcases hrow₁ (ε / 2) hhalf_pos with ⟨K₁, hK₁⟩
  rcases hrow₂ (ε / 2) hhalf_pos with ⟨K₂, hK₂⟩
  refine ⟨max K₁ K₂, ?_⟩
  intro k hk
  have hk₁ : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk₂ : K₂ ≤ k := le_trans (le_max_right _ _) hk
  calc
    row₁ k + row₂ k
        ≤ (ε / 2) * scale k + (ε / 2) * scale k := by
          exact add_le_add (hK₁ k hk₁) (hK₂ k hk₂)
    _ = ε * scale k := by ring

/-- A row-small estimate against the normalized scale `1` is ordinary
real-valued smallness to zero. -/
theorem po3_real_tends_to_zero_of_row_relative_small_one
    {error : ℕ → ℝ}
    (herror : po3_row_relative_small error (fun _ => 1)) :
    po3_real_tends_to_zero error := by
  intro ε hεpos
  have hhalf_pos : 0 < ε / 2 := by positivity
  rcases herror (ε / 2) hhalf_pos with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  have hk_small : error k ≤ ε / 2 := by
    simpa using hK k hk
  exact lt_of_le_of_lt hk_small (by linarith)

/-- If a normalized shifted row error is bounded by two row-small pieces, it is
row-small. -/
theorem po3_shifted_row_error_relative_small_of_parts
    {epsilon mirrorAbs omittedAMass scale : ℕ → ℝ}
    (herror : ∀ k, epsilon k ≤ mirrorAbs k + omittedAMass k)
    (hmirror : po3_row_relative_small mirrorAbs scale)
    (homitted : po3_row_relative_small omittedAMass scale) :
    po3_row_relative_small epsilon scale := by
  intro ε hεpos
  rcases po3_row_relative_small_add hmirror homitted ε hεpos with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  exact le_trans (herror k) (hK k hk)

/-- `PO3-square.2d3.shifted-error-after-stable-rows` consumer.

The shifted row error is small once the mirror row is handled by the log-loss
mirror consumer and the omitted main-side `A` mass is already small by
threshold exhaustion. -/
theorem po3_shifted_row_error_small_of_log_mirror_and_threshold
    {epsilon mirrorAbs nearAMass farMirror eta logLoss omittedAMass scale :
      ℕ → ℝ}
    (hscale_nonneg : ∀ k, 0 ≤ scale k)
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (hmirror :
      ∀ k, mirrorAbs k ≤ eta k * nearAMass k + farMirror k)
    (hnear :
      ∀ k, nearAMass k ≤ logLoss k * scale k)
    (hetaLog : po3_product_tends_to_zero eta logLoss)
    (hfar : po3_row_relative_small farMirror scale)
    (herror : ∀ k, epsilon k ≤ mirrorAbs k + omittedAMass k)
    (homitted : po3_row_relative_small omittedAMass scale) :
    po3_row_relative_small epsilon scale := by
  have hmirror_small : po3_row_relative_small mirrorAbs scale :=
    po3_endpoint_row_log_mass_mirror_control
      hscale_nonneg heta_nonneg hmirror hnear hetaLog hfar
  exact
    po3_shifted_row_error_relative_small_of_parts
      herror hmirror_small homitted

/-! ## Variable-packet capture consumer -/

/-- `VariableComparablePacketCapture` as a stable-projection consumer.

This is the finite-dimensional linear-algebra core of the current
`PO3-square.2d3` threshold-packet plan.  A future analytic argument supplies:

- a row operator `V` for the selected endpoint-adaptive rows;
- a projection `Proj` onto the expected Vandermonde/Hermite kernel;
- a stability constant `C`, analytically `1 / sigma_min^+(V)`;
- the row equation `V q = ε`.

Then the packet vector `q` is captured up to the row error amplified by the
conditioning constant.  The real hard input is therefore exactly
`C_k * ‖ε_k‖ -> 0`, not another shell redesign. -/
theorem po3_variable_comparable_packet_capture_of_stable_projection
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : E →L[ℂ] F) (Proj : E →L[ℂ] E) (C : ℝ)
    (hstable : ∀ x : E, ‖x - Proj x‖ ≤ C * ‖V x‖)
    (q : E) (ε : F)
    (hrow : V q = ε) :
    ‖q - Proj q‖ ≤ C * ‖ε‖ := by
  simpa [hrow] using hstable q

/-- Sequence-level conditioned capture handoff.

If each endpoint-row system has the stable-projection estimate and the
conditioning product `C_k * ‖epsilon_k‖` tends to zero, then the capture error
`‖q_k - Proj_k q_k‖` tends to zero. -/
theorem po3_capture_error_tends_to_zero_of_stable_projection_conditioning
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k)
    (hconditioning :
      po3_product_tends_to_zero C (fun k => ‖rowError k‖)) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) := by
  exact
    po3_real_tends_to_zero_of_le_product
      (capture := fun k => ‖q k - Proj k (q k)‖)
      (C := C)
      (rowError := fun k => ‖rowError k‖)
      (fun k =>
        po3_variable_comparable_packet_capture_of_stable_projection
          (V k) (Proj k) (C k) (hstable k) (q k) (rowError k) (hrow k))
      hconditioning

/-- Exact stable-projection fork for the live `EndpointRowStableProjectionOrRouteKill`
decision.

For this route shape, after the endpoint-row equations and stable-projection
estimate are fixed, either the conditioning product is available and the
capture error tends to zero, or the missing product estimate is the precise
formal obstruction still to be resolved. -/
theorem po3_capture_error_tends_to_zero_or_conditioning_product_obstruction
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) ∨
      ¬ po3_product_tends_to_zero C (fun k => ‖rowError k‖) := by
  classical
  by_cases hconditioning :
      po3_product_tends_to_zero C (fun k => ‖rowError k‖)
  · exact
      Or.inl
        (po3_capture_error_tends_to_zero_of_stable_projection_conditioning
          V Proj C q rowError hstable hrow hconditioning)
  · exact Or.inr hconditioning

/-- Bounded-conditioning specialization of the sequence-level capture handoff.

This is the Lean-side consumer for the bounded-separated branch: once the
stable constants are eventually bounded and the row-error norms tend to zero,
the capture error tends to zero. -/
theorem po3_capture_error_tends_to_zero_of_bounded_stable_projection
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k)
    (hC : po3_eventually_bounded_above_by_pos C)
    (hrowSmall : po3_real_tends_to_zero (fun k => ‖rowError k‖)) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) := by
  exact
    po3_capture_error_tends_to_zero_of_stable_projection_conditioning
      V Proj C q rowError hstable hrow
      (po3_product_tends_to_zero_of_bounded_left
        (fun k => norm_nonneg (rowError k)) hC hrowSmall)

/-- Row-sup norm-correction handoff for conditioned capture.

If `‖epsilon_k‖` is bounded by `rowFactor_k * rowSup_k`, the combined
conditioning factor `C_k * rowFactor_k` is eventually bounded, and the row-sup
error tends to zero, then `C_k * ‖epsilon_k‖ -> 0`. -/
theorem po3_conditioning_product_tends_to_zero_of_row_sup_bound
    {C rowNorm rowFactor rowSup : ℕ → ℝ}
    (hC_nonneg : ∀ k, 0 ≤ C k)
    (hrowNorm_bound : ∀ k, rowNorm k ≤ rowFactor k * rowSup k)
    (hCfactor : po3_eventually_bounded_above_by_pos
      (fun k => C k * rowFactor k))
    (hrowSup_nonneg : ∀ k, 0 ≤ rowSup k)
    (hrowSup : po3_real_tends_to_zero rowSup) :
    po3_product_tends_to_zero C rowNorm := by
  intro ε hεpos
  have hproduct :
      po3_product_tends_to_zero (fun k => C k * rowFactor k) rowSup :=
    po3_product_tends_to_zero_of_bounded_left
      (C := fun k => C k * rowFactor k)
      (rowError := rowSup)
      hrowSup_nonneg hCfactor hrowSup
  rcases hproduct ε hεpos with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  have hrowk : rowNorm k ≤ rowFactor k * rowSup k := hrowNorm_bound k
  have hleft : C k * rowNorm k ≤ C k * (rowFactor k * rowSup k) :=
    mul_le_mul_of_nonneg_left hrowk (hC_nonneg k)
  calc
    C k * rowNorm k ≤ C k * (rowFactor k * rowSup k) := hleft
    _ = (C k * rowFactor k) * rowSup k := by ring
    _ ≤ ε := hK k hk

/-- Stable-projection capture from row-sup error with explicit norm-correction
factor. -/
theorem po3_capture_error_tends_to_zero_of_stable_projection_row_sup
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C rowFactor rowSup : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k)
    (hC_nonneg : ∀ k, 0 ≤ C k)
    (hrowNorm_bound : ∀ k, ‖rowError k‖ ≤ rowFactor k * rowSup k)
    (hCfactor : po3_eventually_bounded_above_by_pos
      (fun k => C k * rowFactor k))
    (hrowSup_nonneg : ∀ k, 0 ≤ rowSup k)
    (hrowSup : po3_real_tends_to_zero rowSup) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) := by
  exact
    po3_capture_error_tends_to_zero_of_stable_projection_conditioning
      V Proj C q rowError hstable hrow
      (po3_conditioning_product_tends_to_zero_of_row_sup_bound
        hC_nonneg hrowNorm_bound hCfactor hrowSup_nonneg hrowSup)

/-- Row-sup capture with separate boundedness inputs for the stable projection
constant and the norm-correction factor. -/
theorem po3_capture_error_tends_to_zero_of_stable_projection_row_sup_bounded_factors
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C rowFactor rowSup : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k)
    (hC_nonneg : ∀ k, 0 ≤ C k)
    (hrowNorm_bound : ∀ k, ‖rowError k‖ ≤ rowFactor k * rowSup k)
    (hC_bound : po3_eventually_bounded_above_by_pos C)
    (hrowFactor_nonneg : ∀ k, 0 ≤ rowFactor k)
    (hrowFactor_bound : po3_eventually_bounded_above_by_pos rowFactor)
    (hrowSup_nonneg : ∀ k, 0 ≤ rowSup k)
    (hrowSup : po3_real_tends_to_zero rowSup) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) := by
  exact
    po3_capture_error_tends_to_zero_of_stable_projection_row_sup
      V Proj C rowFactor rowSup q rowError hstable hrow
      hC_nonneg hrowNorm_bound
      (po3_eventually_bounded_above_by_pos_mul
        hrowFactor_nonneg hC_bound hrowFactor_bound)
      hrowSup_nonneg hrowSup

/-- Euclidean row-norm correction for finitely many selected endpoint rows.

If every component row error is bounded by `rowSup`, then the Euclidean
row-error norm pays exactly the expected `sqrt(card rows)` factor. -/
theorem po3_euclidean_row_error_norm_le_sqrt_card_mul_sup
    {ι : Type*} [Fintype ι]
    (rowError : EuclideanSpace ℂ ι) (rowSup : ℝ)
    (hrowSup_nonneg : 0 ≤ rowSup)
    (hcoord : ∀ i, ‖rowError i‖ ≤ rowSup) :
    ‖rowError‖ ≤ Real.sqrt (Fintype.card ι) * rowSup := by
  classical
  have hsum :
      (∑ i, ‖rowError.ofLp i‖ ^ 2) ≤ ∑ _i : ι, rowSup ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact
      pow_le_pow_left₀ (norm_nonneg (rowError.ofLp i))
        (by simpa using hcoord i) 2
  have hnorm :
      ‖rowError‖ = Real.sqrt (∑ i, ‖rowError.ofLp i‖ ^ 2) :=
    EuclideanSpace.norm_eq rowError
  have hsum_const :
      (∑ _i : ι, rowSup ^ 2) = (Fintype.card ι : ℝ) * rowSup ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    ‖rowError‖ = Real.sqrt (∑ i, ‖rowError.ofLp i‖ ^ 2) := hnorm
    _ ≤ Real.sqrt (∑ _i : ι, rowSup ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt ((Fintype.card ι : ℝ) * rowSup ^ 2) := by
          rw [hsum_const]
    _ = Real.sqrt (Fintype.card ι) * rowSup := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _) (rowSup ^ 2),
            Real.sqrt_sq hrowSup_nonneg]

/-- Normalized row-sup capture consumer for `PO3-square.2d3`.

This combines the bookkeeping pieces in the active route:
log-loss mirror control and omitted `A`-mass control make the normalized row
supremum tend to zero; the explicit row-factor estimate turns that into
conditioned row-norm smallness; stable projection then gives capture. -/
theorem po3_capture_error_tends_to_zero_of_log_mirror_threshold_row_sup
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C rowFactor rowSup : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (mirrorAbs nearAMass farMirror eta logLoss omittedAMass : ℕ → ℝ)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k)
    (hC_nonneg : ∀ k, 0 ≤ C k)
    (hrowNorm_bound : ∀ k, ‖rowError k‖ ≤ rowFactor k * rowSup k)
    (hCfactor : po3_eventually_bounded_above_by_pos
      (fun k => C k * rowFactor k))
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (hmirror :
      ∀ k, mirrorAbs k ≤ eta k * nearAMass k + farMirror k)
    (hnear : ∀ k, nearAMass k ≤ logLoss k)
    (hetaLog : po3_product_tends_to_zero eta logLoss)
    (hfar : po3_row_relative_small farMirror (fun _ => 1))
    (hrowSup_bound : ∀ k, rowSup k ≤ mirrorAbs k + omittedAMass k)
    (homitted : po3_row_relative_small omittedAMass (fun _ => 1))
    (hrowSup_nonneg : ∀ k, 0 ≤ rowSup k) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) := by
  have hrowSup_small : po3_real_tends_to_zero rowSup :=
    po3_real_tends_to_zero_of_row_relative_small_one
      (po3_shifted_row_error_small_of_log_mirror_and_threshold
        (scale := fun _ => 1)
        (fun _ => by norm_num)
        heta_nonneg
        hmirror
        (fun k => by simpa using hnear k)
        hetaLog
        hfar
        hrowSup_bound
        homitted)
  exact
    po3_capture_error_tends_to_zero_of_stable_projection_row_sup
      V Proj C rowFactor rowSup q rowError hstable hrow
      hC_nonneg hrowNorm_bound hCfactor hrowSup_nonneg hrowSup_small

/-- End-to-end finite-count capture assembly for `PO3-square.2d3`.

This is the normalized consumer after the April log-loss correction:

- mirror near-mass comes from a finite local count and pointwise row-mass bound;
- mirror suppression is allowed to pass through the stronger `etaBound`;
- omitted `A`-mass is handled by threshold exhaustion;
- row-sup control pays the explicit row-factor before stable projection.

All analytic estimates remain hypotheses of this theorem. -/
theorem po3_capture_error_tends_to_zero_of_finite_count_threshold_mirror
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {ιMirror ιOmitted : ℕ → Type*}
    [∀ k, Fintype (ιMirror k)] [∀ k, Fintype (ιOmitted k)]
    (mirrorRowMass : ∀ k, ιMirror k → ℝ)
    (omittedRowMass : ∀ k, ιOmitted k → ℝ)
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C rowFactor rowSup : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (mirrorAbs nearAMass farMirror eta etaBound mirrorPointBound
      mirrorCountBound omittedAMass delta logLoss : ℕ → ℝ)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k)
    (hC_nonneg : ∀ k, 0 ≤ C k)
    (hrowNorm_bound : ∀ k, ‖rowError k‖ ≤ rowFactor k * rowSup k)
    (hCfactor : po3_eventually_bounded_above_by_pos
      (fun k => C k * rowFactor k))
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (heta_le : ∀ k, eta k ≤ etaBound k)
    (hmirrorCount_nonneg : ∀ k, 0 ≤ mirrorCountBound k)
    (hetaBoundCount :
      po3_product_tends_to_zero etaBound mirrorCountBound)
    (hmirror :
      ∀ k, mirrorAbs k ≤ eta k * nearAMass k + farMirror k)
    (hmirrorNear : ∀ k, nearAMass k ≤ ∑ i, mirrorRowMass k i)
    (hmirrorPoint :
      ∀ k i, mirrorRowMass k i ≤ mirrorPointBound k)
    (hmirrorCount :
      ∀ k, (Fintype.card (ιMirror k) : ℝ) * mirrorPointBound k ≤
        mirrorCountBound k)
    (hfar : po3_row_relative_small farMirror (fun _ => 1))
    (hrowSup_bound : ∀ k, rowSup k ≤ mirrorAbs k + omittedAMass k)
    (hdelta_nonneg : ∀ k, 0 ≤ delta k)
    (homittedNear :
      ∀ k, omittedAMass k ≤ ∑ i, omittedRowMass k i)
    (homittedPoint : ∀ k i, omittedRowMass k i ≤ delta k)
    (homittedCount :
      ∀ k, (Fintype.card (ιOmitted k) : ℝ) ≤ logLoss k)
    (hdeltaLog : po3_product_tends_to_zero delta logLoss)
    (hrowSup_nonneg : ∀ k, 0 ≤ rowSup k) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) := by
  have hetaCount :
      po3_product_tends_to_zero eta mirrorCountBound :=
    po3_product_tends_to_zero_of_le_left
      hmirrorCount_nonneg heta_le hetaBoundCount
  have hmirror_small :
      po3_row_relative_small mirrorAbs (fun _ => 1) :=
    po3_endpoint_row_log_mass_mirror_control_of_finite_count
      (ι := ιMirror)
      mirrorRowMass
      (hscale_nonneg := fun _ => by norm_num)
      (heta_nonneg := heta_nonneg)
      (hmirror := hmirror)
      (hnear := hmirrorNear)
      (hpoint := fun k i => by
        simpa using hmirrorPoint k i)
      (hcount := hmirrorCount)
      (hetaCount := hetaCount)
      (hfar := hfar)
  have homitted_small :
      po3_row_relative_small omittedAMass (fun _ => 1) :=
    po3_threshold_omitted_mass_row_relative_small_of_finite_count
      (ι := ιOmitted)
      omittedRowMass
      (hscale_nonneg := fun _ => by norm_num)
      (hdelta_nonneg := hdelta_nonneg)
      (hnear := homittedNear)
      (hpoint := fun k i => by
        simpa using homittedPoint k i)
      (hcount := homittedCount)
      (hdeltaLog := hdeltaLog)
  have hrowSup_rel :
      po3_row_relative_small rowSup (fun _ => 1) :=
    po3_shifted_row_error_relative_small_of_parts
      hrowSup_bound hmirror_small homitted_small
  have hrowSup_small : po3_real_tends_to_zero rowSup :=
    po3_real_tends_to_zero_of_row_relative_small_one hrowSup_rel
  exact
    po3_capture_error_tends_to_zero_of_stable_projection_row_sup
      V Proj C rowFactor rowSup q rowError hstable hrow
      hC_nonneg hrowNorm_bound hCfactor hrowSup_nonneg hrowSup_small

/-- End-to-end finite-count capture assembly with a log/count envelope.

This is the same capture consumer as
`po3_capture_error_tends_to_zero_of_finite_count_threshold_mirror`, but in the
form expected from the log-loss route: the analytic product is proved against a
larger envelope `logBound`, while the finite-count estimate only has to compare
`mirrorCountBound <= logBound`. -/
theorem po3_capture_error_tends_to_zero_of_finite_count_log_envelope_threshold_mirror
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {ιMirror ιOmitted : ℕ → Type*}
    [∀ k, Fintype (ιMirror k)] [∀ k, Fintype (ιOmitted k)]
    (mirrorRowMass : ∀ k, ιMirror k → ℝ)
    (omittedRowMass : ∀ k, ιOmitted k → ℝ)
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C rowFactor rowSup : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (mirrorAbs nearAMass farMirror eta etaBound mirrorPointBound
      mirrorCountBound mirrorLogBound omittedAMass delta logLoss : ℕ → ℝ)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k)
    (hC_nonneg : ∀ k, 0 ≤ C k)
    (hrowNorm_bound : ∀ k, ‖rowError k‖ ≤ rowFactor k * rowSup k)
    (hCfactor : po3_eventually_bounded_above_by_pos
      (fun k => C k * rowFactor k))
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (hmirrorLogBound_nonneg : ∀ k, 0 ≤ mirrorLogBound k)
    (heta_le : ∀ k, eta k ≤ etaBound k)
    (hmirrorCount_le_log :
      ∀ k, mirrorCountBound k ≤ mirrorLogBound k)
    (hetaBoundLog :
      po3_product_tends_to_zero etaBound mirrorLogBound)
    (hmirror :
      ∀ k, mirrorAbs k ≤ eta k * nearAMass k + farMirror k)
    (hmirrorNear : ∀ k, nearAMass k ≤ ∑ i, mirrorRowMass k i)
    (hmirrorPoint :
      ∀ k i, mirrorRowMass k i ≤ mirrorPointBound k)
    (hmirrorCount :
      ∀ k, (Fintype.card (ιMirror k) : ℝ) * mirrorPointBound k ≤
        mirrorCountBound k)
    (hfar : po3_row_relative_small farMirror (fun _ => 1))
    (hrowSup_bound : ∀ k, rowSup k ≤ mirrorAbs k + omittedAMass k)
    (hdelta_nonneg : ∀ k, 0 ≤ delta k)
    (homittedNear :
      ∀ k, omittedAMass k ≤ ∑ i, omittedRowMass k i)
    (homittedPoint : ∀ k i, omittedRowMass k i ≤ delta k)
    (homittedCount :
      ∀ k, (Fintype.card (ιOmitted k) : ℝ) ≤ logLoss k)
    (hdeltaLog : po3_product_tends_to_zero delta logLoss)
    (hrowSup_nonneg : ∀ k, 0 ≤ rowSup k) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) := by
  have hmirror_small :
      po3_row_relative_small mirrorAbs (fun _ => 1) :=
    po3_endpoint_row_log_mass_mirror_control_of_finite_count_log_envelope
      (ι := ιMirror)
      mirrorRowMass
      (hscale_nonneg := fun _ => by norm_num)
      (heta_nonneg := heta_nonneg)
      (hlogBound_nonneg := hmirrorLogBound_nonneg)
      (heta_le := heta_le)
      (hcount_le := hmirrorCount_le_log)
      (hmirror := hmirror)
      (hnear := hmirrorNear)
      (hpoint := fun k i => by
        simpa using hmirrorPoint k i)
      (hcount := hmirrorCount)
      (hetaBoundLog := hetaBoundLog)
      (hfar := hfar)
  have homitted_small :
      po3_row_relative_small omittedAMass (fun _ => 1) :=
    po3_threshold_omitted_mass_row_relative_small_of_finite_count
      (ι := ιOmitted)
      omittedRowMass
      (hscale_nonneg := fun _ => by norm_num)
      (hdelta_nonneg := hdelta_nonneg)
      (hnear := homittedNear)
      (hpoint := fun k i => by
        simpa using homittedPoint k i)
      (hcount := homittedCount)
      (hdeltaLog := hdeltaLog)
  have hrowSup_rel :
      po3_row_relative_small rowSup (fun _ => 1) :=
    po3_shifted_row_error_relative_small_of_parts
      hrowSup_bound hmirror_small homitted_small
  have hrowSup_small : po3_real_tends_to_zero rowSup :=
    po3_real_tends_to_zero_of_row_relative_small_one hrowSup_rel
  exact
    po3_capture_error_tends_to_zero_of_stable_projection_row_sup
      V Proj C rowFactor rowSup q rowError hstable hrow
      hC_nonneg hrowNorm_bound hCfactor hrowSup_nonneg hrowSup_small

/-- End-to-end capture assembly with log/count envelopes on both row-error
sides.

The mirror and omitted estimates may use different count and log envelopes.
This is the fully envelope-shaped consumer expected from the current
`PO3-square.2d3` route: prove the analytic products against larger log
envelopes, compare the finite local counts to those envelopes, and keep the
stable-projection amplification explicit through `C * rowFactor`. -/
theorem po3_capture_error_tends_to_zero_of_log_envelopes_threshold_mirror
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {ιMirror ιOmitted : ℕ → Type*}
    [∀ k, Fintype (ιMirror k)] [∀ k, Fintype (ιOmitted k)]
    (mirrorRowMass : ∀ k, ιMirror k → ℝ)
    (omittedRowMass : ∀ k, ιOmitted k → ℝ)
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C rowFactor rowSup : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (mirrorAbs nearAMass farMirror eta etaBound mirrorPointBound
      mirrorCountBound mirrorLogBound omittedAMass delta deltaBound
      omittedCountBound omittedLogBound : ℕ → ℝ)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k)
    (hC_nonneg : ∀ k, 0 ≤ C k)
    (hrowNorm_bound : ∀ k, ‖rowError k‖ ≤ rowFactor k * rowSup k)
    (hCfactor : po3_eventually_bounded_above_by_pos
      (fun k => C k * rowFactor k))
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (hmirrorLogBound_nonneg : ∀ k, 0 ≤ mirrorLogBound k)
    (heta_le : ∀ k, eta k ≤ etaBound k)
    (hmirrorCount_le_log :
      ∀ k, mirrorCountBound k ≤ mirrorLogBound k)
    (hetaBoundLog :
      po3_product_tends_to_zero etaBound mirrorLogBound)
    (hmirror :
      ∀ k, mirrorAbs k ≤ eta k * nearAMass k + farMirror k)
    (hmirrorNear : ∀ k, nearAMass k ≤ ∑ i, mirrorRowMass k i)
    (hmirrorPoint :
      ∀ k i, mirrorRowMass k i ≤ mirrorPointBound k)
    (hmirrorCount :
      ∀ k, (Fintype.card (ιMirror k) : ℝ) * mirrorPointBound k ≤
        mirrorCountBound k)
    (hfar : po3_row_relative_small farMirror (fun _ => 1))
    (hrowSup_bound : ∀ k, rowSup k ≤ mirrorAbs k + omittedAMass k)
    (hdelta_nonneg : ∀ k, 0 ≤ delta k)
    (homittedLogBound_nonneg : ∀ k, 0 ≤ omittedLogBound k)
    (hdelta_le : ∀ k, delta k ≤ deltaBound k)
    (homittedCount_le_log :
      ∀ k, omittedCountBound k ≤ omittedLogBound k)
    (homittedNear :
      ∀ k, omittedAMass k ≤ ∑ i, omittedRowMass k i)
    (homittedPoint : ∀ k i, omittedRowMass k i ≤ delta k)
    (homittedCount :
      ∀ k, (Fintype.card (ιOmitted k) : ℝ) ≤ omittedCountBound k)
    (hdeltaBoundLog :
      po3_product_tends_to_zero deltaBound omittedLogBound)
    (hrowSup_nonneg : ∀ k, 0 ≤ rowSup k) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) := by
  have hmirror_small :
      po3_row_relative_small mirrorAbs (fun _ => 1) :=
    po3_endpoint_row_log_mass_mirror_control_of_finite_count_log_envelope
      (ι := ιMirror)
      mirrorRowMass
      (hscale_nonneg := fun _ => by norm_num)
      (heta_nonneg := heta_nonneg)
      (hlogBound_nonneg := hmirrorLogBound_nonneg)
      (heta_le := heta_le)
      (hcount_le := hmirrorCount_le_log)
      (hmirror := hmirror)
      (hnear := hmirrorNear)
      (hpoint := fun k i => by
        simpa using hmirrorPoint k i)
      (hcount := hmirrorCount)
      (hetaBoundLog := hetaBoundLog)
      (hfar := hfar)
  have homitted_small :
      po3_row_relative_small omittedAMass (fun _ => 1) :=
    po3_threshold_omitted_mass_row_relative_small_of_finite_count_log_envelope
      (ι := ιOmitted)
      omittedRowMass
      (hscale_nonneg := fun _ => by norm_num)
      (hdelta_nonneg := hdelta_nonneg)
      (hlogBound_nonneg := homittedLogBound_nonneg)
      (hdelta_le := hdelta_le)
      (hcount_le := homittedCount_le_log)
      (hnear := homittedNear)
      (hpoint := fun k i => by
        simpa using homittedPoint k i)
      (hcount := homittedCount)
      (hdeltaBoundLog := hdeltaBoundLog)
  have hrowSup_rel :
      po3_row_relative_small rowSup (fun _ => 1) :=
    po3_shifted_row_error_relative_small_of_parts
      hrowSup_bound hmirror_small homitted_small
  have hrowSup_small : po3_real_tends_to_zero rowSup :=
    po3_real_tends_to_zero_of_row_relative_small_one hrowSup_rel
  exact
    po3_capture_error_tends_to_zero_of_stable_projection_row_sup
      V Proj C rowFactor rowSup q rowError hstable hrow
      hC_nonneg hrowNorm_bound hCfactor hrowSup_nonneg hrowSup_small

/-- Bounded-separated branch shape for the double log-envelope capture
consumer.

This version keeps the stable-projection constant and row norm-correction
factor as separate bounded inputs, matching the intended analytic
instantiation for bounded separated endpoint packets. -/
theorem po3_capture_error_tends_to_zero_of_log_envelopes_threshold_mirror_bounded_factors
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {ιMirror ιOmitted : ℕ → Type*}
    [∀ k, Fintype (ιMirror k)] [∀ k, Fintype (ιOmitted k)]
    (mirrorRowMass : ∀ k, ιMirror k → ℝ)
    (omittedRowMass : ∀ k, ιOmitted k → ℝ)
    (V : ℕ → E →L[ℂ] F) (Proj : ℕ → E →L[ℂ] E)
    (C rowFactor rowSup : ℕ → ℝ) (q : ℕ → E) (rowError : ℕ → F)
    (mirrorAbs nearAMass farMirror eta etaBound mirrorPointBound
      mirrorCountBound mirrorLogBound omittedAMass delta deltaBound
      omittedCountBound omittedLogBound : ℕ → ℝ)
    (hstable : ∀ k x, ‖x - Proj k x‖ ≤ C k * ‖V k x‖)
    (hrow : ∀ k, V k (q k) = rowError k)
    (hC_nonneg : ∀ k, 0 ≤ C k)
    (hrowNorm_bound : ∀ k, ‖rowError k‖ ≤ rowFactor k * rowSup k)
    (hC_bound : po3_eventually_bounded_above_by_pos C)
    (hrowFactor_nonneg : ∀ k, 0 ≤ rowFactor k)
    (hrowFactor_bound : po3_eventually_bounded_above_by_pos rowFactor)
    (heta_nonneg : ∀ k, 0 ≤ eta k)
    (hmirrorLogBound_nonneg : ∀ k, 0 ≤ mirrorLogBound k)
    (heta_le : ∀ k, eta k ≤ etaBound k)
    (hmirrorCount_le_log :
      ∀ k, mirrorCountBound k ≤ mirrorLogBound k)
    (hetaBoundLog :
      po3_product_tends_to_zero etaBound mirrorLogBound)
    (hmirror :
      ∀ k, mirrorAbs k ≤ eta k * nearAMass k + farMirror k)
    (hmirrorNear : ∀ k, nearAMass k ≤ ∑ i, mirrorRowMass k i)
    (hmirrorPoint :
      ∀ k i, mirrorRowMass k i ≤ mirrorPointBound k)
    (hmirrorCount :
      ∀ k, (Fintype.card (ιMirror k) : ℝ) * mirrorPointBound k ≤
        mirrorCountBound k)
    (hfar : po3_row_relative_small farMirror (fun _ => 1))
    (hrowSup_bound : ∀ k, rowSup k ≤ mirrorAbs k + omittedAMass k)
    (hdelta_nonneg : ∀ k, 0 ≤ delta k)
    (homittedLogBound_nonneg : ∀ k, 0 ≤ omittedLogBound k)
    (hdelta_le : ∀ k, delta k ≤ deltaBound k)
    (homittedCount_le_log :
      ∀ k, omittedCountBound k ≤ omittedLogBound k)
    (homittedNear :
      ∀ k, omittedAMass k ≤ ∑ i, omittedRowMass k i)
    (homittedPoint : ∀ k i, omittedRowMass k i ≤ delta k)
    (homittedCount :
      ∀ k, (Fintype.card (ιOmitted k) : ℝ) ≤ omittedCountBound k)
    (hdeltaBoundLog :
      po3_product_tends_to_zero deltaBound omittedLogBound)
    (hrowSup_nonneg : ∀ k, 0 ≤ rowSup k) :
    po3_real_tends_to_zero (fun k => ‖q k - Proj k (q k)‖) := by
  exact
    po3_capture_error_tends_to_zero_of_log_envelopes_threshold_mirror
      mirrorRowMass omittedRowMass V Proj C rowFactor rowSup q rowError
      mirrorAbs nearAMass farMirror eta etaBound mirrorPointBound
      mirrorCountBound mirrorLogBound omittedAMass delta deltaBound
      omittedCountBound omittedLogBound
      hstable hrow hC_nonneg hrowNorm_bound
      (po3_eventually_bounded_above_by_pos_mul
        hrowFactor_nonneg hC_bound hrowFactor_bound)
      heta_nonneg hmirrorLogBound_nonneg heta_le hmirrorCount_le_log
      hetaBoundLog hmirror hmirrorNear hmirrorPoint hmirrorCount hfar
      hrowSup_bound hdelta_nonneg homittedLogBound_nonneg hdelta_le
      homittedCount_le_log homittedNear homittedPoint homittedCount
      hdeltaBoundLog hrowSup_nonneg

/-- Analytic certificate shape for the fastest current branch:
`EndpointRowsStableProjection_boundedSeparated`.

The fields are intentionally proof-facing rather than computational.  The
future analytic work must show that a threshold-exhaustive packet is bounded,
its exponential local nodes are separated, the selected endpoint rows converge
to the rectangular Vandermonde row model, and this gives a uniform stable
projection constant.  Once those facts are available, the generic stable-
projection consumer captures the packet vector. -/
structure PO3EndpointRowBoundedSeparatedStableProjectionCertificate
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] where
  V : E →L[ℂ] F
  Proj : E →L[ℂ] E
  C : ℝ
  bounded_packet : Prop
  separated_exponential_nodes : Prop
  endpoint_rows_vandermonde_limit : Prop
  stable_projection : ∀ x : E, ‖x - Proj x‖ ≤ C * ‖V x‖

/-- Consumer for a bounded-separated endpoint-row stable-projection
certificate.

This is the Lean-facing landing surface for the branch recommended by the
latest `PO3-square.2d3` review.  It deliberately treats the Vandermonde gap and
row convergence as certificate fields; the analytic theorem to prove next is
that the real endpoint rows supply such a certificate for the selected
threshold packet. -/
theorem po3_endpoint_rows_stable_projection_of_bounded_separated_packet
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (cert :
      PO3EndpointRowBoundedSeparatedStableProjectionCertificate E F)
    (q : E) (ε : F)
    (hrow : cert.V q = ε) :
    ‖q - cert.Proj q‖ ≤ cert.C * ‖ε‖ :=
  po3_variable_comparable_packet_capture_of_stable_projection
    cert.V cert.Proj cert.C cert.stable_projection q ε hrow

/-- Orientation-safe product asymptotic certificate for endpoint-row
multipliers.

The real endpoint rows may have either sign depending on whether the packet is
near the left or right edge of the pole block.  Thus the row limit is recorded
with a general slope parameter `alpha`, not hardcoded as `p`.

Mathematically this packages the product-model statement:

`m_{k,p}(xi_k + t/Lambda_k) / m_{k,p}(xi_k) -> exp(-alpha_p t)`,

uniformly for bounded row indices and compact `t`-ranges, assuming the
theta-slope ratio, local tube, and second-order bounds. -/
structure PO3EndpointRowProductAsymptoticCertificate where
  alpha : ℕ → ℂ
  edge_log_scale : Prop
  local_tube : Prop
  theta_slope : Prop
  second_order_small : Prop
  uniform_multiplier_asymptotic : Prop
  uniform_multiplier_asymptotic_proof : uniform_multiplier_asymptotic

/-- Marker theorem for the orientation-safe endpoint-row multiplier limit.

This is intentionally a certificate consumer: the analytic proof of the
product expansion belongs to the transform-side wall, while this file records
the exact statement shape needed by the bounded-separated Vandermonde branch. -/
theorem po3_endpoint_row_multiplier_uniform_asymptotic_of_theta_slope
    (cert : PO3EndpointRowProductAsymptoticCertificate) :
    cert.uniform_multiplier_asymptotic :=
  cert.uniform_multiplier_asymptotic_proof

/-- Left-edge upper-extension specialization marker.

This is the consumer name for the concrete orientation where
`Theta/Lambda -> p`, hence the endpoint-row multiplier limit is `exp(-p t)`.
The analytic proof supplies the certificate. -/
structure PO3LeftEdgeUpperExtensionAsymptoticCertificate where
  product : PO3EndpointRowProductAsymptoticCertificate
  alpha_is_integer_row : Prop
  exp_neg_row_limit : Prop
  exp_neg_row_limit_proof : exp_neg_row_limit

theorem po3_left_edge_upper_extension_endpoint_row_asymptotic
    (cert : PO3LeftEdgeUpperExtensionAsymptoticCertificate) :
    cert.exp_neg_row_limit :=
  cert.exp_neg_row_limit_proof

/-- Right-edge later-base lower-truncation specialization marker.

This is the consumer name for the concrete orientation where only bounded
fractions `beta in [0,1]` are available from later-base lower truncation and
the row limit is `exp(+ beta t)`. -/
structure PO3RightEdgeLowerTruncationAsymptoticCertificate where
  product : PO3EndpointRowProductAsymptoticCertificate
  beta_in_unit_interval : Prop
  exp_pos_fractional_row_limit : Prop
  exp_pos_fractional_row_limit_proof : exp_pos_fractional_row_limit

theorem po3_right_edge_lower_truncation_endpoint_row_asymptotic
    (cert : PO3RightEdgeLowerTruncationAsymptoticCertificate) :
    cert.exp_pos_fractional_row_limit :=
  cert.exp_pos_fractional_row_limit_proof

/-- Right-edge lower-truncation obstruction marker.

Later-base lower truncation can remove at most one full long-side logarithmic
slope, so it cannot provide right-edge rows with integer slopes `p > 1`.
The analytic proof should instantiate this certificate when ruling out the
false right-edge integer-row theorem shape. -/
structure PO3RightEdgeLowerTruncationRatioLeOneCertificate where
  lower_truncation_geometry : Prop
  ratio_le_one_asymptotically : Prop
  ratio_le_one_asymptotically_proof : ratio_le_one_asymptotically

theorem po3_right_edge_lower_truncation_ratio_le_one_asymptotically
    (cert : PO3RightEdgeLowerTruncationRatioLeOneCertificate) :
    cert.ratio_le_one_asymptotically :=
  cert.ratio_le_one_asymptotically_proof

/-- Fractional right-edge Vandermonde static certificate.

For the right-edge lower-truncation rows one should take
`beta_j = j / (n - 1)`.  Then the limiting matrix
`exp(beta_j * t_i)` is the ordinary rectangular Vandermonde matrix in
`y_i = exp(t_i / (n - 1))`.  The analytic proof supplies separated fractional
nodes and a uniform nonzero singular gap. -/
structure PO3FractionalVandermondeStableProjectionCertificate
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] where
  V : E →L[ℂ] F
  Proj : E →L[ℂ] E
  C : ℝ
  bounded_packet : Prop
  fractional_exponents : Prop
  fractional_nodes : Prop
  fractional_node_bounds : Prop
  fractional_node_separation : Prop
  row_limit_to_fractional_vandermonde : Prop
  fractional_vandermonde_rank : Prop
  fractional_vandermonde_one_dim_kernel : Prop
  stable_projection : ∀ x : E, ‖x - Proj x‖ ≤ C * ‖V x‖

/-- Consumer for the fractional right-edge Vandermonde branch.

Once the real endpoint rows are certified to converge to the fractional
Vandermonde model and the corresponding stable projection estimate is known,
the generic stable-projection consumer captures the packet vector. -/
theorem po3_endpoint_rows_stable_projection_of_fractional_right_edge_vandermonde
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (cert : PO3FractionalVandermondeStableProjectionCertificate E F)
    (q : E) (ε : F)
    (hrow : cert.V q = ε) :
    ‖q - cert.Proj q‖ ≤ cert.C * ‖ε‖ :=
  po3_variable_comparable_packet_capture_of_stable_projection
    cert.V cert.Proj cert.C cert.stable_projection q ε hrow

/-- Route-kill marker for the bounded-separated right-edge fractional branch.

If the actual fractional nodes `exp(t_i/(n-1))` collapse and no confluent
stable-projection replacement is supplied, the bounded-separated right-edge
capture certificate is unavailable. -/
structure PO3FractionalRightEdgeNodeCollapseRouteKillCertificate where
  fractional_node_collapse : Prop
  no_confluent_replacement : Prop
  bounded_separated_capture_unavailable : Prop
  bounded_separated_capture_unavailable_proof :
    bounded_separated_capture_unavailable

theorem po3_fractional_right_edge_capture_route_kill_of_node_collapse
    (cert : PO3FractionalRightEdgeNodeCollapseRouteKillCertificate) :
    cert.bounded_separated_capture_unavailable :=
  cert.bounded_separated_capture_unavailable_proof

section

variable {𝕜 : Type*} [NormedField 𝕜]

/-- Exact feeder contract for the live `PO3-square.2d3` wall.

The intended future specialization is the transform-side Gamma tower:

- `mainTower` is the signed one-sided main tower on the `A_k` side;
- `dominantPacket` is the extracted top cluster / rightmost packet;
- `remainder` is the surviving lower tail;
- `mirrorTower` is the suppressed mirror-side contribution built from `B_k`. -/
structure PO3SquareDominantPacketCertificate where
  mainTower : ℕ → 𝕜
  dominantPacket : ℕ → 𝕜
  remainder : ℕ → 𝕜
  mirrorTower : ℕ → 𝕜
  split : ∀ k, mainTower k = dominantPacket k + remainder k
  dominant_lower_bound :
    po3_eventually_norm_bounded_below dominantPacket
  remainder_control :
    po3_eventually_dominates_remainder dominantPacket remainder
  mirror_decay :
    po3_norm_tends_to_zero mirrorTower

/-- Direct consumer for the new `PO3-square.2d3` certificate:
once the real Q3-side data certifies a dominant packet, the shell already
produces the exact signed-dominance target needed by `PO3-square.2d2`. -/
theorem po3_square_signed_dominance_target_of_certificate
    (cert : PO3SquareDominantPacketCertificate (𝕜 := 𝕜)) :
    po3_square_signed_dominance_target cert.mainTower cert.mirrorTower := by
  exact
    po3_square_signed_dominance_target_of_dominant_packet
      cert.split
      cert.dominant_lower_bound
      cert.remainder_control
      cert.mirror_decay

/-- Contradiction form of the same feeder:
if the transform-side wall identity still claims `main = mirror`, the
certificate already kills that wall. -/
theorem po3_square_false_of_wall_and_certificate
    (cert : PO3SquareDominantPacketCertificate (𝕜 := 𝕜))
    (hwall : ∀ k, cert.mainTower k = cert.mirrorTower k) :
    False := by
  exact
    po3_square_false_of_wall_and_signed_dominance_target
      hwall
      (po3_square_signed_dominance_target_of_certificate cert)

end

section

variable {ι γ : Type*}

/-- Honest transform-side specialization of the abstract dominant-packet feeder.

This wrapper does not add a lower-bound theorem. It only says:
the future real `PO3-square.2d3` certificate should name the actual transform-
side support/tower data (`Y_a`, `x_γ`, `A_k`, `B_k`) and then prove that this
data fits the already-frozen dominant-packet shell. -/
structure PO3SquareTransformPacketCertificate (ι γ : Type*)
    extends PO3SquareDominantPacketCertificate (𝕜 := ℂ) where
  transform : PO3SquareTransformSideData ι γ
  main_is_Ak : mainTower = transform.Ak
  mirror_is_Bk : mirrorTower = transform.Bk

/-- Direct transform-side consumer:
once the real `A_k/B_k` packet is packaged into the frozen dominant-packet
certificate, the existing shell already returns the exact
`PO3-square.2d2` target. -/
theorem po3_square_signed_dominance_target_of_transform_packet_certificate
    (cert : PO3SquareTransformPacketCertificate ι γ) :
    po3_square_signed_dominance_target cert.transform.Ak cert.transform.Bk := by
  have hbase :
      po3_square_signed_dominance_target cert.mainTower cert.mirrorTower :=
    po3_square_signed_dominance_target_of_certificate
      cert.toPO3SquareDominantPacketCertificate
  simpa [cert.main_is_Ak, cert.mirror_is_Bk] using hbase

/-- Contradiction form of the same transform-side feeder. -/
theorem po3_square_false_of_transform_wall_and_packet_certificate
    (cert : PO3SquareTransformPacketCertificate ι γ)
    (hwall : ∀ k, cert.transform.Ak k = cert.transform.Bk k) :
    False := by
  have hwall' : ∀ k, cert.mainTower k = cert.mirrorTower k := by
    intro k
    simpa [cert.main_is_Ak, cert.mirror_is_Bk] using hwall k
  exact
    po3_square_false_of_wall_and_certificate
      cert.toPO3SquareDominantPacketCertificate
      hwall'

end

end

end Q3.Proofs.PO3Cert
