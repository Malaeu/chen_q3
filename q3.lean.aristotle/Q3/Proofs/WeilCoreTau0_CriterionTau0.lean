import Q3.Proofs.WeilCoreTau0_ExplicitFormulaTau0

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.Proofs.WeilCoreTau0

/-!
Layer 3 (Criterion): exported τ=0 criterion used by `Q3.Main`.

This layer is decomposed into two obligations:
- `RH → NonnegOn` on the τ=0 test class,
- `Tau0Separation` (off-line zero gives a negative τ=0 test witness).

The exported interface stays fixed; we can replace temporary routes
incrementally without touching mainline wiring.
-/

/-- Analytic separation obligation for the τ=0 class. -/
def Tau0Separation (t0 B_min B_max : ℝ) : Prop :=
  ∀ _hNotRH : ¬ Q3.RH,
    ∃ Φ, Φ ∈ TestClass t0 B_min B_max ∧ Q3.Q Φ < 0

/-- Bridge obligation: lift a negative witness from global Weil cone to τ=0 test class. -/
def Tau0WitnessBridge (t0 B_min B_max : ℝ) : Prop :=
  ∀ Φ, Φ ∈ Q3.Weil_cone → Q3.Q Φ < 0 →
    ∃ Ψ, Ψ ∈ TestClass t0 B_min B_max ∧ Q3.Q Ψ < 0

/-- Quantitative bridge obligation: approximate a negative global witness in Q-value
by a τ=0 test witness with strict half-margin. -/
def Tau0QApproxBridge (t0 B_min B_max : ℝ) : Prop :=
  ∀ Φ, Φ ∈ Q3.Weil_cone → Q3.Q Φ < 0 →
    ∃ Ψ, Ψ ∈ TestClass t0 B_min B_max ∧
      |Q3.Q Ψ - Q3.Q Φ| < (-Q3.Q Φ) / 2

/-- Lower window floor used by τ=0 compact-approx routes. -/
def Kfloor (B_min : ℝ) : ℝ := max 1 B_min

/-- Safe compact window: enlarges any `K` to satisfy the floor `Kfloor B_min`. -/
def Ksafe (B_min K : ℝ) : ℝ := max (Kfloor B_min) K

lemma one_le_Kfloor (B_min : ℝ) : (1 : ℝ) ≤ Kfloor B_min := by
  exact le_max_left 1 B_min

lemma Bmin_le_Kfloor (B_min : ℝ) : B_min ≤ Kfloor B_min := by
  exact le_max_right 1 B_min

lemma le_Ksafe (B_min K : ℝ) : K ≤ Ksafe B_min K := by
  exact le_max_right (Kfloor B_min) K

lemma Kfloor_le_Ksafe (B_min K : ℝ) : Kfloor B_min ≤ Ksafe B_min K := by
  exact le_max_left (Kfloor B_min) K

/-- Monotonicity of `W_K`: enlarging the window preserves membership. -/
lemma W_K_mono {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) :
    Q3.W_K K₁ ⊆ Q3.W_K K₂ := by
  intro Φ hΦ
  rcases hΦ with ⟨hCont, hSupp, hEven, hNonneg⟩
  refine ⟨hCont, ?_, hEven, hNonneg⟩
  intro x hx
  have hx' := hSupp hx
  refine ⟨?_, ?_⟩
  · exact lt_of_le_of_lt (neg_le_neg hK) hx'.1
  · exact lt_of_lt_of_le hx'.2 hK

/-- Global compact-support reduction used by the quantitative bridge route. -/
def GlobalWeilToWK : Prop :=
  ∀ Φ, Φ ∈ Q3.Weil_cone → ∃ K, K ≥ 1 ∧ Φ ∈ Q3.W_K K

/-- `GlobalWeilToWK` is provable from compact support: every global Weil test
function belongs to `W_K` for some `K ≥ 1`. -/
theorem globalWeilToWK_thm : GlobalWeilToWK := by
  intro Φ hΦ
  rcases hΦ with ⟨hEven, hNonneg, hCompact, hCont⟩
  rcases (hCompact.isCompact.isBounded.subset_closedBall (0 : ℝ)) with ⟨R, hBall⟩
  refine ⟨max 1 (R + 1), le_max_left _ _, ?_⟩
  refine ⟨hCont, ?_, hEven, hNonneg⟩
  intro x hx
  have hxT : x ∈ tsupport Φ := subset_tsupport Φ hx
  have hxBall : x ∈ Metric.closedBall (0 : ℝ) R := hBall hxT
  have hxAbs : |x| ≤ R := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hxBall
  have hRltK : R < max 1 (R + 1) := by
    have hRlt : R < R + 1 := by linarith
    exact lt_of_lt_of_le hRlt (le_max_right 1 (R + 1))
  have hxLtK : x < max 1 (R + 1) := by
    exact lt_of_le_of_lt (abs_le.mp hxAbs).2 hRltK
  have hxGtNegK : -(max 1 (R + 1)) < x := by
    have hNeg : -(max 1 (R + 1)) < -R := by linarith
    exact lt_of_lt_of_le hNeg (abs_le.mp hxAbs).1
  exact ⟨hxGtNegK, hxLtK⟩

/-- Compact approximation on fixed `W_K` windows above the safe floor. -/
def Tau0CompactApproxOnWK (t0 B_min B_max : ℝ) : Prop :=
  ∀ K, K ≥ Kfloor B_min → ∀ Φ, Φ ∈ Q3.W_K K → ∀ ε > 0,
    ∃ Ψ, Ψ ∈ TestClass t0 B_min B_max ∧ Ψ ∈ Q3.W_K K ∧
      sSup {|Φ x - Ψ x| | x ∈ Set.Icc (-K) K} < ε

/-- Monotonicity of `BaseAtomCone_K_brange` with respect to the window size:
only the terminal `W_K` membership depends on `K`. -/
lemma BaseAtomCone_K_brange_mono
    (t0 B_min B_max K₁ K₂ : ℝ)
    (hK : K₁ ≤ K₂) :
    Q3.BaseAtomCone_K_brange K₁ t0 B_min B_max ⊆
      Q3.BaseAtomCone_K_brange K₂ t0 B_min B_max := by
  intro g hg
  rcases hg with ⟨n, c, B, hc, hBmin, hBmax, hg_sum, hgWK₁⟩
  refine ⟨n, c, B, hc, hBmin, hBmax, hg_sum, ?_⟩
  exact (W_K_mono hK) hgWK₁

/-- Any brange atom-cone witness on a safe compact window is a τ=0 test-class
function (`Weil_cone_tau0`). -/
lemma baseAtomCone_brange_subset_testClass
    (t0 B_min B_max K : ℝ)
    (hK : K ≥ Kfloor B_min) :
    Q3.BaseAtomCone_K_brange K t0 B_min B_max ⊆
      TestClass t0 B_min B_max := by
  intro g hg
  refine ⟨K, ?_, ?_⟩
  · exact le_trans (one_le_Kfloor B_min) hK
  · refine ⟨?_, ?_⟩
    · rcases hg with ⟨_, _, _, _, _, _, _, hgWK⟩
      exact hgWK
    · intro ε hε
      refine ⟨g, hg, ?_⟩
      have hK_nonneg : 0 ≤ K := by
        have hKge1 : (1 : ℝ) ≤ K := le_trans (one_le_Kfloor B_min) hK
        linarith
      have h0_mem : (0 : ℝ) ∈ Set.Icc (-K) K := by
        exact ⟨by linarith, by linarith⟩
      have hzeroSet :
          {|g x - g x| | x ∈ Set.Icc (-K) K} = ({0} : Set ℝ) := by
        ext y
        constructor
        · intro hy
          rcases hy with ⟨x, hx, hyx⟩
          simpa [eq_comm] using hyx
        · intro hy
          rcases hy with rfl
          exact ⟨0, h0_mem, by simp⟩
      rw [hzeroSet]
      simpa using hε

/-- Unpack lemma: on any safe compact window, τ=0 class membership already
provides ε-approximation by brange atom-cone witnesses. -/
theorem wk_tau0_exists_atomcone_approx
    (t0 B_min B_max K : ℝ)
    (_hK : K ≥ Kfloor B_min)
    (Φ : ℝ → ℝ)
    (hΦ : Φ ∈ Q3.W_K_tau0 K t0 B_min B_max)
    (ε : ℝ) (hε : ε > 0) :
    ∃ g, g ∈ Q3.BaseAtomCone_K_brange K t0 B_min B_max ∧
      sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε := by
  exact hΦ.2 ε hε

/-- The τ=0 compact approximation adapter obtained by unpacking `W_K_tau0`
and embedding brange atom-cone witnesses into `TestClass`. -/
theorem tau0_compact_approx_on_WK_tau0
    (t0 B_min B_max : ℝ) :
    ∀ K, K ≥ Kfloor B_min → ∀ Φ, Φ ∈ Q3.W_K_tau0 K t0 B_min B_max → ∀ ε > 0,
      ∃ Ψ, Ψ ∈ TestClass t0 B_min B_max ∧ Ψ ∈ Q3.W_K K ∧
        sSup {|Φ x - Ψ x| | x ∈ Set.Icc (-K) K} < ε := by
  intro K hK Φ hΦ ε hε
  rcases wk_tau0_exists_atomcone_approx t0 B_min B_max K hK Φ hΦ ε hε with
    ⟨g, hg, hsup⟩
  refine ⟨g, ?_, ?_, hsup⟩
  · exact baseAtomCone_brange_subset_testClass t0 B_min B_max K hK hg
  · rcases hg with ⟨_, _, _, _, _, _, _, hgWK⟩
    exact hgWK

/-- Generic criterion assembly from two independent obligations. -/
theorem criterion_of_obligations (t0 B_min B_max : ℝ)
    (hNonnegOfRH : Q3.RH → NonnegOn t0 B_min B_max)
    (hSep : Tau0Separation t0 B_min B_max) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  constructor
  · intro hNonneg
    by_contra hNotRH
    rcases hSep hNotRH with ⟨Φ, hΦ, hneg⟩
    have hge : 0 ≤ Q3.Q Φ := hNonneg Φ hΦ
    linarith
  · exact hNonnegOfRH

/-- Turn a quantitative Q-approximation bridge into a witness bridge. -/
theorem tau0_witness_bridge_of_qapprox
    (t0 B_min B_max : ℝ)
    (hApprox : Tau0QApproxBridge t0 B_min B_max) :
    Tau0WitnessBridge t0 B_min B_max := by
  intro Φ hΦ hneg
  rcases hApprox Φ hΦ hneg with ⟨Ψ, hΨ, hclose⟩
  have hlt : Q3.Q Ψ - Q3.Q Φ < (-Q3.Q Φ) / 2 :=
    (abs_sub_lt_iff.mp hclose).1
  have hqψneg : Q3.Q Ψ < 0 := by
    linarith
  exact ⟨Ψ, hΨ, hqψneg⟩

/-- Build the quantitative Q-approximation bridge from compact sup-norm approximation
plus the proven Lipschitz control of `Q` on each `W_K`. -/
theorem tau0_qapprox_of_compact_approx
    (t0 B_min B_max : ℝ)
    (hWK : GlobalWeilToWK)
    (hApproxWK : Tau0CompactApproxOnWK t0 B_min B_max) :
    Tau0QApproxBridge t0 B_min B_max := by
  intro Φ hΦ hneg
  rcases hWK Φ hΦ with ⟨K0, hK0ge1, hΦWK0⟩
  let K : ℝ := Ksafe B_min K0
  have hKgeFloor : K ≥ Kfloor B_min := by
    simpa [K] using Kfloor_le_Ksafe B_min K0
  have hKge1 : K ≥ 1 := by
    exact le_trans (one_le_Kfloor B_min) hKgeFloor
  have hKpos : K > 0 := by linarith
  have hK0leK : K0 ≤ K := by
    simpa [K] using le_Ksafe B_min K0
  have hΦWK : Φ ∈ Q3.W_K K := (W_K_mono hK0leK) hΦWK0
  rcases Q3.Proofs.Q_Lipschitz_on_W_K_thm K hKpos with ⟨L, hLpos, hLip⟩
  let ε : ℝ := ((-Q3.Q Φ) / 2) / (L + 1)
  have hε : ε > 0 := by
    have hhalf : 0 < (-Q3.Q Φ) / 2 := by linarith
    have hden : 0 < L + 1 := by linarith
    exact div_pos hhalf hden
  rcases hApproxWK K hKgeFloor Φ hΦWK ε hε with ⟨Ψ, hΨtest, hΨWK, hsup⟩
  have hAbsLe :
      |Q3.Q Ψ - Q3.Q Φ| ≤ L * sSup {|Ψ x - Φ x| | x ∈ Set.Icc (-K) K} := by
    exact hLip Ψ hΨWK Φ hΦWK
  have hAbsLe' :
      |Q3.Q Ψ - Q3.Q Φ| ≤ L * sSup {|Φ x - Ψ x| | x ∈ Set.Icc (-K) K} := by
    simpa [abs_sub_comm] using hAbsLe
  have hBound : |Q3.Q Ψ - Q3.Q Φ| < (-Q3.Q Φ) / 2 := by
    have hLt1 : L * sSup {|Φ x - Ψ x| | x ∈ Set.Icc (-K) K} < L * ε := by
      exact mul_lt_mul_of_pos_left hsup hLpos
    have hHalfPos : 0 < (-Q3.Q Φ) / 2 := by linarith
    have hFracLtOne : L / (L + 1) < (1 : ℝ) := by
      have hden : 0 < L + 1 := by linarith
      have hnum : L < L + 1 := by linarith
      have hnum' : L < 1 * (L + 1) := by simpa using hnum
      exact (div_lt_iff₀ hden).2 hnum'
    have hLscaled : L * ε < (-Q3.Q Φ) / 2 := by
      have hMulEq : L * ε = (L / (L + 1)) * ((-Q3.Q Φ) / 2) := by
        dsimp [ε]
        ring_nf
      calc
        L * ε = (L / (L + 1)) * ((-Q3.Q Φ) / 2) := hMulEq
        _ < 1 * ((-Q3.Q Φ) / 2) := by
          exact mul_lt_mul_of_pos_right hFracLtOne hHalfPos
        _ = (-Q3.Q Φ) / 2 := by ring
    exact lt_of_le_of_lt hAbsLe' (lt_trans hLt1 hLscaled)
  exact ⟨Ψ, hΨtest, hBound⟩

/-- Globalized quantitative bridge:
derive `Tau0QApproxBridge` from compact approximation using the proved
`globalWeilToWK_thm` (no extra `GlobalWeilToWK` hypothesis required). -/
theorem tau0_qapprox_of_compact_approx_global
    (t0 B_min B_max : ℝ)
    (hApproxWK : Tau0CompactApproxOnWK t0 B_min B_max) :
    Tau0QApproxBridge t0 B_min B_max := by
  exact
    tau0_qapprox_of_compact_approx t0 B_min B_max
      globalWeilToWK_thm hApproxWK

/-- Optional route: derive `RH → NonnegOn` from global Weil criterion. -/
theorem nonneg_of_RH_via_global_weil (t0 B_min B_max : ℝ) :
    Q3.RH → NonnegOn t0 B_min B_max := by
  intro hRH Φ hΦ
  have hGlobal : ∀ Ψ ∈ Q3.Weil_cone, Q3.Q Ψ ≥ 0 :=
    (Q3.Weil_criterion).2 hRH
  exact hGlobal Φ (testClass_subset_weil_cone t0 B_min B_max hΦ)

/-- Build τ=0 separation from global Weil criterion + witness-bridge obligation. -/
theorem tau0_separation_of_global_weil
    (t0 B_min B_max : ℝ)
    (hBridge : Tau0WitnessBridge t0 B_min B_max) :
    Tau0Separation t0 B_min B_max := by
  intro hNotRH
  have hNotGlobalNonneg : ¬ (∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0) := by
    intro hGlobal
    have hRH : Q3.RH := (Q3.Weil_criterion).1 hGlobal
    exact hNotRH hRH
  classical
  rcases not_forall.mp hNotGlobalNonneg with ⟨Φ, hbad⟩
  rcases _root_.not_imp.mp hbad with ⟨hΦ, hnotge⟩
  exact hBridge Φ hΦ (lt_of_not_ge hnotge)

/-- Future-ready criterion route: no direct τ=0 axiom usage, once `hSep` is provided. -/
theorem criterion_of_global_nonneg_and_separation (t0 B_min B_max : ℝ)
    (hSep : Tau0Separation t0 B_min B_max) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact criterion_of_obligations t0 B_min B_max
    (nonneg_of_RH_via_global_weil t0 B_min B_max) hSep

/-- Preferred future route: derive the τ=0 criterion from global Weil criterion
plus a witness bridge from global cone to τ=0 test class. -/
theorem criterion_of_global_weil_and_witness_bridge (t0 B_min B_max : ℝ)
    (hBridge : Tau0WitnessBridge t0 B_min B_max) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact criterion_of_global_nonneg_and_separation t0 B_min B_max
    (tau0_separation_of_global_weil t0 B_min B_max hBridge)

/-- Direct criterion route from the quantitative Q-approximation contract. -/
theorem criterion_of_global_weil_and_qapprox (t0 B_min B_max : ℝ)
    (hApprox : Tau0QApproxBridge t0 B_min B_max) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact criterion_of_global_weil_and_witness_bridge t0 B_min B_max
    (tau0_witness_bridge_of_qapprox t0 B_min B_max hApprox)

/-- Direct criterion route from compact approximation contracts on `W_K`. -/
theorem criterion_of_global_weil_and_compact_approx (t0 B_min B_max : ℝ)
    (hApproxWK : Tau0CompactApproxOnWK t0 B_min B_max) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact criterion_of_global_weil_and_qapprox t0 B_min B_max
    (tau0_qapprox_of_compact_approx_global t0 B_min B_max hApproxWK)

/-- User-facing τ=0 criterion on `Weil_cone_tau0`, derived from the quantitative bridge contract. -/
theorem criterion_on_weil_cone_tau0_of_qapprox (t0 B_min B_max : ℝ)
    (hApprox : Tau0QApproxBridge t0 B_min B_max) :
    (∀ Φ ∈ Q3.Weil_cone_tau0 t0 B_min B_max, Q3.Q Φ ≥ 0) ↔ Q3.RH := by
  simpa [NonnegOn, TestClass] using
    (criterion_of_global_weil_and_qapprox t0 B_min B_max hApprox)

/-- User-facing τ=0 criterion on `Weil_cone_tau0`, derived from compact
approximation on `W_K`. -/
theorem criterion_on_weil_cone_tau0_of_compact_approx (t0 B_min B_max : ℝ)
    (hApproxWK : Tau0CompactApproxOnWK t0 B_min B_max) :
    (∀ Φ ∈ Q3.Weil_cone_tau0 t0 B_min B_max, Q3.Q Φ ≥ 0) ↔ Q3.RH := by
  simpa [NonnegOn, TestClass] using
    (criterion_of_global_weil_and_compact_approx t0 B_min B_max hApproxWK)

/-- Temporary route (current status): `RH → NonnegOn` via τ=0 criterion axiom. -/
theorem nonneg_of_RH_via_tau0_axiom (t0 B_min B_max : ℝ) :
    Q3.RH → NonnegOn t0 B_min B_max := by
  intro hRH Φ hΦ
  have hTau0 : ∀ Ψ ∈ TestClass t0 B_min B_max, Q3.Q Ψ ≥ 0 :=
    (Q3.Weil_criterion_tau0 t0 B_min B_max).2 hRH
  exact hTau0 Φ hΦ

/-- Temporary separation witness route from the τ=0 criterion axiom. -/
theorem tau0_separation_via_axiom (t0 B_min B_max : ℝ) :
    Tau0Separation t0 B_min B_max := by
  intro hNotRH
  have hNotNonneg : ¬ NonnegOn t0 B_min B_max := by
    intro hNonneg
    have hRH : Q3.RH := (Q3.Weil_criterion_tau0 t0 B_min B_max).1 hNonneg
    exact hNotRH hRH
  unfold NonnegOn at hNotNonneg
  classical
  rcases not_forall.mp hNotNonneg with ⟨Φ, hbad⟩
  rcases _root_.not_imp.mp hbad with ⟨hΦ, hnotge⟩
  exact ⟨Φ, hΦ, lt_of_not_ge hnotge⟩

/-- Temporary witness-bridge built from current axiomatic routes. -/
theorem tau0_witness_bridge_via_axiom (t0 B_min B_max : ℝ) :
    Tau0WitnessBridge t0 B_min B_max := by
  intro Φ hΦ hneg
  have hNotRH : ¬ Q3.RH := by
    intro hRH
    have hGlobal : ∀ Ψ ∈ Q3.Weil_cone, Q3.Q Ψ ≥ 0 :=
      (Q3.Weil_criterion).2 hRH
    have hge : 0 ≤ Q3.Q Φ := hGlobal Φ hΦ
    linarith
  exact tau0_separation_via_axiom t0 B_min B_max hNotRH

/-- Same separation route as `tau0_separation_of_global_weil`, with temporary bridge. -/
theorem tau0_separation_via_global_route_with_axiom_bridge (t0 B_min B_max : ℝ) :
    Tau0Separation t0 B_min B_max :=
  tau0_separation_of_global_weil t0 B_min B_max
    (tau0_witness_bridge_via_axiom t0 B_min B_max)

/-- Temporary global-route criterion (still axiom-backed through the bridge). -/
theorem criterion_via_global_route_with_axiom_bridge (t0 B_min B_max : ℝ) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact criterion_of_global_weil_and_witness_bridge t0 B_min B_max
    (tau0_witness_bridge_via_axiom t0 B_min B_max)

/-- τ=0 Weil criterion exported through a stable core interface. -/
theorem criterion (t0 B_min B_max : ℝ) :
    NonnegOn t0 B_min B_max ↔ Q3.RH := by
  exact criterion_of_obligations t0 B_min B_max
    (nonneg_of_RH_via_tau0_axiom t0 B_min B_max)
    (tau0_separation_via_axiom t0 B_min B_max)

end Q3.Proofs.WeilCoreTau0
