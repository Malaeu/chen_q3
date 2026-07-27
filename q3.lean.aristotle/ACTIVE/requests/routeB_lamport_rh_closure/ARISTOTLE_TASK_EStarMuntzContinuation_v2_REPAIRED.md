TASK:
EStarMuntzZeroMassContinuation_Standalone_v2

CONTEXT:
Self-contained Mathlib-only theorem. Prove the zero-mass continuation for the
positive-half source class actually needed by the prolate packet. Do not use
the raw Mathlib value of ζ at 1 as the removable value.

SETUP:
  variables (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b)
  (K : NNReal)
  (hsupp : ∀ v, v ∉ Set.Icc (0:ℝ) b → h v = 0)
  (hlip : LipschitzOnWith K h (Set.Ico (0:ℝ) b))
  (hmass : ∫ v in Set.Ioi (0:ℝ), h v = 0)
  (Λ : ℝ) (hΛ : 1 ≤ Λ)

The assumptions deliberately exclude b from the Lipschitz set. They allow the
source midpoint value h(b)=one-half of the left limit, followed by the zero
extension outside [0,b]. A midpoint value at b changes at most one summand for
a fixed u and does not change any Mellin integral.

DEFINITIONS:
  Estar, Mellin, Gwin, Rminus, Rplus exactly as in v1.

  noncomputable def ZetaMellinReg (w : ℂ) : ℂ :=
    if w = 1 then deriv (Mellin h) 1
    else riemannZeta w * Mellin h w

TARGETS (no sorry/admit):

T1 — right-tail support and holomorphy.
  For u>b, Estar h u=0. Prove Rplus is entire.

T2 — zero-mass Riemann-sum bound.
  ∃ C, ∀ u∈Ioo 0 1, ‖∑' n:ℕ+, h(n*u)‖ ≤ C.
  Use right-endpoint cells inside [0,b] and one terminal boundary cell.
  The interior cells use hlip. The terminal cell is bounded crudely; do not
  assume the zero extension is globally Lipschitz.
  Corollary: ‖Estar h u‖ ≤ C' sqrt(u).

T3 — left-tail holomorphy.
  Rminus is analytic on {s | -1/2 < s.re}, using local domination by
  u^(Re s - 1/2) and the corresponding log factor for the derivative.

T4 — Mellin and the REGULARIZED zeta product.
  (a) Mellin h is analytic on {w | 0 < w.re}; do not claim it is entire.
  (b) Mellin h 1 = 0.
  (c) ZetaMellinReg is analytic on {w | 0 < w.re}.
  (d) For w≠1,
        ZetaMellinReg w = riemannZeta w * Mellin h w.
  At w=1 use riemannZeta_residue_one and the derivative/slope limit for
  Mellin h. The removable value is deriv (Mellin h) 1.

T5 — continued window identity.
  Given
    habs : ∀ s, 1/2 < s.re →
      Gwin s = riemannZeta (s+1/2) * Mellin h (s+1/2)
                 - Rminus s - Rplus s,
  prove for all -1/2 < s.re:
      Gwin s = ZetaMellinReg (s+1/2) - Rminus s - Rplus s.
  Then derive the raw-product corollary under s≠1/2.
  Use AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq on the half-plane.

PL1 — zero mass is load-bearing.
  Give an explicit nonnegative Lipschitz triangular bump supported in [1,2]
  with positive mass. Along u=1/k prove the positive-integer sums grow at
  least c*k, hence Estar grows at least c/sqrt(u).

PL2 — raw ζ·M value at the pole is WRONG in general.
  Let φ(t)=max(1-4|t|,0) and
    h0(v)=φ(v-5/4)-φ(v-9/4).
  Prove h0 is Lipschitz, compactly supported away from 0, and has zero mass,
  but
    deriv (Mellin h0) 1
      = ∫ φ(t)[log(t+5/4)-log(t+9/4)] dt < 0.
  Hence the punctured limit of riemannZeta w * Mellin h0 w at w=1 is nonzero,
  while its raw point value is 0 because Mellin h0 1=0. This plant must fail
  any theorem asserting the raw product is continuous or differentiable at 1.

FORBIDDEN:
- no raw claim that w ↦ riemannZeta w * Mellin h w is differentiable at w=1;
- no global Lipschitz assumption on the zero extension;
- no claim that Mellin h is entire when support reaches 0;
- no axioms, native_decide, sorry, admit;
- Mathlib only; no RH or zeta-zero statements.

VALIDATION:
- lake build;
- #print axioms T1–T5, PL1, PL2 exactly standard axioms;
- grep clean;
- report exact Mathlib APIs for the residue, identity theorem, parametric
  integral, and the derivative/slope extension.

RETURN ONE STATUS:
ESTAR_MUNTZ_CONTINUATION_PROVED
RIEMANN_SUM_BOUNDARY_CELL_GAP
ZETA_REMOVABLE_EXTENSION_GAP
MELLIN_HALFPLANE_ANALYTICITY_GAP
