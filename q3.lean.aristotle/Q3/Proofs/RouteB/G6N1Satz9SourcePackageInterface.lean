import Q3.Proofs.RouteB.G6N1CenterNormalizedUniquenessReceiver

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.0B2B/D — the Satz-9 source package as a typed hole, and the bind

The judge's REQ-2026-08-20-K verdict
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_K_F72_0B2_CENTER_NORMALIZED_SATZ9_SOURCE_BIND_2026-08-20.md`)
selects a private source witness feeding the generic receiver, and lists what
that witness must carry. It also says, in the same paragraph, that an abstract
structure inhabited only by assuming all its fields is **not** a proof of the
floor.

This file therefore does exactly two things and claims exactly nothing more.

1. It writes the required fields down as a structure, so that the remaining
   obligation stops being a sentence and becomes a type. Nothing here inhabits
   it, and the floor `F72_0B2B` stays OPEN. The structure is a *payload*, not a
   firewall — see the corrected note on `Satz9SourceData` below.
2. It proves the bind: **given** such a package and the matching project data,
   the two center-normalized views agree on the closed physical window. That
   composition is unconditional in the package; only the package is missing.

Provenance the eventual inhabitant must carry, per the verdict: Meixner–Schäfke
"Mathieusche Funktionen und Sphäroidfunktionen", Springer 1954, chapter 3
section 3.2, Satz 9, printed page 243, first-kind spheroidal representative
`ps_n^0` of full degree `n = 2j` at parameter `gamma_k^2`; see
`docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md`.

LEDGER:
  CLOSES: [F72_0B2D_SOURCE_BIND_COMPOSITION]
  OPENS:  []   -- the inhabitant is SATZ9_FIXED_MODE_SOURCE_DATA_INHABITANT,
               -- already named as the exact missing identity by the verdict;
               -- this file makes it typed, it does not create it
-/

/-- Receiver payload: the data on one physical window that the uniqueness
receiver consumes.

⚠️ **CORRECTED 2026-08-21.** The first version of this docstring claimed that,
because no field mentions a project object, the structure could not be
inhabited by renaming one of ours. That is false, and the judge refuted it in
the REQ-2026-08-20-L verdict (`e9c1e470`): our own selected mode is even,
regular, has a nonzero centre and solves the same equation, so the term
`{ p := (selectedFerrersPreAnchorPair k).h0, .. }` typechecks perfectly well.

His formulation, recorded verbatim because it is the general lesson:
provenance is a **dependency and statement property**, not something inferred
from field names. A structure cannot enforce where its inhabitant came from.

What enforces it is the shape of the supplying theorem, per his repaired
discriminator `INDEPENDENT_SOURCE_THEOREM_THEN_SEPARATE_EIGENVALUE_CROSSWALK`:
a source-only theorem first supplies the Meixner–Schäfke mode and its own
source eigenvalue at `gamma_k^2`, and only a later theorem proves
`theta_source = theta_project` and feeds this receiver. An existential stated
directly at the project eigenvalue, or one whose proof selects the project
mode, is the kill.

The mathematics below is unaffected — `source_interface_theorems_invalidated:
false` — the bind is and always was conditional on whatever is supplied.

`theta` is carried explicitly rather than derived, because equality of
separation eigenvalues does **not** follow from equality of the parameter:
`theta_equality_is_automatic_from_G: false`. -/
structure Satz9SourceData (lambda theta : ℝ) where
  /-- The raw source function in the physical coordinate. -/
  p : ℝ → ℂ
  /-- Its derivative on the open window. -/
  dp : ℝ → ℂ
  /-- Regularity: differentiable on the open window. -/
  hasDeriv : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt p (dp x) x
  /-- The divergence-form prolate equation at the separation value `theta`. -/
  flux : ∀ x ∈ Ioo (-lambda) lambda,
    HasDerivAt
      (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dp y))
      (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * p x) x
  /-- Parity, which is what makes the centre derivative vanish. -/
  even : Function.Even p
  /-- Nonzero centre, which is what makes the normalization legal. -/
  center_ne : p 0 ≠ 0
  /-- Continuity of the normalized view, needed only to reach the endpoints. -/
  normalized_continuous : Continuous (centerNormalized p)

/-- The matching project-side data on the same window and at the same
separation value.  Stated symmetrically so that neither side is privileged. -/
structure ProjectModeData (lambda theta : ℝ) where
  f : ℝ → ℂ
  df : ℝ → ℂ
  hasDeriv : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt f (df x) x
  flux : ∀ x ∈ Ioo (-lambda) lambda,
    HasDerivAt
      (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * df y))
      (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * f x) x
  even : Function.Even f
  center_ne : f 0 ≠ 0
  normalized_continuous : Continuous (centerNormalized f)

/-- **The source bind.**  On the open window the two center-normalized views
coincide.  No identification of the two functions is assumed anywhere: they
enter through separate packages and meet only in the uniqueness receiver. -/
theorem satz9_source_bind_open
    {lambda theta : ℝ} (hlambda : 0 < lambda)
    (S : Satz9SourceData lambda theta) (P : ProjectModeData lambda theta) :
    EqOn (centerNormalized P.f) (centerNormalized S.p)
      (Ioo (-lambda) lambda) :=
  centerNormalized_eqOn_of_sameProlateODE lambda theta hlambda
    P.f P.df S.p S.dp P.hasDeriv S.hasDeriv P.flux S.flux
    P.even S.even P.center_ne S.center_ne

/-- **The source bind on the closed window**, which is the form floor F72.0B2D
hands downstream: the equality holds at the endpoints too. -/
theorem satz9_source_bind_closed
    {lambda theta : ℝ} (hlambda : 0 < lambda)
    (S : Satz9SourceData lambda theta) (P : ProjectModeData lambda theta) :
    EqOn (centerNormalized P.f) (centerNormalized S.p)
      (Icc (-lambda) lambda) :=
  centerNormalized_eqOn_closed_of_continuousOn lambda hlambda P.f S.p
    (satz9_source_bind_open hlambda S P)
    P.normalized_continuous S.normalized_continuous

/-- The pointwise form: on the closed window the source determines the project
mode up to its own centre value.  This is the shape the rate floors consume,
since dividing by a constant is exactly what the center-anchored scalars of
`G6N1CenterAnchorScalarLock.lean` do. -/
theorem satz9_source_bind_pointwise
    {lambda theta : ℝ} (hlambda : 0 < lambda)
    (S : Satz9SourceData lambda theta) (P : ProjectModeData lambda theta)
    {x : ℝ} (hx : x ∈ Icc (-lambda) lambda) :
    P.f x / P.f 0 = S.p x / S.p 0 :=
  satz9_source_bind_closed hlambda S P hx

#print axioms Satz9SourceData
#print axioms ProjectModeData
#print axioms satz9_source_bind_open
#print axioms satz9_source_bind_closed
#print axioms satz9_source_bind_pointwise

end Q3.RouteB.D0Pstar
