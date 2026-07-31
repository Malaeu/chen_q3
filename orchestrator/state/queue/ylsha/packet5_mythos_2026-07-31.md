PACKET 5 FOR MYTHOS — kill-test of the crosswalk card + 044 bytes + 045 issued
Repo: Malaeu/chen_q3 · rh_clean · HEAD 4a9338a41efa194ac90d7d855cba44bbc9430176
Built: 2026-07-31 by conductor-CLI (Linux). UTF-8, LF.

COVER NOTE (your queue, in your priority order):
(1) ROOF file: CanonicalRHRouteSkeleton.lean IN FULL — contains
    rh_of_canonical_strip_slots, the canonical family and the G-slot signatures.
    This is your FAMILY_CROSSWALK kill-test material (card status CANDIDATE).
(2) 044ANSWER in bytes — closes your CLOSED_PER_RELAY on hRm; on-disk SHA-256
    425d36a0d1d0b2a9ff00304644f8d092285e3979ab913d572a508591815c6ee8.
(3) LEGACY-PROFILE-EXCERPT — Q3/Main.lean documented axiom-profile block for the
    WHY_NOT_LEGACY appendix. A live `#print axioms` run needs a full Q3 build on
    this machine; the documented profile names Q3.Weil_criterion and
    Q3.prime_term_le_at_t_critical_axiom (matches Proshka's ROUTES verdict). If
    the card needs the live run, say so and the conductor schedules the build.
(4) GOAL045 transcribed from your contour + source-lock BONUS: the exported
    Rplus_differentiable concludes GLOBAL Differentiable ℂ (entire), with NO mass
    hypothesis — your P045-2 is pre-supported by the signature itself. Codex
    launch pending owner.

STATUS: hRm DISCHARGED (bytes herein) · 045 READY · WITNESS_CLASS gap at Proshka
as request #1 · crosswalk card awaiting your FAMILY_CROSSWALK verdict on item (1).

VERIFICATION CONTRACT: each payload lies strictly BETWEEN its BEGIN/END marker
lines; payload = source file byte-exact (including repeated trailing newlines).
SHA-256 over exactly those bytes = on-disk SHA.

MANIFEST (label · bytes · sha256):
  ROOF: docs/routeB_bus/CanonicalRHRouteSkeleton.lean · 9326 · 2e849d677e0ec771c47a436abdf657690e833e52555af8c8698185e30274536b
  044ANSWER: docs/routeB_bus/044_muntz_v3_r6_export_hrm_wrapper.answer.md · 10643 · 425d36a0d1d0b2a9ff00304644f8d092285e3979ab913d572a508591815c6ee8
  LEGACY-PROFILE-EXCERPT: Q3/Main.lean lines 30-60 (documented axiom profile) · 1160 · 7e8347e04bcf8ed0c05e802fca73c5985916903f687183a3cae656f96543c39b
  GOAL045: docs/routeB_bus/045_muntz_v3_supplier_hrp.goal.md · 3163 · 90413b99281a29e0bd3fc734b9640b10973113ad0e6d8b4ee4babc717a5eb30c

═══ FILE BEGIN: ROOF: docs/routeB_bus/CanonicalRHRouteSkeleton.lean ═══
import Q3.Proofs.RouteB.ClassicalXiInterface
import Q3.Proofs.RouteB.GenericZeroTransfer
import Q3.Proofs.RouteB.SoftL2Round13Integration

set_option linter.mathlibStandardSet false

open Filter Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.CanonicalRHRoute

/-!
# Fail-closed canonical Route-B roof

This file repairs the quantifiers in the Aristotle draft recovered on 2026-07-22.
There is one fixed approximation family `Pstar`; none of the supply statements
is quantified over an arbitrary family.  `H2aAt` and `S1At` are deliberately
abstract predicates so that the logical roof can typecheck without pretending
that the concrete `(m,N)` instantiation has been proved.

The finite simple/even ground certificate and the real-zero conclusion are
separated by `Theorem510RealZeroBridge`.  In particular, evenness is not used as
a substitute for the determinant/self-adjoint factorization of Theorem 5.10.
-/

/-- The one approximation family selected by the construction. -/
structure ApproximationFamily (Index : Type*) where
  family : Index → ℂ → ℂ

/-- A fixed canonical family together with one parent cofinal path and the
nested extraction which `S2` is allowed to consume. -/
structure CanonicalApproximation (Index : Type*) where
  Pstar : ApproximationFamily Index
  parent : ℕ → Index
  parentCofinal : Prop
  parentCofinalProof : parentCofinal
  extract : ℕ → ℕ
  extractStrictMono : StrictMono extract

/-- The family on the single nested subsequence fixed by the construction. -/
def selectedFamily {Index : Type*} (C : CanonicalApproximation Index) : ℕ → ℂ → ℂ :=
  fun k => C.Pstar.family (C.parent (C.extract k))

/-- Entire holomorphy of the fixed family.  This stronger whole-plane form is
the exact input consumed by the already-checked generic Hurwitz theorem. -/
def SlotH1 {Index : Type*} (C : CanonicalApproximation Index) : Prop :=
  ∀ i, Differentiable ℂ (C.Pstar.family i)

/-- `H2a` lives only on the one parent cofinal path. -/
def SlotH2a {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt : Index → Prop) : Prop :=
  ∀ k, H2aAt (C.parent k)

/-- Anchor normalization for the fixed family. -/
def SlotAnchor {Index : Type*} (C : CanonicalApproximation Index)
    (anchor : ℂ) : Prop :=
  ∀ i, C.Pstar.family i anchor = centeredXi anchor

/-- `S1` is required on the same parent path as `H2a`. -/
def SlotS1 {Index : Type*} (C : CanonicalApproximation Index)
    (S1At : Index → Prop) : Prop :=
  ∀ k, S1At (C.parent k)

/-- Materialize the Round-13 same-subsequence guard from the two parent-path
slots.  The resulting S2 carrier is definitionally
`parent (extract k)`; no independent diagonal can enter. -/
def sameCofinalGuard {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop)
    (hH2a : SlotH2a C H2aAt) (hS1 : SlotS1 C S1At) :
    SoftSameCofinalSubsequence Index H2aAt S1At where
  parent := C.parent
  parentCofinal := C.parentCofinal
  h2aOnParent := hH2a
  s1OnParent := hS1
  extract := C.extract
  extractStrictMono := C.extractStrictMono

@[simp] theorem sameCofinalGuard_s2Sequence
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop)
    (hH2a : SlotH2a C H2aAt) (hS1 : SlotS1 C S1At) :
    (sameCofinalGuard C H2aAt S1At hH2a hS1).s2Sequence =
      fun k => C.parent (C.extract k) := rfl

/-- The centered critical strip is open. -/
theorem isOpen_centeredCriticalStrip : IsOpen centeredCriticalStrip := by
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/-- Output of the Montel-plus-anchor gate on the guarded selected family.
Every analytic and convergence field is restricted to the only domain used by
the RH transfer.  `limitNonzero` is local nontriviality, the exact form needed
by isolated-zero theory on that domain. -/
structure ClusterData {Index : Type*} (C : CanonicalApproximation Index) where
  limit : ℂ → ℂ
  limitHolomorphicOn : DifferentiableOn ℂ limit centeredCriticalStrip
  convergence :
    TendstoLocallyUniformlyOn (selectedFamily C) limit atTop centeredCriticalStrip
  limitNonzero :
    ∀ z ∈ centeredCriticalStrip, ¬ ∀ᶠ w in 𝓝 z, limit w = 0

/-- The exact interface to be proved from `H1 + H2a + ANCHOR + S1`.
It returns a cluster only on the already-fixed nested sequence. -/
def MontelAnchorGate {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop) (anchor : ℂ) : Prop :=
  SlotH1 C → SlotH2a C H2aAt → SlotAnchor C anchor → SlotS1 C S1At →
    Nonempty (ClusterData C)

/-- Full Theorem-5.10 interface.  This is intentionally a separate input:
`H2aAt i` alone does not produce real zeros.  A concrete implementation must
contain the determinant identity, the modified-Hilbert self-adjoint descent,
the complement/lattice factor, and the nonvanishing phase. -/
def Theorem510RealZeroBridge {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt : Index → Prop) : Prop :=
  ∀ i, H2aAt i → Differentiable ℂ (C.Pstar.family i) →
    ZerosRealOn Set.univ (C.Pstar.family i)

/-- `S2` identifies the nonzero cluster produced on the same selected family.
The multiplier is a nonzero scalar times a zero-free gauge on the centered
critical strip. -/
def SlotS2 {Index : Type*} (C : CanonicalApproximation Index) : Prop :=
  ∀ D : ClusterData C,
    ∃ c : ℂ, ∃ gamma : ℂ → ℂ,
      c ≠ 0 ∧
      (∀ z ∈ centeredCriticalStrip, gamma z ≠ 0) ∧
      (∀ z ∈ centeredCriticalStrip,
        D.limit z = c * centeredXi z * gamma z)

/-- The derived H2b statement on the selected sequence. -/
theorem selectedFamily_realZeros
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt : Index → Prop)
    (hH1 : SlotH1 C)
    (hH2a : SlotH2a C H2aAt)
    (h510 : Theorem510RealZeroBridge C H2aAt) :
    ∀ k, ZerosRealOn Set.univ (selectedFamily C k) := by
  intro k
  exact h510 (C.parent (C.extract k)) (hH2a (C.extract k))
    (hH1 (C.parent (C.extract k)))

/-- Conditional roof assembly for the one canonical family.  All analytic
gaps occur as named inputs; the proof itself is hole-free and composes the
checked generic Hurwitz transfer with the classical Xi/RH interface. -/
theorem rh_of_canonical_strip_slots
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop) (anchor : ℂ)
    (hH1 : SlotH1 C)
    (hH2a : SlotH2a C H2aAt)
    (hanchor : SlotAnchor C anchor)
    (hS1 : SlotS1 C S1At)
    (hMontel : MontelAnchorGate C H2aAt S1At anchor)
    (h510 : Theorem510RealZeroBridge C H2aAt)
    (hS2 : SlotS2 C) :
    Q3.RH := by
  obtain ⟨D⟩ := hMontel hH1 hH2a hanchor hS1
  have hselectedZeros : ∀ k, ZerosRealOn Set.univ (selectedFamily C k) :=
    selectedFamily_realZeros C H2aAt hH1 hH2a h510
  have happroach :
      ZerosApproachOn centeredCriticalStrip (selectedFamily C) D.limit :=
    zerosApproachOn_of_tendstoLocallyUniformlyOn_local
      isOpen_centeredCriticalStrip (fun _ hz => hz)
      (fun k => hH1 (C.parent (C.extract k))) D.limitHolomorphicOn
      D.convergence D.limitNonzero
  have hlimitZeros : ZerosRealOn centeredCriticalStrip D.limit :=
    zerosRealOn_of_zerosApproachOn centeredCriticalStrip
      (selectedFamily C) D.limit hselectedZeros happroach
  rcases hS2 D with ⟨c, gamma, hc, hgamma, hidentify⟩
  apply rh_iff_centeredXi_zeros_real.mpr
  intro z hzXi hzstrip
  apply hlimitZeros z hzstrip
  rw [hidentify z hzstrip, hzXi]
  simp

/-- Compatibility name for older conditional consumers.  The implementation
is now strip-local; it does not restore a `Set.univ` convergence hypothesis. -/
theorem rh_of_canonical_slots
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop) (anchor : ℂ)
    (hH1 : SlotH1 C)
    (hH2a : SlotH2a C H2aAt)
    (hanchor : SlotAnchor C anchor)
    (hS1 : SlotS1 C S1At)
    (hMontel : MontelAnchorGate C H2aAt S1At anchor)
    (h510 : Theorem510RealZeroBridge C H2aAt)
    (hS2 : SlotS2 C) :
    Q3.RH :=
  rh_of_canonical_strip_slots C H2aAt S1At anchor hH1 hH2a hanchor hS1
    hMontel h510 hS2

/-! ## Plant: evenness is not the Theorem-5.10 bridge -/

/-- The standard even entire function with nonreal zeros. -/
def evenNonrealZeroPlant (z : ℂ) : ℂ := z ^ 2 + 1

theorem evenNonrealZeroPlant_even :
    ∀ z : ℂ, evenNonrealZeroPlant (-z) = evenNonrealZeroPlant z := by
  intro z
  simp [evenNonrealZeroPlant]

theorem evenNonrealZeroPlant_not_realZeros :
    ¬ ZerosRealOn Set.univ evenNonrealZeroPlant := by
  intro h
  have hI : evenNonrealZeroPlant Complex.I = 0 := by
    simp [evenNonrealZeroPlant, pow_two]
  have := h Complex.I (Set.mem_univ _) hI
  norm_num at this

theorem evenness_alone_does_not_imply_real_zeros :
    (∀ z : ℂ, evenNonrealZeroPlant (-z) = evenNonrealZeroPlant z) ∧
      ¬ ZerosRealOn Set.univ evenNonrealZeroPlant :=
  ⟨evenNonrealZeroPlant_even, evenNonrealZeroPlant_not_realZeros⟩

#check sameCofinalGuard
#check Theorem510RealZeroBridge
#check rh_of_canonical_strip_slots
#check rh_of_canonical_slots

#print axioms sameCofinalGuard_s2Sequence
#print axioms selectedFamily_realZeros
#print axioms rh_of_canonical_strip_slots
#print axioms rh_of_canonical_slots
#print axioms evenness_alone_does_not_imply_real_zeros

end Q3.RouteB.CanonicalRHRoute
═══ FILE END: ROOF: docs/routeB_bus/CanonicalRHRouteSkeleton.lean ═══

═══ FILE BEGIN: 044ANSWER: docs/routeB_bus/044_muntz_v3_r6_export_hrm_wrapper.answer.md ═══
HRM_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES

```yaml
PRIMARY: HRM_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES
PRIMARY_COUNT: 1
SCOPE: ABSTRACT_SUPPLIER_CONSUMPTION
VERIFIER: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID
ARISTOTLE_SUBMISSIONS_THIS_CYCLE: 0
FROZEN_FILES_CHANGED: 0
MUNTZ_R6_FILES_CHANGED: 0
EXPORTED_DEPENDENCY_FILES: 7
EXPORTED_PROOF_BODY_DIFFS: 0

GOAL_VERSION_CONSUMED:
  FILE: 044_muntz_v3_r6_export_hrm_wrapper.goal.md
  SHA256: 425b54615a7cf142105fa1bb060cb2ef5a2c815efcfe5776b8071aedbfcd79a1

TARGET:
  THEOREM: rminus_analyticOnNhd_shiftedHalfPlane
  MATERIALIZED: true
  WRAPPER_LINES: 32
  WRAPPER_SHA256: b91b723b00fa2f1f7e36ace2ba138307e045d48ef159e64665f8379f6d6379b5
  AXIOMS: [propext, Classical.choice, Quot.sound]
  TAINT_MATCHES: 0

HONESTY_INTERFACE:
  NAME: WITNESS_CLASS_VS_R6_HYPOTHESES_GAP
  STATUS: OPEN

GIT:
  CODEX_COMMIT_INVOKED: false
  EXTERNAL_CONDUCTOR_HEAD_ADVANCE: 93bddc77caf1f867f6ac3d82b988de490f5ddb45
```

All theorem claims are `[ABSTRACT][LEAN]`; hashes are `[CONTROL][SHA256]`,
while route, bus, submission, frozen-file, and git fields are
`[CONTROL][LOCAL]`.

## PHASE A — collision-free R6 export

The complete transitive closure is:

```text
TailAnalyticity
  -> WindowAnalyticity
  -> IntegralAnalyticity
  -> ConcreteAnalyticity
  -> PoleSubtracted
  -> Main
  -> RiemannBoundaryCellBridge
  -> Mathlib
```

The first seven local files were exported under module paths
`RequestProject.R6Export.*`. Six R6 files originally in namespace
`EStarMuntzZeroMassContinuation` now live in its nested `R6Export` namespace.
`RiemannBoundaryCellBridge` deliberately remains at root: the byte-preserved
`Main.lean` proof refers to its `_root_.Estar`. `[ABSTRACT][SOURCE_AUDIT]`

| Source / export | Source SHA-256 | Export SHA-256 | Normalized body |
| --- | --- | --- | --- |
| `RiemannBoundaryCellBridge.lean` | `5d324b16934b6bf6da5487f0006d1e0b29389ceb8eb048894c9f3274bcd525a0` | `b0c3a16db5627f4b3fbbc785ac7dc446d84a20975aa19b6296a4c25ccef65ce6` | IDENTICAL |
| `Main.lean` | `58f5f30907c64494416301539414270f64e51864d2b4570ed70bd471446efb92` | `2a4beee999d0613eb2ae0e2ecbf67986ed5c3f4415e2dc1d42e2da979baca29d` | IDENTICAL |
| `PoleSubtracted.lean` | `4b20c3d9b505a40ff7c1472798697e36ce34cd4a716c3a9dbbb76d11181aed8d` | `7daace344032ba7eb130146394a7d23b97c910896901bd3e75367bcba0151eca` | IDENTICAL |
| `ConcreteAnalyticity.lean` | `e660b739969b17fda26845b12f1d5798eac0b27c4e5b452a6e3d1d6cdf4ff3c9` | `6e765f8ea67aabd13e22d2e832a00dd0283dd483f93fa136fbeba3fb07ba9554` | IDENTICAL |
| `IntegralAnalyticity.lean` | `3b547341b44b3d31b2c07f9912e0c904a54502aa6db79db5fde32dfffd243ed3` | `d64d5de884a597785a358d400d04de70246593c75155f4f480963d86369374ce` | IDENTICAL |
| `WindowAnalyticity.lean` | `e427a3d579a03d9369c35eaa042bf3ac18d4429f6799ecf9ca22ebd4fa86ea71` | `ce279d4214569b0767b54e1ae0b8aa63544f7a481c7c04e749b4e4d4c7eb04b9` | IDENTICAL |
| `TailAnalyticity.lean` | `88ba75b8b28df9a6b826f339a002c6e9af6c2263ccc4f79f022b0c2b99b87fc5` | `18d7e0cafb3cae5001367dbe741919e89be3b594ad2040f05fbd2c93ca97507a` | IDENTICAL |

Canonical and mirror export hashes match for all seven rows.
`[CONTROL][SHA256]`

### Exact export diff

Every exported file has exactly this seven-line provenance addition, with
`SOURCE` and `SHA` instantiated by its row above:

```diff
+/-
+Provenance source: SOURCE
+Provenance SHA-256: SHA
+exported verbatim, imports renamed only
+Export date: 2026-07-31
+-/
+
```

`RiemannBoundaryCellBridge.lean` has no other difference.

The complete remaining raw diff is:

```diff
# Main.lean
-import RequestProject.RiemannBoundaryCellBridge
+import RequestProject.R6Export.RiemannBoundaryCellBridge
-namespace EStarMuntzZeroMassContinuation
+namespace EStarMuntzZeroMassContinuation.R6Export
-end EStarMuntzZeroMassContinuation
+end EStarMuntzZeroMassContinuation.R6Export

# PoleSubtracted.lean
-import RequestProject.Main
+import RequestProject.R6Export.Main
-namespace EStarMuntzZeroMassContinuation
+namespace EStarMuntzZeroMassContinuation.R6Export
-end EStarMuntzZeroMassContinuation
+end EStarMuntzZeroMassContinuation.R6Export

# ConcreteAnalyticity.lean
-import RequestProject.PoleSubtracted
+import RequestProject.R6Export.PoleSubtracted
-namespace EStarMuntzZeroMassContinuation
+namespace EStarMuntzZeroMassContinuation.R6Export
-end EStarMuntzZeroMassContinuation
+end EStarMuntzZeroMassContinuation.R6Export

# IntegralAnalyticity.lean
-import RequestProject.ConcreteAnalyticity
+import RequestProject.R6Export.ConcreteAnalyticity
-namespace EStarMuntzZeroMassContinuation
+namespace EStarMuntzZeroMassContinuation.R6Export
-end EStarMuntzZeroMassContinuation
+end EStarMuntzZeroMassContinuation.R6Export

# WindowAnalyticity.lean
-import RequestProject.IntegralAnalyticity
+import RequestProject.R6Export.IntegralAnalyticity
-namespace EStarMuntzZeroMassContinuation
+namespace EStarMuntzZeroMassContinuation.R6Export
-end EStarMuntzZeroMassContinuation
+end EStarMuntzZeroMassContinuation.R6Export

# TailAnalyticity.lean
-import RequestProject.WindowAnalyticity
+import RequestProject.R6Export.WindowAnalyticity
-namespace EStarMuntzZeroMassContinuation
+namespace EStarMuntzZeroMassContinuation.R6Export
-end EStarMuntzZeroMassContinuation
+end EStarMuntzZeroMassContinuation.R6Export
```

After removing the provenance block and reversing only the displayed import
and namespace substitutions, every export compares byte-for-byte equal to its
R6 source. Thus no statement or proof body changed. `[CONTROL][STRUCTURAL_DIFF]`

## PHASE B — thin hRm wrapper

`RequestProject/MuntzV3R6HrmWrapper.lean` proves:

```lean
theorem rminus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane
```

The proof has only three passages:

1. `shiftedHalfPlane_eq_r6HalfPlane` changes `-(1/2)` to `(-1)/2`.
2. `change` uses definitional equality of the byte-identical v3 and exported
   R6 definitions of `Rminus`.
3. `R6Export.Rminus_differentiableOn_halfPlane` is converted with
   `.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)`.

The hypothesis list is exactly R6's list; no consumer weakening or silent
strengthening was introduced. `[ABSTRACT][LEAN]`

## WITNESS_CLASS_VS_R6_HYPOTHESES_GAP

**OPEN.** This goal discharges hRm only under R6 hypotheses. The PL1/PL2 v3
witness class allows support touching zero and provides only
`LipschitzOnWith K h (Ico 0 b)`. It does not supply positive lower support
`0 < a` plus support in `Icc a b`, nor global `LipschitzWith K h`.
No bridge is asserted or repaired here. `[ABSTRACT][OPEN_INTERFACE]`

## Validation ledger

```text
[ABSTRACT][LEAN] lake build RequestProject.R6Export.TailAnalyticity       PASS (8032 jobs)
[ABSTRACT][LEAN] lake env lean RequestProject/MuntzV3R6HrmWrapper.lean   PASS
[ABSTRACT][LEAN] full v3 lake build                                      PASS (8039 jobs)
[ABSTRACT][LEAN] #check wrapper signature                                EXACT R6 INPUT LIST
[ABSTRACT][LEAN] #print axioms wrapper                                   [propext, Classical.choice, Quot.sound]
[CONTROL][TAINT] all new Lean files                                      0 matches
[CONTROL][STRUCTURAL_DIFF] seven normalized exported bodies              IDENTICAL
[CONTROL][MIRROR] canon versus mirror, eight new Lean files               IDENTICAL
[CONTROL][GIT] existing/frozen v3 files changed                           0
[CONTROL][GIT] muntz_r6 files changed                                     0
[CONTROL][LOCAL] Aristotle submissions                                    0
```

## Prediction score

- `P044-C1`: **PARTIAL**. The closure-size prediction misses (`7`, not `≤3`),
  while the wrapper prediction hits (`32 ≤ 40`) and the theorem closes in one
  local Codex session with no new mathematics.
- `P044-C2`: **HIT**. The normalized export diff is import/namespace-only;
  the mandatory provenance headers are the only additional raw lines, and
  every statement/proof body is byte-identical.

## ACTIONS LOG

```text
1.  [CONTROL][GIT] Checked rh_clean and ran git pull --ff-only first.              PASS
2.  [CONTROL][SHA256] Locked both Goal 044 copies at 425b5461...cd79a1.            PASS
3.  [CONTROL][LOCAL] Read Route B state/control/bus protocol; status check.        PASS
4.  [CONTROL][SEARCH] Ran four q3_docs queries and official Lean/API search.       DONE
5.  [ABSTRACT][SOURCE_AUDIT] Enumerated the seven-file R6 closure.                 DONE
6.  [CONTROL][EXPORT] Copied closure into RequestProject.R6Export.* canon+mirror.  DONE
7.  [CONTROL][EXPORT] Added provenance; renamed only imports/namespaces.           DONE
8.  [ABSTRACT][LEAN] Built isolated R6Export TailAnalyticity.                      PASS
9.  [ABSTRACT][LEAN] Added and directly checked the 32-line consumer wrapper.      PASS
10. [ABSTRACT][LEAN] Ran full v3 lake build.                                       PASS
11. [CONTROL][TAINT] Scanned all new Lean files.                                   ZERO
12. [ABSTRACT][LEAN] Audited wrapper theorem type and axioms.                      PASS
13. [CONTROL][STRUCTURAL_DIFF] Audited every source/export pair.                   IDENTICAL
14. [CONTROL][GIT] Verified frozen v3 and both muntz_r6 mirrors untouched.         PASS
15. [CONTROL][MIRROR] Verified canon/mirror byte identity.                         PASS
16. [CONTROL][GIT] Codex invoked no commit; conductor advanced HEAD externally.    RECORDED
17. [CONTROL][STATE] Added one non-promoting success-history row last.             DONE
```

## MYTHOS_PROSHKA_HANDOFF

```text
PRIMARY: HRM_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES
GOAL_SHA256: 425b54615a7cf142105fa1bb060cb2ef5a2c815efcfe5776b8071aedbfcd79a1
EXPORT_NAMESPACE: RequestProject.R6Export.*
DEPENDENCY_CLOSURE: 7 local files
PROOF_BODY_DIFF: zero
WRAPPER: rminus_analyticOnNhd_shiftedHalfPlane
WRAPPER_LINES: 32
R6_INPUTS: 0<a; a≤b; support Icc a b; global LipschitzWith; zero mass; 1≤Λ
LEAN: direct wrapper PASS; full build PASS (8039 jobs)
TAINT: zero
AXIOMS: [propext, Classical.choice, Quot.sound]
OPEN_INTERFACE: WITNESS_CLASS_VS_R6_HYPOTHESES_GAP
ARISTOTLE: no submission
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
NEXT_DECISION: Mythos/Proshka must decide whether to strengthen the witness
class, prove a genuine local-to-global/support-away-zero bridge, or use a
different hRm supplier whose hypotheses match supports touching zero
```

═══ FILE END: 044ANSWER: docs/routeB_bus/044_muntz_v3_r6_export_hrm_wrapper.answer.md ═══

═══ FILE BEGIN: LEGACY-PROFILE-EXCERPT: Q3/Main.lean lines 30-60 (documented axiom profile) ═══
noncomputable section

namespace Q3.Main

/-- Current top-level broad-cone positivity export.

This export reflects the active compiled route and its live axiom profile; it
should not be read as the frozen public RH contract after the target-cone audit
or after the 2026-06-25 Weil-square audit. -/
theorem Q_nonneg_on_Weil_cone :
    ∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0 :=
  Q3.Q_nonneg_on_Weil_cone_current_atom_route

/-- Current top-level RH wrapper for the compiled broad-cone route.

Its present meaning is structural: it records the active route and axiom profile
used by `Q3.Main`, while the scalar closure gate is still unresolved and the
public target cone has already been narrowed in the paper/control-doc layer.
This wrapper must not be used as the corrected Weil-square RH export. -/
theorem RH_of_Weil_and_Q3 : Q3.RH :=
  Q3.RH_of_shifted_atom_route

-- Check what axioms the proof depends on.
#check RH_of_Weil_and_Q3
-- Axiom dependencies (run `#print axioms RH_of_Weil_and_Q3`):
-- Standard: propext, Classical.choice, Quot.sound
-- Tier-1: Q3.Weil_criterion
-- Tier-2 in main theorem: `Q3.prime_term_le_at_t_critical_axiom`

end Q3.Main

═══ FILE END: LEGACY-PROFILE-EXCERPT: Q3/Main.lean lines 30-60 (documented axiom profile) ═══

═══ FILE BEGIN: GOAL045: docs/routeB_bus/045_muntz_v3_supplier_hrp.goal.md ═══
# Goal 045 — MuntzV3 Supplier hRp via R6Export (registered path 043→044 continued)

ISSUED: 2026-07-31, Mythos (contour in dispatch answer; transcribed by conductor-CLI
  on owner's order; source-lock added from R6Export)
MODE: LOCAL_FIRST · NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE
SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen untouched
PARENT: Goal 044 (export closure already contains the supplier theorem).

## Consumer (exact T5 input type, Main.lean:159)

```lean
hRp : AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane
```

## Supplier (source-locked, ALREADY EXPORTED in 044)

RequestProject.R6Export.TailAnalyticity (bus copy:
docs/routeB_bus/muntz_v3/RequestProject/R6Export/TailAnalyticity.lean:16):

```lean
theorem Rplus_differentiable
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Differentiable ℂ (Rplus h Λ)
```

NOTE: conclusion is GLOBAL differentiability (entire) — no mass hypothesis, no
half-plane restriction. P045-2 (no domain bridge needed) is already supported by
the signature; the wrapper passage is Differentiable → AnalyticOnNhd on any set
(name the exact Mathlib lemma, e.g. Differentiable.analyticOnNhd-class API).

## PHASE 0-lite

Confirm the exported signature above compiles as read (it is in the 044 closure);
record the exact Mathlib passage lemma. No inventory diff needed — same objects
as 044 by construction.

## PHASE 1

Wrapper in a NEW file (pattern of MuntzV3R6HrmWrapper.lean):

```lean
theorem rplus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane
```

Hypothesis list = exactly the R6 list (note: NO hmass — do not add it).

## Honesty clause

Same as 044: discharge is UNDER R6 HYPOTHESES; WITNESS_CLASS_VS_R6_HYPOTHESES_GAP
remains OPEN and is restated in the answer (do not repair here).

## Forbidden

frozen files; muntz_r6/; edits inside R6Export/ (it is a sealed certificate);
reproving R6 content; taint; bundling hG/habs; promotion; Aristotle.

## Validation

```text
lake build (v3, includes wrapper)
grep taint on new file
#print axioms rplus_analyticOnNhd_shiftedHalfPlane
axioms exactly [propext, Classical.choice, Quot.sound]
```

## Success code

HRP_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES

## Failure codes (exactly one, fail-closed)

R6_RPLUS_DOMAIN_MISMATCH
LEAN_BUILD_FAIL

## Registered predictions

P045-1 (Mythos): wrapper ≤ 40 lines, zero new analysis.
P045-2 (Mythos): no domain bridge needed (Rplus wider than the half-plane) —
  pre-supported by the entire-conclusion signature.

## Answer requirements

045_muntz_v3_supplier_hrp.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS LOG;
scoring P045-1..2; goal consumed by SHA-256; WITNESS_CLASS gap restated; one
non-promoting state row; ROUTE_B_STATE last; canon+mirror one transaction.
═══ FILE END: GOAL045: docs/routeB_bus/045_muntz_v3_supplier_hrp.goal.md ═══

