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

