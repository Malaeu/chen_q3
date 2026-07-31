HRP_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES

```yaml
PRIMARY: HRP_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES
PRIMARY_COUNT: 1
SCOPE: ABSTRACT_SUPPLIER_CONSUMPTION
VERIFIER: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID
ARISTOTLE_SUBMISSIONS_THIS_CYCLE: 0
FROZEN_FILES_CHANGED: 0
R6EXPORT_FILES_CHANGED: 0
MUNTZ_R6_FILES_CHANGED: 0

GOAL_VERSION_CONSUMED:
  FILE: 045_muntz_v3_supplier_hrp.goal.md
  SHA256: 90413b99281a29e0bd3fc734b9640b10973113ad0e6d8b4ee4babc717a5eb30c

TARGET:
  THEOREM: rplus_analyticOnNhd_shiftedHalfPlane
  MATERIALIZED: true
  WRAPPER_LINES: 21
  WRAPPER_SHA256: 49283d50602d5f792b91bf3f84c2c523575d5ba9ace1f9400e69b4cf2062d17e
  HAS_HMASS_HYPOTHESIS: false
  TAINT_MATCHES: 0
  AXIOMS: [propext, Classical.choice, Quot.sound]

HONESTY_INTERFACE:
  NAME: WITNESS_CLASS_VS_R6_HYPOTHESES_GAP
  STATUS: OPEN
```

All theorem claims are `[ABSTRACT][LEAN]`; hashes are `[CONTROL][SHA256]`,
while route, bus, submission, sealed, and frozen-file fields are
`[CONTROL][LOCAL]`.

## PHASE 0-lite

The exported supplier compiles with the exact type:

```lean
R6Export.Rplus_differentiable
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Differentiable ℂ (R6Export.Rplus h Λ)
```

There is no `hmass` input. The conclusion is global differentiability, so no
half-plane equality bridge is needed. `[ABSTRACT][LEAN]`

The exact pinned Mathlib passage is:

```lean
DifferentiableOn.analyticOnNhd
    (hd : DifferentiableOn ℂ f s) (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s
```

The global supplier is first restricted with
`Differentiable.differentiableOn`. The suggested name
`Differentiable.analyticOnNhd` does not exist in the pinned Mathlib.
`[ABSTRACT][LEAN_API]`

## PHASE 1 — thin hRp wrapper

The new file `RequestProject/MuntzV3R6HrpWrapper.lean` proves:

```lean
theorem rplus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane
```

The proof performs only:

1. a definitional `change` from the v3 `Rplus` to the byte-identical exported
   `R6Export.Rplus`;
2. exact consumption of `R6Export.Rplus_differentiable`;
3. `.differentiableOn.analyticOnNhd` with
   `isOpen_lt continuous_const Complex.continuous_re`.

The hypothesis list is exactly R6's list and contains no mass hypothesis.
`[ABSTRACT][LEAN]`

## Sealed-certificate audit

The seven `R6Export/` SHA-256 values remain exactly those registered by
Goal 044:

```text
ConcreteAnalyticity.lean        6e765f8ea67aabd13e22d2e832a00dd0283dd483f93fa136fbeba3fb07ba9554
IntegralAnalyticity.lean        d64d5de884a597785a358d400d04de70246593c75155f4f480963d86369374ce
Main.lean                       2a4beee999d0613eb2ae0e2ecbf67986ed5c3f4415e2dc1d42e2da979baca29d
PoleSubtracted.lean             7daace344032ba7eb130146394a7d23b97c910896901bd3e75367bcba0151eca
RiemannBoundaryCellBridge.lean b0c3a16db5627f4b3fbbc785ac7dc446d84a20975aa19b6296a4c25ccef65ce6
TailAnalyticity.lean            18d7e0cafb3cae5001367dbe741919e89be3b594ad2040f05fbd2c93ca97507a
WindowAnalyticity.lean          ce279d4214569b0767b54e1ae0b8aa63544f7a481c7c04e749b4e4d4c7eb04b9
```

No file in `R6Export/`, either `muntz_r6/` tree, or the frozen v3 source set
was edited. `[CONTROL][GIT_SHA256]`

## WITNESS_CLASS_VS_R6_HYPOTHESES_GAP

**OPEN.** hRp is discharged only under R6 hypotheses. The v3 witness class
allows support touching zero and supplies only
`LipschitzOnWith K h (Ico 0 b)`; it does not supply positive lower support
plus global `LipschitzWith K h`. No bridge is claimed or repaired.
`[ABSTRACT][OPEN_INTERFACE]`

## Validation ledger

```text
[ABSTRACT][LEAN] exported Rplus_differentiable signature                    PASS; no hmass
[ABSTRACT][LEAN] exact Mathlib API                                          DifferentiableOn.analyticOnNhd
[ABSTRACT][LEAN] lake env lean RequestProject/MuntzV3R6HrpWrapper.lean      PASS
[ABSTRACT][LEAN] full v3 lake build                                         PASS (8040 jobs)
[ABSTRACT][LEAN] #check wrapper signature                                   EXACT R6 INPUT LIST
[ABSTRACT][LEAN] #print axioms wrapper                                      [propext, Classical.choice, Quot.sound]
[CONTROL][TAINT] new Lean file                                              0 matches
[CONTROL][SHA256] sealed R6Export hashes                                    UNCHANGED
[CONTROL][MIRROR] canon versus mirror wrapper                               IDENTICAL
[CONTROL][GIT] frozen and muntz_r6 files changed                            0
[CONTROL][LOCAL] Aristotle submissions                                      0
```

## Prediction score

- `P045-1`: **HIT**. The wrapper is 21 lines and uses zero new analysis.
- `P045-2`: **HIT**. The supplier is entire; no half-plane equality/domain
  bridge is used.

## ACTIONS LOG

```text
1.  [CONTROL][GIT] Checked rh_clean and ran git pull --ff-only first.              PASS
2.  [CONTROL][SHA256] Locked both Goal 045 copies at 90413b99...a5eb30c.           PASS
3.  [CONTROL][LOCAL] Read Route B state/control and ran status check.              PASS
4.  [ABSTRACT][LEAN] Confirmed exported supplier signature as read.                PASS
5.  [ABSTRACT][LEAN_API] Rejected nonexistent Differentiable.analyticOnNhd.        DONE
6.  [ABSTRACT][LEAN_API] Confirmed DifferentiableOn.analyticOnNhd exact type.       PASS
7.  [ABSTRACT][LEAN] Added the 21-line wrapper canon+mirror without hmass.          DONE
8.  [ABSTRACT][LEAN] Ran direct wrapper check and full v3 build.                    PASS
9.  [CONTROL][TAINT] Scanned the new Lean file.                                    ZERO
10. [ABSTRACT][LEAN] Audited final theorem signature and axioms.                    PASS
11. [CONTROL][SHA256] Rechecked the sealed R6Export certificate.                   UNCHANGED
12. [CONTROL][GIT] Verified frozen and both muntz_r6 trees untouched.              PASS
13. [CONTROL][MIRROR] Verified canon/mirror wrapper byte identity.                 PASS
14. [CONTROL][LOCAL] Emitted no Aristotle submission or route promotion.           PASS
15. [CONTROL][STATE] Added one non-promoting success-history row last.             DONE
```

## MYTHOS_PROSHKA_HANDOFF

```text
PRIMARY: HRP_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES
GOAL_SHA256: 90413b99281a29e0bd3fc734b9640b10973113ad0e6d8b4ee4babc717a5eb30c
SUPPLIER: R6Export.Rplus_differentiable
SUPPLIER_SCOPE: global Differentiable / entire
PASSAGE: Differentiable.differentiableOn -> DifferentiableOn.analyticOnNhd
DOMAIN_BRIDGE: none
WRAPPER: rplus_analyticOnNhd_shiftedHalfPlane
WRAPPER_LINES: 21
HMASS: absent
R6_INPUTS: 0<a; a≤b; support Icc a b; global LipschitzWith; 1≤Λ
LEAN: direct wrapper PASS; full build PASS (8040 jobs)
TAINT: zero
AXIOMS: [propext, Classical.choice, Quot.sound]
SEALED_R6EXPORT: unchanged
OPEN_INTERFACE: WITNESS_CLASS_VS_R6_HYPOTHESES_GAP
ARISTOTLE: no submission
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
```

