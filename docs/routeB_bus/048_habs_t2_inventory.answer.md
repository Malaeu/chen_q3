HABS_EXPORT_VIABLE

```yaml
PRIMARY: HABS_EXPORT_VIABLE
PRIMARY_COUNT: 1
SCOPE: PHASE_0_READ_ONLY_INVENTORY
BRANCH_EXECUTED: false
LEAN_FILES_CREATED_OR_MODIFIED: 0
ARISTOTLE_SUBMISSIONS_THIS_CYCLE: 0
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID

GOAL_VERSION_CONSUMED:
  FILE: 048_habs_t2_inventory.goal.md
  SHA256: d694edcee28081775d627ceed4f432d7dd0c982c226de962e2e21d5c890fb12c

SOURCE_THEOREM:
  MODULE: Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk
  DECLARATION: windowedMellin_E_star_zeroMass_decomposition_abs
  SOURCE_LINE: 573
  ROOT_FILE_LOC: 730
  DEPENDENCY_FILES_EXCLUDING_ROOT: 12
  DEPENDENCY_LOC_EXCLUDING_ROOT: 1946
  EXPORT_PAYLOAD_FILES_INCLUDING_ROOT: 13
  EXPORT_PAYLOAD_LOC_INCLUDING_ROOT: 2676

IMPORT_AUDIT:
  PULLS_Q3_MAIN: false
  PROJECT_AXIOM_OR_OPAQUE_DECLARATIONS: 0
  WEIL_CRITERION_FAMILY: absent
  PRIME_CERT_FAMILY: absent
  PRIME_TERM_CRITICAL_AXIOM_FAMILY: absent
  LOCKED_SOURCE_AXIOMS: [propext, Classical.choice, Quot.sound]

DEFINITION_BYTE_COMPARE:
  E_STAR_VS_ESTAR: DIFFERENT_BYTES
  MATHLIB_MELLIN_VS_V3_MELLIN: DIFFERENT_BYTES
  SEMANTIC_TRANSPORT: small
```

The file count called “transitive import closure” below excludes the root
module containing the queried declaration.  The complete copy/export payload
includes that root, so both conventions are stated explicitly.

## Transitive Q3 import closure

| Module | LOC | Project axiom/opaque declaration |
| --- | ---: | --- |
| `Q3.Basic.Defs` | 301 | none |
| `Q3.Proofs.RouteB.CanonicalRHRouteSkeleton` | 225 | none |
| `Q3.Proofs.RouteB.ClassicalXiInterface` | 142 | none |
| `Q3.Proofs.RouteB.D0CanonicalApproximation` | 193 | none |
| `Q3.Proofs.RouteB.D0KTrialStage1` | 152 | none |
| `Q3.Proofs.RouteB.D0KTrialStage2` | 68 | none |
| `Q3.Proofs.RouteB.FplusConstantMode` | 69 | none |
| `Q3.Proofs.RouteB.GenericZeroTransfer` | 261 | none |
| `Q3.Proofs.RouteB.Proposition59EntireTransform` | 140 | none |
| `Q3.Proofs.RouteB.RawIntegralRhsCrosswalk` | 217 | none |
| `Q3.Proofs.RouteB.SoftL2Round13Integration` | 114 | none |
| `Q3.Proofs.RouteB.ZeroEscapeLogic` | 64 | none |
| **Dependency total** | **1946** | **12 clean modules** |
| `Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk` (root) | 730 | none |
| **Export-payload total** | **2676** | **13 clean modules** |

The graph is rooted by

```text
EStarWindowedMellinCrosswalk
  -> D0KTrialStage2
  -> D0KTrialStage1
  -> D0CanonicalApproximation
     -> CanonicalRHRouteSkeleton
        -> ClassicalXiInterface -> Q3.Basic.Defs
        -> GenericZeroTransfer -> ZeroEscapeLogic
        -> SoftL2Round13Integration
     -> RawIntegralRhsCrosswalk
        -> FplusConstantMode
        -> Proposition59EntireTransform
```

The root also imports Mathlib's `MellinTransform` and `RiemannZeta`; the
dependency modules add only Mathlib modules.  No node imports `Q3.Main`.
A source scan over all 13 files found zero declarations matching
`^\s*(axiom|opaque)` and zero occurrences of the requested project axiom
families.  The already locked 012 post-audit records the source theorem with
exactly `[propext, Classical.choice, Quot.sound]`.

This is an import-surface result, not a claim that every unrelated theorem in
the dependency files is needed by the proof term.  It is nevertheless the
correct closure that a byte-preserving module export must transport.

## Definition byte comparison

### Starred comb

012 source (`D0KTrialStage2.lean:24-26`):

```lean
def E_star (hTrial_m : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.sqrt u : ℂ) *
    ∑' n : ℕ+, hTrial_m ((n : ℕ) * u)
```

Raw declaration SHA-256:
`b76b04b3b8564150a906359c5406ea5ca40c5a76889db8b62cbbf6b106439b2c`.

v3 (`RequestProject/Main.lean:15-16`):

```lean
noncomputable def Estar (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  Real.sqrt u * ∑' n : ℕ+, h (n * u)
```

Raw declaration SHA-256:
`f9edf555c427c279a669c2922717b87bf9db2faef2859b819af2801f8649f1aa`.

Verdict: **not byte-identical**.  The mathematical bodies differ only by the
declaration name, explicit coercion spelling, binder name, and layout.  A
small unfolding/coercion bridge is expected; Goal 048 does not execute it.

### Mellin transform

012 uses Mathlib `mellin`:

```lean
def mellin (f : ℝ → E) (s : ℂ) : E :=
  ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • f t
```

Raw declaration SHA-256:
`942eec32826b25d9039056f64c094c7fc032d4f1c5f4d37511be8b4dc6ed4908`.

v3 uses:

```lean
noncomputable def Mellin (k : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), k u * (u : ℂ) ^ (s - 1)
```

Raw declaration SHA-256:
`39b42db4ab1ee29ad93b4dc27686c0c7a523fa97610a182e382ddd42d98dee65`.

Verdict: **not byte-identical**.  On complex-valued inputs the bridge is
pointwise scalar-multiplication-to-multiplication plus commutativity.  This
bridge shape is already used by checked v3 files such as
`MuntzV3PL1MassBlowupWitness.lean` and `R6Export/ConcreteAnalyticity.lean`.

The remaining measure-theoretic transport is the window convention:
012's `sourceWindow` is `Icc Λ⁻¹ Λ`, while `Gwin` integrates over
`Ioo Λ⁻¹ Λ`.  Their indicators agree almost everywhere because the two
endpoints form a null finite set.  This is the sole substantive semantic
window bridge; it is not constructed in this PHASE 0 goal.

## Exact source hypotheses and candidate discharges

The theorem takes exactly these explicit hypotheses:

```lean
hlambda : 1 ≤ lambda
hmass   : ZeroPositiveMass h
hp      : 1 < (s + 1 / 2).re
habs    : EStarMellinAbsolute h (s + 1 / 2)
hEconv  : MellinConvergent (E_star h) s
```

| Source obligation | Candidate v3 discharge | Status after PHASE 0 |
| --- | --- | --- |
| `hlambda` | The consumer's `hΛ : 1 ≤ Λ`. | direct |
| `hmass` | The canonical zero-mass input, bridged to `ZeroPositiveMass`. The source proof locks and clears it, so it contributes no absolute-region estimate. | direct but syntactically retained by export |
| `hp` | From the consumer domain assumption `1/2 < s.re` by simplifying the real part. | direct |
| `habs : EStarMellinAbsolute …` | Candidate lemma `eStarMellinAbsolute_of_IccZero_IcoLipschitz`: `hmeas` supplies per-dilate a.e. measurability; the 046 Ico bound plus singleton-null endpoint handles `b`; compact support and `p.re>1` reduce the norm series to a convergent positive-integer Dirichlet series after scaling. | not yet materialized; standard absolute-Fubini wrapper |
| `hEconv : MellinConvergent (E_star h) s` | Candidate lemma `mellinConvergent_Estar_of_zeroMass_IccZero_IcoLipschitz`: near zero use queued `EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz`; for `u>b`, every positive-integer dilation lies outside support, so `E_star h u=0` (T1 tail); measurability uses the same locally finite sum/endpoint firewall as 046. | waits on queued E-star bound plus short assembly |

Thus `MellinConvergent` has exactly the advertised load-bearing split:
E-star control at zero plus tail vanishing.  `EStarMellinAbsolute` is a
separate per-dilate absolute-summability wrapper; it needs no new contour or
continuation input, but it must not be silently identified with the aggregate
E-star bound.

## Verdict rationale

The dependency closure meets the registered 12-module threshold when the
queried root is excluded, pulls neither `Q3.Main` nor a project axiom module,
and the non-byte-identical object definitions have short explicit bridge
shapes already represented in v3.  Therefore a collision-free, provenance-
locked export following the Goal 044 packaging pattern is viable.

This verdict does not execute that export.  The source project is pinned to
Lean 4.26 while v3 is pinned to Lean 4.28, so the subsequent branch goal must
still validate every copied proof body under v3 rather than treating source
compatibility as automatic.

## Prediction score

- `P048-1`: **MISS**. Neither `E_star/Estar` nor `mellin/Mellin` is literally
  byte-identical. Both have small transport shapes.
- `P048-2`: **HIT** under the standard import-closure convention: exactly 12
  dependency files, no `Q3.Main`, and no project axiom-bearing module. The
  copy payload including the root is 13 files.
- `P048-3`: **HIT WITH SYNTACTIC CAVEAT**. The only substantive semantic
  bridge is `Icc` versus `Ioo` modulo the null endpoints; two additional
  definition-transport rewrites are required because P048-1 missed.
- `P048-4`: **PARTIAL HIT**. `MellinConvergent` reduces to the queued E-star
  bound plus T1 tail, but `EStarMellinAbsolute` still requires an explicit
  per-dilate measurability/scaling/Dirichlet-summability wrapper. This is
  standard absolute convergence, not a new continuation theorem.

## ACTIONS LOG

```text
1.  Checked rh_clean and ran git pull --ff-only first.                    PASS
2.  Locked both Goal 048 copies at d694edce...fb12c.                     PASS
3.  Read Route B control/state/bus and ran routeb_status.py --check.      PASS
4.  Parsed the complete transitive Q3 import graph mechanically.          DONE
5.  Counted 12 dependency modules / 1946 LOC; payload 13 / 2676 LOC.      DONE
6.  Scanned the closure for Q3.Main and project axiom families.           CLEAN
7.  Byte-compared the exact E-star and Mellin declaration slices.         DIFFERENT
8.  Mapped every explicit theorem hypothesis to a candidate discharge.    DONE
9.  Ran four q3_docs semantic queries; all timed out without results.      TIMEOUT
10. Checked official Mathlib MellinConvergent/integral_tsum APIs.          DONE
11. Did not construct either transport branch or modify a Lean file.      PASS
12. Did not submit to Aristotle or promote Route B.                       PASS
13. Added one non-promoting state-history row last.                       DONE
```

A fresh diagnostic invocation of the bare Q3 root did not resolve the `Q3`
module prefix under that Lake configuration.  It changed no tracked file and
is not used as evidence for this verdict; the axiom result above comes from
the complete source/import scan and the locked 012 post-audit.

## MYTHOS_PROSHKA_HANDOFF

```text
GOAL: 048 / habs T2 PHASE 0 inventory
GOAL_SHA256: d694edcee28081775d627ceed4f432d7dd0c982c226de962e2e21d5c890fb12c
DEPENDENCY_CLOSURE: 12 files / 1946 LOC (root excluded)
EXPORT_PAYLOAD: 13 files / 2676 LOC (root included)
Q3_MAIN: absent
PROJECT_AXIOM_MODULES: absent
LOCKED_SOURCE_AXIOMS: [propext, Classical.choice, Quot.sound]
E_STAR_VS_ESTAR_BYTES: different; short coercion/unfold bridge
MELLIN_BYTES: different; scalar-mul/commutativity bridge already patterned
WINDOW_BRIDGE: Icc versus Ioo modulo two null endpoints
ESTAR_ABSOLUTE: separate compact-support/scaling/Dirichlet wrapper required
ESTAR_MELLIN_CONVERGENT: queued zero-edge bound + T1 tail + measurability
BRANCH_EXECUTED: none
LEAN_SOURCE_CHANGES: none
ARISTOTLE: no submission
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
```
