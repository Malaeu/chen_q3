LEAN_BUILD_FAIL

```yaml
PRIMARY: LEAN_BUILD_FAIL
PRIMARY_COUNT: 1
PHASE_0_OUTPUT: DOMAIN_BRIDGE_NEEDED
SCOPE: ABSTRACT_SUPPLIER_CONSUMPTION
VERIFIER: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID
ARISTOTLE_SUBMISSIONS_THIS_CYCLE: 0
FROZEN_FILES_CHANGED: 0
R6_PROOF_COPIED_OR_REPROVED: false

GOAL_VERSION_CONSUMED:
  FILE: 043_muntz_v3_supplier_hrm.goal.md
  SHA256: 5531ef30cf15d1372bb3174a421695c8816d7719b0bf1eef06a0afe762c5e786

SUPPLIER:
  THEOREM: Rminus_differentiableOn_halfPlane
  FILE: muntz_r6/RequestProject/TailAnalyticity.lean
  FILE_SHA256: 88ba75b8b28df9a6b826f339a002c6e9af6c2263ccc4f79f022b0c2b99b87fc5
  DIRECT_LEAN: PASS
  LAKE_BUILD: PASS_8032_JOBS
  TAINT_MATCHES: 0
  AXIOMS: [propext, Classical.choice, Quot.sound]

TARGET:
  THEOREM: rminus_analyticOnNhd_shiftedHalfPlane
  MATERIALIZED: false
  FAILURE: REQUESTPROJECT_MAIN_MODULE_COLLISION
```

All mathematical/source inventory claims are `[ABSTRACT][LEAN]` or
`[ABSTRACT][SOURCE_AUDIT]`; hashes are `[CONTROL][SHA256]`, while
route, bus, submission, and frozen-file fields are `[CONTROL][LOCAL]`.

## PHASE 0 — mandatory inventory

1. **Same `Rminus` object: YES.** The R6 and v3 `Estar` plus
   `Rminus` definition blocks are byte-identical. The extracted four-line
   blocks have the same SHA-256
   `470385c431682160760b3f564676a3ce29294f9e036c3a209e7a077b8a540ba7`.
   `[ABSTRACT][SOURCE_AUDIT]`

2. **Same half-plane: propositionally YES, definitionally NO.**
   v3 defines `shiftedHalfPlane` with `-(1/2)`; R6 states `(-1)/2`.
   The required bridge is exactly:

   ```lean
   lemma shiftedHalfPlane_eq_r6HalfPlane :
       shiftedHalfPlane = {s : ℂ | -(1 : ℝ) / 2 < s.re} := by
     ext s
     simp only [shiftedHalfPlane, Set.mem_setOf_eq]
     norm_num
   ```

   This lemma was checked locally. `[ABSTRACT][LEAN]`

3. **`DifferentiableOn → AnalyticOnNhd`: RESOLVED.** The exact Mathlib
   API is `DifferentiableOn.analyticOnNhd`; openness is supplied by
   `isOpen_lt continuous_const Complex.continuous_re`.
   `[ABSTRACT][LEAN]`

4. **Hypothesis inventory: R6 INPUTS MUST BE RETAINED.** The wrapper would
   require exactly `0 < a`, `a ≤ b`, support in `Icc a b`, global
   `LipschitzWith K h`, zero mass on `Ioi 0`, and `1 ≤ Λ`.
   The v3 class used by `MuntzV3Unconditional.lean` only supplies
   `Measurable h`, support in `Icc 0 b`, and
   `LipschitzOnWith K h (Ico 0 b)`; it does not imply positive lower
   support or global Lipschitz continuity. No such implication is claimed.
   `[ABSTRACT][SOURCE_AUDIT]`

The mandatory PHASE 0 output is therefore
`DOMAIN_BRIDGE_NEEDED`, with the exact bridge lemma
`shiftedHalfPlane_eq_r6HalfPlane`. `[CONTROL][LOCAL]`

## PHASE 1 — fail-closed integration result

The domain bridge itself passes Lean, and the harvested R6 supplier separately
passes both direct Lean checking and its 8032-job Lake build.
`[ABSTRACT][LEAN]`

The requested consumption wrapper cannot be made a module of the frozen v3
project without an additional packaging/refactor contract. Both independent
archives export different files under the same Lean import name
`RequestProject.Main`: R6's `TailAnalyticity` transitively imports the R6
`RequestProject.Main`, while the v3 package's
`globs = ["RequestProject.+"]` resolves that name to the v3 file.
`[CONTROL][LEAN_MODULES]`

With the v3 resolver first, the diagnostic wrapper fails exactly with:

```text
object file '.../muntz_v3/.lake/build/lib/lean/RequestProject/TailAnalyticity.olean'
of module RequestProject.TailAnalyticity does not exist
```

With the R6 resolver first, `TailAnalyticity` loads but the v3 declaration
`shiftedHalfPlane` is absent. Thus the two source projects cannot be
co-imported merely from the byte equality of their initial definitions.
`[CONTROL][LEAN_MODULES]`

Per Goal 043's instruction to report rather than repair divergence, no proof
body was copied, no R6 source was reproved, no Lake/package topology was
changed, and no frozen file was touched. The target theorem is therefore not
materialized, and the one exact failure code is `LEAN_BUILD_FAIL`.
`[CONTROL][LOCAL]`

## Validation ledger

```text
[ABSTRACT][LEAN] R6 lake env lean RequestProject/TailAnalyticity.lean     PASS
[ABSTRACT][LEAN] R6 lake build RequestProject.TailAnalyticity             PASS (8032 jobs)
[ABSTRACT][LEAN] R6 supplier taint scan                                   0 matches
[ABSTRACT][LEAN] #print axioms Rminus_differentiableOn_halfPlane          [propext, Classical.choice, Quot.sound]
[ABSTRACT][LEAN] isolated shiftedHalfPlane_eq_r6HalfPlane                 PASS
[CONTROL][LEAN] joint v3/R6 wrapper import                                FAIL (module collision)
[CONTROL][LEAN] v3 baseline lake build                                    PASS (8031 jobs)
[CONTROL][GIT]  frozen source diff                                        0
[CONTROL][LOCAL] Aristotle submissions                                    0
```

## Prediction score

- `P043-M1`: **MISS AT INTEGRATION BOUNDARY**. The mathematical wrapper is
  below 80 lines and needs no new analysis, but it cannot be materialized in
  the v3 package without resolving the duplicate `RequestProject.Main`
  ownership. `[ABSTRACT][LEAN]`
- `P043-M2`: **PARTIAL**. Domain normalization and `Λ` bookkeeping are
  indeed trivial; the dominant friction is the unregistered module/package
  collision. `[CONTROL][LEAN_MODULES]`
- `P043-M3`: **PARTIAL**. The mismatch names itself in one line as
  `REQUESTPROJECT_MAIN_MODULE_COLLISION`, but it is not an `Estar` edge
  bound: the existing R6 bound and theorem compile cleanly.
  `[ABSTRACT][SOURCE_AUDIT]`

## ACTIONS LOG

```text
1. [CONTROL][GIT] Checked rh_clean and ran git pull --ff-only first.             PASS
2. [CONTROL][SHA256] Locked both Goal 043 copies at 5531ef30...c5e786.           PASS
3. [CONTROL][LOCAL] Read Route B execution state/control and ran status check.   PASS
4. [ABSTRACT][SOURCE_AUDIT] Byte-compared Estar/Rminus definitions.              IDENTICAL
5. [ABSTRACT][LEAN] Proved and checked the exact half-plane equality bridge.     PASS
6. [ABSTRACT][LEAN] Located DifferentiableOn.analyticOnNhd and openness API.     PASS
7. [ABSTRACT][SOURCE_AUDIT] Enumerated every R6 supplier hypothesis.              DONE
8. [CONTROL][LOCAL] Ran four q3_docs queries; all timed out.                      RECORDED
9. [ABSTRACT][LEAN] Built and checked the harvested R6 supplier locally.         PASS
10. [CONTROL][LEAN_MODULES] Tested both v3-first and R6-first import resolution.  COLLISION
11. [CONTROL][LOCAL] Removed diagnostic scratch files; retained no failed code.   DONE
12. [CONTROL][GIT] Verified v3 baseline build and frozen files.                   PASS
13. [CONTROL][LOCAL] Emitted no Aristotle submission and no numerical run.        PASS
14. [CONTROL][MIRROR] Wrote canonical and mirror answers together.                DONE
15. [CONTROL][STATE] Added one non-promoting failure-history row last.            DONE
```

## MYTHOS_PROSHKA_HANDOFF

```text
PRIMARY: LEAN_BUILD_FAIL
PHASE_0: DOMAIN_BRIDGE_NEEDED
GOAL_SHA256: 5531ef30cf15d1372bb3174a421695c8816d7719b0bf1eef06a0afe762c5e786
OBJECT_DIFF: Estar and Rminus byte-identical
DOMAIN_DIFF: -(1/2) versus (-1)/2; tested bridge lemma available
ANALYTIC_API: DifferentiableOn.analyticOnNhd
R6_INPUTS: 0<a; a≤b; support Icc a b; global LipschitzWith; zero mass; 1≤Λ
V3_CLASS_BRIDGE: not supplied and not implied
R6_SUPPLIER: direct Lean/build PASS; taint zero; standard axiom triple
BLOCKER: REQUESTPROJECT_MAIN_MODULE_COLLISION
TARGET_THEOREM: not materialized
REPROOF_OR_COPY: none
ARISTOTLE: no submission
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
RECOMMENDED_NEXT_CONTRACT: collision-free R6 export under a unique module name,
or an explicit generic supplier certificate whose public type does not import
either RequestProject.Main; keep Main.lean frozen until that contract is approved
```

