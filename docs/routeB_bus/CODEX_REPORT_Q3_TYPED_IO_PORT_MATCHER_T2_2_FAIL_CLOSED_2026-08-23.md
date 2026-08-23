# REPORT — Q3_TYPED_IO_PORT_MATCHER_T2_2_FAIL_CLOSED

DATE: 2026-08-23
EXECUTOR: Claude (Linux body)
GRANT: owner goal-scoped grant given in chat ("Go", 2026-08-23), as required by
`OWNER_GOAL_SCOPED_GRANT_REQUIRED: true` of the killing verdict
ANSWERS: `PROSHKA_VERDICT_T2_1_DURABLE_PORT_MATCHER_FAIL_CLOSED_AUDIT_2026-08-23.md`
(commit `7a92845ecbb29aa556a6c2dd0ae61b47b5210207`)
TASK_ID: Q3_TYPED_IO_PORT_MATCHER_T2_2_FAIL_CLOSED

BASE_HEAD (pasted verbatim from `git rev-parse HEAD` before commit):
775fc9cb3b3fef789e4acf3a35e20fd13f9e285e

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
LIVE_ROUTE_MUTATION: false
LEAN_SOURCE_EDIT: false

## 0. The four kills, reproduced against the source before repairing

The verdict's own "next cheapest decisive test" was run first, against the
T2.1 matcher as committed. All four attacks landed exactly as the judge
predicted. This is recorded because a repair report that only shows the
repaired state is the same failure mode as T2.1.

| Plant | Expected | T2.1 actually returned |
|---|---|---|
| P7 missing metadata | `UNVERIFIED` | `EXACT_MATCH` |
| P8 missing trust | `UNVERIFIED` | `EXACT_MATCH` |
| P9 fabricated adapter row | `UNVERIFIED` | `EXPLICIT_ADAPTER_MATCH` |
| P10 a.e. function offered as `Lp` | `ADAPTER_REQUIRED` | `EXACT_MATCH` |

`receipt()` as committed returned the fields `RECEIPT, schema_sha256,
matcher_sha256, tests_sha256, fixture_manifest, replay_command` — the
mandatory `toolchain` and `results` of `RECEIPT_V1` were absent. The T2.1
claim `T2_PORT_MATCHER_RECEIPT_V1_COMPLETE` was therefore stronger than the
artefact, exactly as judged.

## 1. What was changed

WRITE list respected exactly; no Lean source touched, no live route mutated.

- `docs/cartographer/typed_io_schema_v1_2.yaml` (new)
- `docs/cartographer/comparator/port_matcher.py` (repaired)
- `docs/cartographer/comparator/test_port_matcher.py` (repaired)
- `docs/cartographer/comparator/fixtures/{adapter_registry,adaptable_pairs,plants}.json`
- this report

The T2.1 prototype, its schema `v1.1` and its report are preserved unchanged,
as the verdict directed.

### 1.1 Schema validation before matching

`validate_port` runs before any gate. `REQUIRED_PORT_FIELDS` is
`{provider: [kernel_type, source_family, trust], consumer: [kernel_type,
source_family, trust_floor]}`. A missing or empty required field returns
`UNVERIFIED`.

The floor is deliberately minimal. A wider required set would reject the
frozen P1–P6 / NC / C2 corpus, and the verdict mandates
`false_rejection = 0` on it. The choice is stated in the schema rather than
hidden in code.

### 1.2 No permissive trust default

`provider.get("trust", "LEAN")` is gone. Both `trust` and `trust_floor` are
required fields, and an unrecognized token (`"TRUSTED"`) is `UNVERIFIED`
rather than a match. Silence is no longer Lean evidence.

### 1.3 Adapter evidence is validated before use

`validate_adapter` checks every field of `ADAPTER_SPEC_V1_2`: the twelve
required record fields, the six required `EVIDENCE` fields, `VERIFIER` at or
above the proof-edge floor, a known `DIRECTION`, a known `SCOPE`, list-typed
`PRESERVES`/`DROPS` and a map-typed `SHARED_PARAMETER_CONTEXT`.

`_find_adapter` reports a malformed candidate rather than skipping it, so a
fabricated row cannot be silently replaced by a lawful row further down the
registry. That escape was checked explicitly (attack A9 below).

New field `REQUIRED_INPUT`: an adapter that consumes a construction witness
declares it, and a provider that does not carry the witness cannot use the
row.

### 1.4 The a.e. / `Lp` conflation is repaired at the root

The v1.1 order `[pointwise, ae-representative, Lp-class]` made `Lp-class` the
weakest level, so any a.e. function silently became an `Lp` element. In Lean
an `Lp` element is not a function: it is built by `MemLp.toLp` from a `MemLp`
proof.

v1.2 replaces the linear order with a declared transition table separating
`WEAKENING` (data is forgotten, free) from `CONSTRUCTION` (a witness is
required) and `FORBIDDEN` (`REFINEMENT_LOSS`). An undeclared transition is
`UNVERIFIED`, not a pass.

The killed row `A_AE_TO_LP_CLASS` is removed. Three evidence-bearing rows
replace it, each carrying its `#check` output pasted verbatim from
`lake env lean` against the pin:

- `A_MEMLP_TO_LP` — `MeasureTheory.MemLp.toLp`, `REQUIRED_INPUT: MemLp`;
- `A_LP_EXT_EQUALITY` — `MeasureTheory.Lp.ext`, which proves equality of two
  **already existing** `Lp` elements from an a.e. equality (the direction
  T2.1 had backwards);
- `A_LP_TO_AE_COEFN` — `MeasureTheory.MemLp.coeFn_toLp`, the lawful weakening
  back to an a.e. representative.

### 1.5 Receipt is schema-complete

`receipt()` now carries `toolchain` (read from disk: `lean-toolchain` plus
the mathlib rev out of `lake-manifest.json`) and `results` (the frozen plant
outcomes, passed in by the replay suite). The replay suite fails the run if
any mandatory field is empty.

The receipt is printed, never written beside the sources: a receipt file
inside the hashed tree would hash itself and stop being reproducible.

## 2. Replay — 16/16

```
P1  HARD_MISMATCH          PASS      P7   UNVERIFIED             PASS
P2  HARD_MISMATCH          PASS      P8   UNVERIFIED             PASS
P3  ADAPTER_REQUIRED       PASS      P9   UNVERIFIED             PASS
P4  REFINEMENT_LOSS        PASS      P10  ADAPTER_REQUIRED       PASS
P5  HARD_MISMATCH          PASS      NC4  EXPLICIT_ADAPTER_MATCH PASS
P6  REFINEMENT_LOSS        PASS      NC5  EXPLICIT_ADAPTER_MATCH PASS
NC1 EXPLICIT_ADAPTER_MATCH PASS      C2      HARD_MISMATCH       PASS
NC2 EXACT_MATCH            PASS      C2_POS  EXACT_MATCH         PASS

FAILURES=0  WRONG_OBJECT_ESCAPE=0  FALSE_REJECTION=0
```

`NC3` is removed as mandated: it asserted `ae-representative -> Lp-class =
EXACT_MATCH`, an instance of C04/C10. `NC4` (`MemLp -> Lp` construction) and
`NC5` (`Lp.ext` equality) replace it. All other frozen outcomes are
unchanged.

## 3. Self-directed counterexample hunt

Passing one's own fixtures is what T2.1 did before being killed. Ten further
attacks were written against the repair, none of them in the mandate. All
ten fail closed:

| Attack | Result |
|---|---|
| A1 empty string in a required field | `UNVERIFIED` |
| A2 `PAPER` provider against a `LEAN` floor | `HARD_MISMATCH` |
| A3 adapter with real evidence but `VERIFIER: PAPER` | `UNVERIFIED` |
| A4 adapter evidence missing `source_line` | `UNVERIFIED` |
| A5 `MemLp-witness` port not carrying the witness | `UNVERIFIED` |
| A6 hyperedge containing one unvalidatable port | `UNVERIFIED` |
| A7 undeclared transition `Lp-class -> pointwise` | `UNVERIFIED` |
| A8 empty `kernel_type` | `UNVERIFIED` |
| A9 fabricated row placed **before** the lawful row | `UNVERIFIED` |
| A10 unknown `trust_floor` token | `UNVERIFIED` |

## 4. Receipt (T2_PORT_MATCHER_RECEIPT_V1, complete)

```
schema_sha256   21c41fc8dab330201e803860e4fca908f38e178341cc3504658c768c23559750
matcher_sha256  acc4295749484271cc2f3686366801a3ce1330a30de39579536ab21bcff6d28e
tests_sha256    ae57a1f89b785b6ce651e968c72e298915ddfffc62b34177cc6902e5e11a4565
fixture_manifest
  adaptable_pairs.json   aa571c071b0706e93d51571bf87e30ba329ddfb3e7e90fee9f3387aa878cd69f
  adapter_registry.json  9bfaa08f648eeb922d2b508e7f9ea6eda6b6f7c517bce71870b33d45e27b8d50
  plants.json            0dda3772207e6618790e6696230f6c9cf1017f96634560d688a2b4ed4aec0be0
toolchain
  lean_toolchain  leanprover/lean4:v4.26.0
  mathlib_rev     2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
results          16 plants, all PASS (section 2)
replay_command   python3 docs/cartographer/comparator/test_port_matcher.py
```

The `schema_sha256`, `matcher_sha256` and `tests_sha256` values above are the
hashes at the time of this run; they change with any later edit, which is the
point of content addressing.

## 5. Ledger

```
CLOSES:
  T2_2_FAIL_CLOSED_SCHEMA_EVIDENCE_GATE
  T2_1_MISSING_METADATA_DEFAULTS_TO_EXACT_AND_LEAN
  T2_1_ADAPTER_EVIDENCE_NOT_VALIDATED
  T2_1_AE_REPRESENTATIVE_TO_LP_CLASS_FALSE_EXACT_MATCH
  T2_1_RECEIPT_SCHEMA_NONCONFORMANCE

OPENS:
  none
```

No new supplier, tool or input is requested by this repair.

## 6. What I am NOT claiming

The narrow claim is: the matcher now fails closed on the sixteen frozen
plants and on ten self-authored attacks, and its positive labels require
validated evidence.

The stronger claim — that every possible wrong-object composition is now
impossible — is not made. The plant corpus is finite. Cheap next attacks a
reviewer may want: adapter chains of length > 1 (currently each key is
matched independently, and no cross-key chain coherence is checked), scope
interaction between chained adapters, and `context` preservation claimed by
`SHARED_PARAMETER_CONTEXT` but never verified against the actual binding.

That last one is a real remaining hole and is named here rather than left for
the next audit to find: `SHARED_PARAMETER_CONTEXT` is validated for **shape**
(it must be a map), not for **agreement** with the edge's substitution
environment.

## 7. Requested next node

Per the verdict, `NEXT_IF_PASS: T3_TYPED_GAP_SIGNATURE_IN_CHEAP`.

I do not start T3. The judge holds `T3` and the forbidden move stands: do not
rank routes before positive edge labels are proof-grade. Whether section 6's
named hole must close first is the judge's call, not mine.
