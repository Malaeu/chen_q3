# REPORT 2026-08-24 — repair the default `q3_check.sh` gate

```yaml
TASK_ID: 2026-08-23-q3-check-default-gate-repair
BASE_HEAD: 2fbd66907fe00fb2aee9517ec0607bfed57bd0a2
SELECTED_OPTION: A_DEFAULT_BUILDS_PROTECTED_TARGETS_FIRST
CLOSES:
  - Q3_CHECK_DEFAULT_TARGETS_MISSING_OLEAN_CLASS
OPENS: []
```

## Decision

Option A was selected. In default mode, `scripts/q3_check.sh` converts the
three protected Lean source paths to module names, builds those exact modules
in one `lake build` invocation, and only then runs the existing direct Lean,
hole-marker, and new-axiom checks on each source file.

Option B was rejected because the task supplied no evidence that the three PSD
targets had stopped being the protected set. Replacing them would make the gate
green by changing its subject.

Option C was rejected because adding the targets to `Q3.lean` would enlarge the
root import graph solely to repair a tool-ordering defect. The protected modules
can be built honestly without changing the mathematical root.

## Positive gates

### 1. Repaired default

Command:

```bash
./scripts/q3_check.sh ; echo "EXIT=$?"
```

Verbatim decisive output after the normal Lean linter replay:

```text
Build completed successfully (7782 jobs).
lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
scan Q3/Proofs/PSD_CenteredCardinalBSpline.lean
lean Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
scan Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
lean Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean
scan Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean
q3_check ok
EXIT=0
```

Full captured output SHA-256:
`9fa7dddd51fa57a48e05cb24ccabed8cab027e43579e66daae44f3cb4eb7d41e`.

### 2. Explicit target mode

Command:

```bash
./scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean ; echo "EXIT=$?"
```

Verbatim decisive output:

```text
scan Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean
q3_check ok
EXIT=0
```

Full captured output SHA-256:
`5aa0c3b1fbcf921e4cd70bc409fefba3c3e94ddbab56c3ca777a7f12814d2f13`.

### 3. Full build

Command:

```bash
cd q3.lean.aristotle && lake build ; echo "EXIT=$?"
```

Verbatim decisive output after the normal Lean linter replay:

```text
ℹ [7815/7817] Replayed Q3.Main
info: Q3/Main.lean:53:0: Q3.Main.RH_of_Weil_and_Q3 : RH
Build completed successfully (7817 jobs).
EXIT=0
```

Full captured output SHA-256:
`b1e890b828d23fe6460a2e2c5edece797cd181092dbb881519ec3063bdddb122`.

## Negative control

The following declaration was inserted temporarily after the imports in the
first protected source and removed immediately after the gate rejected it:

```lean
def q3CheckNegativeControl : Nat := missingNegativeControlIdentifier
```

Command:

```bash
./scripts/q3_check.sh ; echo "EXIT=$?"
```

Verbatim failure:

```text
✖ [7765/7782] Building Q3.Proofs.PSD_CenteredCardinalBSpline (73s)
error: Q3/Proofs/PSD_CenteredCardinalBSpline.lean:10:36: Unknown identifier `missingNegativeControlIdentifier`
error: Lean exited with code 1
error: build failed
Some required targets logged failures:
- Q3.Proofs.PSD_CenteredCardinalBSpline
EXIT=1
```

After restoration, `git diff --exit-code --
q3.lean.aristotle/Q3/Proofs/PSD_CenteredCardinalBSpline.lean` returned exit 0,
and the repaired default gate passed again.

## Boundary echo

```text
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
ARISTOTLE: false
```
