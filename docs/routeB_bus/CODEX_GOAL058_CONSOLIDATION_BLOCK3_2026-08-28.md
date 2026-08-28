# Goal 058 consolidation — Block 3 closeout

```yaml
TASK_ID: GOAL058_CONSOLIDATION_BLOCK3
DATE: 2026-08-28
BODY: CODEX
STATUS: DONE
SOURCE_TASK: docs/Codex/TASK_2026-08-28_goal058_consolidation.md
SOURCE_COMMIT: 56e144c49cae5f8c2dc80a09f6ca963a17dda88d
BASELINE_HEAD: 96654163b83bc223e12e2529785c08392ffee6fe
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
CLOSES:
  - GOAL058_DATABASE_DERIVED_PUBLICATION_BLUEPRINT
  - GOAL058_DEFINITION_FAITHFULNESS_SECTION
  - BLUEPRINT_PUBLICATION_STATUS_FIREWALL
  - BLUEPRINT_DETERMINISTIC_REGENERATION
OPENS:
  - BLUEPRINT_CHECKDECLS_NESTED_PROJECT_INTEGRATION
  - BLUEPRINT_READY_ROWS_WITHOUT_EXACT_DECLARATION_RECEIPTS
  - ROUTEB_OPEN_MATHEMATICAL_ASSEMBLY_ROWS
```

## Result

Block 3 is complete.  One deterministic generator now reads the canonical
`assembly` table, `aristotle_proofs.db`, and the complete Route B EnvDump index,
then publishes one shared model as:

- the Markdown dashboard at `full/blueprint/blueprint.md`;
- the leanblueprint source tree at `q3.lean.aristotle/blueprint/src/`;
- the machine receipt at
  `q3.lean.aristotle/blueprint/blueprint_manifest.json`.

The publication partition on the final inputs is exact:

```text
assembly rows                                      69
GREEN: exact public safe Lean declaration          22
VALIDATION_ONLY                                     3
OPEN_MATH                                          18
READY_WITHOUT_EXACT_DECLARATION_RECEIPT            26
```

The 18 open mathematical rows remain non-green.  The 26 prose/module/composite
`READY` rows remain visibly unresolved as publication receipts.  A validation
record never becomes a theorem.  Open nodes receive `\notready` and no invented
`\lean` name.

## Exact receipt firewall

A row is green only when all of the following agree:

1. `assembly.status = READY`;
2. exactly one `aristotle_proofs.db` row has the supplier name;
3. its registry status is `proven`, its statement is nonempty, and its document
   path matches the assembly supplier module;
4. the complete EnvDump resolves exactly one fully-qualified declaration in
   that module;
5. the source is not newer than EnvDump;
6. the declaration is public and safe;
7. its axiom closure is contained in `propext`, `Classical.choice`, and
   `Quot.sound`.

The proof registry remains metadata and EnvDump remains a kernel-derived index;
neither is represented as independent mathematical proof authority.

Statements are transferred without truncation.  The two generated receipt
views are marked `-whitespace` in `.gitattributes` because three registry
statements contain trailing spaces that must survive the byte-exact transfer.
No source-code whitespace rule is weakened.

## Definitions and honesty boundary

Section 0 records that `Q3.RH` is the classical open-strip Riemann Hypothesis
over Mathlib `riemannZeta` and publishes the checked equivalence
`Q3.RouteB.rh_iff_centeredXi_zeros_real`.  The next section publishes
`Q3.RouteB.rh_of_canonical_strip_slots` as a conditional roof with its complete
statement.  The generated Markdown, TeX and JSON all carry:

```text
Route B: CHALLENGER / NOT_RH
PX_RH_CLAIM: NOT_MADE
```

The equivalence is not a proof of either side, and the conditional roof does not
close any open assembly row.

## Reproducibility receipts

The final complete EnvDump run used all 367 source-backed Route B modules:

```text
source-backed modules : 367
selected modules      : 367
stale .olean          : 0
orphan .olean         : 0
indexed declarations  : 3362
sorryAx declarations  : 0
other-axiom declarations: 0
env_index SHA-256     : 9f5e59f08f8dfed5289777b8be2dbe9b71bd92972dd8878ee7c6a52cb1d9b765
```

The generator published atomically only after constructing and validating the
whole model in memory.  Two consecutive write runs produced byte-identical
outputs, and the intervening and final `--check` runs reported no stale path.

Adversarial tests cover false-green prose suppliers, validation and open rows,
duplicate or non-proven proof rows, wrong module identity, private or
nonstandard-axiom declarations, nested namespaces, statement byte preservation,
Verbatim termination, stale output, determinism, honesty tokens, and preservation
of every live open row.  All 13 tests pass; Ruff passes.

The generated TeX contains exactly 25 `\lean` macros (22 assembly receipts plus
the definition and two interface theorems), 47 `\notready` macros, and three
validation environments.  All 22 green registry statements occur byte-for-byte
in `content.tex`; all 18 open rows are non-green.

Pinned `leanblueprint==0.0.20` builds the printable artifact with XeLaTeX and
BibTeX against `docs/routeB_bus/litreview/references.bib`: 24 A4 pages, no missing
glyphs, no overfull boxes, and no undefined citations or references.  Visual
inspection of pages 1, 10, and 24 is clean.  A planted paragraph boundary before
each Verbatim block prevents theorem headings from overlapping Lean statements.

## Exact remaining boundary

`leanblueprint checkdecls` was not run.  The Lean project is nested below the Git
root, the official CLI assumes a root-level lakefile and blueprint directory,
and the current lake target does not yet carry the Route B import-root/checkdecls
integration.  That integration is explicitly deferred to workflow-refactor
Block E.  Until then, complete EnvDump is the declaration-identity gate.

The remaining 26 exact-receipt debts and 18 mathematical rows are exposed by the
artifact; this transaction does not silently create target names, dependency
edges, statements, or proofs for them.
