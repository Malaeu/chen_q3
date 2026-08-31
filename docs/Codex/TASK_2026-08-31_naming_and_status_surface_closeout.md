# Codex task — legacy naming closeout and status-surface honesty

Date: 2026-08-31
Status: `DRAFT_AWAITING_OWNER_ACTIVATION`
Class: `CONTROL_PLANE_AND_LEAN_RENAME / NO_NEW_MATH / NO_PROOF_BODY_CHANGES`
Branch: `rh_clean`
Original pin at drafting: `4da62702066748b8acb1c8a23740189e60435b04`
Corrected activation pin: `2d2a6441328f70ae28de5058c336518b6733ff04`
Parent: Mythos repo audit 2026-08-27 (findings M3a, M3b, M3g, M4, K1),
re-scoped by the observer against the semantic-quarantine layer landed
2026-08-27 … 2026-08-31.

## Why this re-scope exists

The 2026-08-27 Mythos drafts predate three landed receipts. Executing them
literally would now break the quarantine layer. This task keeps the findings
and replaces the obsolete steps. Read this section before touching anything.

Already closed — do not redo:

1. `9716df6c` created the honest declaration
   `Q3.Conditional.LegacyBroadCone.RH_of_legacyBroadConeAxioms`
   (`q3.lean.aristotle/Q3/Proofs/PaperMainlineAtomRoute.lean:87`) and pointed
   every legacy wrapper at it through `@[deprecated … (since := "2026-08-27")]`.
2. `ROUTE_B_EXECUTION_STATE.json:5` already holds `"."` with
   `repo_relative_to: GIT_TOPLEVEL`;
   `PORTABILITY_MANIFEST_v1.json` records `canonical_repo_path_consumer_count: 0`.
3. `PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md:143` already carries the
   pre-change `#print axioms` profile of `Q3.MainTheorems.RH_proven`.

Now forbidden — the 2026-08-27 draft asked for these and they are wrong today:

1. Do NOT write an absolute path into `ROUTE_B_EXECUTION_STATE.json`. It is
   `ACTIVE_PORTABLE`; an absolute path violates `P7_PORTABILITY_RECEIPT`.
2. Do NOT edit `loop_state.json`. `STATUS_SURFACE_REGISTRY_v1.json` classifies
   it `HISTORICAL / COMPATIBILITY_MIRROR / MUST_NOT_SELECT_WORK`. Its Mac path
   is frozen history, not drift.
3. Do NOT regenerate the live-state snapshot inside
   `ROUTE_B_EXECUTION_CONTROL.md`. The same registry classifies it
   `HISTORICAL / FROZEN_DAG_CONTRACT / selector_effect: NONE`. Pouring live
   state into a historical surface is exactly `STALE_MONITOR_SELECTED_WORK`.

Corrected fact the draft got wrong: none of the four `RH_proven*` declarations
is in the default build. `lakefile.toml` sets `globs = ["Q3", "Q3.Proofs.RouteB.+"]`
and `Q3.lean` imports neither `Q3.MainTheorems` nor `Q3.Clean.MainClean`.
Verify this yourself before Block A; if it changed, stop and report.

## Block A — remove the "proven" name (finding M4)

Current sites, all outside `archive/`:

| File | Line | Declaration | State |
|---|---|---|---|
| `q3.lean.aristotle/Q3/MainTheorems.lean` | 55 | `RH_proven` | deprecated, delegates to honest name |
| `q3.lean.aristotle/MainTheorems.lean` | 51 | `RH_proven` | deprecated, delegates to honest name |
| `q3.lean.aristotle/Q3/Clean/MainClean.lean` | 48 | `RH_proven_clean` | untouched, `sorry` at line 59 |
| `q3.lean.aristotle/Clean/MainClean.lean` | 48 | `RH_proven_clean` | byte-identical duplicate, sha256 `68ef05ca…` |

Owner-selected variant: **A1 (delete the name).**

A1. Rename all four declarations; keep no alias.
  - `RH_proven` → `RH_of_legacyBroadConeAxioms_compat`
  - `RH_proven_clean` → `RH_conditional_on_Gate_clean_broken`
  Drop the now-redundant `@[deprecated]` attribute on the two `RH_proven`
  wrappers when the old name no longer exists; keep the delegation body.
  On `RH_proven_clean` add nothing beyond the rename and the docstring line.

Rationale for A1: no Lean consumer exists. The live preflight found prose-only
references outside the four declaration files in both copies of
`Tier2_Verification.lean` and both copies of `Clean/PoC.lean`; none is a Lean
consumer. The alias was introduced four days ago and serves no external
compatibility. The goal is that an outside reader's grep no longer finds a
theorem *named* "proven" or live prose that still presents that name as the
current export.

Owner may switch to variant A2 (keep the deprecated aliases, rename nothing)
by editing this line before activation. If A2 is chosen, Block A reduces to
the docstring warnings and the two `RH_proven_clean` sites only.

Steps:

1. Snapshot `#print axioms` of the two buildable wrappers before any edit and
   compare against `PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md:143`. If the
   profile already differs from that receipt, stop and report — do not rename
   over an unexplained change.
2. Apply the renames plus every in-file mention (docstrings, `#print axioms`
   comment lines in the same files).
3. Add one docstring line to each renamed declaration:
   `Renamed from RH_proven(_clean) 2026-08-31; conditional — see #print axioms.`
4. Update the prose-only references in both copies of
   `Tier2_Verification.lean` and both copies of `Clean/PoC.lean` to name the
   replacement declarations. These edits change no declaration or proof body.
5. Regenerate the Aristotle queue through its canonical generator:

   ```text
   python3 q3.lean.aristotle/scripts/aristotle_dag_loop.py --refresh --print-next 10
   ```

   Verify that all four generated surfaces consistently name the replacement
   declaration and target:
   `ACTIVE/aristotle/ARISTOTLE_QUEUE.json`,
   `ACTIVE/aristotle/ARISTOTLE_QUEUE.md`,
   `ACTIVE/aristotle/queue/sorry_Q3_Clean_MainClean_lean/PROMPT.txt`, and
   `ACTIVE/aristotle/queue/sorry_Q3_Clean_MainClean_lean/NODE_BRIEF.md`.
   If the generator changes unrelated queue entries, stop and report the exact
   diff rather than hand-editing generated output.
6. `git grep -n "RH_proven" -- '*.lean'` must afterwards return only the
   "Renamed from" docstring lines and files under `archive/`.
7. Prose references: append one dated note, do not rewrite, in
   `q3.lean.aristotle/ARCHITECTURE.md`,
   `q3.lean.aristotle/PROJECT_STATUS.md`, `q3.lean.aristotle/PROOF_MAP.md`,
   `q3.lean.aristotle/REPO_POLICY.md`.
   Leave `docs/Paper_RH/`, `STRATEGIC_CONTEXT.md`, `*_old.md`, `*_dradt.md`,
   `UNIFORM_MIGRATION_PLAN.md`, and everything under `archive/` untouched —
   they are history and do not select a current declaration.
8. Append a dated migration row to
   `docs/semantic_quarantine/PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md`
   recording old name → new name and the post-change axiom profile.
   Append only; the audited baseline block stays as written.
9. Compile the two buildable wrapper files explicitly; `lake build Q3` does
   not cover them:

   ```text
   cd q3.lean.aristotle
   env -u LD_LIBRARY_PATH lake env lean Q3/MainTheorems.lean
   env -u LD_LIBRARY_PATH lake env lean MainTheorems.lean
   ```

   Their post-change `#print axioms` output must be identical to the
   pre-change profile. Then run `lake build Q3` as a separate default-target
   regression gate.
10. Hole scan (`q3_check`) shows no new match.

The `sorry` at `MainClean.lean:59` is **not** to be fixed here. The module is
registered `LEGACY / BROKEN / BROKEN_BUILD`; leave the build failure in place.

## Block B — registry coverage gap

`docs/semantic_quarantine/MODULE_CLASS_REGISTRY_v1.json` classifies
`q3.lean.aristotle/Q3/Clean/MainClean.lean` but has no entry for the byte-identical
root duplicate `q3.lean.aristotle/Clean/MainClean.lean`. Its `declared_coverage`
only covers `q3.lean.aristotle/Q3/Proofs/RouteB/`.

Add the missing entry with the same class as its twin
(`LEGACY / BROKEN`, trait `BROKEN_BUILD`). Do not delete either duplicate —
deduplication is a separate owner decision.

## Block C — status-surface honesty (findings M3a, M3b)

C1. `ROUTE_B_EXECUTION_CONTROL.md`: insert one dated header block directly
under the title, quoting the registry verbatim:

```text
CLASSIFICATION 2026-08-31: HISTORICAL · selector_effect NONE ·
source_store FROZEN_DAG_CONTRACT (docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json).
This file does not report current state and must not select work.
Current state comes only from the authoritative machine state.
```

Change nothing else in that file. The stale `RB-IDLE` body stays as history.

C2. `SESSION_ENTRY.md` and `q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`, both
at line 101: replace

```text
4. `ROUTE_B_THEOREM_CONTRACT_v2.md` и `ROUTE_B_EXECUTION_CONTROL.md` задают DAG.
```

with a statement that the executable DAG is master route 058
(`docs/routeB_bus/proshka/PROSHKA_MASTER_ROUTE_REALZERO_GROUND_DIAGONAL_TO_XI_2026-08-11.md`),
that `ROUTE_B_THEOREM_CONTRACT_v2.md` is a historical candidate whose
disciplinary articles (K7, anti-circularity, `SAFE_IS_RH_REPACKAGING`,
tau0-substitution ban) remain project-wide, and that `ROUTE_B_EXECUTION_CONTROL.md`
is a historical surface with no selector effect. Keep both copies identical.

C3. The owner ratified the addendum on 2026-08-31. Its canonical materialization
is `docs/ROUTE_B_CONTRACT_V2_STATUS_ADDENDUM_v1.md`. Preserve the historical
`TIP_AT_DRAFT`; record the execution commit separately as `RATIFIED_AT` and
`EVIDENCE_REVALIDATED_AT`. The source draft remains as a provenance pointer
unless the owner separately authorizes deletion. Reference the canonical
addendum from C1 and C2.

`ROUTE_B_THEOREM_CONTRACT_v2.md` itself is never edited.

## Block D — close the K1 checker blind spot

`routeb_status.py` (unchanged since `056a30fc`, 2026-08-13) reports `CHECK: OK`
while `ROUTE_B_EXECUTION_CONTROL.md` carries a stale live-state claim, because
it never reads that file.

Add one read-only check to `--check`, matching the post-quarantine semantics —
freshness of a snapshot is the wrong test now that the file is historical:

D1. Add a `required_marker` field to the
`ROUTE_B_EXECUTION_CONTROL.md` row in the status-surface registry. In `--check`,
iterate over registry rows marked `role: HISTORICAL` that carry a nonempty
`required_marker`, and assert that the named file contains that exact marker.
Do not infer this requirement for every historical row: many immutable JSON,
JSONL, monitor, queue, and snapshot surfaces are intentionally unmodified.
D2. Fail with `STALE_MONITOR_MISSING_HISTORICAL_MARKER` when a registered
historical surface lacks it.
D3. Keep the checker read-only. No auto-repair.
D4. Negative test: temporarily remove the marker, confirm the failure, restore.

Registry path is `docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json`.
Read the path and marker from it; do not hardcode either value in the checker.

## Not in this task

- Deck acceptance re-pin (finding M3g). The standing acceptance
  `PROSHKA_VERDICT_ARSENAL_ACCEPTANCE_2026-08-17.md` pins `018dbf6b…`; the live
  deck `q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md` is
  `46065599a77c36df14cdda1dcb7e838fe1a23789c7f31736d5890255a08b0918`. This needs
  a judge verdict, not a Codex edit. It goes to `docs/routeB_bus/PROSHKA_QUEUE.md`
  by the 2–4 batching rule.
- Deduplication of the root `MainTheorems.lean` / `Clean/` twins.
- Anything mathematical. No dependency packet under
  `docs/Codex/RESEARCH_DEPENDENCY_PROTOCOL.md` is required or permitted here:
  this task names no candidate dependency and no downstream consumer.

## Hard bounds

`ROUTE`, `BUS_010`, `GOAL_055`, `PX_RH_CLAIM` are untouched. No bus number is
consumed. No goal is created or closed. No verdict, goal/answer pair, or
`ARSENAL_CARDS_v1.md` is edited. No proof body changes; no axiom added or
removed. Nothing under `archive/` is touched.

## Verification and closeout

1. Explicitly compile both renamed buildable wrapper files and compare their
   `#print axioms` output with the pre-change receipt; then run `lake build Q3`
   as the default-target regression gate. Take `${PIPESTATUS[0]}`, not the tail
   of a pipe.
2. `python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check`
   — exit 0, plus the D4 negative test.
3. `bash specs_docs/session_start.sh` — exit 0, no divergence.
4. `uv run pytest orchestrator/tests/` — green.
5. `git diff --stat` — only files named in this task.
6. Report to `docs/Codex/REPORT_2026-08-31_naming_and_status_surface_closeout.md`.
7. Commit manifest to the owner. Commit and push only after per-action approval.

If the tree moves after `Corrected activation pin`, stop and revalidate the
task inputs before editing. Preserve both historical pins rather than rewriting
their meaning.
