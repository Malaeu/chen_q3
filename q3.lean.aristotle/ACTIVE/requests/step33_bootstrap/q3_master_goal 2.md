# Q3_MASTER_GOAL Operating Contract

Status: active
Date: 2026-06-05

## Objective

Drive the Q3 PSD route through the theorem-complete local gates:

```text
Step33A -> Step33B -> Step33C -> Step34 -> Step35
```

This is the long-run Codex/Louise tandem contract.  It overrides stale thread
goal wording, old Step32 requests, and the parked H1/PO3 monitor for this PSD
lane.

The project-level ambition is the Q3/RH route, but the local completion
definition is strict: do not claim RH, Q3, or Step33 closure until the relevant
Lean gates compile with no holes.

End-to-end ambition, stated operationally:

```text
Q3 theorem-complete local route
  -> exported Q3 mainline wrapper
  -> RH-facing conclusion through the approved project chain
```

The proof-loop must keep working step by step toward that chain, but every
claim is gated by compiled Lean artifacts.  No natural-language route decision,
numeric sanity pass, browser answer, or generated table counts as closure until
it is consumed by a Lean theorem with no holes.

## Current Canonical Choice

Latest Louise/Pro route decision after the source/sign audit:

```text
CHOSEN: S
first prove the upstream/C-level assembler sign-location theorem:
finite Weil C = step22PositiveAxisOmegaAProfile - centered finite Prime
```

Current live gate:

```text
Step33A.1-A
raw-Omega A abs-distance hbox certs; Step33B/Step33C raw-Omega packaging is compiled conditional support
```

Canonical finite convention for the current finite certificate:

```text
A_rawOmega = step22PositiveAxisOmegaAProfile
C_rawOmega = A_rawOmega - centered finite Prime
finite model matrix = step22PositiveAxisOmegaCMatrix
```

The current route is not:

```text
raw-Omega A payload generation before the C-level assembler theorem
centered positive-A finite-tail payload generation
naive Q3.a_star migration
-Q3.a_star scalar fit
ARadius/CSV/radius-floor/LDL mutation as a proof patch
Q3.Main packaging
H1/PO3 reroute
```

The centered positive-A direct-distance wrappers remain compiled support, but
they are not the active target after the A2 smoke and PSD sanity fork.

## Checked Route-S Backend

Compiled in `Q3/Proofs/PSD_CenteredCoeffAnalyticABoundsBackend.lean`:

```lean
step22PositiveAxisOmegaWeilForm_eq_quadFormC_of_rawOmegaArchReceiver
step22PositiveAxisOmegaFiniteWeilMatrixModel_of_rawOmegaArchReceiver
Step22PositiveAxisOmegaRawArchReceiver
Step22PositiveAxisOmegaFiniteWeilReceiver
Step22PositiveAxisOmegaFiniteWeilReceiver.weil_ident
Step22PositiveAxisOmegaFiniteWeilReceiver.toFiniteWeilMatrixModel
step22PositiveAxisOmegaArchPacketCoeffBilinearForm_synth_eq_quadForm
primaryK11AnalyticC_eq_step22PositiveAxisOmegaCMatrix_iff_archMatrix_eq
controlK9AnalyticC_eq_step22PositiveAxisOmegaCMatrix_iff_archMatrix_eq
step22PositiveAxisOmegaRawArchKernelReceiver
step22PositiveAxisOmegaFiniteWeilPacketCoeffForm
step22PositiveAxisOmegaFiniteWeilKernelReceiver
primaryK11RawOmegaAnalyticDFromR
primaryK11RawOmegaAnalyticSplitFromR
primaryK11RawOmegaFiniteWeilMatrixModel
primaryK11RawOmega_weil_nonneg_on_analyticBoundary_of_penalty_boxes
controlK9RawOmegaAnalyticDFromR
controlK9RawOmegaAnalyticSplitFromR
controlK9RawOmegaFiniteWeilMatrixModel
controlK9RawOmega_weil_nonneg_on_analyticBoundary_of_penalty_boxes
step22PositiveAxisOmegaAProfile_even
primaryK11RawOmegaAnalyticA
primaryK11RawOmegaAAbsDistanceHboxCert
primaryK11RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
primaryK11RawOmegaAnalyticR
primaryK11RawOmegaAnalyticDtheta
primaryK11RawOmegaPrimeProfileMatrix_eq_analyticP
primaryK11RawOmegaAnalyticDFromR_eq_Dtheta
primaryK11RawOmegaAnalyticR_hbox_of_base_hboxes
primaryK11RawOmegaAnalyticDtheta_hbox_of_base_hboxes
primaryK11RawOmegaDPenaltyBox_of_matrix_and_importedQRadius
primaryK11RawOmegaDPenaltyBox_of_matrix_and_importedQRadius_hbox
primaryK11RawOmega_weil_nonneg_on_analyticBoundary_of_base_hboxes
controlK9RawOmegaAnalyticA
controlK9RawOmegaAAbsDistanceHboxCert
controlK9RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
controlK9RawOmegaAnalyticR
controlK9RawOmegaAnalyticDtheta
controlK9RawOmegaPrimeProfileMatrix_eq_analyticP
controlK9RawOmegaAnalyticDFromR_eq_Dtheta
controlK9RawOmegaAnalyticR_hbox_of_base_hboxes
controlK9RawOmegaAnalyticDtheta_hbox_of_base_hboxes
controlK9RawOmegaDPenaltyBox_of_matrix_and_importedQRadius
controlK9RawOmegaDPenaltyBox_of_matrix_and_importedQRadius_hbox
controlK9RawOmega_weil_nonneg_on_analyticBoundary_of_base_hboxes
PsdStep33RawOmegaFiniteAnalyticPositivity
psd_step33_rawOmega_finite_analytic_weil_positivity_of_base_hboxes
psd_step33_rawOmega_finite_analytic_weil_positivity_of_generated_prime_and_p0
psd_step33_rawOmega_finite_analytic_weil_positivity_of_rawOmegaAAbsDistanceCerts
```

Meaning:

```text
The raw Step22 positive-axis Omega Arch profile now has a profile-sourced
coefficient-space receiver.

raw-Omega Arch receiver + centered finite Prime receiver
  -> raw-Omega finite Weil receiver
  -> FiniteWeilMatrixModel over step22PositiveAxisOmegaCMatrix
```

This avoids the rejected local rewrite:

```text
existing centeredContract.C = rawOmegaC
```

because that rewrite is equivalent to the false local equality:

```text
centeredBSplineArchKernelProfile = step22PositiveAxisOmegaAProfile
```

## Exact Next Gate

Generate/import the primary/control raw-Omega A comparison-integral finite/tail
payload premises.  The receiver now accepts finite-window comparison integrals
plus a tail-window `(T,U]` comparison-integral enclosure; positive-axis
integrability and the `(U,∞)` tail remainder are structural checked support, so
the generator only needs to prove that its tail-remainder radii dominate the
explicit linear-growth `U^{-2}` majorants.

The comparison-integral/tail-window receiver compiles to finite/tail certs,
then to interval certs, then to abs-distance hbox certs, and the
profile-sourced raw-Omega finite Weil receiver plus raw-Omega Step33C
singleton/DirectedFamily handoff are compiled conditional support.

Concrete next targets:

```text
1. Generate/import primary/control raw-Omega A comparison-integral/tail-window
   premises consumed by:
      primaryK11RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailWindow
      controlK9RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailWindow
      activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailWindow
      psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAComparisonIntegralsAndTailWindow
      PrimaryK11RawOmegaAComparisonTailWindowPayload
      ControlK9RawOmegaAComparisonTailWindowPayload
      PrimaryK11RawOmegaAComparisonTailWindowArithmeticPayload
      ControlK9RawOmegaAComparisonTailWindowArithmeticPayload
      primaryK11RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_comparison
      controlK9RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_comparison
      psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaATailWindowPayloads
      rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability_and_tail_growth
   The rational arithmetic sublayer is already split and checked by:
      PSD_CenteredCoeffRawOmegaATailWindowArithmeticSupport
      PSD_CenteredCoeffRawOmegaATailWindowArithmeticImport
   The remaining premises are analytic: finite-window comparison functions and
   integral containments, tail-window comparison functions and integral
   containments on `(T,U]`, plus arithmetic domination of the explicit
   structural tail-remainder majorants.
2. Feed those premises to:
      psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAComparisonIntegralsAndTailBounds
   where generated P and P0 are already inserted and Step33C singleton handoff
   is already packaged by the new all-the-way tail-window support wrapper.
   Prefer generating the two payload structures and feeding
   `psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaATailWindowPayloads`.
   Keep the checked rational arithmetic import separate from the analytic
   comparison/integrability import until the final payload constructor.
3. Continue Step34/Step35 through the raw-Omega finite analytic positivity and
   singleton-family surface.
```

Candidate theorem names, to be adjusted to repo-real receivers:

```lean
centeredBSplineFiniteWeilCProfile_eq_step22PositiveAxisOmega_sub_primeProfile
centeredBSplineFiniteWeilAProfile_eq_step22PositiveAxisOmega_throughAssembler
activeCenteredCoeffEntryHboxCert_of_step22PositiveAxisOmegaA
primaryK11RawOmegaAAbsDistanceHboxCert_generated
controlK9RawOmegaAAbsDistanceHboxCert_generated
primaryK11RawOmegaAAbsDistanceIntervalCert_generated
controlK9RawOmegaAAbsDistanceIntervalCert_generated
primaryK11RawOmegaAFiniteTailBoundsCert_generated
controlK9RawOmegaAFiniteTailBoundsCert_generated
primaryK11RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailWindow
controlK9RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailWindow
activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailWindow
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAComparisonIntegralsAndTailWindow
PrimaryK11RawOmegaAComparisonTailWindowPayload
ControlK9RawOmegaAComparisonTailWindowPayload
PrimaryK11RawOmegaAComparisonTailWindowArithmeticPayload
ControlK9RawOmegaAComparisonTailWindowArithmeticPayload
primaryK11RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_comparison
controlK9RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_comparison
rawOmegaAComparisonTailWindowPayloadActiveCert
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaATailWindowPayloads
activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailBounds
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAComparisonIntegralsAndTailBounds
primaryK11RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
controlK9RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
psd_step33_rawOmega_finite_analytic_weil_positivity_of_generated_prime_and_p0
psd_step33_rawOmega_finite_analytic_weil_positivity_of_rawOmegaAAbsDistanceCerts
activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAAbsDistanceCerts
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAAbsDistanceCerts
activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAIntervalCerts
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAIntervalCerts
activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAFiniteTailBoundsCerts
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAFiniteTailBoundsCerts
step33_rawOmega_finite_analytic_weil_positivity
step33_rawOmega_singleton_directed_family_handoff
psd_step33_closed_from_step22PositiveAxisOmegaFiniteWeilModel
```

If the receiver cannot accept raw-Omega `FiniteWeilMatrixModel` without a new
contract, the blocker report must name the exact hardwired field and theorem:

```text
theorem:
file:
required C matrix:
available C matrix:
missing adapter:
Codex recommendation:
question for Louise:
```

## Full Closure Definition

The goal is complete only when all of these are Lean-checked with no
`sorry`, `admit`, `exact?`, fake axiom, or theorem weakening:

```text
1. Step33A:
   raw-Omega compatible finite certificate receiver / entry-hbox replacement
   sufficient to feed the active finite PSD cert.

2. Step33B:
   finite analytic Weil positivity from the certified finite model.

3. Step33C:
   singleton / DirectedFamily handoff.

4. Step34:
   next local positivity/boundary handoff required by the Q3 route.

5. Step35:
   final local theorem-complete Q3 gate before Q3.Main.
```

Do not report "Step33 closed" after only A-input progress, raw-Omega receiver
progress, or a single model theorem.  Step33 is closed only after Step33C
compiles.

Do not report "Q3 done" after Step33.  Q3 is done only after Step35 compiles
and the mainline wrapper can be exported without changing the mathematics.

## Louise / Pro Tandem Rule

Codex is the local worker:

```text
edit Lean/docs/scripts
run builds/checks
write exact blocker reports
integrate only Lean-checked consequences
```

Louise/Pro is the route architect/reviewer:

```text
choose theorem shape at real forks
review source/sign/canonical-convention decisions
avoid proof-route thrash
```

If the Pro/Louise browser tab is available, Codex may read the attached or
visible answer and integrate it.  If it is not available or the route fork is
new, append `PRO_REVIEW_REQUEST` to `report.md` instead of guessing.

When the user explicitly asks Codex to use the open Pro/Louise tab, the loop is:

```text
1. Read the visible Louise answer.
2. Extract only the route decision, theorem shape, and exact next action.
3. Compare it against repo-real Lean declarations and the active monitor.
4. Implement only the Lean/docs/scripts consequence that can be checked locally.
5. If the answer conflicts with compiled facts, write the conflict into
   `report.md` and ask a narrower follow-up instead of forcing the route.
```

Louise output is advisory route architecture.  The accepted source of proof
truth remains:

```text
Lean-checked code
hole-free Aristotle output
verified local mathematics recorded in report/INSIGHTS
```

Required escalation shape:

```md
## PRO_REVIEW_REQUEST

Route:
Current step:
Current theorem:
File:
Lean error / blocker:
Options:
A.
B.
C.
Codex recommendation:
Question for Louise:
```

## Continuous Execution Loop

For each autonomous work slice:

```text
1. Read:
   AGENTS.md
   Q3_OBSTRUCTION_ATLAS.md
   SESSION_ENTRY.md
   ACTIVE/PSD_STEP33_MONITOR.md
   ACTIVE/requests/step33_bootstrap/node.md
   ACTIVE/requests/step33_bootstrap/report.md
   docs/INSIGHTS.md

2. Check local model sanity after crash/update when useful:
   claude --print-model
   fallback: claude -p "what model are you running?"

   Current local observation on 2026-06-05:
   claude --print-model is unsupported here;
   fallback reported claude-opus-4-7[1m].

3. Identify the smallest repo-real theorem or diagnostic that advances the
   current raw-Omega Step33 gate.

4. Implement only that theorem/diagnostic/control-plane update.

5. Validate touched Lean:
   lake env lean <touched Lean file>
   scripts/q3_check.sh <touched Lean file>
   rg -n "sorry|exact\\?|admit|axiom|unsafe" <touched Lean file>

6. Update:
   ACTIVE/requests/step33_bootstrap/report.md
   ACTIVE/PSD_STEP33_MONITOR.md if the live pointer changed
   docs/INSIGHTS.md

7. Stage only relevant files.

8. Continue to the next gate or write an exact blocker.
```

For docs-only updates, use `git diff --check` over touched docs and state that
no Lean file changed.

Stopping rule:

```text
Do not stop merely because a subproblem expanded.
Compress the expansion back into:
  current gate
  exact theorem/file
  missing premise
  next Lean-checkable move
  optional Louise question if there is a real fork
```

## Hard Stops

```text
no sorry
no admit
no exact?
no axiom
no unsafe
no theorem weakening
no row crawl
no entry crawl
no A CSV / ARadius / radius-floor / LDL mutation as proof patch
no Q3.Main before local gates are theorem-complete
no H1/PO3 route unless explicitly requested
```
