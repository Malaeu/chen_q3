# Q3 Master Goal Operating Contract

Status: active
Date: 2026-06-05

## Objective

Drive the Q3 PSD route through the local Lean-checked gate chain:

```text
Step33A -> Step33B -> Step33C -> Step34 -> Step35 -> Q3 mainline wrapper
```

This is the long-run Codex/Louise tandem contract for the PSD lane.  It
overrides stale thread-goal wording, old Step32 requests, and the parked
H1/PO3 monitor for this route.

The project-level ambition is the Q3/RH route.  The local completion rule is
strict:

```text
Do not claim RH, Q3, Step35, Step34, or Step33 closure until the corresponding
Lean theorem chain compiles with no holes.
```

Natural-language route decisions, numeric sanity checks, generated table
existence, browser answers, and Pro/Louise reviews are not proof closure until
their consequences are consumed by Lean theorems with no holes.

## Human Completion Meaning

The human ambition behind this operating contract is the Q3/RH route: finish
the formal chain far enough that the project can point to a Lean-checked proof
route for the zeta-zero line statement.

The local working agent must keep that ambition compressed into theorem gates,
not rhetoric:

```text
Q3/RH ambition
-> Step33A
-> Step33B
-> Step33C
-> Step34
-> Step35
-> Q3 mainline wrapper
```

Do not say "RH is proved", "Q3 is proved", or "all zeros are on the critical
line" from this PSD lane until the corresponding final Lean theorem chain is
present, imported, and checked without holes.  Until then the correct status is
the exact current gate plus the next proof-producing action.

## Autonomous Multistep Goal

This file is the compact metagoal for long autonomous Codex work on the PSD/Q3
lane.  The assistant should not wait for repeated "go" messages when the next
local action is clear.

Work order:

```text
1. Continue the current Step33A.1-A raw-Omega A input until
   RawOmegaADirectTailWindowInputs is Lean-checked.
2. Consume it through ActiveRawOmegaCoeffEntryHboxCert.
3. Close Step33B finite analytic positivity.
4. Close Step33C singleton DirectedFamily handoff.
5. Only after Step33C compiles, open Step34.
6. Only after Step34 compiles, open Step35.
7. Touch Q3.Main only after the local Step35 chain is theorem-complete.
```

Current live front:

```text
Step33A.1-A raw-Omega direct analytic input.
Immediate proof-data front:
  remaining Taylor/model PayloadFin fields for the direct chunk-integral
  backend used to produce RawOmegaADirectTailWindowInputs.

Closed structural support:
  direct post-520 tail-remainder bounds
  tailRemainderAbs generator row fields removed from the active payload contract
```

Louise/Pro is part of the operating loop, not a proof oracle:

```text
If a real fork appears:
  read the open Pro/Louise browser tab if the user provided it,
  or write a compact PRO_REVIEW_REQUEST in report.md.

Then:
  extract only route choice / theorem shape / next Lean action;
  check it against repo-real declarations;
  integrate only Lean-checkable consequences.
```

Do not accept browser text, Arb/acb diagnostics, numeric probes, or generated
tables as proof.  A gate closes only when Lean checks the corresponding theorem
with no `sorry`, `admit`, `exact?`, fake `axiom`, or `unsafe`.

## Tandem Execution Loop

The local agent keeps working without waiting for repeated "go" messages when
the next theorem/data step is clear:

```text
1. Read this master goal, PSD_STEP33_MONITOR.md, node.md, report.md, and the
   latest INSIGHTS.md Step33 notes.
2. Confirm the repo-real live gate and exact theorem target.
3. Implement the smallest proof/data/script change that advances that gate.
4. Run the relevant Lean/script validation and scan touched Lean files for
   holes or fake trusted surfaces.
5. Update report.md, PSD_STEP33_MONITOR.md when the frontier changes, and
   INSIGHTS.md with the reusable lesson.
6. Continue to the next local gate if validation passes.
```

If a blocker is a route-choice blocker rather than a local implementation
error, use the Louise/Pro tandem:

```text
1. Write the exact blocker in report.md as PRO_REVIEW_REQUEST, unless the user
   has already supplied the open Pro/Louise browser tab or pasted answer.
2. Ask/read only the route question: theorem shape, source convention, payload
   contract, or next proof gate.
3. Convert the answer into a repo-real Lean/script action.
4. Accept nothing as closed until Lean checks the resulting theorem chain with
   no holes.
5. If Louise/Pro advice conflicts with current compiled support, prefer the
   compiled repo state and write the conflict back to report.md.
```

After crash, update, context compaction, or model restart, resume from this
file and the active monitor instead of stale thread-goal wording.  A quick
local model sanity check may be recorded in the report, but model identity is
not part of the mathematical proof state.

## Runtime Goal Override

If an internal thread goal, old browser answer, or old monitor note says
`positive-A`, centered receiver, signed `Q3.a_star`, or raw source migration,
ignore that wording for the active PSD lane unless the active monitor and this
file are both changed by a later Lean-checked route review.

The current live goal is:

```text
Continue autonomously from Step33A.1-A raw-Omega A finite/tail payloads through
Step33A -> Step33B -> Step33C -> Step34 -> Step35 -> Q3 mainline wrapper.
```

The current concrete next Lean target is:

```lean
rawOmegaADirectTailWindowInputs_of_generatedChunkIntegralBounds
```

Generator-facing constructor:

```lean
rawOmegaADirectTailWindowInputs_of_generatedChunkIntegralBounds
```

This target is not the whole proof.  It is the next proof-producing generated
analytic input feeding:

```text
raw-Omega A finite/tail certs
-> raw-Omega A interval/hbox certs
-> ActiveRawOmegaCoeffEntryHboxCert
-> Step33B finite analytic positivity
-> Step33C singleton DirectedFamily handoff
```

Exact generated cert surfaces:

```lean
RawOmegaAChunkedRangePayload
PrimaryK11RawOmegaAFiniteWindowChunkedRangePayload
PrimaryK11RawOmegaATailWindowChunkedRangePayload
ControlK9RawOmegaAFiniteWindowChunkedRangePayload
ControlK9RawOmegaATailWindowChunkedRangePayload
RawOmegaAChunkIntegralBoundsCert
PrimaryK11RawOmegaAFiniteWindowChunkIntegralBoundsCert
PrimaryK11RawOmegaATailWindowChunkIntegralBoundsCert
ControlK9RawOmegaAFiniteWindowChunkIntegralBoundsCert
ControlK9RawOmegaATailWindowChunkIntegralBoundsCert
```

The earlier full-window constant-comparison target:

```lean
RawOmegaAConstComparisonDirectTailInputs
```

is checked support, but it is no longer the next target for the current data:
`rawomega_a_const_route_diagnostic.json` reports
`full_window_constant_route_sampled_too_coarse` with 257 Arb samples per window.
Do not spend more Lean time on full-window constants unless a later generator
changes the comparison granularity and records a new diagnostic.

Follow-up sampled diagnostics also reject chunkwise constant comparisons on
the current raw-Omega grid:
`rawomega_a_nonconstant_route_diagnostic.json` reports
`chunkwise_constant_route_sampled_too_coarse` for `chunk_size = 10`.
Additional scratch scans with `chunk_size = 5, 2, 1, 0.5, 0.25` still had
positive finite-window excess.  Those checked comparison-function constructors
remain support, but they are no longer the active generated import target.

The active generated import should instantiate the direct chunk-integral
surface:

```lean
RawOmegaAChunkedRangePayload
RawOmegaAChunkedRangePayload.toChunkIntegralBoundsCert
rawOmegaADirectTailWindowInputs_of_generatedChunkIntegralBounds
```

## Current Refinement Checkpoint

As of 2026-06-05 the active route keeps the outer parent chunk payload shape
and proves hard parent chunks through refined Taylor/model subchunks.

Checked receiver:

```lean
RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert
RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.of_refinedSubchunkSums
RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunkSums
RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunks
RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedTaylorSubchunks
```

Address-only worklist:

```text
a_chunk_taylor_payload_refined_subchunk_worklist.{json,md}
```

Counts:

```text
parent chunks = 2392
refined subchunks = 40020
finite first chunk split = 100
finite remaining chunk split = 10
tail chunk split = 20
degree candidate = 16
```

Next proof-producing local target:

```text
Generate rational Taylor/model cert fields for the 40020 refined subchunks,
then fold them back to parent WindowPartBoundsCerts through
RefinedWindowPartBoundsCert and continue to RefinedPayloadFin.
```

The generator must supply Lean-checkable finite-window and tail-window direct
integral bounds through:

```lean
RawOmegaAChunkIntegral.WindowPartBoundsCert
RawOmegaAChunkedRangePayload
RawOmegaAChunkIntegralBoundsCert
```

Checked refinement:

```lean
rawOmegaAAnalyticTailWindowInputs_of_generated_quadratic_comparison_builtin_integrability
```

is now available for distance-indexed quadratic comparison functions.  Prefer
this only as inactive support unless a later route review revives polynomial
comparison envelopes.  It discharges the finite/tail window integrability
premises for the eight primary/control lower/upper comparison families; the
generated import still owns the pointwise comparison, scalar integral
containment, and Taylor/model cell certificates.

Follow-up diagnostic:

```text
rawomega_a_quadratic_route_diagnostic.json
rawomega_a_piecewise_quadratic_route_diagnostic.json
```

rejects full-window quadratic and current-grid piecewise quadratic comparisons
on the worst finite row `d=5.50`.  Do not generate a full-window quadratic
payload as the next proof route.

Latest Louise/Pro backend decision on 2026-06-05:

```text
Keep the direct chunk-integral receiver surface, but do not trust Arb/acb
integral output as a theorem.

The proof-producing backend is a reusable Taylor/model certificate checker:
  rational Taylor/model certificate
  -> RawOmegaAChunkIntegral.WindowPartBoundsCert

The generator may use Arb/acb only to discover good rational certificate data.
Lean must check the analytic certificate theorem and the rational
side-conditions.
```

Checked backend adapter:

```lean
rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate
```

Checked checker file:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean
```

Current generated payload target:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorPayloadImport.lean
```

The adapter in that file now compiles.  The active generated content must keep
the 26 parent chunk shape and fill
`RawOmegaAChunkTaylorPayload.RefinedPayloadFin`: each parent chunk receives a
`RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert`, whose `subCert` fields
come from refined subchunk Taylor/model certificates.  Do not switch the
top-level payload to fully refined chunks and do not replace this with trusted
Arb/acb integral theorems.

The active worklist has been synced to this target:

```text
ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_worklist.{json,md}
ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_proof_data_skeleton.{json,md}
ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_lean_emitter.{json,md}
ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_row_sum_worklist.{json,md}
lean_payload_type = RawOmegaAChunkTaylorPayload.RefinedPayloadFin
parent_receiver = RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert
exact_sum_parent_constructor = RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.of_refinedSubchunkSums
```

Do not re-ask Louise for the already-settled upstream raw-Omega semantic
receiver unless a new repo-real theorem failure contradicts the compiled
support layer.

## Current Source Of Truth

Current active monitor:

```text
q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md
```

Current active request:

```text
q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md
```

Current active report:

```text
q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/report.md
```

Current live gate:

```text
Step33A.1-A
raw-Omega A finite/tail bounds certs feeding interval and hbox receivers
```

Canonical finite convention for this route:

```text
A_rawOmega = step22PositiveAxisOmegaAProfile
C_rawOmega = A_rawOmega - centered finite Prime
finite model matrix = step22PositiveAxisOmegaCMatrix
```

Inactive support only:

```text
centered positive-A direct-distance route
naive Q3.a_star migration
-Q3.a_star scalar fit
H1/PO3 route
Q3.Main packaging
```

Do not use any inactive route unless a new Lean-checked route review changes
the active monitor and this file.

## Current Exact Gate

The raw-Omega semantic finite Weil receiver and Step33B/Step33C conditional
packaging are already compiled support.  The remaining open Step33A.1-A layer
is the generated analytic payload layer:

```text
one rational Taylor/model certificate per refined raw-Omega subchunk
one RefinedWindowPartBoundsCert fold per 26-wide parent chunk
structural finite/tail endpoint checks discharged by chunk constructors
radius/nonnegativity checks for each Taylor subchunk
raw-integrand and Taylor-polynomial value enclosures on each subchunk
value-bound comparisons implying the Taylor diff enclosure:
  -remainder <= rawLower - polyUpper
  rawUpper - polyLower <= remainder
endpoint-form refined model integral comparisons:
  subLower <= lowerModelIntegral
  upperModelIntegral <= subUpper
parent fold comparisons:
  parentLower <= sum subLower
  sum subUpper <= parentUpper
  or exact parent sums via RefinedWindowPartBoundsCert.of_refinedSubchunkSums
row-level comparisons still required by RefinedPayloadFin:
  hLowerSum
  hUpperSum
  exact address worklist:
    a_chunk_taylor_payload_refined_row_sum_worklist.{json,md}
primary/control finite-window row-sum comparisons on (0,260]
primary/control tail-window row-sum comparisons on (260,520]
```

The current target surface is:

```text
primaryK11RawOmegaAFiniteTailBoundsCert
controlK9RawOmegaAFiniteTailBoundsCert
primaryK11RawOmegaAAbsDistanceIntervalCert
controlK9RawOmegaAAbsDistanceIntervalCert
primaryK11RawOmegaAAbsDistanceHboxCert
controlK9RawOmegaAAbsDistanceHboxCert
ActiveRawOmegaCoeffEntryHboxCert
PsdStep33RawOmegaFiniteAnalyticPositivity
PsdStep33RawOmegaSingletonDirectedFamilyHandoff
```

The generated payload import has four checked wrapper routes:

```lean
RawOmegaAAnalyticTailWindowInputs
RawOmegaAAnalyticTailWindowInputs.toPayloads
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAAnalyticTailWindowInputs
```

and the compact constant-comparison/direct-tail route:

```lean
RawOmegaAConstComparisonDirectTailInputs
RawOmegaAConstComparisonDirectTailInputs.toPayloads
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonDirectTailInputs
```

and:

```lean
RawOmegaAConstComparisonTailGrowthInputs
RawOmegaAConstComparisonTailGrowthInputs.toPayloads
rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability_and_tail_growth
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonPayloads_builtin_integrability_and_tail_growth
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonTailGrowthInputs
```

and the direct finite/tail-window integral route:

```lean
RawOmegaADirectTailWindowInputs
RawOmegaADirectTailWindowInputs.toFiniteTailBoundsCerts
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs
```

The full-window constant-comparison/direct-tail route was tried first and is
too coarse for the current generated data.  The current next proof-producing
route is therefore the direct analytic route, where the generated import
supplies nonconstant finite/tail window enclosures.  Chunkwise constant
comparisons on the current raw-Omega grid are also sampled-too-coarse, so do
not spend the next generator pass on constant step functions unless the grid or
function family changes and a new diagnostic passes.  Use the structural
tail-growth route only if the generator also supplies concrete `C0/C1` growth
data and proves the generated tail radii dominate the resulting structural
`U^{-2}` tail majorants.

Checked direct-integral refinement on 2026-06-05:

```text
The direct receiver surface now compiles all the way through the raw-Omega
Step33B/Step33C conditional handoff.  The remaining proof-producing generator
target is not a new receiver; it is concrete direct finite-window integral
bounds, tail-window integral bounds, and tail-remainder bounds for
RawOmegaADirectTailWindowInputs.
```

Louise route-A chunk-integral refinement on 2026-06-05:

```text
Louise chose direct chunk-integral finite/tail certificates.  Repo-real Lean
adaptation is checked in:
  Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkIntegralBoundsImport.lean
```

Exact next generated cert surfaces:

```lean
RawOmegaAChunkedRangePayload
PrimaryK11RawOmegaAFiniteWindowChunkedRangePayload
PrimaryK11RawOmegaATailWindowChunkedRangePayload
ControlK9RawOmegaAFiniteWindowChunkedRangePayload
ControlK9RawOmegaATailWindowChunkedRangePayload
RawOmegaAChunkIntegralBoundsCert
PrimaryK11RawOmegaAFiniteWindowChunkIntegralBoundsCert
PrimaryK11RawOmegaATailWindowChunkIntegralBoundsCert
ControlK9RawOmegaAFiniteWindowChunkIntegralBoundsCert
ControlK9RawOmegaATailWindowChunkIntegralBoundsCert
rawOmegaADirectTailWindowInputs_of_generatedChunkIntegralBounds
```

Checked local target refresh on 2026-06-05:

```text
The raw-Omega chunk probe found 51 current-target misses across 92 distance
rows, all absorbable by local target slack.  The refreshed worklist and
arithmetic import now share those local intervals, and the post-refresh
all-row probe reports rows_failed = 0.

This is not an A data migration.  Do not use it as permission to edit A CSV,
ARadius, radius-floor, LDL, Q3.Main, or H1/PO3.  The next proof-producing gate
is still the Lean-checkable RawOmegaAChunkIntegral.WindowPartBoundsCert import
for the refreshed 92-row / 2392 distance-chunk worklist.
```

Latest Louise proof-producing backend on 2026-06-05, with first local checker
adapter checked:

```text
CHOSEN: C

Checked:
  rawOmegaATaylorPolynomial
  RawOmegaATaylorModelCertificate
  RawOmegaATaylorModelCertificate.Valid
  rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate

Next generate the 2392 rational payload instances proving Valid and fold them
through:
  RawOmegaAChunkedRangePayload
  RawOmegaAChunkedRangePayload.toChunkIntegralBoundsCert
  RawOmegaAChunkIntegralBoundsCert.toDirectTailWindowInputs
  psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs
```

## Multistep Closure Plan

### Gate 33A

Close `ActiveRawOmegaCoeffEntryHboxCert`.

Immediate subgoal:

```text
close primary/control raw-Omega A finite-tail certs
```

Then verify the remaining generated P/P0 premises already feed the raw-Omega
entry-hbox receiver.  If a P/P0 premise is missing, name the exact theorem and
file; do not switch routes.

Step33A is closed only when the active raw-Omega entry-hbox certificate
compiles without premises that are meant to be generated.

### Gate 33B

Use the compiled raw-Omega finite model receiver to derive finite analytic Weil
positivity from the certified raw-Omega finite model.

Step33B is closed only when the finite analytic positivity theorem compiles
from the Step33A certificate and generated payload facts.

### Gate 33C

Package the singleton `DirectedFamily` handoff.

Step33 is closed only after Step33C compiles.  A-input progress, hbox progress,
receiver progress, or Step33B alone must not be reported as Step33 closure.

### Gate 34

Move only after Step33C is checked.  Read the active monitor before choosing
the first Step34 theorem, then create the next local theorem target with exact
file and premise list.

### Gate 35

Move only after Step34 is checked.  Close the final local Q3 gate before
touching `Q3.Main`.

### Q3 Mainline Wrapper

Touch `Q3.Main` only after the local Step35 theorem-complete chain is checked.
The wrapper must not change mathematics; it only exports the approved chain.

## Codex / Louise Tandem Protocol

Codex is the local worker:

```text
edit Lean/docs/scripts
run local validation
write exact blocker reports
stage only relevant files
integrate only Lean-checked consequences
```

Louise/Pro is the route architect/reviewer:

```text
choose theorem shape at real forks
review canonical source/sign decisions
prevent route thrash
answer narrow blocker questions
```

Use Louise/Pro only at real forks, for example:

```text
two plausible theorem routes
source/sign/canonical-A uncertainty
generated payload shape ambiguity
monitor conflict
H1/PO3 vs PSD route conflict
```

If the browser tab is available and the user explicitly asks to use it:

```text
1. Read the visible Louise answer.
2. Extract the route decision, theorem shape, and next Lean action.
3. Check that the answer matches repo-real declarations and the active monitor.
4. Implement only locally checkable consequences.
5. If the answer conflicts with compiled facts, write the conflict to report.md
   and ask a narrower follow-up.
```

If the visible Louise answer is still incomplete, streaming, truncated, or only
shows an opening token, do not treat it as a route decision.  Keep working from
the current repo-real monitor and record only that no completed new review was
available yet.

Current visible Louise reconciliation on 2026-06-05:

```text
Earlier visible Louise answer chose route A:
  build an upstream raw-Omega semantic receiver and avoid a matrix-only fake
  FiniteWeilMatrixModel.

Repo status has already advanced past that decision:
  raw-Omega semantic receiver support and Step33B/Step33C conditional packaging
  are compiled.

Later Louise answer chose route A at the generated-payload surface fork:
  direct chunk-integral finite/tail certificates.

Repo status has already advanced past that decision:
  the direct chunk-integral folder surface compiles, and the local target
  refresh leaves zero diagnostic row failures.

Latest visible Louise answer chose route C at the proof-producing backend fork:
  build a Lean-checkable Taylor/model certificate checker, then generate
  rational certificate payloads for the 2392 distance/chunk cells.

Repo status has advanced into that decision:
  `PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean` now compiles with
  `rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate`.
  `PSD_CenteredCoeffRawOmegaAChunkTaylorPayloadImport.lean` now compiles with
  the generator-facing `RawOmegaAChunkTaylorPayload.Payload` adapter.
  The current checked generator-facing layer is:
    `RawOmegaATaylorModelCertificate.ValueBounds`
    `RawOmegaATaylorModelCertificate.PolynomialTermBounds`
    `RawOmegaATaylorModelCertificate.polynomial_value_bounds_of_term_bounds`
    `RawOmegaATaylorModelCertificate.ValueBounds.of_raw_and_polynomial_term_bounds`
    `RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds`
    `RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds`
    `RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds`
    `RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds`

Therefore the next question is not source/sign/receiver selection and not a
bare Arb integral import.  The next local target is the concrete generated
payload inside:
  PSD_CenteredCoeffRawOmegaAChunkTaylorPayloadImport.lean

That payload must prove `RawOmegaATaylorModelCertificate.Valid` instances and
feed:
  RawOmegaAChunkIntegral.WindowPartBoundsCert
  RawOmegaAChunkedRangePayload
  rawOmegaADirectTailWindowInputs_of_generatedChunkIntegralBounds.
For each chunk, the preferred generator obligation is a lower/upper interval
enclosure for `rawOmegaIntegrand`, per-term Taylor-polynomial enclosures,
rational comparisons from those value bounds to the Taylor remainder, and
endpoint-form model integral comparisons.

The older visible answer predates the sampled rejection of full-window
constants; do not reopen the receiver route because of it.
```

If the browser tab is unavailable or no answer is attached, write this block in
`report.md` instead of guessing:

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
1. Read the current control files:
   AGENTS.md
   Q3_OBSTRUCTION_ATLAS.md
   SESSION_ENTRY.md
   ACTIVE/PSD_STEP33_MONITOR.md
   ACTIVE/requests/step33_bootstrap/node.md
   ACTIVE/requests/step33_bootstrap/report.md
   docs/INSIGHTS.md

2. After crash/update, check local model sanity when useful:
   claude --print-model
   fallback: claude -p "what model are you running?"

   Current local observation on 2026-06-05:
   /Users/emalam/.local/bin/claude exists;
   claude --print-model is unsupported here;
   fallback reported Claude Opus 4.7 (1M context),
   model id `claude-opus-4-7[1m]`.

3. Identify the smallest repo-real theorem, generator target, or diagnostic
   that advances the current raw-Omega Step33 gate.

4. Implement only that theorem, generator target, diagnostic, or control-plane
   update.

5. Validate touched Lean files:
   lake env lean <file>
   scripts/q3_check.sh <file>
   rg -n "sorry|exact\\?|admit|axiom|unsafe" <file>

6. For docs-only updates:
   git diff --check -- <touched docs>

7. Update:
   ACTIVE/requests/step33_bootstrap/report.md
   ACTIVE/PSD_STEP33_MONITOR.md if the live pointer changed
   docs/INSIGHTS.md

8. Stage only relevant files.

9. Continue to the next gate or write an exact blocker.
```

Stopping rule:

```text
Do not stop because a subproblem expanded.
Compress the expansion back into:
  current gate
  exact theorem/file
  missing premise
  next Lean-checkable move
  optional Louise question if there is a real fork
```

## Current checked surface update -- 2026-06-05

Repo-real current Step33A.1-A target is the raw-Omega/Taylor payload, not the
older positive-A wording in the Codex goal text.

Newest checked helper layer:

```lean
RawOmegaATaylorModelCertificate.RawIntegrandComponentBounds
RawOmegaATaylorModelCertificate.rawOmegaAIntegrand_value_bounds_of_component_bounds
RawOmegaATaylorModelCertificate.ValueBounds.of_raw_component_and_polynomial_term_bounds
```

Meaning:

```text
The generated payload should prove component bounds for Omega, E^2, and cos,
plus the two sign-sensitive product comparisons.  Lean then turns that into
raw integrand value bounds and continues through the existing Taylor
polynomial-term bridge.
```

Immediate next action:

```text
build the concrete RawOmegaAChunkTaylorPayload.PayloadFin generator/instance using
the direct raw-component/term chunk constructors, then fold it into
RawOmegaADirectTailWindowInputs.
```

Direct constructors now checked:

```lean
RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
```

Checked payload surface update:

```lean
RawOmegaAChunkTaylorPayload.PayloadFin
RawOmegaAChunkTaylorPayload.PayloadFin.toDirectTailWindowInputs
```

Meaning:

```text
The concrete generator should emit chunk data as CoeffIndex23 -> Fin 26 -> Real.
Lean folds it through chunkValueFromFin26 into the existing Nat-indexed
receiver, so the old receiver stays checked and the generated code avoids
repeating i < 26 Nat proof plumbing.
```

Local model sanity on 2026-06-05:

```text
claude --print-model unsupported here;
fallback claude -p "what model are you running?" reports
Claude Opus 4.7 (1M context), model id claude-opus-4-7[1m].
```

Current proof-data inventory on 2026-06-05:

```text
script:
  scripts/q3_psdpd_step33_a_chunk_taylor_payload_inventory.py

report:
  ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_inventory.{json,md}

status:
  missing_proof_data

counts:
  families = 4
  distance rows = 92
  chunk cells = 2392
  complete cells = 0

diagnostic probe:
  numeric chunk intervals complete = true
  Taylor proof data present = false
```

Meaning:

```text
The existing Arb/acb probe covers all 2392 numeric chunk intervals, but it is
not proof data and cannot be emitted as a trusted Lean theorem.  The next
generator must produce schema
q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1 with Taylor/model fields,
component bounds, polynomial-term bounds, integral endpoint comparisons, row
sums, and tail-remainder facts.
```

Current proof-data skeleton on 2026-06-05:

```text
script:
  scripts/q3_psdpd_step33_a_chunk_taylor_payload_proof_data_skeleton.py

report:
  ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_proof_data_skeleton.{json,md}

status:
  skeleton_address_only_missing_values

counts:
  families = 4
  distance rows = 92
  chunk cells = 2392
  populated proof cells = 0
```

Meaning:

```text
The proof-data schema is now address-complete.  All 92 distance rows and 2392
distance/chunk cells exist in the skeleton, but every proof-bearing field is
still absent and inventory still reports missing_proof_data.  The next
generator should populate this skeleton with real rational Taylor/model facts,
then emit the concrete RawOmegaAChunkTaylorPayload.PayloadFin instance.
```

Inactive product-proof support from 2026-06-05:

```lean
RawOmegaATaylorModelCertificate.product_bounds_of_nonneg_boxes_and_abs_cos
RawOmegaATaylorModelCertificate.RawIntegrandComponentBounds.of_nonneg_abs_cos_product_bounds
```

Meaning:

```text
This abs-cos helper is checked support only.  It is not the active raw-Omega
payload surface because it requires omegaLowerNonneg, which fails on early
finite chunks.  The active generator should use the sign-generic
ComponentChunkProofData route below.
```

Inactive direct abs-cos constructor surface on 2026-06-05:

```lean
RawOmegaATaylorModelCertificate.ValueBounds.of_raw_component_abs_cos_and_polynomial_term_bounds
RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds
RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds
RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds
RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds
```

Meaning:

```text
This direct abs-cos constructor family is also inactive for raw Step22 Omega
because it inherits the nonnegative-Omega restriction.  The active raw-Omega
payload uses sign-generic ComponentChunkProofData with direct
componentProductLower/componentProductUpper fields.
```

Contract cleanup:

```text
The proof-data schema no longer requires a rawComponentBounds aggregate field.
It now asks for the six component enclosure facts directly:
omegaLowerBound, omegaUpperBound, shapeSqLowerBound, shapeSqUpperBound,
cosLowerBound, and cosUpperBound.
```

Current proof-data record surface on 2026-06-05:

```lean
RawOmegaATaylorModelCertificate.AbsCosComponentTermBounds
RawOmegaATaylorModelCertificate.AbsCosComponentTermBounds.toValueBounds
RawOmegaATaylorModelCertificate.AbsCosChunkProofData
RawOmegaATaylorModelCertificate.AbsCosChunkProofData.valid
```

Meaning:

```text
The next generated Lean payload can now emit one checked record per chunk
instead of a long local proof script for every Valid constructor call.  The
records collect the schema fields, derive ValueBounds, and then derive
cert.Valid through a checked wrapper.
```

Current Lean-emitter guard on 2026-06-05:

```text
script:
  q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_lean.py

report:
  q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_lean_emitter.{json,md}

status:
  missing_proof_data_no_lean_emitted

counts:
  families = 4
  distance rows = 92
  chunk cells = 2392
  complete cells = 0
  missing cells = 2392
  out_lean_written = false
```

Meaning:

```text
The emitter route is now protected.  It will not create the generated Lean
payload import until the proof-data schema is actually complete.  This keeps the
master goal honest: the next closure step is real rational Taylor/model proof
data, not a cosmetic Lean file.
```

Current renderer refinement on 2026-06-05:

```text
proof-data schema now requires:
  chunkLower
  chunkUpper

Lean helper added:
  RawOmegaAChunkTaylorPayload.chunkValueFromFin26_apply

emitter complete path:
  implemented

current skeleton status:
  missing_proof_data_no_lean_emitted
  complete_cells = 0
  missing_cells = 2392
  out_lean_written = false
```

Meaning:

```text
The next generator must produce actual chunk bounds as well as the model
comparison proofs.  When that proof-data is complete, the emitter writes the
generated PayloadFin import, which must then be checked by Lean before Step33A.1-A
can consume it.
```

Current probe-seed refinement on 2026-06-05:

```text
seed source:
  rawomega_a_chunk_integral_probe_all_256.json

seed output:
  a_chunk_taylor_payload_probe_seed.{json,md}

seeded chunk bounds:
  2392 / 2392

proof fields populated:
  0

Lean emitted:
  false
```

Meaning:

```text
The current best proof-data starting point is no longer the empty skeleton but
the probe seed.  It contains candidate chunkLower/chunkUpper values only.  The
remaining generator work is still proof-bearing Taylor/model data.
```

Current geometry seed refinement on 2026-06-05:

```text
seed output:
  a_chunk_taylor_payload_geometry_seed.{json,md}

filled for all 2392 chunks:
  center
  radius
  radiusNonneg
  radiusLeft
  radiusRight

still missing for all 2392 chunks:
  degree
  coeff
  remainder
  analytic component bounds
  polynomial term bounds
  integral comparison proofs

Lean emitted:
  false
```

Meaning:

```text
Endpoint geometry is no longer part of the hard gap.  The remaining gate is the
actual Taylor/model proof data needed by PayloadFin.
```

Current row-sum seed refinement on 2026-06-05:

```text
seed output:
  a_chunk_taylor_payload_row_sum_seed.{json,md}

seeded rows:
  lowerSum = 92 / 92
  upperSum = 92 / 92

remaining row-sum gaps:
  row.lowerSum = 0
  row.upperSum = 0
  row-sum failures = 0

target refresh:
  local target refresh rows = 71
  A CSV / ARadius / radius-floor / LDL changed = no

Lean emitted:
  false
```

Meaning:

```text
The row-sum arithmetic seed layer is now complete for all 92 rows on both
sides, after a local serialized-row target refresh that is Lean-checked by the
raw-Omega arithmetic import.  This is still not a proof payload.  The next
narrow action is real Taylor/model analytic fields for all 2392 chunks.
```

Current scale seed refinement on 2026-06-05:

```text
seed output:
  a_chunk_taylor_payload_scale_seed.{json,md}

filled for all 2392 chunks:
  scaleNonneg

shared Lean lemmas:
  RawOmegaAChunkIntegral.primaryK11Ell_div_pi_nonneg
  RawOmegaAChunkIntegral.controlK9Ell_div_pi_nonneg

still missing:
  degree
  coeff
  remainder
  analytic component bounds
  polynomial term bounds
  diff/integral comparison proofs

Lean emitted:
  false
```

Meaning:

```text
The current best proof-data starting point is the scale seed.  It removes one
global repeated proof field without pretending that the analytic Taylor/model
certificate exists yet.
```

## Hard Stops

```text
no sorry
no admit
no exact?
no fake axiom
no unsafe
no theorem weakening
no row crawl
no entry crawl
no A CSV / ARadius / radius-floor / LDL mutation as proof patch
no Q3.Main before local gates are theorem-complete
no H1/PO3 route unless explicitly requested
```

## Current Seed Checkpoint -- 2026-06-05 Cosine Envelope

Current cosine-envelope seed refinement:

```text
seed output:
  a_chunk_taylor_payload_cos_seed.{json,md}

filled for all 2392 chunks:
  cosLower
  cosUpper
  cosLowerBound
  cosUpperBound

shared Lean lemmas:
  RawOmegaAChunkIntegral.cos_neg_one_le_mul
  RawOmegaAChunkIntegral.cos_mul_le_one

remaining proof-producing target:
  degree / coeff / remainder
  omega and shape-square enclosures
  sign-generic raw component/product bounds
  polynomial term bounds
  diff/integral comparison proofs

Lean emitted:
  false
```

The current best proof-data starting point is now:

```text
a_chunk_taylor_payload_cos_seed.json
```

## Current Surface Correction -- 2026-06-05 Generic Component Product

The payload surface is now sign-generic:

```text
RawOmegaATaylorModelCertificate.ComponentChunkProofData
```

Reason:

```text
The old AbsCosChunkProofData route required omegaLowerNonneg.  That is not a
valid global requirement for raw Step22 Omega chunks.  Product signs must be
handled by generated interval-product proofs per cell.
```

Current required product fields:

```text
componentProductLower
componentProductUpper
```

No longer required by the guarded payload contract:

```text
componentProductAbsLower
componentProductAbsUpper
omegaLowerNonneg
shapeSqLowerNonneg
cosAbsLower
cosAbsUpper
scaleNonneg
```

Current starting point remains:

```text
a_chunk_taylor_payload_cos_seed.json
```

## Current Product Receiver -- 2026-06-05 Direct Abs Box

The current product receiver supersedes both the stale nonnegative-Omega wording
and the intermediate corner-packet route for this raw-Omega route.

Checked Lean receiver:

```lean
RawOmegaATaylorModelCertificate.product_bounds_of_scale_abs_box
```

Generator contract:

```text
For each cell, emit direct:
  componentProductLower
  componentProductUpper

Corner packets remain fallback support only:
  componentProductCornerLowerLLL..componentProductCornerLowerUUU
  componentProductCornerUpperLLL..componentProductCornerUpperUUU
```

The active product seed fills the universal `hProductLower/hProductUpper`
fields consumed by:

```lean
RawOmegaATaylorModelCertificate.ComponentChunkProofData
```

Current status:

```text
PayloadFin not closed.
Step33A.1-A not closed.
Next proof-producing work:
  generate Taylor/model data
  generate Taylor polynomial/remainder and term bounds
  generate diff/integral comparisons
```

## Current Pro/Louise Route Override -- 2026-06-05

The open Pro/Louise browser tab was re-read after the product-corner checkpoint.
Visible decision:

```text
CHOSEN: S.
Do not continue payload generation as the semantic route.
Do not prove rawStep22A = centeredBSplineArchKernelProfile.
Use the upstream finite Weil C / assembler sign-location route.
```

Repo-real integration has already refined S to the raw-Omega route-A receiver:

```lean
step22PositiveAxisOmegaFiniteWeilKernelReceiver
primaryK11RawOmegaFiniteWeilMatrixModel
controlK9RawOmegaFiniteWeilMatrixModel
ActiveRawOmegaCoeffEntryHboxCert
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_entryHboxCert
psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs
```

Current live goal override:

```text
Do not treat PayloadFin generation as the semantic route target.
Treat it only as optional backend support for producing
RawOmegaADirectTailWindowInputs.

The active landing surface is:
  RawOmegaADirectTailWindowInputs
  -> raw-Omega entry hbox cert
  -> raw-Omega finite analytic positivity
  -> raw-Omega singleton DirectedFamily handoff
```

Hard guard:

```text
no ActiveCenteredCoeffEntryHboxCert reroute
no centered positive-A payload restart
no Q3.a_star migration
no A CSV / ARadius / radius-floor / LDL mutation
no Q3.Main
no H1/PO3
```

## Current Route Checkpoint -- 2026-06-05

The old Louise theorem name

```lean
centeredBSplineFiniteWeilCProfile_eq_step22PositiveAxisOmega_sub_primeProfile
```

is not the live theorem against the existing centered assembler.  Lean already
reduced that local centered-C statement to the false local Arch equality:

```lean
centeredBSplineFiniteWeilCProfile_eq_step22PositiveAxisOmegaCProfile_iff_archProfile_eq
```

The repo-real S/A route is the raw-Omega finite Weil receiver:

```lean
step22PositiveAxisOmegaCMatrix_eq_matrixSub
step22PositiveAxisOmegaWeilForm_eq_quadFormC_of_rawOmegaArchReceiver
step22PositiveAxisOmegaFiniteWeilKernelReceiver
primaryK11RawOmegaFiniteWeilMatrixModel
controlK9RawOmegaFiniteWeilMatrixModel
```

So the active target is not to prove a centered-C equality.  The active target
is to finish the generated analytic raw-Omega A input feeding:

```lean
RawOmegaADirectTailWindowInputs
```

then:

```text
RawOmegaADirectTailWindowInputs
-> ActiveRawOmegaCoeffEntryHboxCert
-> PsdStep33RawOmegaFiniteAnalyticPositivity
-> PsdStep33RawOmegaSingletonDirectedFamilyHandoff
```

Tail-remainder guard:

```text
Do not try to fill the 46 tailRemainderAbs fields only by destructing
step22OmegaArchWeight_linear_growth.
```

Reason:

```text
step22OmegaArchWeight_linear_growth ultimately depends on the existential
axiom Q3.a_star_linear_growth.  It gives some C0/C1 but no concrete numeric
majorant.  The generated tailRemainderRadius fields are concrete small
rational constants, so a Lean row proof needs either:

1. a concrete numeric Omega-growth-majorant certificate, or
2. direct tail-window analytic remainder certificates.
```

Preferred next proof-producing route:

```text
Use the direct tail-window analytic route already wired by
PrimaryK11RawOmegaADirectTailWindowAnalyticPayload /
ControlK9RawOmegaADirectTailWindowAnalyticPayload, where
step22PositiveAxisOmegaATail_abs_le_of_tailWindowIntervalCert consumes
hTailWindowLower, hTailWindowUpper, and hTailRemainder.

If a numeric global growth majorant is introduced later, it must be a separate
concrete certificate, not an implicit use of the existential linear-growth
axiom.
```

## Current Tail-Remainder Refinement -- 2026-06-05

The tail-window route above has now been compressed by a checked raw-Omega
log-tail helper layer.

Checked Lean surface:

```lean
step22PositiveAxisOmegaATail_abs_le_of_logOmegaFullTransformTailMajorant
primaryK11RawOmegaATailRemainder_abs_le_of_logOmegaFullTransformTailMajorant
controlK9RawOmegaATailRemainder_abs_le_of_logOmegaFullTransformTailMajorant
```

Current exact missing proof-data:

```text
46 tailRemainderAbs rows remain missing, but they should not be proved by hand.
They are reduced to:
  hMajorantInt
  hOmega: concrete |step22OmegaArchWeight eta| <= omegaFactor * log(3*eta)
          for eta > 520
  hIntegral: generated integral-majorant <= tailRemainderRadius comparisons
```

Louise confirmed the same compression route:

```text
A-first, but not 46 analytic proofs.
Use one common analytic helper, two block-level tail theorems, and generated
rational comparisons.
```

Next local action:

```text
Prove or generate the concrete Omega/log majorant and integral-comparison
proof-data layer, then instantiate the primary/control tailRemainderAbs facts
for PayloadFin.toDirectTailWindowInputs.
```

Guard from local search:

```text
Do not instantiate hOmega by blindly reusing a_star_abs_le_ten_logOmega_after_520.
The bridge step22OmegaArchWeight_eq_neg_inv_twoPi_aStar evaluates
Q3.a_star (eta / (2*pi)); eta > 520 does not imply eta/(2*pi) > 520.
```

Checked update:

```text
hOmega is now closed by:
  step22OmegaArchWeight_abs_le_ten_logOmega_after_520

This theorem uses the lower-threshold Stieltjes envelope at eta/(2*pi) > 1.
```

Remaining immediate proof-data:

```text
hMajorantInt
hIntegral generated integral-majorant <= tailRemainderRadius comparisons
```

Checked update:

```text
hMajorantInt is now closed by:
  primaryK11RawOmegaATailLogMajorant_integrable_after_520
  controlK9RawOmegaATailLogMajorant_integrable_after_520
```

Remaining immediate proof-data:

```text
hIntegral generated integral-majorant <= tailRemainderRadius comparisons
```

Checked update:

```text
hIntegral is now closed by:
  primaryK11RawOmegaATailLogMajorant_integral_le_tailRemainderRadius_after_520
  controlK9RawOmegaATailLogMajorant_integral_le_tailRemainderRadius_after_520

The direct raw-Omega tail remainder is now structural checked support:
  primaryK11RawOmegaATailRemainder_abs_le_generated
  controlK9RawOmegaATailRemainder_abs_le_generated

PayloadFin.toDirectTailWindowInputs supplies these structural facts internally.
The active generator contract no longer contains tailRemainderAbs row fields.
Current live frontier:
  RawOmegaAChunkTaylorPayload.PayloadFin
  2392 chunk-cell Taylor/model analytic certificates
  92 row lowerSum/upperSum comparisons already seed-checked, pending final
  generated Lean payload consumption
```

## Current Product/Scale Checkpoint -- 2026-06-05

The active product receiver surface is sign-generic and scale-interval aware:

```lean
RawOmegaATaylorModelCertificate.ComponentChunkProofData
RawOmegaATaylorModelCertificate.product_bounds_of_scale_interval_and_sixteen_corners
```

Checked family scale interval:

```text
9/100 <= primaryK11Ell / Real.pi <= 1/10
9/100 <= controlK9Ell / Real.pi <= 1/10
```

Seed status:

```text
scaleLower/scaleUpper/scaleLowerBound/scaleUpperBound:
  2392 / 2392 cells

cosLower/cosUpper/cosLowerBound/cosUpperBound:
  2392 / 2392 cells

out_lean_written:
  false
```

Next proof-producing target:

```text
Generate the scale-corner product comparisons:
  componentProductScaleCornerLowerLLLL..UUUU
  componentProductScaleCornerUpperLLLL..UUUU

Then continue:
  taylor_model_data
  omega_shape_enclosures
  polynomial_value_bounds
  diff_integral_comparisons
```

## Current Shape-Square Checkpoint -- 2026-06-05

Checked support:

```lean
RawOmegaAChunkIntegral.centeredBSplineImagTransformSqGlobalMajorant
RawOmegaAChunkIntegral.centeredBSplineImagTransformRealClosedForm_sq_nonneg
RawOmegaAChunkIntegral.centeredBSplineImagTransformRealClosedForm_sq_le_globalMajorant
```

Seed status:

```text
shapeSqLower/shapeSqUpper/shapeSqLowerBound/shapeSqUpperBound:
  2392 / 2392 cells

out_lean_written:
  false
```

The shape-square component now uses the checked structural sinc envelope:

```text
shapeSqLower = 0
shapeSqUpper = centeredBSplineImagTransformSqGlobalMajorant k
```

This reduces the active `omega_shape_enclosures` group to only the Omega
component fields:

```text
omegaLower
omegaUpper
omegaLowerBound
omegaUpperBound
```

Next proof-producing target:

```text
Add finite-window `step22OmegaArchWeight` enclosures:
  omegaLower
  omegaUpper
  omegaLowerBound
  omegaUpperBound

Then generate the scale-corner product comparisons:
  componentProductScaleCornerLowerLLLL..UUUU
  componentProductScaleCornerUpperLLLL..UUUU
```

## Current Omega Checkpoint -- 2026-06-05

Closed the shared log-Omega component enclosure for all chunks after the first
finite chunk.

Checked support:

```lean
RawOmegaAChunkIntegral.step22OmegaArchWeight_abs_le_ten_logOmega_after_ten
RawOmegaAChunkIntegral.step22OmegaArchWeight_abs_le_ten_logOmega_right_on_Ioc
RawOmegaAChunkIntegral.step22OmegaArchWeight_neg_ten_logOmega_right_le_on_Ioc
RawOmegaAChunkIntegral.step22OmegaArchWeight_le_ten_logOmega_right_on_Ioc
```

Payload state:

```text
Omega seeded cells = 2392 / 2392
omega_shape_enclosures remaining = 0
raw_product_bounds remaining = 0
PayloadFin emitted = false
```

This means the Omega and raw-product component layers are no longer the active
blocker.  The compact first finite chunk was closed with:

```text
RawOmegaAChunkIntegral.step22OmegaArchWeight_neg_twoHundred_le_on_Ioc_zero_ten
RawOmegaAChunkIntegral.step22OmegaArchWeight_le_twoHundred_on_Ioc_zero_ten
```

Next exact target:

```text
Step33A.1-A.rawOmegaTaylorPayload.TaylorModelData
```

Goal:

```text
fill the remaining rational Taylor/model fields:
  taylor_model_data
  polynomial_value_bounds
  diff_integral_comparisons
```

Current compressed polynomial contract:

```text
The generator should prefer the direct polynomial value route:

  polyLower
  polyUpper
  polynomialLowerBound
  polynomialUpperBound

feeding:

  RawOmegaATaylorModelCertificate.ComponentValueChunkProofData

instead of the older termLower/termUpper + PolynomialTermBounds +
polyLowerSum/polyUpperSum packet, unless direct polynomial value proofs fail.
```

Current grouped missing fields after Omega/product/direct-polynomial
compression:

```text
taylor_model_data = 9568
polynomial_value_bounds = 9568
diff_integral_comparisons = 9568
```

## Runtime Checkpoint -- 2026-06-05 Taylor/model refined-grid route

The current multistep goal is unchanged:

```text
Step33A -> Step33B -> Step33C -> Step34 -> Step35 -> Q3 mainline wrapper
```

The current executable front is now narrower:

```text
Step33A.1-A.rawOmegaTaylorPayload.TaylorModelData
```

Already closed for this A payload front:

```text
Omega component enclosures: 2392 / 2392 cells
raw product bounds: 2392 / 2392 cells
row lowerSum/upperSum fields: 92 / 92 rows
structural tail remainder handoff: checked support, not a PayloadFin row field
direct polynomial value receiver: checked support
```

Remaining generated proof-data fields:

```text
degree / coeff / remainder / remainderNonneg
polyLower / polyUpper / polynomialLowerBound / polynomialUpperBound
diffLower / diffUpper / integralLower / integralUpper
```

Latest diagnostic route signal:

```text
a_refined_grid_width_accounting_degree16_decimal_split100_tail20:
  first finite chunk split100, remaining finite chunks split10,
  tail chunks split20,
  exceeds_recorded_slack = 0
```

This is not proof data and must not be imported by Lean.  It is the current
engineering signal for the next fail-closed generator step:

```text
build a refined-grid Taylor/model worklist,
emit rational degree/coeff/remainder and direct polynomial/diff/integral
proof fields only when the completeness guard passes,
then fold the generated RefinedPayloadFin into RawOmegaADirectTailWindowInputs.
```

The open Pro/Louise browser tab was read.  The previous complete answer still
described the now-superseded product-bounds layer; the new post-product query
has no completed route answer yet.  Continue locally from the active monitor
unless Louise later returns a concrete contradiction or a strictly better
Lean-checkable theorem shape.

Runtime sanity:

```text
claude model check returned Claude Opus 4.7 (1M context)
```

## Checked Receiver Checkpoint -- 2026-06-05 refined subchunks

The refined-grid route now has local Lean support.

Checked theorem names:

```lean
RawOmegaAChunkIntegral.rawOmegaAWindowPartBoundsCert_of_taylorModelSubchunkCertificates
RawOmegaAChunkIntegral.rawOmegaAWindowPartBoundsCert_of_taylorModelSubchunkCertificates_bounds
```

Meaning:

```text
Keep the outer 26 parent chunks.
Prove each parent chunk by folding N uniform refined Taylor subchunk certs.
Feed the folded parent WindowPartBoundsCert into the existing raw-Omega
ChunkedRange/Payload path.
```

Current local recommendation:

```text
Route A:
  parent 26 chunks outside,
  refined subchunks inside each hard parent chunk,
  parent lower/upper = subchunk sums or slack-adjusted sum bounds,
  then RefinedPayloadFin/toDirectTailWindowInputs path.
```

Checked refined landing surface:

```lean
RawOmegaAChunkTaylorPayload.RefinedPayloadFin
RawOmegaAChunkTaylorPayload.RefinedPayloadFin.toDirectTailWindowInputs
```

Next generator target:

```text
emit refined subchunk Taylor/model proof-data and parent fold fields:
  subDegree / subCoeff / subRemainder / subRemainderNonneg
  subPolyLower / subPolyUpper / subPolynomialLowerBound / subPolynomialUpperBound
  subDiffLower / subDiffUpper / subIntegralLower / subIntegralUpper
  parentLowerSum / parentUpperSum comparisons
```

The exact field names may be adjusted to the emitter schema, but the semantic
shape should remain: refined subchunk certificates first, parent fold second,
outer 26-row receiver last.

Current refined proof-data skeleton:

```text
a_chunk_taylor_payload_refined_subchunk_proof_data_skeleton.{json,md}
status = structural_skeleton_seeded_missing_analytic_fields
```

Explicit missing groups:

```text
taylor_model_data = 120060
polynomial_value_bounds = 160080
diff_integral_comparisons = 160080
parent_fold_comparisons = 4784
```

Next proof-producing generator pass:

```text
Fill these analytic groups in the refined skeleton, then add a guarded
RefinedPayloadFin emitter that refuses Lean output unless all missing groups
are zero.
```

Current refined emitter guard:

```text
a_chunk_taylor_payload_refined_subchunk_lean_emitter.{json,md}
status = missing_analytic_fields_no_lean_emitted
outLeanWritten = false
missingTotal = 445004
```

The intended generated Lean file must remain absent until the missing groups
are zero:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaARefinedSubchunkGeneratedPayloadImport.lean
```
