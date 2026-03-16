# Worker report — `proshka_h1_po2_cross_sign_bulk_2026_03_16`

## Status

Done. No extra artifacts created.

## What I read

Required control files:

1. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`
2. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`
3. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md`
4. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_h1_po2_cross_sign_bulk_2026_03_16/node.md`

Supporting files from the request node:

1. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po1_tail_defect_attack_2026_03_16.md`
2. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md`
3. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_proof_obligation_table_2026_03_16.md`
4. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_minus_cancellation_ledger_2026_03_15.md`
5. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_raw_entry_reduction_2026_03_08.md`
6. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`

## What I claim

### 1. Best theorem-grade receiver for `PO2`

The clean primary statement should stay as a pure bulk lemma:

```tex
\textbf{PO2a.}\qquad \mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

This is the right receiver because:

- `PO1` already froze the tail object `\mathcal D_{a,N}` and its sign split;
- `Main_closure.tex` already treats the filtered `(+,-)` family as a direct
  bulk identity target;
- the raw mismatch is already quarantined in the raw-entry note, so `PO2`
  should not weaken itself by reintroducing raw-level caveats.

The sharp acceptable equivalent form is:

```tex
\textbf{PO2b.}\qquad
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-}.
```

Interpretation:

- no genuine filtered bulk residue survives in `(+,-)`;
- every admissible remainder is already named and belongs to the later
  boundary/cap classification problem;
- compression is not part of `PO2`, because `PO2` lives at the tail-operator
  level and compression belongs later to `PO6`.

### 2. Best boundary/cap-only formulation

The cleanest formulation is not "there is some small correction", but exactly:

```tex
\mathcal D_{a,N}^{+-}
\in
\{\text{boundary channel}\}
\oplus
\{\text{finite cap channel}\}.
```

In theorem language this should still be written concretely as

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-},
```

with the following meaning frozen already at `PO2`:

- `\mathcal D_{a,\partial}^{+-}` may depend on the tail cutoff and is the only
  admissible non-cap dynamic remainder;
- `\mathcal D_{a,\mathrm{cap}}^{+-}` is finite-dimensional cap content and is
  the only admissible non-boundary static remainder;
- anything else is not a "weaker version" of the same theorem, but a different
  defect story.

### 3. Sharp route-kill condition

The exact kill event is:

```tex
\exists\ \mathcal R_{a,N}^{+-}\neq 0
\quad\text{such that}\quad
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-}
+ \mathcal R_{a,N}^{+-},
```

where `\mathcal R_{a,N}^{+-}` cannot be reclassified as either boundary or cap.

This is the theorem-grade version of "unnamed bulk residue kills the route".
The route is dead already at `PO2` if the residual:

- persists as genuine cross-sign bulk content;
- is not absorbed by the boundary channel;
- does not factor through the finite cap channel.

So the kill condition should be stated operationally as:

```text
any nonzero cross-sign remainder outside the named boundary/cap channels is a
route-kill for the current H1 reset.
```

### 4. Must vanish / may remain / route-kill table

| Channel | Status at `PO2` | Comment |
| --- | --- | --- |
| `\mathcal D_{a,\mathrm{bulk}}^{+-}` | must vanish | this is the primary lemma |
| `\mathcal D_{a,\partial}^{+-}` | may remain temporarily | this is exactly the handoff target for `PO3` |
| `\mathcal D_{a,\mathrm{cap}}^{+-}` | may remain explicitly | admissible fallback, but not to be resolved inside `PO2` |
| compression term | not part of `PO2` | keep deferred to `PO6` |
| unnamed residual outside boundary/cap | route-kill | this breaks the whole boundary/cap reset |

### 5. Should `PO2` mention cap explicitly?

Yes, but only in the fallback decomposition, not in the primary exact lemma.

Best split:

- primary `PO2` statement: `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- equivalent admissible fallback: `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`;
- cap analysis itself is postponed, not solved inside `PO2`.

Reason:

- if cap is omitted from `PO2` completely, the post-`PO2` remainder is too
  ambiguous and the worker/orchestrator loses the exact theorem fork;
- if cap is promoted too early as a proof target inside `PO2`, then `PO2`
  stops being the clean bulk lemma and starts eating `PO5`.

So the right posture is:

```text
name cap already in PO2; prove bulk vanishing in PO2; classify/settle cap later.
```

### 6. Best handoff from `PO2` to `PO3`

The cleanest handoff is one-line and asymmetric:

```tex
\textbf{PO3.}\qquad \mathcal D_{a,\partial}^{+-}=0.
```

Then the cross-sign branch becomes:

1. `PO2`: kill bulk;
2. `PO3`: kill boundary;
3. leftover, if any: explicit cap only;
4. later cap handling stays with the cap stage rather than contaminating the
   cross-sign bulk argument.

This is the best handoff because it preserves the intended route asymmetry:

- `(+,-)` is the calibration block that should collapse to exactness or
  cap-only;
- `(++)` remains the location where the real same-sign boundary story lives.

## Exact deliverables created or updated

Updated only:

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_h1_po2_cross_sign_bulk_2026_03_16/report.md`

No extra artifacts created.

## Open questions / blockers

No blocker at the report level.

One notation risk remains for the orchestrator artifact:
`PO2` should avoid introducing new pseudo-definitions of "boundary-local" or
"cap-factorizing" operators unless those names are frozen elsewhere. The safe
move is to keep the theorem statement at the level of named channels
`\mathcal D_{a,\partial}^{+-}` and `\mathcal D_{a,\mathrm{cap}}^{+-}`.

## Recommended next step for orchestrator

Update the active `PO2` artifact so that it presents:

1. the primary lemma `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
2. the exact equivalent fallback decomposition
   `\mathcal D_{a,N}^{+-}
    =\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`;
3. the explicit route-kill condition as "any residual outside boundary/cap";
4. the handoff line `PO3 := \mathcal D_{a,\partial}^{+-}=0`.

That is the tightest receiver I would take forward.
