# Worker Report — `proshka_h1_po4_same_sign_boundary_2026_03_18`

## Status

Done.

## What I read

Required control files:

1. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`
2. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`
3. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md`
4. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_h1_po4_same_sign_boundary_2026_03_18/node.md`

Supporting files from the request node:

1. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md`
2. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_plus_boundary_inventory_2026_03_15.md`
3. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_proof_obligation_table_2026_03_16.md`
4. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h_bridge_three_doors_macro_map_2026_03_16.md`
5. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_external_foundations_split_2026_03_16.md`

## What I claim

### 1. Best theorem-grade receiver for `PO4`

The minimal primary statement should stay as a pure boundary-identification
lemma:

```tex
\textbf{PO4a.}\qquad \mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}.
```

This is the right receiver because:

- Door 1 is already frozen as calibration, so `PO4` must not reopen `(+,-)`;
- the proof-obligation table already fixes `PO4` as same-sign boundary
  identification, not cap separation and not compression;
- the `(++)` inventory already isolates the correct contrast:
  boundary may survive, cap may survive, bulk must not survive unnamed.

So `PO4` should identify the same-sign survivor as a real operator object, not
as a numerical residual and not as a floating matrix-fit remainder.

### 2. Minimal boundary/cap split after `PO4`

The cleanest post-`PO4` shape is:

```tex
\mathcal D_{a,N}^{++}
=
H_a^{\mathrm{ss}}
+ \mathcal D_{a,\mathrm{cap}}^{++}.
```

This is better than jumping directly to
`H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}`, because `PO4` should name the
boundary channel but should not consume `PO5`.

Operational meaning:

- `PO4` freezes the same-sign survivor as boundary-type operator content;
- the leftover is carried only as the cap channel;
- bulk and compression do not belong to the `PO4` theorem receiver.

### 3. Admissible operator shapes for `H_a^{\mathrm{ss}}`

The support notes converge to one narrow acceptable list:

| Admissible operator source | Still acceptable at `PO4`? | Why |
| --- | --- | --- |
| Toeplitz-Hankel residue | yes | this is the cleanest classical same-sign boundary mechanism |
| commutator with cutoff / filtered shift | yes | same-sign boundary language remains operator-theoretic |
| short-range near-edge boundary term | yes | matches the current Door-2 phenotype without reopening bulk |
| unnamed moving matrix residual | no | route-kill / near-route-kill |
| rank/basis-fit explanation | no | forbidden as theorem content |
| generic bulk mismatch | no | contradicts the current same-sign boundary/cap picture |

So the route does not need to choose one of the first three in advance, but it
does need to land on one named operator channel.

### 4. Sharp route-kill condition

The `P4` route dies if the same-sign survivor remains only an unnamed moving
residual. The exact bad form is:

```tex
\mathcal D_{a,N}^{++}
=
\mathcal R_{a,N}^{++}
+ \mathcal D_{a,\mathrm{cap}}^{++},
\qquad
\mathcal R_{a,N}^{++}\neq 0,
```

with `\mathcal R_{a,N}^{++}` not identifiable as Toeplitz-Hankel,
commutator, or near-edge boundary operator.

This is the theorem-grade version of the Door-2 kill gate:

```text
if the same-sign survivor cannot be named as an operator source, the current
boundary/cap split loses its structural content.
```

At the phase level this is already a `P4` kill or near-route-kill, and if the
ambiguity persists into `PO5` then Door 2 fails outright.

### 5. Best handoff from `PO4` to `PO5`

The cleanest next move is exactly:

```tex
\textbf{PO5.}\qquad \mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}.
```

with explicit separation from `H_a^{\mathrm{ss}}`.

So the intended local theorem packet is:

1. `PO4`: identify the same-sign boundary object;
2. freeze the remainder as cap-only;
3. `PO5`: turn that cap remainder into explicit finite-dimensional cap data.

That preserves the intended asymmetry:

- `(+,-)` remains the calibration block;
- `(++)` carries the true surviving boundary object;
- cap is separated only after the boundary operator has been named.

## Exact deliverables created or updated

Updated only:

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_h1_po4_same_sign_boundary_2026_03_18/report.md`

No extra artifacts created.

## Open questions / blockers

No hard blocker at the report level.

One notation caution remains:

- the active notes mostly write `H_a^{\mathrm{ss}}`, while some support language
  still suggests an `N`-aware boundary mechanism;
- the orchestrator should freeze one notation and keep it stable before
  manuscript-level integration.

This is a notation choice, not a reason to delay `PO4`.

## Recommended next step for orchestrator

Update the active `PO4` artifact so that it presents:

1. the primary lemma `\mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}`;
2. the exact post-`PO4` split
   `\mathcal D_{a,N}^{++}=H_a^{\mathrm{ss}}+\mathcal D_{a,\mathrm{cap}}^{++}`;
3. the admissible operator-source table
   `Toeplitz-Hankel / commutator / near-edge`;
4. the route-kill condition as
   "unnamed same-sign moving residual";
5. the handoff line `PO5 := \mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}`.

That is the tightest theorem-grade receiver I would carry forward.
