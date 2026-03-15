# Worker Report: `proshka_q_zeta_a2_plus_minus_2026_03_15`

## Status

- state: completed
- verdict: preferred theorem-grade shape for `(+,-)` is
  `bulk exact + no cross-sign boundary term + no extra compression term`,
  with only a cap-only fallback still admissible

## What I read

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/SPRINT_MONITOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_q_zeta_a2_plus_minus_2026_03_15/node.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/q_zeta_core_short_circuit_sprint_2026_03_15.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_minus_adapter_ledger_2026_03_15.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_minus_cancellation_ledger_2026_03_15.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/q_zeta_core_skeleton_2026_03_15.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`

## What I claim

### 1. Preferred theorem candidate for `(+,-)`

The clean theorem-grade target should be stated first at the infinite-tail
level and only then shadowed to finite sections.

Preferred infinite-tail statement:

```tex
\mathcal D_{a,N}^{+-}
:=
S_{a,\infty,N}^{+*}G_g[a]S_{a,\infty,N}^{-}
-\kappa_{+-}(a)\Delta_N^{+*}Q_\infty^{+-}\Delta_N^{-}
=
\mathcal C_a^{+-,\mathrm{cap}},
```

with

```tex
\mathcal C_a^{+-,\mathrm{cap}}
\text{ factoring through the finite-dimensional Suzuki cap }
A_a^{\mathrm{cap}}.
```

Preferred stronger version:

```tex
\mathcal C_a^{+-,\mathrm{cap}}=0.
```

So the finite-section theorem candidate is

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q_{M,N}^{+-}+E_{a,\mathrm{cap}}^{+-},
```

with the theorem-grade identification

```tex
E_a^{+-}=E_{a,\mathrm{cap}}^{+-},
\qquad
E_{a,\mathrm{bulk}}^{+-}=0,
\qquad
E_{a,\partial}^{+-}=0,
\qquad
E_{a,\mathrm{comp}}^{+-}=0.
```

Interpretation:

- `bulk exact` is the main claim;
- `boundary exact` is the real asymmetry claim;
- `compression exact` says `\widetilde Q_{M,N}` already absorbed the naive
  finite-section bookkeeping;
- only `cap-only` is allowed as a nonzero fallback, because it is the only
  correction channel already frozen by the current route and by the old
  `H2^f` tail/cap split.

This is the strongest shape consistent with all read materials:

- the old strongest filtered thesis in `Main_closure.tex` still points to
  exact filtered `(+,-)`;
- the local Day 1/Day 2 notes already isolate cross-sign exactness as the
  first honest adapter target;
- the sprint skeleton already freezes `(++)` as the place where the surviving
  same-sign boundary channel should live.

### 2. Preferred operator decomposition at the infinite-tail level

The clean split is not
`bulk + arbitrary structured correction`,
but

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\mathrm{bulk}}^{+-}
+\mathcal D_{a,\partial}^{+-}
+\mathcal D_{a,\mathrm{cap}}^{+-},
```

with preferred theorem values

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0,
\qquad
\mathcal D_{a,\partial}^{+-}=0,
\qquad
\mathcal D_{a,\mathrm{cap}}^{+-}=\mathcal C_a^{+-,\mathrm{cap}}.
```

The finite compression term should not appear at this infinite-tail level at
all. Its role is only the finite-section shadow bookkeeping, and the current
best reading is that this shadow also vanishes once the comparison object is
written as `\widetilde Q_{M,N}`.

So the recommended slogan is:

```text
(+,-) = bulk identity on the tail, with no cross-sign boundary channel,
and at most an explicit cap shadow.
```

### 3. Cancellation table: cross-sign block versus same-sign block

| channel | operator meaning | `(+,-)` | `(++)` |
| --- | --- | --- | --- |
| filtered bulk | true mismatch between the Suzuki tail operator and the filtered `Q` block | must vanish | expected to vanish as bulk; not the live obstruction |
| boundary / commutator / Toeplitz-Hankel | short-range near-edge same-sign channel produced by finite-side interaction | must vanish | may survive as the named same-sign term `H_a^{\mathrm{ss}}` |
| Suzuki cap | finite-dimensional complement after tail classification | preferred to vanish; if not, must remain explicit and finite-rank | allowed to survive as `C_a^{\mathrm{cap}}` |
| compression bookkeeping | pure finite-section artifact already absorbed by `\widetilde Q_{M,N}` | must vanish | should also not survive as an independent theorem term |

Equivalent theorem-level summary:

```tex
M^{+-}(a)-\kappa_{+-}(a)\widetilde Q^{+-}
=
E_{a,\mathrm{cap}}^{+-}
```

with preferred stronger value `E_{a,\mathrm{cap}}^{+-}=0`, whereas

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

That is the clean asymmetry:

- `(+,-)` is the adapter/calibration block;
- `(++)` is the genuinely hard same-sign block;
- the surviving boundary channel is same-sign, not cross-sign.

### 4. Exact contrast with the same-sign block `(++ )`

The crucial contrast is not merely “`(+,-)` is easier”.
It is sharper:

1. `(+,-)` should not carry an independent boundary/commutator theorem term.
2. `(++)` should carry exactly that kind of term.
3. Both blocks may still see the finite-dimensional cap, but only `(++)`
   should need a named same-sign boundary operator on top of it.

So the recommended theorem ladder for the next memo is:

```tex
\textbf{Cross-sign adapter:}\quad
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_{a,\mathrm{cap}}^{+-},
```

```tex
\textbf{Same-sign contrast:}\quad
M^{++}(a)=\kappa_{+-}(a)\widetilde Q^{++}+H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

with the preferred strict fork

- best case: `E_{a,\mathrm{cap}}^{+-}=0`;
- acceptable case: `E_{a,\mathrm{cap}}^{+-}` is explicit, finite-rank, and
  cap-only;
- failure case: a non-cap cross-sign boundary term survives.

### 5. Why this is the right theorem-grade shape

This shape is better than a generic “structured correction” statement because:

- it preserves the sprint asymmetry `(+,-)` first, `(++)` hard later;
- it isolates one exact vanishing claim that can actually be attacked:
  cross-sign boundary cancellation;
- it keeps the only permitted nonzero remainder inside the already-frozen
  Suzuki tail/cap split;
- it avoids reopening rank/basis language as theorem content.

## Exact deliverables created or updated

- updated:
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_q_zeta_a2_plus_minus_2026_03_15/report.md`
- new artifacts created: none

## Open questions / blockers

- The exact symbolic mechanism forcing
  `\mathcal D_{a,\partial}^{+-}=0`
  is still not written as a lemma in the local notes; this remains the main
  proof obligation.
- There is still one honest fork to settle:
  whether the cap contribution in `(+,-)` vanishes identically, or only
  factors transparently through `A_a^{\mathrm{cap}}`.
- One legacy sentence in `Main_closure.tex` describes `(+,-)` as
  “numerically the hardest family”, while the current sprint notes treat
  `(+,-)` as the stable anchor and `(++)` as the hard block. This does not
  affect the theorem shape above, but the wording is no longer aligned with the
  active sprint picture.

## Recommended next step for orchestrator

- Keep `A2` focused on one lemma-scale target:
  prove that the same-sign boundary / commutator / Toeplitz-Hankel channel
  cancels in the cross-sign pairing.
- If that lands, freeze the Day 2 theorem target exactly as
  `(+,-) = filtered bulk + cap-only fallback`,
  then move `A3` to the explicit inventory of `H_a^{\mathrm{ss}}` in `(++)`.
- If that lemma does not land cleanly, weaken only one notch:
  keep the same theorem shape but allow an explicit named cross-sign boundary
  operator and test whether it still factors through the cap.
