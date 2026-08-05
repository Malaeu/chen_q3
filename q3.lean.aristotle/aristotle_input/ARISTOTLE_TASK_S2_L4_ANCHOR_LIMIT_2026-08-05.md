# S2-L4′ — an anchored locally-uniform limit keeps the anchor value

> ## ⛔ SUPERSEDED — DO NOT SUBMIT (2026-08-05, same day)
> Closed locally on the Linux body instead, once the Mathlib cache was in place.
> Production file: `Q3/Proofs/RouteB/S2GaugeNonvanishing.lean` — generic `limit_eq_anchor`
> plus the consumer form `limit_at_zero_ne_zero`, which already discharges
> `D.limit 0 ≠ 0` against the proved `centeredXi_zero_ne_zero`.
> `lake build` PASS, axioms exactly `[propext, Classical.choice, Quot.sound]`, no sorry.
> Kept for the record only.

> **TRANSPORT ARMOUR (lesson of 054.1).** Aristotle *input*, not a production artifact.
> Materialization into the project goes ONLY through the Codex fill-sorries pipeline, into a
> real project file with real project imports, after owner per-action OK. A proof that
> invents surrogate structures instead of the generic statement below is REJECTED.
>
> Address: `G6 · SlotS2 · S2-L4′`. Route B = CHALLENGER / NOT_RH. Bus 010 VOID.

## Goal

Prove, with `import Mathlib` only:

```lean
theorem limit_eq_anchor {F : ℕ → ℂ → ℂ} {L : ℂ → ℂ} {S : Set ℂ} {z a : ℂ}
    (hconv : TendstoLocallyUniformlyOn F L Filter.atTop S) (hz : z ∈ S)
    (hanchor : ∀ k, F k z = a) : L z = a
```

## Why this statement

`SlotS2` needs a nonzero constant `c`. In the project, `SlotAnchor` already gives
`∀ i, C.Pstar.family i anchor = centeredXi anchor`, and `centeredXi 0 ≠ 0` is now a proved
project theorem (`Q3/Proofs/RouteB/CenteredXiZeroNonzero.lean`, `centeredXi_zero_ne_zero`,
sorry-free). What is missing is the completely generic bridge: a locally uniform limit of
functions that all take the same value at an interior point takes that value too. Once this
is available, `D.limit 0 = centeredXi 0 ≠ 0` is immediate and `c ≠ 0` costs no new analysis.

The statement is deliberately kept **generic** (no project structures, no `ClusterData`,
no `centeredXi`) so it is reusable and so nothing in it can drift with the project.

## Available lemmas (verified present in the pinned Mathlib — use, do not reprove)

- `TendstoLocallyUniformlyOn.tendsto_at (hf : TendstoLocallyUniformlyOn F f p s) {a : α}
  (ha : a ∈ s) : Tendsto (fun i => F i a) p (𝓝 (f a))`
  (`Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean:238`)
- `tendsto_nhds_unique` (needs `Filter.atTop` `NeBot` on ℕ — instance available)
- `tendsto_const_nhds`

## Proof strategy (3 steps)

1. Apply `hconv.tendsto_at hz` to obtain `Tendsto (fun k => F k z) atTop (𝓝 (L z))`.
2. Rewrite with `hanchor`, turning the sequence into the constant sequence `fun _ => a`.
3. The constant sequence also tends to `a`; conclude by `tendsto_nhds_unique` and `symm`.

## Candidate proof (UNVERIFIED — this machine has no Mathlib build; treat as a hint)

```lean
theorem limit_eq_anchor {F : ℕ → ℂ → ℂ} {L : ℂ → ℂ} {S : Set ℂ} {z a : ℂ}
    (hconv : TendstoLocallyUniformlyOn F L Filter.atTop S) (hz : z ∈ S)
    (hanchor : ∀ k, F k z = a) : L z = a := by
  have h1 : Filter.Tendsto (fun k => F k z) Filter.atTop (nhds (L z)) := hconv.tendsto_at hz
  simp only [hanchor] at h1
  exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
```

## Policy

- Keep it generic: no `ClusterData`, no `centeredXi`, no project imports.
- No `aesop`. Explicit lemma names.
- Target: under 15 lines. If it closes in three, that is the correct answer, not a red flag —
  the value of this leaf is that it is small and reusable, not that it is hard.

## Generality note (do NOT over-restrict)

Do not add hypotheses such as continuity of `L`, holomorphy, or openness of `S`. The
statement is true as written for any `S` and any point of `S`; strengthening the hypotheses
makes it unusable at the consumer site.

## Consumer (where this plugs in)

Applied at `z = 0` with `F = selectedFamily C`, `S = centeredCriticalStrip`,
`a = centeredXi 0`, `hconv = D.convergence`, `hanchor` from `SlotAnchor`. Yields
`D.limit 0 = centeredXi 0`, which combined with the proved `centeredXi_zero_ne_zero` gives
`D.limit 0 ≠ 0`. Touches none of the frozen G2/CCM files or any bus file.

## Falsification plants (must fire on the returned proof)

- **P-L4-1** drop `hz : z ∈ S` → must break (a limit says nothing off the set).
- **P-L4-2** weaken `∀ k, F k z = a` to `∃ k, F k z = a` → must break.
