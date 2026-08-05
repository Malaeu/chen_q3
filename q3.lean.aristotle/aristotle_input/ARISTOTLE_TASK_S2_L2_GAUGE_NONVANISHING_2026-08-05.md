# S2-L2 — the ζ→Ξ gauge is zero-free on the open critical strip

> ## ⛔ SUPERSEDED — DO NOT SUBMIT (2026-08-05, same day)
> Closed locally on the Linux body instead, once the Mathlib cache was in place.
> Production file: `Q3/Proofs/RouteB/S2GaugeNonvanishing.lean`
> (`xiGauge_ne_zero_of_mem_strip`, plus the stronger `riemannXi_eq_xiGauge_mul_riemannZeta`
> and the centered forms). `lake build` PASS, axioms exactly
> `[propext, Classical.choice, Quot.sound]`, no sorry.
> The production version is **better than this brief**: it defines the gauge through
> Mathlib's `Gammaℝ` and reuses the project's existing `riemannXi_eq_completedRiemannZeta`
> and `completedRiemannZeta_eq_Gamma_mul_riemannZeta` instead of re-deriving
> `π ^ (-s/2) * Γ (s/2)` by hand. Kept for the record only.

> **TRANSPORT ARMOUR (lesson of 054.1).** This file is an Aristotle *input*, not a
> production artifact. The returned proof is materialized into the project ONLY via the
> Codex fill-sorries pipeline, into a real project file with real project imports, and
> only after owner per-action OK. A returned proof that invents its own surrogate
> definitions instead of the ones below is REJECTED.
>
> Address: `G6 · SlotS2 · S2-L2`. Route B = CHALLENGER / NOT_RH. Bus 010 VOID.
> Nothing here promotes a route or claims RH.

## Goal

Prove, with `import Mathlib` only:

```lean
theorem gauge_ne_zero_of_mem_strip (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    gauge s ≠ 0
```

where `gauge` is the definition given below.

## Why this statement

`SlotS2` in `Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean` demands a multiplier
`gamma : ℂ → ℂ` that is **nonvanishing on the open centered strip**. The Müntz branch
produces `ζ(w) · Mellin h (w)`, while the roof consumes `centeredXi`. The two are related by
the classical completion `ξ(s) = (s(s−1)/2) · π^{−s/2} · Γ(s/2) · ζ(s)`; the bracket is the
gauge. Every candidate `gamma` factors through it, so its nonvanishing is the reusable brick.

Coordinates: the project uses `centeredXi z = riemannXi (1/2 + I*z)` on
`centeredCriticalStrip = {z | |z.im| < 1/2}`, which is exactly `Re s ∈ (0,1)` in the
`s`-variable. Hence the hypotheses `0 < s.re` and `s.re < 1`.

## Definitions (use these verbatim, do not restate)

```lean
import Mathlib

open Complex

noncomputable def gauge (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)
```

## Available lemmas (verified present in the pinned Mathlib — use, do not reprove)

- `Complex.Gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < re s) : Gamma s ≠ 0`
  (`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:454`)
- `Complex.Gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0`
  (same file, line 428 — the stronger form, only if the weaker one does not fit)
- `Complex.cpow_ne_zero_iff {x y : ℂ} : x ^ y ≠ 0 ↔ x ≠ 0 ∨ y = 0`
  (`Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean:49`)
- `Real.pi_ne_zero`
- `mul_ne_zero`, `div_ne_zero`, `two_ne_zero`

## Proof strategy (4 steps, no search needed)

1. `s ≠ 0` from `0 < s.re` (a zero complex number has zero real part).
2. `s - 1 ≠ 0` from `s.re < 1` (if `s = 1` then `s.re = 1`).
3. `(π : ℂ) ^ (-s/2) ≠ 0` by `cpow_ne_zero_iff`, left disjunct, `Real.pi_ne_zero`.
4. `Γ(s/2) ≠ 0` by `Gamma_ne_zero_of_re_pos`, since `(s/2).re = s.re / 2 > 0`.
Then unfold `gauge` and close with nested `mul_ne_zero` / `div_ne_zero`.

## Candidate proof (UNVERIFIED — this machine has no Mathlib build; treat as a hint)

```lean
theorem gauge_ne_zero_of_mem_strip (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    gauge s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination h
    rw [this] at h1; simp at h1
  have hpi : ((Real.pi : ℂ)) ^ (-s / 2) ≠ 0 := by
    rw [cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
  have hgamma : Complex.Gamma (s / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [Complex.div_re]
    simp
    linarith
  unfold gauge
  exact mul_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero hs0 hs1) two_ne_zero) hpi) hgamma
```

If step 4's `Complex.div_re` normalization is awkward, an acceptable alternative is
`Complex.Gamma_ne_zero` with `∀ m : ℕ, s/2 ≠ -m`, discharged by comparing real parts
(`(-m : ℂ).re ≤ 0 < (s/2).re`).

## Policy

- `suffices` for goal reduction; explicit lemma names in the final patch.
- Minimize `aesop` (≤ 1); prefer `simp`, `linarith`, `positivity`.
- No numerical bounds, no π-value estimates — this is a pure nonvanishing statement.
- Target: under 40 lines.

## Boundary conditions of the statement (do NOT weaken)

- The strip is **open**: `0 < s.re < 1` strictly. The factor `s(s−1)` vanishes exactly at
  `s = 0` and `s = 1`, i.e. at `z = ±i/2`, which are the strip's boundary points. A version
  proved on a closed strip is FALSE and will be rejected.
- Γ's poles sit at `s = 0, −2, −4, …`, all with `Re ≤ 0`, hence outside. Do not add
  hypotheses excluding them — `0 < s.re` already does.

## Consumer (where this plugs in)

`Q3/Proofs/RouteB/` — new file, imported by the future S2 assembly. It is a leaf: nothing in
the current chain imports it yet, and it touches none of the frozen G2/CCM files
(`CCMFiniteWeilCell13N2*`, `CCMFiniteWeilSourceMatrixN1`) or any bus file.

## Falsification plants (must fire on the returned proof)

- **P-L2-1** replace the open hypothesis `s.re < 1` by `s.re ≤ 1` → the statement must break
  at `s = 1` (gauge = 0 there).
- **P-L2-2** replace `Γ(s/2)` by `Γ(s/2 − 1)` → must break, since `Re(s/2 − 1) < 0` admits a pole.
