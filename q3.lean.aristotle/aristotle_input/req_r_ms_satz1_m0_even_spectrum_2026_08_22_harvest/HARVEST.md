# Aristotle project 438ebdba-8eae-4e2c-a6b1-9df7a279e686 — harvest

Run ended `OUT_OF_BUDGET` after 3h40m, delivered `RequestProject.Main.sorry`
at one location. Not a completed proof; the deep run is over.

## Five mechanical repairs applied by the Linux body

1. `Spectrum.lean` — `tsum_eq_zero_add` exists only as dot notation
   (`hx.tsum_eq_zero_add`) in the pinned Mathlib v4.28.0; two call sites fixed.
2. `Spectrum.lean` (h5) — `norm_num` left a bare commutativity goal
   `9^k*81 = 81*9^k`; appended `; ring`.
3. `Spectrum.lean` (hstep) — an `nlinarith [hpow k, hA]` call replaced by the
   direct lemma `mul_le_of_le_one_right (hAp k) h5` it needed.
4. `Spectrum.lean` (hshiftA) — a natural-subtraction index (`k+1-1`) that
   `ring` cannot see through an opaque `c (...)` application; normalized with
   `simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]` before `ring`.
5. `Spectrum.lean` (hzero) — a bare `have hcongr := tsum_congr hterm` could
   not infer its implicit filter argument outside an expected-type context;
   merged into `rw [tsum_congr hterm]`.

None of the five touch the ODE, endpoint regularity, or eigenvalue theory.
Each was found by reading the exact failing goal and closed with the specific
lemma or rewrite it needed.

## Kernel result after repair

```
lake build   8030 jobs, success
#print axioms spheroidal_even_spectrum
  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` enters through exactly one declaration:

```lean
theorem spheroidal_spectrum_infinite (G : ℝ) :
    {Λ : ℝ | RegularEvenSpheroidalEigenvalue G Λ}.Infinite := by
  sorry
```

## What is proved (kernel-verified, no sorry)

- the degenerate Green/Wronskian identity with the actual endpoint limits
- one-dimensionality of a regular even eigenspace at a fixed eigenvalue
- separation of eigenvalues
- local finiteness of the spectrum on every bounded set
- the final `StrictMono` sequence assembly (conditional on infiniteness)
- all registered plants: G=0 gives Lambda=0 on f=1, f=x (Lambda=2) excluded
  as odd, (3x^2-1)/2 gives Lambda=6

## What remains — the single named gap

```text
spheroidal_spectrum_infinite : the regular even spectrum is infinite
```

Not attempted here: this is exactly the boundary the judge's plants flagged as
the most likely load-bearing failure (`P_R_4`, probability 0.76). No
integration into Q3 sources; this stays Mathlib-only content pending the
judge's read.
