# D2g25 Fejer shrinking-target bridge

## Goal

Formalize a finite Fourier-analytic lemma that turns counting points in a very
small interval modulo `1` into control of exponential sums.

Work in a purely finite setting. Do **not** use any zeta-specific facts.

Let:

- `α : ℝ`
- `ε : ℝ` with `0 < ε` and `ε ≤ 1/4`
- `H : ℕ := ⌊1 / (2*ε)⌋`
- `Γ : Finset ℝ`
- `e(x) := Complex.exp (2 * Real.pi * Complex.I * x)`

Define:

- the shrinking-target count

```text
Aα(Γ, α, ε) := #{γ ∈ Γ : ‖α*γ‖ ≤ ε}
```

where `‖x‖` means distance from `x` to the nearest integer;

- the exponential sums

```text
Sα(j) := ∑ γ in Γ, e (j * α * γ)
```

- the Fejér kernel

```text
F_H(x) := ∑_{|j|<H} (1 - |j|/H) e(jx)
```

and also use the standard closed form

```text
F_H(x) = (1/H) * (sin(π H x) / sin(π x))^2.
```

## Target statement

Prove a theorem of the following shape:

```text
Aα(Γ, α, ε)
≤ C * ε * Γ.card + C * ε * ∑_{j=1}^{H-1} ‖Sα(j)‖
```

for some absolute constant `C`.

It is enough to prove this with any explicit absolute constant, for example
coming from `π^2`.

## Preferred explicit route

1. Define the Fejér kernel and prove it is nonnegative.
2. Prove the lower bound on the target arc:

```text
if ‖x‖ ≤ ε and H = ⌊1/(2ε)⌋, then F_H(x) ≥ (4/π^2) * H.
```

3. Deduce the pointwise majorization

```text
1_{‖x‖ ≤ ε} ≤ (π^2 / (4H)) * F_H(x).
```

4. Sum this over `γ ∈ Γ`.
5. Expand the Fejér kernel Fourier series.
6. Bound the nonzero frequencies by absolute values of the exponential sums.
7. Use `H ≍ 1/ε` to rewrite the prefactor as `O(ε)`.

## Allowed simplifications

- You may define `distToInt x := infi (fun n : ℤ => |x - n|)` or use any
  existing Mathlib notion if available.
- You may work with a slightly different but equivalent indexing of the Fejér
  kernel if that simplifies the proof.
- You may use a concrete constant instead of an asymptotic `O(ε)`.
- It is fine if the theorem is stated for a finite list or multiset instead of
  `Finset`, as long as it is genuinely finite and reusable.

## Good follow-up lemma if convenient

If the main proof closes cleanly, also state a tiny corollary:

```text
if ε * ∑_{j=1}^{H-1} ‖Sα(j)‖ → 0 and ε * Γ.card → 0,
then Aα(Γ, α, ε) = 0 eventually.
```

This corollary is optional. The main target is the finite Fejér-kernel bridge.

## Policy

- Keep the proof small and explicit.
- No `sorry` or `admit`.
- `exact?` is allowed only if the final file compiles cleanly.
- Prefer elementary inequalities, `linarith`, `nlinarith`, `ring`, `field_simp`,
  and basic finite-sum lemmas.
- Do not introduce any zeta-zero machinery.
