# Blind re-derivation: the weighted energy identity for RΔ on the CCM even block

**Agent:** independent verification agent (paper mathematics + source reading, READ-ONLY).
**Date:** 2026-09-04. **Branch:** `rh_clean`.
**Status:** DIAGNOSTIC / derivation audit. `PX_RH_CLAIM: NOT_MADE`. No Lean, no route promotion.

**Blindness statement.** Nothing under `docs/routeB_bus/AGENT_REPORT_2026-09-04*` was read;
`docs/routeB_bus/phase5_codex/out/lattice_equation.md`, `odd_floor.*` and
`docs/routeB_bus/phase5_codex/lattice_equation.py` were not opened. The derivation below is
built only from

* `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_scripts/edge_ledger_build.py`
  (class `CCMArbBuilder`: `w02`, `wr`, `prime`, `tau_entry`, `even_block`), and
* `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean`
  (`ccmQKernel`, `ccmW02Entry`, `ccmPrimeEntryN1`, `ccmWREntry`, `ccmWeilTauN1`),
* `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean`
  (`ccmBetaScalar`, `ccmWeilTau_structured_offdiag`, `ccmBetaFinite_unique`).

Two throwaway float scripts were used **only** to check the linear algebra of the identity on
random symmetric matrices and the closed-form `w02` algebra; they touch no project object and
produced no artefact. They are listed in §9.

---

## 0. Notation (fixed once; collisions with the code are called out)

Production schedule: `m = N = k+2`, `L = log m`, `z = 1/m²`, prime powers `k ≤ m`.

| symbol | meaning | source |
|---|---|---|
| `τ(n,p)` | full literal Weil entry `W02(n,p) − W_ℝ(n,p) − Prime(n,p)`, `n,p ∈ ℤ` | `CCMArbBuilder.tau_entry`; Lean `ccmWeilTauN1` |
| `α_n, β_n, γ_n` | the builder's archimedean coefficients (`_alpha`, `_beta`, `_gamma`) | code only |
| `B_n` | **beta scalar** `B_n := n · τ(n,0)`, `B_0 = 0` | Lean `ccmBetaScalar` |
| `K̃` | EVEN block, size `(N+1)×(N+1)`, indices `0..N` | `even_block()` / `parity_blocks` |
| `λ₁` | bottom eigenvalue of `K̃` | |
| `x` | bottom eigenvector, center-normalised: `K̃x = λ₁x`, `x₀ = 1` | |
| `y` | trial row: `y₀ = 1`, `y_n = (−1)ⁿ Ξ(t_n)/Ξ(0)`, `t_n = 2πn/L` | `centeredXi` |
| `Δ` | `x − y` (so `Δ₀ = 0` exactly) | |
| `R` | `diag(1/n)` on `n ≥ 1` | |
| `𝓡(y)_n` | `(K̃y)_n − y_n (K̃y)₀`, `n ≥ 1` | |
| `ν` | `(K̃y)₀` | |
| `D` | `K̃` with row and column `0` deleted, i.e. `D_{np} = K̃_{np}`, `n,p ≥ 1` | |

I write `t_n = 2πn/L` for the abscissa (the task text calls it `x_n`, which collides with the
eigenvector `x`). Lower-case `δ`, `Y`, `X`, `ρ` denote the restrictions of `Δ, y, x, 𝓡(y)` to
`n ≥ 1`. `Λ(k)` is von Mangoldt, `y_k := log k`.

---

## 1. Ground truth read off the builder

`CCMArbBuilder.even_block()` builds, with `sqrt2 = √2` and `k(i,j) = tau_entry(i,j)`:

```
K̃[0,0] = τ(0,0)
K̃[0,j] = K̃[j,0] = √2 · τ(0,j)          (j ≥ 1)
K̃[i,j] = τ(i,j) + τ(i,−j)              (i,j ≥ 1, including i = j)
```

so in block form

```
        ┌ a    wᵀ ┐              a   = τ(0,0)
  K̃ =   │         │              w_n = √2 τ(0,n)              (n ≥ 1)
        └ w    D  ┘              D_{np} = τ(n,p) + τ(n,−p)     (n,p ≥ 1)
```

`τ` is symmetric (`w02`, `wr`, `prime` all are — checked entry by entry), hence `K̃` and `D`
are real symmetric.

### 1.1 The pairing: **no factor 2**, and where the √2 lives

The even basis is `e₀ = mode₀`, `e_i = (mode_i + mode_{−i})/√2`, which is **orthonormal**.
The coordinate map from `±N` mode coefficients `c_n` (`c_n = c_{−n}`) to even coordinates is

```
ξ₀ = c₀ ,      ξ_i = √2 c_i   (i ≥ 1),
```

an isometry: `Σ_{|n|≤N} c_n² = c₀² + 2Σ_{i≥1} c_i² = ξ₀² + Σ_{i≥1} ξ_i² = ‖ξ‖²`
(the builder's own docstring states exactly this). Consequently:

> **In even-basis coordinates the inner product is the plain Euclidean one,
> `⟨u,v⟩ = Σ_{i} u_i v_i`. There is no factor 2 on `n ≥ 1` and no factor at `n = 0`.**

The `√2` at `n = 0` enters in exactly **two** places, both structural, neither in the pairing:

1. **In the matrix**: `K̃[0,j] = √2 τ(0,j)`, i.e. `w = √2 · R B` where `B = (B_n)_{n≥1}` is the
   beta-scalar vector (§2), because `τ(0,n) = τ(n,0) = B_n/n`.
2. **In the meaning of `y`** (see §8, uncertainty U1): if `y` is meant as the *mode-coefficient*
   sampler `c_n ∝ (−1)ⁿ Ξ(t_n)`, then its even-basis representative is
   `ŷ₀ = 1, ŷ_n = √2 (−1)ⁿ Ξ(t_n)/Ξ(0)`, not `ŷ_n = (−1)ⁿ Ξ(t_n)/Ξ(0)`.

That `x` and `𝓡` live in even coordinates is forced by the problem statement itself:
`K̃x = λ₁x` is the even block acting, and `𝓡(x)_n = (K̃x)_n − x_n (K̃x)₀ = λ₁x_n − x_n λ₁ = 0`
uses `x₀ = 1` in even coordinates. So the whole computation below is even-basis / Euclidean.

---

## 2. The divided-difference (beta-scalar) structure — re-derived, not assumed

Lean's `ccmWeilTau_structured_offdiag` states, for `n ≠ m`,

```
   τ(n,m) = (B_n − B_m)/(n − m),         B_n := n · τ(n,0),  B_0 = 0.        (2.1)
```

I re-derived this from the builder's own closed forms rather than taking it on trust.

**(a) W02.** With `D_n := L² + 16π²n²`, `w02(n,0) = 32 L sinh²(L/4)/D_n`, hence
`n·w02(n,0) − m·w02(m,0) = 32 L sinh²(L/4)·(n D_m − m D_n)/(D_n D_m)` and
`n D_m − m D_n = (n−m)(L² − 16π² nm)`, giving
`(n·w02(n,0) − m·w02(m,0))/(n−m) = 32 L sinh²(L/4)(L² − 16π² nm)/(D_n D_m) = w02(n,m)`. ✔

**(b) Prime.** With `q(n,m,x) = (sin(2πmx/L) − sin(2πnx/L))/(π(n−m))` and
`s_k(n) := sin(2πn log k /L)/π`, one has `−q(n,m,y_k) = (s_k(n) − s_k(m))/(n−m)` and
`−q(n,0,y_k) = s_k(n)/n`, so `−Prime` is a divided difference of `Σ_k Λ(k)k^{−1/2} s_k(n)`. ✔

**(c) Archimedean.** `ccmWREntry L n m` depends on `(n,m)` **only** through `q(n,m,·)`, and
`q` obeys the same identity; `−wr(n,m) = (α_n − α_m)/(n−m)` with `α_{−n} = −α_n`, `α_0 = 0`. ✔

So `B_n = n τ(n,0) = 2 n C₀ C_n + α_n + Σ_{k≤m} Λ(k) k^{−1/2} s_k(n)` (with `C` as in §4),
and `B` is **odd**: `τ(−n,0) = τ(n,0)` (each of `w02`, `wr`, `prime` is even in `n` at `m=0`,
since `q(−n,0,x) = q(n,0,x)`), hence `B_{−n} = −B_n`. `ccmBetaFinite_unique` says `B` is the
*only* such vector vanishing at the centre, so (2.1) fixes the whole off-diagonal.

**Numerical spot check** (floats, `L = log 13`): `w02(n,m) − (B_n−B_m)/(n−m)` and the same for
the prime kernel agree to `1.1e−16` over `−5 ≤ n ≠ m ≤ 5`.

### 2.1 The reflection identity `τ(n,−n) = τ(n,0)`

From `q(n,−n,x) = (sin(−2πnx/L) − sin(2πnx/L))/(2πn) = −sin(2πnx/L)/(πn) = q(n,0,x)`
(exact, for every `x`), and from `w02(n,−n) = 32L sinh²(L/4)/D_n = w02(n,0)`:

```
   τ(n,−n) = τ(n,0) = B_n / n          for every n ≥ 1.                      (2.2)
```

Equivalently, from (2.1): `τ(n,−n) = (B_n − B_{−n})/(2n) = 2B_n/(2n) = B_n/n`. The Lean file
carries the `N = 1` instance of exactly this: `ccmW02Entry_neg_one_one_eq_neg_one_zero`.
Verified numerically to `2.8e−17` / `0.0`.

---

## 3. Structure of `D − λ₁` in source terms

### 3.1 Diagonal

By (2.2), for `n ≥ 1`:

```
   (D − λ₁)_{nn} = τ(n,n) + τ(n,−n) − λ₁ = τ(n,n) + τ(n,0) − λ₁
                 = τ(n,n) + B_n/n − λ₁.                                       (3.1)
```

**The sign is PLUS.** Written in the shape "`τ(n,n) − (something) − λ₁`" the *something* is
`−τ(n,0) = −B_n/n`, i.e. the central-column entry enters with a **positive** sign, and its
`1/n` is where the weight `R` first appears on its own. Fully expanded:

```
 τ(n,n) = 32 L sinh²(L/4)(L² − 16π²n²)/D_n²
          − 2γ_n + 2β_n
          − 2 Σ_{k≤m} Λ(k) k^{−1/2} (1 − log k / L) cos(2πn log k / L)

 τ(n,0) = 32 L sinh²(L/4)/D_n
          + α_n / n
          + (1/(πn)) Σ_{k≤m} Λ(k) k^{−1/2} sin(2πn log k / L)
```

(`−wr(n,n) = −2γ_n + 2β_n` from `CCMArbBuilder.wr`; `−wr(n,0) = +α_n/n`.)

**Consistency remark (mine, not in any source).** `2β_n` is exactly the `n`-derivative of `α_n`
(both reduce to `Re ψ'(1/4 + iπn/L)/(2L)`), and `DD[f](n,n) := f'(n) + f(n)/n` is the confluent
limit of `f[n,m] + f[n,−m]`. So `D_{nn}` equals its own confluent limit **minus a diagonal
defect**
`2γ_n + 2Σ_k Λ(k)k^{−1/2} cos(2πn log k/L)`
— the `W02` part has no defect. This is the finite Weil "diagonal counterterm"; it is worth
naming because a derivation that obtains `D_{nn}` by taking `m → n` in the off-diagonal formula
will silently drop it.

### 3.2 Off-diagonal, divided-difference form

For `n ≠ p`, `n,p ≥ 1`, using (2.1) twice (`p` and `−p`) and `B_{−p} = −B_p`:

```
   D_{np} = (B_n − B_p)/(n − p) + (B_n + B_p)/(n + p).                        (3.2)
```

Equivalently, splitting into sources with `s_k(n) = sin(2πn log k/L)/π`:

```
   D_{np} = 4 C_n C_p
          + [ (α_n − α_p)/(n−p) + (α_n + α_p)/(n+p) ]
          + Σ_{k≤m} Λ(k) k^{−1/2} [ (s_k(n) − s_k(p))/(n−p) + (s_k(n) + s_k(p))/(n+p) ].
```

Both forms agree with (3.1) at `n = p` only up to the diagonal defect above.

### 3.3 The `W02` pole part is rank one in this sector — and why

With the Lean/task constants
`C_{L,n} = 4√L sinh(L/4) L / (L² + 16π²n²)`, `S_{L,n} = 16π√L sinh(L/4) n / (L² + 16π²n²)`:

```
 2 C_n C_p − 2 S_n S_p = 32 L sinh²(L/4)(L² − 16π² np)/(D_n D_p) = w02(n,p).   ✔ (checked, 8.9e−16)
```

`C` is **even** in the mode index (`n` appears only as `n²`), `S` is **odd**. Hence

```
   w02(n,p) + w02(n,−p) = (2C_nC_p − 2S_nS_p) + (2C_nC_p + 2S_nS_p) = 4 C_n C_p.   (3.3)
```

The `S` (sine) half cancels identically in the even sector; only the `C` (cosine) half
survives, and it is a pure outer product. **So the pole part of `D` is rank one and positive
semidefinite: `D^{W02} = 4 C Cᵀ` on `n ≥ 1`.** (Numerically `max |w02(n,p)+w02(n,−p) − 4C_nC_p|
= 3.8e−17`.)

For completeness, the same computation on the whole even block gives
`W02_even = 2 𝐜 𝐜ᵀ` with `𝐜₀ = C₀ = 4 sinh(L/4)/√L` and `𝐜_n = √2 C_n` (`n ≥ 1`) — the `√2`
of the `0`-row again — so the pole is rank one on `K̃` entire, not just on `D`.

**In the parity-ODD block** (`τ(i,j) − τ(i,−j)`, `i,j ≥ 1`) the same computation gives
`−4 S_i S_j`: also rank one, but **negative** semidefinite, and the diagonal there is
`τ(n,n) − τ(n,0)`. See §8 U2: this is the single most likely place for a sign slip, because
the phrase "diagonal `τ(n,n) − (something)`" matches the *odd* block, while `D` as defined
(a block of `K̃`) is the *even* one. The odd block cannot be the intended `D`: the odd basis
contains no `n = 0` vector at all, so `(K̃y)₀`, `ν` and `𝓡(y)` are undefined there.

---

## 4. The two exact linear relations

Write `x = (1, X)`, `y = (1, Y)`, `δ = X − Y = Δ|_{n≥1}`, `ρ = 𝓡(y)`.

`K̃x = λ₁x` splits as

```
  row 0 :   a + ⟨w, X⟩ = λ₁ x₀ = λ₁                                            (4.1)
  rows n≥1: w + D X = λ₁ X                                                     (4.2)
```

and by definition `ν = (K̃y)₀ = a + ⟨w, Y⟩`, `ρ = w + D Y − ν Y`.

### 4.1 `ν` versus `λ₁` (asked explicitly)

Because `x₀ = y₀ = 1`, `λ₁ = (K̃x)₀` and `ν = (K̃y)₀` are the *same functional* evaluated at
`x` and at `y`. Subtracting,

```
   ν − λ₁ = ⟨w, Y − X⟩ = −⟨w, δ⟩ = −√2 Σ_{n≥1} τ(0,n) Δ_n = −√2 ⟨B, RΔ⟩.       (4.3)
```

using `w_n = √2 τ(0,n) = √2 B_n / n`. Equivalently `λ₁ − ν = √2 ⟨B, RΔ⟩`. Three consequences:

* `λ₁ − ν` is **not an independent quantity**: it is an explicit linear functional of `RΔ`
  with pure source coefficients `√2 B_n`, `B_n = n τ(n,0)`.
* `ν` is the "would-be eigenvalue" of the trial `y`: `𝓡(y) = 0 ⟺ K̃y = ν y` (row `0` then
  reads `(K̃y)₀ = ν = ν y₀` automatically).
* **No inequality holds between `ν` and `λ₁`.** `ν` is a single matrix entry of `K̃y`, not a
  Rayleigh quotient; `ν ≥ λ₁` is *not* automatic. (A derivation that uses `ν ≥ λ₁` needs a
  separate argument.)

### 4.2 The residual equation

Subtract (4.2) from `ρ = w + DY − νY`, i.e. substitute `w = λ₁X − DX`:

```
  ρ = λ₁X − DX + DY − νY = −Dδ + λ₁X − νY = −(D − ν)δ + (λ₁ − ν)X
```

(using `Y = X − δ`), hence the two equivalent forms

```
   (D − ν) δ = (λ₁ − ν) X − ρ                                                  (4.4)
   (D − λ₁) δ = (λ₁ − ν) Y − ρ                                                 (4.5)
```

Cross-check of (4.5) by the other route: `(D−λ₁)X = −w` by (4.2), and
`(D−λ₁)Y = ρ − w + (ν−λ₁)Y`, so `(D−λ₁)δ = −w − ρ + w − (ν−λ₁)Y = (λ₁−ν)Y − ρ`. ✔
Sanity: `y = x ⟹ δ = 0, ρ = 0, ν = λ₁`, both sides vanish. ✔
Numerically verified on random symmetric `K̃` to `5.3e−15` (§9).

---

## 5. The commutator: why `R` costs a term

`R` does **not** commute with `D`, so `(D−λ₁)Rδ ≠ R(D−λ₁)δ` and (4.5) cannot be inserted
directly. Set `M := D − λ₁` (symmetric) and use the exact operator identity

```
   R M R = ½ (R²M + M R²) − ½ [R,[R,M]],      [R,[R,M]] = R²M − 2RMR + MR².    (5.1)
```

The double commutator is entrywise

```
   [R,[R,M]]_{np} = (1/n − 1/p)² M_{np} = D_{np} (n−p)²/(n²p²)                 (5.2)
```

(the `λ₁I` part drops out because the weight vanishes on the diagonal), and it is **symmetric**.
Define, for `u = RΔ`,

```
   G_{np} := D_{np} · (n − p)² / (n p),      G_{nn} = 0,                       (5.3)
```

so that `⟨δ, [R,[R,M]] δ⟩ = ⟨u, G u⟩` because `(1/n−1/p)² Δ_nΔ_p = [(n−p)²/(np)]·u_n u_p`.

**This is the step a naive derivation drops.** The `1/(n−p)` of the divided difference is
*over*-cancelled in `G`: from (3.2),

```
   G_{np} = (B_n/p + B_p/n − B_n/n − B_p/p)  +  (n−p)²(B_n + B_p)/(np(n+p))    (5.4)
```

— completely regular at `n = p`, and the first bracket is finite rank
(`⟨u,G⁽¹⁾u⟩ = 2⟨B,u⟩⟨R𝟙,u⟩ − 2⟨RB,u⟩⟨𝟙,u⟩`, `𝟙_n ≡ 1`).

*(Aside: `[D,R]_{np} = D_{np}(n−p)/(np)` is antisymmetric, so it drops out of `⟨δ,·δ⟩` but
**not** out of `⟨Rδ,·δ⟩`. The double-commutator form (5.1) is the arrangement in which the
whole correction is symmetric.)*

---

## 6. The identity

Combining (5.1), (4.5) and (4.3), with `u := RΔ` (supported on `n ≥ 1`):

```
⟨δ, ½(R²M + MR²) δ⟩ = ⟨R²δ, Mδ⟩ = ⟨R²δ, (λ₁−ν)Y − ρ⟩ = (λ₁−ν)⟨RΔ, Ry⟩ − ⟨RΔ, R𝓡(y)⟩
```

so that

> ### Main identity (exact, no approximation)
>
> ```
>   ⟨RΔ, (D − λ₁) RΔ⟩ = (λ₁ − ν) ⟨RΔ, R y⟩ − ⟨RΔ, R 𝓡(y)⟩ − ½ ⟨RΔ, G RΔ⟩       (6.1)
>
>   with   λ₁ − ν = √2 ⟨B, RΔ⟩ = √2 Σ_{n≥1} n τ(n,0) (Δ_n / n) = √2 Σ_{n≥1} τ(0,n) Δ_n
>          G_{np} = D_{np} (n − p)² / (n p)
>          ⟨·,·⟩  = plain Euclidean sum over n ≥ 1  (even basis; NO factor 2)
> ```

Every object on the right is `RΔ`, `R𝓡(y)`, `ν = (K̃y)₀`, `λ₁`, the explicit source row
`B_n = n τ(n,0)` and the source entries `D_{np}`, exactly as required. Index ranges: all sums
`n, p = 1 … N`; `Δ₀ = 0` is used to drop the `0`-component throughout.

### 6.1 Closed (single-operator) form

Because `λ₁ − ν` is itself linear in `Δ`, the first right-hand term is *quadratic*. Put
`p_n := n w_n = √2 B_n` and `q_n := y_n/n`, so `(λ₁−ν)⟨RΔ,Ry⟩ = ⟨p,u⟩⟨q,u⟩ = ⟨u, S u⟩` with
`S := ½(p qᵀ + q pᵀ)` (symmetric, rank ≤ 2). Then (6.1) becomes

> ```
>   ⟨RΔ, 𝔅 RΔ⟩ = − ⟨RΔ, R 𝓡(y)⟩ ,     𝔅 := D − λ₁ + ½G − S .                   (6.2)
> ```

This is the useful form: **left side purely quadratic in `RΔ`, right side purely linear in
`RΔ`.** Verified numerically to `7.1e−15` on random symmetric matrices (§9).

### 6.2 Unweighted variant (no commutator at all)

If the `1/n` weight is not needed, (4.5) alone gives

```
   ⟨Δ, (D − λ₁ − S₀) Δ⟩ = −⟨Δ, 𝓡(y)⟩ ,      S₀ := ½(w yᵀ + y wᵀ),
```

with **no** `G`. The whole commutator cost in (6.1)/(6.2) is the price of the `R` weight.

---

## 7. Where the pole goes, and the scalar `c_n`

**In the left-hand quadratic form of (6.1): yes, it is a perfect square of one scalar.**
By (3.3) the pole part of `D` on `n ≥ 1` is `4 C_n C_p`, so

```
   ⟨RΔ, D^{W02} RΔ⟩ = 4 (Σ_{n≥1} C_n Δ_n / n)² = ( Σ_{n≥1} Δ_n c_n )²
```

with

> ```
>   c_n = 2 C_{L,n} / n = 8 √L · sinh(L/4) · L / ( n (L² + 16π² n²) )
>       = 8 L^{3/2} sinh(L/4) / ( n (L² + 16π² n²) ) ,      n ≥ 1.             (7.1)
> ```

Sign: `+`, because `τ = w02 − wr − prime` carries `w02` with a plus and `4CCᵀ ⪰ 0`. The pole is
a **positive rank-one bump** in `D`; it therefore *helps* coercivity of `D − λ₁` and cannot be
the source of a negative direction.

**But it is NOT a single square in the closed operator `𝔅` of (6.2).** The commutator drags in
the same rank-one kernel with a different weight:

```
   G^{W02}_{np} = 4 C_n C_p (n−p)²/(np) = 4 C_n C_p (n/p + p/n − 2),
```

so with `A_j := Σ_{n≥1} C_n Δ_n / n^j` (`j = 0,1,2`):

```
   pole in ⟨RΔ,(D−λ₁)RΔ⟩ :  + 4 A₁²                    (perfect square, PSD)
   pole in −½⟨RΔ,G RΔ⟩   :  − 4 A₀A₂ + 4 A₁²
   pole in ⟨RΔ, 𝔅 RΔ⟩    :  + 4 A₀ A₂                  (rank two, INDEFINITE)
```

i.e. in `𝔅` the pole is `2(f gᵀ + g fᵀ)` with `f_n = n C_n`, `g_n = C_n/n`, which has one
positive and one negative eigenvalue. **A derivation that keeps the pole as "one square"
after moving the commutator correction to the left has lost the `A₀A₂` cross term and with it
the only indefinite piece the pole contributes.** This is the second most likely error site.

---

## 8. Uncertainties (explicitly flagged)

**U1 — the `√2` convention for `y`. NOT RESOLVABLE from the material I was given.**
The problem statement gives `x` in even-basis coordinates (forced: `K̃x = λ₁x`, and
`𝓡(x) = 0` needs `x₀ = 1` there) but writes `y_n = (−1)ⁿ Ξ(t_n)/Ξ(0)` with no `√2`. If `y` is
meant as the *mode-coefficient* Ξ-sampler, its even-basis representative is
`ŷ₀ = 1`, `ŷ_n = √2(−1)ⁿΞ(t_n)/Ξ(0)`, and then `Δ = x − ŷ`, not `x − y`. The derivation of
(6.1)/(6.2) is **entirely convention-independent** (it uses only `y₀ = 1` and the definition of
`𝓡`), but the *numerical content* of `Δ`, `ν`, `𝓡(y)` differs by that `√2` on `n ≥ 1`. Any
numerical corroboration of this identity must state which `y` was used. My reading: the
even-basis `ŷ` is the mathematically right object (it is the one whose `𝓡` measures failure of
the Ξ-sampler to be the ground state of `K̃`), but I cannot confirm the project's convention
without reading the excluded files.

**U2 — "odd sector".** The task calls `D − λ₁` an odd-sector object but defines `D` as a block
of `K̃`, which is the *even* block. I have taken the definition as authoritative: `D` = even
block, `n ≥ 1`, diagonal `τ(n,n) + τ(n,0)` (plus sign), pole `+4C_nC_p`. The genuine
parity-odd block has diagonal `τ(n,n) − τ(n,0)` (minus) and pole `−4S_nS_p`, with
`c_n^{odd} = 2S_{L,n}/n = 32π√L sinh(L/4)/(L² + 16π²n²)` entering as `−(ΣΔ_n c_n^{odd})²`. If
the derivation under audit uses the minus sign on the diagonal or `S` in the pole, it has
silently switched blocks — and then `(K̃y)₀`, `ν` and `𝓡(y)` are undefined, since the odd
basis has no `n = 0` vector.

**U3 — the diagonal defect.** §3.1: `D_{nn}` is *not* the confluent limit of (3.2); it differs
by `−2γ_n − 2Σ_k Λ(k)k^{−1/2}cos(2πn log k/L)`. I derived this myself from the code's separate
`n = m` branches in `wr` and `q_nm`; I did not find it stated anywhere. Medium confidence in
the exact constant, high confidence that a defect exists and is non-zero.

**U4 — `‖R𝓡(y)‖` vs `‖𝓡(y)‖`.** I have not attempted any estimate of the size of `𝓡(y)`;
the identity is exact and says nothing about it.

**U5 — I did not verify** that `flint`'s bottom eigenvector has `ξ₀ ≠ 0` at the production
cells (it must, for `x` to exist), nor that `λ₁` is simple. Both are assumed.

---

## 9. Can `‖RΔ‖²` be bounded from this identity?

**No — not without a strictly positive lower bound on the smallest eigenvalue of the operator
that actually appears, and that operator is `𝔅 = D − λ₁ + ½G − S`, not `D − λ₁`.** Given
`μ := λ_min(𝔅) > 0` on the `n ≥ 1` sector, (6.2) plus Cauchy–Schwarz gives immediately
`μ‖RΔ‖² ≤ ⟨RΔ,𝔅RΔ⟩ ... ` — more precisely `μ‖RΔ‖² ≤ |⟨RΔ, R𝓡(y)⟩| ≤ ‖RΔ‖·‖R𝓡(y)‖`, hence
`‖RΔ‖ ≤ ‖R𝓡(y)‖/μ`, the usual residual-over-gap bound. Without such a `μ` the identity yields
nothing at all: it is homogeneous of degree two on both sides, so if `𝔅` is singular in some
direction the identity is satisfied by arbitrarily large `RΔ` at fixed residual. What the
lower bound has to be, concretely: (i) Cauchy interlacing gives `D − λ₁ ⪰ 0` for free (`D` is
the compression of `K̃` to `{u₀ = 0}`, so `λ_min(D) ≥ λ_min(K̃) = λ₁`) and `λ_min(D) ≤ λ₂(K̃)`,
so **no bound better than the spectral gap `λ₂ − λ₁` of `K̃` is achievable even in the best
case**, and `λ_min(D) − λ₁ > 0` strictly only because the ground state has `x₀ = 1 ≠ 0`;
(ii) that free positivity is *not enough*, because `½G − S` must be absorbed: `G` is not a
small perturbation (its entries carry the factor `(n−p)²/(np)`, which is large for
`|n−p| ≫ 1`, and its finite-rank part (5.4) pairs `B` against `R𝟙`), and `S` is an indefinite
rank-two term of size `√2‖B‖·‖Ry‖`. So the required statement is an explicit
`λ_min(D − λ₁ + ½G − S) ≥ μ > 0` with `μ` bounded below in terms of `m, L` — a genuinely
stronger claim than a gap bound for `K̃`, and one that the `W02` pole does not supply (it is
PSD in `D` but indefinite inside `𝔅`, §7). If only the unweighted `‖Δ‖` is wanted, §6.2 avoids
`G` entirely and the requirement drops to `λ_min(D − λ₁ − S₀) ≥ μ > 0`.

---

## 10. Verification runs (scratchpad only, no project object touched)

* `chk.py` — random real symmetric `K̃` (`7×7`), random trial `y`: verified
  `⟨w,δ⟩ = λ₁−ν` (1.8e−15), `(D−λ₁)δ = (λ₁−ν)Y − ρ` (5.3e−15), `𝓡(x) = 0` (5.3e−15),
  main identity (6.1) (1.1e−14 against a form of size 19.5), closed form (6.2) (7.1e−15).
* `chk2.py` — float evaluation of the closed `W02`/`q` formulas at `L = log 13`: verified
  `w02 = 2CCᵀ − 2SSᵀ` (8.9e−16), `w02(n,p)+w02(n,−p) = 4C_nC_p` (3.8e−17),
  `w02(n,−n) = w02(n,0)` (2.8e−17), `q(n,−n,x) = q(n,0,x)` (exact 0),
  `C₀ = 4 sinh(L/4)/√L` (5.6e−17), divided difference (2.1) on `w02 + prime` (1.1e−16).

Both scripts live in the session scratchpad
`/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/`
and are throwaway; nothing was written into the repository except this report.

DIAGNOSTIC_NEVER_A_PROOF. `PX_RH_CLAIM: NOT_MADE`.
