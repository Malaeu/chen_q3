# Agent report — Goal 058: normalized-ξ lattice eigen-equation preflight

Date: 2026-09-04
Executor: Linux-Claude subagent (Opus), standing in for Codex (owner decision 2026-09-03 late)
Task: `docs/Codex/TASK_2026-09-04_goal058_normalized_xi_lattice_eigen_equation_preflight.md`
Mode: PAPER_AND_SOURCE_READ_ONLY — no Lean edit, no numerical run, no commit, no queue/verdict/precommit edit

```yaml
TASK_ID: GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT
CODE: P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP
JUDGE_PREDICTION_SCORED: [P_LOW_MODE_RECURRENCE_CLOSES_BEFORE_GAP, 0.40, REFUTED]
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
ROUTE_PROMOTION: false
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
```

**One line.** The center-normalized equation collapses much further than expected — the
whole `W02` pole and the whole no-decay part of the row fold into **one** global scalar
with an explicit profile, and the surviving coupling has genuine `n²/j²` source decay —
but the surviving scalar is, by an exact identity, an affine function of the target
functional `E` itself, and the surviving `j > n₀` tail is the `1/j²`-weighted tail moment
of the same `E`. The equation is a **fixed-point relation for the quantity to be bounded**,
not a bound; and using it as a bound would additionally need a lower bound on an
arch/prime diagonal defect `D_n` that the judge's own `2×2` plant sets to exactly zero.

---

## 0. Verification status of each input

| Input | Status |
|---|---|
| `parity_blocks` even block (`√2` on `n=0`) | read literally in `docs/routeB_bus/phase5_scripts/edge_ledger_build.py::CCMArbBuilder.even_block` (lines 320–344) |
| `w02`, `wr`, `prime`, `q_nm`, `tau_entry` | read literally, same file, lines 283–318 |
| `ccmW02Entry`, `ccmQKernel`, `ccmWREntry`, `ccmPrimeEntryN1`, `ccmWeilTauN1` | read in `CCMFiniteWeilSourceMatrixN1.lean` lines 41–100 |
| `ccmWeilTau_structured_offdiag` (`τ(n,m) = (β_n−β_m)/(n−m)`) | read in `CCMFiniteWeilSourceCommutator.lean` line 282, `#print axioms` present in file; **not** re-run through `lake` (read-only mode) |
| `proposition59SecondJetCoefficient` (`c₀=1/12`, `c_k=1/(2π²k²)`) | read in `Proposition59EntireTransform.lean` lines 314–320 |
| seven-class `(13,2)` entry normal form | read in `CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean` — independent confirmation of the `Q(n,0,x)` and `W02` literals used below |
| `κ_k = 0.0259…0.0245`, `λ₂/λ₁ = 3.6e5…3.6e8`, `x_n ≈ −1/2` | **relay, not re-verified** (no numerics run) — from `WALL_OBJECT_CARD_2026-09-03.md` and `AGENT_REPORT_2026-09-03_…ODD_GRAM…` §8 |
| `E = Σ_{n≤N}(1+2x_n)/n² + Σ_{n>N}1/n²`, `κ = (L²/4π²)E` | derived in the odd-Gram preflight §4, re-derived here independently |

All algebra below is my own and is checkable by hand; every coefficient is named by its
source formula.

---

## 1. Source dictionary (production schedule `m = N = k+2`, `L = log m`)

```
d_n  := L² + 16π²n²                                    (ccmW02Entry denominator)
A_L  := 32 L sinh²(L/4)                                (ccmW02Entry numerator constant)
```

Pole rank-two factors (task's `W02 = 2CCᵀ − 2SSᵀ`, verified against `ccmW02Entry` /
`CCMArbBuilder.w02` term by term):

```
𝒞_n = 4√L sinh(L/4)·L / d_n ,        𝒞_0 = 4 sinh(L/4)/√L
𝒮_n = 16π√L sinh(L/4)·n / d_n ,      𝒮_0 = 0
W02(n,j) = 2𝒞_n𝒞_j − 2𝒮_n𝒮_j
```

Center column and diagonal, from the literal constructors (`ccmQKernel L n 0 x =
−sin(2πnx/L)/(πn)`, `ccmQKernel L n n 0 = 2`, `ccmQKernel L n 0 0 = 0`):

```
p_n := W02(n,0) = 2𝒞_0𝒞_n = A_L/d_n                         (pole part of the center column)
J_n := ∫_{(0,L]} e^{x/2} sin(2πnx/L) / (2 sinh x) dx        (ccmWREntry integral, n ≥ 1)
P_n := Σ_{k=2}^{m} Λ(k) k^{-1/2} sin(2πn log k / L)         (ccmPrimeEntryN1, n ≥ 1)
a_n := (J_n + P_n)/(π n)                                     (arch+prime part of the center column)
b_n := τ(n,0) = p_n + a_n                                    (W_ℝ(n,0) = −J_n/(πn), Prime(n,0) = −P_n/(πn))
B_n := n² b_n = n·β_n                                        (β from ccmBetaScalar)
```

Diagonals (the `ccmQKernel L n n 0 = 2` branch keeps the Euler–Mascheroni constant, which
is absent from the center column — the S3 observation of the odd-Gram report):

```
G_L        := γ + log(4π(e^L−1)/(e^L+1))
W_ℝ(n,n)   =  G_L + ∫_{(0,L]} [ e^{x/2}·(2(L−x)/L)·cos(2πnx/L) − 2 ] / (2 sinh x) dx
Prime(n,n) =  Σ_{k=2}^{m} Λ(k) k^{-1/2}·2(1 − log k/L)·cos(2πn log k/L)
W02(n,n)   =  A_L (L² − 16π²n²)/d_n²
τ(n,n)     =  W02(n,n) − W_ℝ(n,n) − Prime(n,n)
τ(0,0)     =  A_L/L² − W_ℝ(0,0) − Prime(0,0)
```

**Even block exactly as `parity_blocks` builds it** (`even[0,j] = √2 k(0,j)`,
`even[i,j] = k(i,j) + k(i,−j)`), on indices `0..N`. Using `ccmWeilTau_structured_offdiag`
and `β_{−j} = −β_j`:

```
K̃₀₀ = τ(0,0)
K̃₀ⱼ = K̃ⱼ₀ = √2 b_j                                          (j ≥ 1)
K̃ₙₙ = τ(n,n) + τ(n,−n) = τ(n,n) + b_n                        (τ(n,−n) = 2β_n/2n = b_n)
K̃ₙⱼ = τ(n,j) + τ(n,−j) = 2 (B_n − B_j)/(n² − j²)             (n ≠ j, both ≥ 1)      (★)
```

`(★)` is the **squared-node Loewner form**: the even block off-diagonal is a divided
difference of the single source sequence `B_n = n²τ(n,0)` at the nodes `u = n²`. This is
one `submatrix`+parity step from the kernel-checked `ccmWeilTau_structured_offdiag`.

Ground row in even coordinates: `ξ̃₀ = ξ₀`, `ξ̃_n = √2 ξ_n`, so

```
y_n = ξ̃_n/ξ̃₀ = √2 · ξ_n/ξ₀ = √2 x_n ,      y₀ = 1
```

with `x_n` the raw-carrier ratio of the odd-Gram report. The `√2` is basis, not source
(S2 of that report) — carried explicitly everywhere below.

Equivalent rank-one form of the pole, used in §4: with `c̃₀ := √2 𝒞₀`, `c̃_j := 2𝒞_j`,

```
K̃ = c̃ c̃ᵀ − Ã − P̃        (Ã, P̃ = even blocks of W_ℝ and Prime)
```

because `W02(i,j) + W02(i,−j) = 4𝒞_i𝒞_j` kills the `𝒮` half by parity. In the even sector
the `W02` displacement rank drops from 2 to **1**.

---

## 2. `R(y)_n = 0` written out for `n = 1, 2, 3`

```
R(y)_n = √2 b_n + K̃ₙₙ y_n + Σ_{j≥1, j≠n} K̃ₙⱼ y_j − y_n [ τ(0,0) + √2 Σ_{j≥1} b_j y_j ] = 0
```

with every entry replaced by its source formula from §1.

**n = 1**

```
R(y)₁ = √2 b₁
      + [ τ(1,1) + b₁ ] y₁
      + (2/3)(4b₂ − b₁) y₂ + (1/4)(9b₃ − b₁) y₃ + (2/15)(16b₄ − b₁) y₄ + …
        … + Σ_{j≥2} 2(j²b_j − b₁)/(j²−1) · y_j
      − y₁ [ τ(0,0) + √2 (b₁y₁ + b₂y₂ + b₃y₃ + …) ]  = 0
```

**n = 2**

```
R(y)₂ = √2 b₂
      + (2/3)(4b₂ − b₁) y₁
      + [ τ(2,2) + b₂ ] y₂
      + (2/5)(9b₃ − 4b₂) y₃ + (1/6)(16b₄ − 4b₂) y₄ + … + Σ_{j≥3} 2(j²b_j − 4b₂)/(j²−4) · y_j
      − y₂ [ τ(0,0) + √2 Σ_{j≥1} b_j y_j ]  = 0
```

**n = 3**

```
R(y)₃ = √2 b₃
      + (1/4)(9b₃ − b₁) y₁ + (2/5)(9b₃ − 4b₂) y₂
      + [ τ(3,3) + b₃ ] y₃
      + (2/7)(16b₄ − 9b₃) y₄ + … + Σ_{j≥4} 2(j²b_j − 9b₃)/(j²−9) · y_j
      − y₃ [ τ(0,0) + √2 Σ_{j≥1} b_j y_j ]  = 0
```

with, spelled out to the last literal,

```
b_n     = 32 L sinh²(L/4)/(L² + 16π²n²)                                  ← ccmW02Entry(n,0)
        + (1/πn) ∫_{(0,L]} e^{x/2} sin(2πnx/L)/(2 sinh x) dx             ← −ccmWREntry(n,0)
        + (1/πn) Σ_{k=2}^{m} Λ(k) k^{-1/2} sin(2πn log k/L)              ← −ccmPrimeEntryN1(n,0)

τ(n,n)  = 32 L sinh²(L/4)(L²−16π²n²)/(L²+16π²n²)²                        ← ccmW02Entry(n,n)
        − G_L − ∫_{(0,L]} [e^{x/2}(2(L−x)/L)cos(2πnx/L) − 2]/(2 sinh x)dx ← −ccmWREntry(n,n)
        − Σ_{k=2}^{m} Λ(k) k^{-1/2}·2(1−log k/L) cos(2πn log k/L)         ← −ccmPrimeEntryN1(n,n)

τ(0,0)  = 32 sinh²(L/4)/L − G_L − ∫_{(0,L]}[e^{x/2}(2(L−x)/L) − 2]/(2 sinh x)dx
        − 2 Σ_{k=2}^{m} Λ(k) k^{-1/2}(1 − log k/L)
```

Note the equation is **quadratic** in `y` (the `y_n·Σ b_j y_j` term); §3 shows the
quadratic part cancels identically.

---

## 3. Exact reduction — three identities, no inverse, no `λ₁` assumed

### LATTICE-1 (the center-normalized identity)

Two exact source steps.

*(a) Loewner splitting of `(★)`.* For `n ≠ j`, `n, j ≥ 1`,

```
K̃ₙⱼ = 2(j²b_j − n²b_n)/(j² − n²) = 2 b_j + 2n² (b_j − b_n)/(j² − n²)          (SPLIT)
```

(one line: `2b_j(j²−n²) + 2n²b_j − 2n²b_n = 2j²b_j − 2n²b_n`).

*(b) Row-0 collapse.* Let `S := Σ_{j≥1} b_j y_j` and `μ := (K̃y)₀ = τ(0,0) + √2 S`.
Then `Σ_{j≠n} 2b_j y_j = 2S − 2b_n y_n = √2(μ − τ(0,0)) − 2b_n y_n`, the `−2b_n y_n`
merges with `K̃ₙₙ = τ(n,n) + b_n`, and the two `y_n²` terms cancel exactly. Result, for
**every** `y` with `y₀ = 1` — no eigenvector hypothesis, no `λ₁`:

```
┌──────────────────────────────────────────────────────────────────────────────┐
│  R(y)_n = √2 ( b_n + μ − τ(0,0) ) + ( τ(n,n) − b_n − μ ) y_n + Ω_n           │
│                                                                              │
│  Ω_n := 2n² Σ_{j≥1, j≠n} (b_j − b_n) y_j / (j² − n²) ,   μ := (K̃y)₀         │
└──────────────────────────────────────────────────────────────────────────────┘
```

At the ground row `μ = λ₁`, so `R(y)_n = 0` reads

```
( τ(n,n) − b_n − λ₁ ) y_n = √2 ( τ(0,0) − b_n − λ₁ ) − Ω_n                    (LATTICE-1)
```

### LATTICE-2 (the pole collapses to one scalar)

The pole divided difference is **exact and rank one**:

```
(p_j − p_n)/(j² − n²) = −16π² A_L /(d_n d_j)      (p_n = A_L/d_n)
```

so `Ω_n^{pole} = −(32π² A_L n²/d_n) Σ_{j≠n} y_j/d_j`. The excluded `j = n` term is
`+(32π² A_L n²/d_n²) y_n`, and

```
(τ(n,n) − b_n)_{pole} = W02(n,n) − W02(n,0) = −32π² A_L n²/d_n²
```

cancels it **identically**. Likewise `(τ(0,0) − b_n)_{pole} = A_L/L² − A_L/d_n =
16π²A_L n²/(L² d_n)`, which is `κ_n/(√2 L²)` with `κ_n` below. Hence:

```
┌──────────────────────────────────────────────────────────────────────────────┐
│  D_n · y_n  =  κ_n · Ŝ  −  √2 [ W_ℝ(0,0) + Prime(0,0) + a_n + λ₁ ]  −  Ω_n^{ap}  │
│                                                                              │
│  D_n     := − W_ℝ(n,n) − Prime(n,n) − a_n − λ₁          (arch/prime diagonal defect)│
│  κ_n     := 32π² A_L n²/d_n = 1024 π² L sinh²(L/4) n²/(L²+16π²n²)            │
│  Ŝ       := Σ_{j=1}^{N} y_j/d_j + 1/(√2 L²)                                  │
│  Ω_n^{ap} := 2n² Σ_{j≠n} (a_j − a_n) y_j/(j² − n²)                            │
└──────────────────────────────────────────────────────────────────────────────┘
                                                                    (LATTICE-2)
```

This is the maximal structural gain the equation admits: **the entire `W02` pole — the
`e^{L/2}`-sized object that destroyed probes 5–8 — enters every low-mode row through one
single scalar `Ŝ` times the explicit profile `n²/d_n`.** Everything else on the left is
archimedean-plus-prime.

### LATTICE-3 (the scalar `Ŝ` *is* the target functional)

`16π²j²/d_j = 1 − L²/d_j`, hence exactly `1/d_j = (1 − L²/d_j)/(16π²j²)`, and with
`y_j = √2x_j`, `Σ_{j≥1} x_j/j² = (E − π²/6)/2`, `E := Σ_{n≤N}(1+2x_n)/n² + Σ_{n>N} 1/n²`:

```
┌──────────────────────────────────────────────────────────────────────────────┐
│  Ŝ = (√2/32π²)( E − π²/6 )  −  (√2 L²/16π²) Σ_{j=1}^{N} x_j/(j² d_j)  +  1/(√2 L²) │
└──────────────────────────────────────────────────────────────────────────────┘
                                                                    (LATTICE-3)
```

and `κ = (L²/4π²) E` (odd-Gram report §4, re-derived). So the scalar that carries the
whole pole into the low-mode equation is an **affine function of the very functional the
route must bound**, plus a second, more strongly weighted moment of the same row.

---

## 4. Closure decision (step 3) — the honest reading

**What does close.** The naive failure mode does *not* occur. After `(SPLIT)` the
coefficient of `y_j` in row `n` is `2n²(b_j − b_n)/(j² − n²) = O(n²(|b_j| + |b_n|)/j²)`
for `j ≫ n`: a genuine, explicit, source-named `1/j²` decay, whose pole component is
*exactly* `−32π²A_L n²/(d_n d_j)`. There is no "full row with no decay of the
coefficient". LATTICE-2 goes further and removes the no-decay part altogether.

**What does not close — three independent obstructions.**

1. **The remainder is not one-sided.** `Ω_n` runs over *all* `j ≠ n`. Upward
   (`n = 1, 2, …`) the equation is **non-causal**: `y_n` needs `y_j` for `j > n`.
   Downward (`n = N, N−1, …`) it is causal but the coefficients lose their decay:
   at `n = N`, `2N²(b_j − b_N)/(j² − N²) → −2(b_j − b_N)` for `j ≪ N` — dense in the
   low modes, which is precisely the shape the failure code names.

2. **The `j > n₀` remainder is the target's own tail.** Split `Ω_n^{ap}` at `n₀`. The
   dominant `j > n₀` component is

   ```
   ρ_n(n₀) := − (2n/π)(J_n + P_n) · Σ_{j>n₀} y_j/(j² − n²)
              + (2n²/π) Σ_{j>n₀} (J_j + P_j) y_j /( j (j² − n²) )
   ```

   whose leading factor is `Σ_{j>n₀} y_j/j² = √2 Σ_{j>n₀} x_j/j²` — **the `1/j²`-weighted
   tail moment of `x`, i.e. the tail of `E` itself**
   (`Σ_{j>n₀}(1+2x_j)/j² = Σ_{j>n₀}1/j² + 2Σ_{j>n₀}x_j/j²`). Bounding it is not a step
   toward `E = O(L^{-2})`; it is the same task restricted to `j > n₀`.

3. **The global scalar is the target.** By LATTICE-3, `Ŝ` is affine in `E`. Its
   coefficient `κ_n ≍ 256π²√m·n²/L` for `n ≪ L` is exponentially large in `L`
   (`sinh²(L/4) ≍ √m/4`), while the left side `D_n y_n` is of arch/prime size
   `O(√m)` at most. So the equation reads, in orders of magnitude,

   ```
   (arch/prime) · y_n  =  (e^{L/2}-sized source constant) · E  +  (source) · E_tail
   ```

   — a fixed-point relation for `E`, not an estimate of it. This is the **third**
   independent time this route folds back onto `E`: CURVBRIDGE (record 8 of the wall
   card), C5 (`C5_RECIPROCAL_COMMUTATOR_ONLY_RENAMES_CURVATURE`), now the lattice
   equation.

**What a bound would additionally require, and why it is the forbidden object.** Even
granting a favourable `Ŝ`, using LATTICE-2 needs
`Σ_{j>n₀} |y_j|/j² ≤ C` — a bound on the tail mass of the ground row *relative to its
center entry*. Since `‖y‖ = ‖ξ‖/ξ₀ = 1/|⟨e₀,ξ⟩|` and `x = −(D−λ₁)^{-1}b`, every known
route to that number is `‖(D−λ₁)^{-1}‖`, the absolute gap, or an odd-sector floor — all
three forbidden, all three already killed (`P_ODD_SECTOR_FLOOR_NONCOLLAPSING: REFUTED`;
`λ₂/λ₁ ≈ 3.6e5…3.6e8` with `λ₁ ≈ 10^{-1.9m}`, so `D − λ₁` is itself collapsed by
interlacing `λ₁(K̃) ≤ λ₁(D) ≤ λ₂(K̃)`). **The remainder is controlled only through the
near-null directions.**

Verdict of step 3: the equation does **not** close on modes `≤ n` with a bounded
`j > n₀` remainder.

```text
P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP
```

---

## 5. Two-by-two plant check (step 4) — and what it isolates

`K_t = [[λ + b²/t, b],[b, λ + t]]`, `t > 0`, `b ≠ 0`. Note `K_t = λ I + v vᵀ` with
`v = (b/√t, √t)`: the plant is exactly *rank-one pole plus scalar arch/prime diagonal* —
a legal degenerate instance of `K̃ = c̃c̃ᵀ − Ã − P̃`. Its ground pair is `λ` with
`y₁ = −b/t`, arbitrary as `t → 0` at fixed `b`.

*The identity reproduces the plant exactly.* Mapping `N = 1`: `τ(0,0) = λ + b²/t`,
`√2 b₁ = b`, `τ(1,1) + b₁ = λ + t`, `λ₁ = λ`, `Ω₁ = 0`. LATTICE-1 gives
`(t − √2 b) y₁ = √2(λ + b²/t − b/√2 − λ) = √2 b²/t − b`, i.e. `y₁ = −b/t`. ✔

*What the plant kills.* In the plant `a₁ = 0` (no off-center arch/prime), the arch/prime
diagonal is `λ`, and therefore

```
D₁ = −W_ℝ(1,1) − Prime(1,1) − a₁ − λ₁ = λ − 0 − λ = 0 .
```

LATTICE-2 degenerates to `0 · y₁ = κ₁ Ŝ`, which determines only `Ŝ = 0` and says nothing
whatever about `y₁`. Consequently every argument of the following shapes is **rejected**,
because each holds verbatim for the plant while `y₁` is unbounded:

- "the pole is rank one, so the low modes decouple from the tail";
- "displacement rank 2 / Loewner divided differences bound the off-diagonal";
- "the tail coefficient decays like `n²/j²`, hence the remainder is negligible";
- "the diagonal dominates the row" (Gershgorin-type);
- any use of centrosymmetry, the squared-node interpolant, or the secular determinant
  alone.

*What the plant isolates.* The one datum the plant sets to zero and CCM need not — the
**arch/prime diagonal defect** `D_n = −W_ℝ(n,n) − Prime(n,n) − a_n − λ₁`. It is fully
source-computable (no inverse, no eigenvector), it is the exact non-generic input that any
proof must use, and nothing in the current ledger bounds it away from zero. That is a
second missing input, independent of the tail-mass obstruction of §4 — and unlike the
tail-mass bound it is *not* circular, which makes it the one genuinely new object this
preflight produces.

---

## 6. First surviving remainder term, exactly

After the maximal collapse (LATTICE-2), the two terms that survive with no source bound
are, in order of size:

```
(F1)  κ_n Ŝ  =  (32π² A_L n²/d_n) · [ Σ_{j=1}^{N} y_j/d_j + 1/(√2 L²) ] ,
      A_L = 32 L sinh²(L/4),  d_n = L² + 16π²n²
      — affine in E by LATTICE-3; coefficient of order 256π²√m n²/L.

(F2)  ρ_n(n₀) = − (2n/π)(J_n + P_n) Σ_{j>n₀} y_j/(j² − n²)
                + (2n²/π) Σ_{j>n₀} (J_j + P_j) y_j /( j (j² − n²) ) ,
      J_j = ∫_{(0,L]} e^{x/2} sin(2πjx/L)/(2 sinh x) dx  (ccmWREntry),
      P_j = Σ_{k=2}^{m} Λ(k) k^{-1/2} sin(2πj log k/L)   (ccmPrimeEntryN1),
      |P_j| ≤ Σ_{k≤m} Λ(k)k^{-1/2} = O(√m)
      — the 1/j²-weighted tail moment of x, i.e. the tail of E itself.
```

`(F2)`'s first factor `Σ_{j>n₀} y_j/(j²−n²)` is the exact point where the collapsed
complement re-enters: it is the tail mass of the ground row normalized by its center
entry.

---

## 7. Typed statements: what is Lean-ready, what is NEW_ANALYTIC

**Lean-ready (finite algebra, no cofinal quantifier, no inverse, no eigenvector
hypothesis).** Hypotheses throughout: `2 ≤ mProject`, `1 ≤ N`, `L = ccmL mProject`,
`K̃` the even parity block of `ccmWeilMatFinite`, `y : Fin (N+1) → ℝ` with `y 0 = 1`,
`μ := (K̃ *ᵥ y) 0`.

1. `ccmEvenBlock_squaredNode_loewner` :
   `K̃ n j = 2 (B n − B j)/((n:ℝ)² − (j:ℝ)²)` for `n ≠ j`, `n,j ≥ 1`, `B n = n² * τ(n,0)`.
   *(one `submatrix` + `ccmWeilTauN1_neg_neg` step from `ccmWeilTau_structured_offdiag`.)*
2. `ccmEvenBlock_pole_rank_one` : `(W02 even block) = c̃ c̃ᵀ`, `c̃ 0 = √2 𝒞₀`, `c̃ j = 2𝒞_j`.
   *(parity of `ccmW02Entry_rank_two_factorization`, already kernel-checked.)*
3. `ccmLattice_centerNormalized_identity` (LATTICE-1) :
   `R(y) n = √2 (b n + μ − τ(0,0)) + (τ(n,n) − b n − μ) * y n + Ω n`.
   *(unconditional; the `y_n²` cancellation is `ring` after `(SPLIT)`.)*
4. `ccmLattice_pole_collapse` (LATTICE-2) : as boxed in §3, using
   `(p j − p n)/(j²−n²) = −16π² A_L/(d_n d_j)` and
   `W02(n,n) − W02(n,0) = −32π² A_L n²/d_n²` — both `field_simp; ring` from
   `ccmW02Entry`.
5. `ccmLattice_scalar_eq_curvature_functional` (LATTICE-3) : the affine identity between
   `Ŝ`, `E`, and `Σ x_j/(j² d_j)`.

These five are honest theorems and worth having: (1) and (2) are new normal forms of the
even block, (3)–(5) are the exact statement of what the lattice equation *is*. None of
them bounds anything.

**NEW_ANALYTIC (not Lean-ready, no derivation in hand).** Two independent inputs, both
required, only the second non-circular:

- `P59_LATTICE_TAIL_MASS_BOUND` (circular): `Σ_{j>n₀} |x_j|/j² ≤ C/L` for
  `n₀ ≍ L`. This is the tail half of `E = O(L^{-2})` itself; it may not be assumed.
- `P59_ARCH_PRIME_DIAGONAL_DEFECT_NONDEGENERACY` (new, non-circular):
  `|D_n| = |W_ℝ(n,n) + Prime(n,n) + a_n + λ₁| ≥ δ(L) > 0` for `1 ≤ n ≤ n₀`, with `δ`
  explicit. Purely source-side (archimedean integral + von Mangoldt sum + `λ₁ ≤ τ(0,0)`
  by Rayleigh at `e₀`). The plant shows this is exactly the datum a proof must use;
  nothing in the ledger supplies it.

---

## 8. Strange things, recorded before they are explained

**S4 — the naive pole-only limit shape `x_n ≈ −1/2` is an artifact.** Dropping `Ω_n` in
LATTICE-1 and keeping only the pole gives
`x_n = (τ(0,0)−b_n)/(τ(n,n)−b_n) = −d_n/(2L²) = −½ − 8π²n²/L²`, which matches the
relayed numerical `x_n ≈ −1/2` of the odd-Gram report S1 startlingly well. **It is
nevertheless not a derivation**: the pole part of `Ω_n` is of exactly the same order and
cancels the whole `y_n` coefficient (that is precisely LATTICE-2), so the pole-only
system is degenerate and fixes only `Ŝ = 0`. Two readings: (A) the agreement is
coincidence of two `O(1)` pole ratios; (B) the true `−1/2` is produced by the arch/prime
data and `Ω_n^{ap}`, and the pole ratio merely shares its leading constant. Distinguishing
measurement in §9 (compare `x_n` against `−d_n/(2L²)` at `n = 1..8` across cells: reading
A predicts the `n²/L²` correction is *wrong* in sign or size, reading B predicts a
systematic residue tracking `D_n`). Logged now, unexplained.

**S5 — the even sector halves the pole's displacement rank.** `W02` has displacement
rank 2 on the raw `±N` carrier (`2CCᵀ − 2SSᵀ`); on the even block the `𝒮` half dies by
parity and the pole is exactly rank **one** (`c̃c̃ᵀ`). Every previous probe (5–8) worked on
the raw carrier and paid for a rank-2 object. Whether this halving is usable anywhere
else has not been checked.

**S6 — `Ŝ` must be exponentially small.** `D_n y_n = O(√m·|y_n|)` while `κ_n ≍ 256π²√m n²/L`,
so consistency forces `|Ŝ| ≲ L|y_n|/(256π²n²)`, i.e. `Σ_j y_j/d_j ≈ −1/(√2L²)` to high
relative accuracy. That is a sharp, cheap, falsifiable prediction about the ground row
that is *independent* of the curvature question, and it has never been measured.

---

## 9. What the numerical companion should measure

One precommit, read-only against the existing production cells `m = N = 13, 23, 43, 83,
163` (the frozen edge-ledger schedule; `dps` 240 for `m ≤ 43`, 360 for `m = 83`, and the
existing higher setting for `m = 163`), importing the unmodified `CCMArbBuilder` and the
already-resolved ground eigenpair — **no new solve, no new matrix.** It should print, for
`n = 1..8` and cut `n₀ ∈ {⌊L⌋, ⌊L²⌋}`: (i) the residual of LATTICE-1 and LATTICE-2 —
these must vanish to working precision, which validates the whole derivation of §3 for
free and is the cheapest possible check on this report; (ii) the four terms of LATTICE-2
separately — `D_n y_n`, `κ_n Ŝ`, `√2[W_ℝ(0,0)+Prime(0,0)+a_n+λ₁]`, `Ω_n^{ap}` — with
`Ω_n^{ap}` split at `n₀` into head (`j ≤ n₀`) and the surviving tail `ρ_n(n₀)` of §6;
(iii) the ratios `|ρ_n(n₀)|/|D_n y_n|` and `|κ_n Ŝ|/|D_n y_n|`, which decide whether the
`j > n₀` coupling is a remainder at all or the leading term; (iv) `min_n |D_n|` and its
trend in `L` — the non-circular new target of §7, and the quantity the plant sets to zero;
(v) `Ŝ` against the prediction `−1/(√2L²)` of S6; (vi) the tail mass
`Σ_{j>n₀}|y_j|/j²` and `Σ_{j>n₀} y_j/j²` — whether an `O(1/n₀)` a priori bound is even
numerically plausible; and (vii) `x_n` against `−d_n/(2L²)` for the S4 distinguishing
outcome. Everything here is `DIAGNOSTIC_NEVER_A_PROOF`: five cells license no cofinal
quantifier, and a favourable table would change only which of the two NEW_ANALYTIC items
of §7 is attacked first, never the code returned here.

---

## 10. Boundaries

`HONESTY_STATE: CHALLENGER_NOT_RH`. `PX_RH_CLAIM: NOT_MADE`. No Lean file was edited, no
numerical run was performed, nothing under `phase5_scripts/`, no precommit, no queue, no
verdict, no commit. `‖(D−λ₁)^{-1}‖`, a uniform absolute gap, an odd-sector floor, and the
desired bound were used nowhere — where they would have been needed, that is stated as the
failure. `κ_k`, `λ₂/λ₁` and the `x_n ≈ −1/2` observation are relay from the wall card and
the 2026-09-03 odd-Gram report and were not re-verified here.

Per the judge's `f788d2fa` directive the front returns to the projective two-jet route
`|A| L^{5/2} √p = O(1)`, carrying forward LATTICE-1/2/3 as the exact statement of what the
lattice equation contains, and `P59_ARCH_PRIME_DIAGONAL_DEFECT_NONDEGENERACY` as the one
new non-circular source object this preflight produced.
