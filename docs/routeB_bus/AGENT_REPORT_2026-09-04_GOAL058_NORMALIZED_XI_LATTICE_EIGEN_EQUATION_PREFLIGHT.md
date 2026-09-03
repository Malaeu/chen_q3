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

---

## §11 Re-derivation 2026-09-04: NO ERROR FOUND in §1 / LATTICE-1 / LATTICE-2 / LATTICE-3 — but two magnitude claims elsewhere are wrong and are corrected here

Trigger: owner assertion that §1 or §3 carries an error. The three identities and the
source dictionary were re-derived from scratch, line by line, against the literal code of
`docs/routeB_bus/phase5_scripts/edge_ledger_build.py` (`q_nm`, `w02`, `wr`, `prime`,
`tau_entry`, `even_block`) — **not** against §1. Result: **NO ERROR FOUND** in §1, §2,
LATTICE-1, LATTICE-2 or LATTICE-3, including every factor of `2`, every `√2`, every sign,
every index range, and the additive constant `1/(√2L²)` in `Ŝ`. Two claims **outside**
those sections are wrong and are corrected in §11.4; both stem from one root cause (§11.3).
The code, the closure decision and the first surviving remainder term are unchanged.

### §11.1 The checks that were actually performed

Each line below was re-derived from the builder's own expression, not from §1.

1. `w02(n,m) = 32 L sinh²(L/4)(L²−16π²mn)/((L²+16π²m²)(L²+16π²n²))`. Hence
   `w02(n,0) = A_L/d_n = p_n` ✔, `w02(0,0) = 32 sinh²(L/4)/L = A_L/L²` ✔,
   `w02(n,n) = A_L(L²−16π²n²)/d_n²` ✔.
2. Rank-two factorization: `2𝒞_n𝒞_m = A_L L²/(d_nd_m)` and `2𝒮_n𝒮_m = 16π²A_L nm/(d_nd_m)`
   (using `A_L·16π² = 512π²L sinh²(L/4)`), so `w02 = 2𝒞𝒞ᵀ − 2𝒮𝒮ᵀ` ✔; `𝒞_0 = 4 sinh(L/4)/√L`,
   `2𝒞_0𝒞_n = A_L/d_n` ✔, `𝒮_0 = 0` ✔.
3. `q_nm(n,0,y) = (sin0 − sin(2πny/L))/(π(n−0)) = −sin(2πny/L)/(πn)` ✔ — independently
   confirmed by the literal `K10`, `K20` kernels in
   `CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean`.
4. `wr(n,0) = (α_0 − α_n)/(n−0) = −α_n/n` with `α_0 = arb(0)` from `_alpha`; so
   `a_n = −wr(n,0) − prime(n,0) = α_n/n + P_n/(πn)` ✔ and `b_n = τ(n,0) = p_n + a_n` ✔.
5. Symmetry `τ(n,m) = τ(m,n)`: `w02` symmetric ✔; `wr(m,n) = (α_n−α_m)/(m−n) = wr(n,m)` ✔;
   `q_nm(m,n,y) = q_nm(n,m,y)` ✔. Needed because `even_block`'s cache key sorts the pair.
6. Antipodal symmetry `τ(−i,−j) = τ(i,j)` verified separately for all three parts, hence
   `τ(0,−j) = τ(0,j)` (so `even[0,j] = √2 b_j` is the orthonormal-basis entry) ✔ and
   `⟨e_i⁺,K e_j⁺⟩ = τ(i,j)+τ(i,−j) = even[i,j]` ✔. So `K̃` **is** the matrix of `K` in the
   orthonormal even basis and `y_n = √2 x_n` ✔.
7. `τ(n,−n) = b_n`, re-derived directly from the builder rather than from the Lean Loewner
   theorem: `w02(n,−n) = A_L(L²+16π²n²)/d_n² = A_L/d_n = w02(n,0)` ✔;
   `wr(n,−n) = (−α_n−α_n)/(2n) = −α_n/n = wr(n,0)` ✔;
   `q_nm(n,−n,y) = −2sin(2πny/L)/(2πn) = q_nm(n,0,y)` ✔. Hence `K̃ₙₙ = τ(n,n) + b_n` ✔.
8. **(★) re-derived component by component**, not quoted from Lean:
   pole `w02(n,j)+w02(n,−j) = 2A_LL²/(d_nd_j)`, and
   `2(B_n^{pole}−B_j^{pole})/(n²−j²) = 2A_L(n²d_j − j²d_n)/(d_nd_j(n²−j²))` with
   `n²d_j − j²d_n = L²(n²−j²)` exactly ✔;
   arch `wr(n,j)+wr(n,−j) = 2(jα_j − nα_n)/(n²−j²)`, and `B_n^{arch} = nα_n` ✔;
   prime `= 2(js_j − ns_n)/(π(n²−j²))` per prime power, and `B_n^{prime} = nP_n/π` ✔.
   All three match `K̃ₙⱼ = 2(B_n−B_j)/(n²−j²)`, `B_n = n²b_n`.
9. `(SPLIT)`: `2b_j(j²−n²) + 2n²b_j − 2n²b_n = 2j²b_j − 2n²b_n` ✔.
10. LATTICE-1 re-derived twice by different groupings (once forming `T_{nj} = K̃ₙⱼ −
    y_nK̃₀ⱼ` first, once keeping `S` atomic); both give
    `R(y)_n = √2(b_n+μ−τ(0,0)) + (τ(n,n)−b_n−μ)y_n + Ω_n`, unconditional for `y₀=1` ✔.
11. Pole divided difference: `d_n − d_j = 16π²(n²−j²)` gives
    `(p_j−p_n)/(j²−n²) = −16π²A_L/(d_nd_j)` exactly ✔, hence
    `Ω_n^{pole} = −κ_n Σ_{j≠n} y_j/d_j`, `κ_n = 32π²A_Ln²/d_n = 1024π²L sinh²(L/4)n²/d_n` ✔.
12. Diagonal pole cancellation: `w02(n,n) − w02(n,0) = A_L(L²−16π²n²−d_n)/d_n²
    = −32π²A_Ln²/d_n² = −κ_n/d_n` ✔ — cancels the excluded `j=n` term exactly.
13. `√2·(w02(0,0) − w02(n,0)) = √2·16π²A_Ln²/(L²d_n) = κ_n/(√2L²)` using `32/√2 = 16√2` ✔ —
    this is where the additive constant `1/(√2L²)` in `Ŝ` comes from.
14. `D_n = (τ(n,n)−b_n)_{ap} − λ₁ = −wr(n,n) − prime(n,n) − a_n − λ₁` ✔; the builder's
    diagonal `wr(n,n) = 2γ_n − 2β_n` with `constant = (γ + log(4π(m−1)/(m+1)))/2 = G_L/2`
    carries `G_L` with coefficient exactly `1`, matching the Lean `ccmQKernel(n,n,0)/2 = 1`
    prefactor ✔ (a real factor-2 trap, checked, and it is correct).
15. `prime(n,n) = Σ Λ(k)k^{-1/2}·2(1−log k/L)cos(2πn log k/L)`, `prime(0,0) =
    2ΣΛ(k)k^{-1/2}(1−log k/L)` ✔.
16. LATTICE-3: `16π²j²/d_j = 1 − L²/d_j` ⟹ `1/d_j = (1−L²/d_j)/(16π²j²)`; with `y_j = √2x_j`
    and `Σ_{j≤N} x_j/j² = (E−π²/6)/2` this gives the boxed identity ✔.
17. **Independent third route for `κ_n` and the additive constant.** In the even sector the
    `W02` block is exactly `c̃c̃ᵀ` with `c̃₀ = √2𝒞₀`, `c̃_j = 2𝒞_j`, so the pole part of
    `R(y)_n` is `(c̃_n − y_nc̃₀)⟨c̃,y⟩`. Direct computation gives
    `⟨c̃,y⟩ = 8L^{3/2}sinh(L/4)·Ŝ` — **the additive constant `1/(√2L²)` is precisely the
    normalized centre contribution `√2𝒞₀`** — and consistency of the two accountings
    requires `κ_n = (√2c̃₀ − c̃_n)·8L^{3/2}sinh(L/4)`, which evaluates to
    `1024π²L sinh²(L/4)n²/d_n` ✔✔. This reproduces `κ_n` **and** the constant from a route
    that never uses the divided-difference algebra of §3.
18. Explicit `n = 1,2,3` coefficients of §2 recomputed from `(★)`: `(2/3)(4b₂−b₁)`,
    `(1/4)(9b₃−b₁)`, `(2/15)(16b₄−b₁)`, `(2/5)(9b₃−4b₂)`, `(1/6)(16b₄−4b₂)`,
    `(2/7)(16b₄−9b₃)`, and the `n↔j` symmetry of each ✔.
19. Index ranges: even block `0..N`; every `Σ_{j≥1}` means `Σ_{j=1}^{N}`; `Ω_n` excludes
    `j=n`; `N = m` on the production schedule ✔.
20. Plant: LATTICE-1 reproduces `y₁ = −b/t` exactly, and `D₁ = 0` there because the plant's
    pole `c̃ = (b/√t, √t)` gives `c̃₀c̃₁ = b` (so the ap part of `K̃₀₁` is `0`) and `c̃₁² = t`
    (so the ap part of `K̃₁₁` is `λ`) ✔; also `⟨c̃,y⟩ = b/√t − b/√t = 0`, i.e. `Ŝ = 0`,
    confirming §5 ✔.

### §11.2 Is Probe 10's confirmation circular? — Mostly not, and the one exposed ingredient is still tested

Read from `docs/routeB_bus/phase5_codex/lattice_equation.py` (read-only). The answer is
**no** for every load-bearing quantity, and the reason is that the probe grounds one side
of each comparison in the builder's own methods:

- `b[j] = even[0,j]/√2` — taken **from** the builder's `even_block`, not from §1;
  `tau_nn = even[n,n] − b[n]`; `R_n = Σ_j even[n,j]y_j − μ y_n` — the left side of both
  identity residuals is a builder mat-vec. Non-circular.
- `p[j] = A_L/d[j]` is §1's formula, but `pole_defect` compares it against
  `builder.w02(j,0)`; `a[j] := b[j] − p[j]` is compared against
  `−builder.wr(j,0) − builder.prime(j,0)`; `b[j]` against `builder.tau_entry(j,0)`;
  `τ(0,0)` against `A_L/L² − wr(0,0) − prime(0,0)`; `(★)` against `even[i,j]`;
  `D_n` against `−wr(n,n) − prime(n,n) − a_n − μ`; `Ω^{pole}` against `−κ_nΣy_j/d_j`;
  `w02(n,n) − w02(n,0)` against `−κ_n/d_n`. All non-circular.
- The one ingredient with **no** independent check of its own is the additive constant
  `1/(√2L²)` inside `Ŝ` (it appears only in `t2b = κ_n·shat`). It is nevertheless tested,
  because every other term of the LATTICE-2 residual (`R_n`, `t2a`, `t2c`, `Ω^{ap}`) is
  builder-grounded and `κ_n` is separately validated: a wrong constant would leave
  `id2 ≈ κ_n·δ`, i.e. `O(10)`, not `1e-237`. Combined with the independent derivation of
  the same constant in check 17 above, it is confirmed twice.
- **Not** checked by Probe 10, and therefore still resting on my algebra alone:
  LATTICE-3 (no `E` column in the probe) — re-derived by hand here, check 16; and the
  naming of `a_n`'s components as `(J_n+P_n)/(πn)`, since the probe carries `a_n` as one
  lump. See the naming caveats in §11.5.
- The `eigen resid` column is a solver-quality number, not an identity check, and the
  probe says so.

Conclusion: the `1e-233` agreement is a genuine confirmation of LATTICE-1/2 and of the §1
dictionary against the builder, not a self-consistency artifact.

### §11.3 Root cause of the two wrong claims: an empty asymptotic regime

Several statements in §4 and §8 were written "for `n ≪ L`", meaning the regime where the
pole denominator is centre-dominated, `16π²n² ≪ L²`. The correct condition is

```
n ≪ L/(4π) ,   which for n = 1 requires L > 4π ≈ 12.566 , i.e. m > e^{4π} ≈ 2.9·10^5 .
```

**No computed cell is in that regime, and none can be:** at `m = 163`, `L² = 25.95` while
`16π² = 157.91`, so `d_n` is dominated by `16π²n²` by a factor `≥ 6.1` at every cell and
every `n ≥ 1`. The whole "low-mode plateau" picture is asymptotic only. In the actual
regime `16π²n² ≫ L²` one gets instead `κ_n → 2A_L = 64L sinh²(L/4)`, **independent of `n`**
— which is exactly what Probe 10's `κ_nŜ` column shows (`7.500, 7.732, 7.777, 7.792, …`
saturating at `m = 13`, where `2A_L = 77.2` and `κ_1 = 74.1`).

### §11.4 The two corrections

**(a) §8 S4 — wrong line:** *"Dropping `Ω_n` in LATTICE-1 and keeping only the pole gives
`x_n = (τ(0,0)−b_n)/(τ(n,n)−b_n) = −d_n/(2L²) = −½ − 8π²n²/L²`, which matches the relayed
numerical `x_n ≈ −1/2` of the odd-Gram report S1 startlingly well."*

The algebra `−d_n/(2L²)` is **correct**; the claimed numerical match is **false**, and its
`= −½ − 8π²n²/L²` reading is only meaningful in the empty regime of §11.3. At the computed
cells (`n = 1`):

| m | L | `−d₁/(2L²)` (pole-only) | `y₁ = (D₁y₁)/D₁` (Probe 10 (ii)/(iv)) | `x₁ = y₁/√2` |
|---:|---:|---:|---:|---:|
| 13 | 2.564949 | −12.501 | −1.2098 | −0.8555 |
| 23 | 3.135494 | −8.531 | −1.2723 | −0.8996 |
| 43 | 3.761200 | −6.081 | −1.3156 | −0.9303 |
| 83 | 4.418841 | −4.544 | −1.3439 | −0.9503 |
| 163 | 5.093750 | −3.543 | −1.3624 | −0.9634 |

The pole-only value is off by a factor `3.7`–`14.6`, and the true `x₁` is drifting toward
`−1`, not `−1/2`. **Corrected statement of S4:** the pole-only ratio `−d_n/(2L²)` is an
artifact twice over — it is obtained by dropping a term (`Ω_n^{pole}`) of exactly the same
order, which LATTICE-2 shows cancels the whole `y_n` coefficient; and it does not match the
data at any computed cell. The relayed S1 reading "`x_n ≈ −1/2`" is a `1/n²`-**weighted-sum**
statement about `E`, not a pointwise one: pointwise `x₁ ≈ −0.86 … −0.96`. The distinguishing
measurement proposed in the old S4 is superseded by the table above, which already
discriminates: reading (A) ("pointwise limit shape `−1/2`") is **refuted at `n = 1`**; what
survives is a possible pointwise limit near `−1`, untested for `n ≥ 2`.

**(b) §8 S6 — wrong line:** *"`Ŝ` must be exponentially small … `Σ_j y_j/d_j ≈ −1/(√2L²)`
to high relative accuracy."* **Refuted by Probe 10 (v)**, and wrong in its derivation: the
bound it rested on is `|Ŝ| ≲ |D_n y_n|/κ_n`, and since `κ_n` and the crude bound on `D_n`
both carry the same pole scale `√m`, no exponential smallness follows — the honest bound
degrades like `L³` relative to `1/(√2L²)` and is vacuous beyond `L ≈ 12`. The data:

| m | `Σ_j y_j/d_j` | `1/(√2L²)` | `Ŝ` | `Ŝ·√2L²` |
|---:|---:|---:|---:|---:|
| 13 | −6.3747e−3 | 0.1074799 | 0.1011052 | 0.941 |
| 23 | −6.4414e−3 | 0.0719239 | 0.0654825 | 0.910 |
| 43 | −6.3902e−3 | 0.0499841 | 0.0435940 | 0.872 |
| 83 | −6.2490e−3 | 0.0362133 | 0.0299643 | 0.827 |
| 163 | −6.0469e−3 | 0.0272527 | 0.0212058 | 0.778 |

**Corrected statement (new S6).** `Ŝ` is *not* small: it is `1/(√2L²)` reduced by only
`6%→22%`. The real content of the column is a different and sharper observation:
`Σ_{j=1}^{N} y_j/d_j = −6.2·10⁻³ ± 3%` across `L ∈ [2.56, 5.09]` — **essentially
independent of `m`**, while `1/(√2L²)` falls by a factor `4` over the same range. That
near-constancy is the fact worth explaining, and it is new. `DIAGNOSTIC_NEVER_A_PROOF`.

**(c) §4 point 3 — corrected mechanism, unchanged conclusion.** The line
*"`κ_n ≍ 256π²√m n²/L` for `n ≪ L` is exponentially large in `L`, while the left side
`D_n y_n` is of arch/prime size `O(√m)`"* is wrong twice: the regime is empty (§11.3), and
the crude `O(√m)` bound on `D_n` carries the same pole scale, so no separation follows from
those two lines. The corrected version: at the computed cells `κ_n ≈ 2A_L = 64L sinh²(L/4)`
(`n`-independent) and `Ŝ ≈ 1/(√2L²)`, so `κ_nŜ ≈ 45.3 sinh²(L/4)/L`, which grows like
`√m/L`; measured `D_n` is `O(1)` (`0.047 … 4.13`, Probe 10 (iv)), giving the measured
dominance `|κ_nŜ|/|D_ny_n| = 2.86 … 2.1·10⁵`. The dominance is therefore **real and
measured**, not asserted from an asymptotic that does not apply. The conclusion of §4
point 3 — that LATTICE-3 makes the equation a fixed-point relation for `E` — is exact
algebra and never depended on any magnitude.

**(d) §9 item (v) — mis-stated test.** It asked for "`Ŝ` against the prediction
`−1/(√2L²)`", whereas S6's prediction was `Σ_j y_j/d_j ≈ −1/(√2L²)`, i.e. `Ŝ ≈ 0`. Probe 10
implemented the literal wording and gated `|Ŝ + 1/(√2L²)| ≤ 0.5|1/(√2L²)|` (FAIL, rel dev
`1.78–1.94`). **What it should have printed** is the gate `|Ŝ| ≤ 0.5·|1/(√2L²)|` — which
also FAILS, with the much more informative ratios `Ŝ·√2L² = 0.941, 0.910, 0.872, 0.827,
0.778` of the table above. Both readings of S6 are refuted; the corrected quantity to track
is `Σ_j y_j/d_j` itself (near-constant `≈ −6.2e−3`).

### §11.5 Two naming hazards, recorded

- `B_n = n²b_n = n·β_n` uses `β = ccmBetaScalar` (`β_n = n·τ(n,0)`, Lean). The **builder's**
  `self.beta[n]` is an unrelated archimedean quantity used in `wr(n,n) = 2γ_n − 2β_n`.
  Anyone re-implementing §1 from the builder must not identify the two.
- `a_n = (J_n+P_n)/(πn)` names the builder's `α_n/n + P_n/(πn)` via the cross-representation
  identification `α_n = J_n/π` (builder `_alpha` ↔ literal `ccmWREntry` integral). That
  identification was checked here only for its leading asymptotics (`α_n → 1/4` from
  `Im ψ(1/4+iπn/L)/2 → π/4`, and `J_n → π/4` from `∫₀^∞ sin(at)/t = π/2` with the `1/(2x)`
  singular part) — it is **not** re-derived exactly, and Probe 10 never separates `J_n` from
  `P_n`. Nothing in LATTICE-1/2/3 depends on it; only the *naming* of the components in §6's
  `ρ_n` and in §9's instrumentation does. The builder-literal safe form is
  `a_n = −wr(n,0) − prime(n,0)`.
- §2's rows list `j = 2,3,4` explicitly and then re-state the general term as a sum from
  `j ≥ 2`; that is a presentation ambiguity (the explicit terms are *instances* of the sum,
  not additional to it), not a mathematical error.

### §11.6 What does not change

The code stays `P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP`. The closure decision
of §4 rests on points 1 (non-causality: upward needs `j>n`, downward loses all decay) and 2
(the `j>n₀` remainder is the `1/j²`-weighted tail of `E` itself) plus LATTICE-3 — all three
magnitude-free and all three unaffected. The first surviving remainder term of §6 is
unchanged. Probe 10's ratio table (iii) independently **strengthens** the failure: at the
small cut `|ρ_n(n₀)|/|D_n y_n| > 1` from `n = 4`–`7` upward at every cell (up to `9.5·10²`),
so for most modes the "remainder" is the leading term, not a remainder. Probe 10 (iv) also
adds an unforeseen positive datum for the one non-circular new target: `D_1 ≈ 0.028 · L³`
across the five cells (`0.0268, 0.0275, 0.0284, 0.0297, 0.0312`), i.e. the arch/prime
diagonal defect grows rather than collapsing — though `min_{n≤8}|D_n|` stays at
`0.047–0.117` with `min/max ≈ 0.015–0.055`, so individual modes still come close to the
plant's degenerate `D_n = 0`. `DIAGNOSTIC_NEVER_A_PROOF`; five cells license no cofinal
quantifier.
