# Agent report — Goal 058: reciprocal-mode ξ-lattice energy source preflight

Date: 2026-09-04
Executor: Linux-Claude subagent (Opus), standing in for Codex (owner decision 2026-09-03 late)
Task: `docs/Codex/TASK_2026-09-04_goal058_reciprocal_mode_xi_lattice_energy_source_preflight.md`
Refines (does not replace): `AGENT_REPORT_2026-09-04_GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT.md`
Mode: PAPER_AND_SOURCE_READ_ONLY — no Lean edit, no numerical run, no commit, nothing under
`phase5_scripts/`, no precommit, no queue, no verdict

```yaml
TASK_ID: GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT
CODE: P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP
JUDGE_PREDICTION_SCORED: [P_LOW_MODE_RECURRENCE_CLOSES_BEFORE_GAP, 0.40, REFUTED]
WHICH_HALF_OF_THE_CODE: GAP        # NOT the dense tail — probe 10 refuted that half
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
ROUTE_PROMOTION: false
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
```

**One line.** The identity asked for **exists, is exact, uses no inverse anywhere, and its right
side is built only from source entries and the Ξ-sample residual** — it is (MAIN-P) in §3:
`Σ_{n≤N} D_n|Δ_n|²/n² − 32π²A_L(Σ_{n≤N}Δ_n/d_n)² + 2⟨Δ,L[a]Δ⟩ = −Σ_n Δ_n𝓡(y)_n/n² + (ν−λ₁)Σ_n Δ_n(1−y_n)/n²`
— but its left side is not the target: it is the odd-sector quadratic form `⟨RΔ,(D−λ₁)RΔ⟩`, whose
own diagonal `δ_n = D_n − 32π²A_L n²/d_n²` is, by arithmetic on probe 10's committed `D_n` table,
**`1.4·10⁻⁴` at `n=1, m=163` while its two constituents are `4.129` each** — a four-digit
cancellation. The target `‖RΔ‖²` is reached only by dividing by that residue, i.e. by an
odd-sector floor. The one genuinely new fact is its *scale*: this route does **not** pay
`1/λ₂ ≈ 10^{300}`; it pays `1/δ_odd ≈ 10⁴`, roughly flat over the five cells.

---

## 0. Verification status of each input

| Input | Status |
|---|---|
| `proposition59PoleKernel_at_lattice_sign`, `proposition59RawTransform_at_zero_eq_sqrt`, `proposition59Pole L k = 2πk/L` | read literally in `Q3/Proofs/RouteB/Proposition59EntireTransform.lean` lines 13, 103–115, 177–205 |
| `ccmBetaScalar mProject n = n·τ(n,0)`, `ccmWeilTau_structured_offdiag`, `ccmWeilMatFinite_commutator` | read literally in `CCMFiniteWeilSourceCommutator.lean` lines 20, 282, 374; `#print axioms` present, **not** re-run through `lake` (read-only) |
| `centeredXi z = riemannXi (1/2 + I z)` | read in `ClassicalXiInterface.lean` line 17 |
| `parity_blocks` builds the **even** block only (`even[i,j] = k(i,j)+k(i,−j)`, `even[0,j] = √2 k(0,j)`) | read in `phase5_scripts/edge_ledger_build.py` lines 321–343 — the **odd** block is not built by the current builder |
| source dictionary `d_n, A_L, p_n, a_n, b_n, τ(n,n), τ(0,0), D_n` | reused verbatim from the 2026-09-04 eigen-equation preflight §1 (itself read off the literal constructors) |
| `D R − R D = b rᵀ − r bᵀ`, `rᵀAb = 0`, `E`, `κ = (L²/4π²)E` | reused verbatim from the 2026-09-03 odd-Gram preflight §2–§4 (C5 verdict `3dc82357`) |
| probe-10 numbers (`D_n` per mode, `κ_nŜ/D_ny_n`, `ρ_n/D_ny_n`, `Σ_j y_j/d_j`, `x_n`) | **relay** from `docs/routeB_bus/phase5_codex/out/lattice_equation.md`, committed; not re-run here |
| `δ_n`, `q_pole`, `‖ĝ‖` numbers in §5 and §10 | **my arithmetic on the committed `D_n` table and the closed-form pole entries** — pencil arithmetic, not a new probe; the companion must confirm |

All algebra below is my own and is checkable by hand; every coefficient is named by its source
formula.

**Notation reconciliation (mandatory — the two preflights use `y` for opposite objects).** The
2026-09-04 eigen-equation preflight calls `y` the *ground* row in even-block coordinates
(`y_n = √2 ξ_n/ξ_0`). This task, following verdict H4, calls `x` the ground row and `y` the
Ξ-sample row, both in **raw ±N coordinates**. This report uses the task's convention and works on
the raw carrier throughout (S2 of the odd-Gram report: never mix the two bases). The even-block
translation is `(·)^even_n = √2 (·)^raw_n` for `n ≥ 1`, identity at `n = 0`.

---

## 1. Item 1 — the exact target row `y` in source coordinates

Carrier `M = {−N,…,N}\{0}`, `K = [[a₀, bᵀ],[b, D]]`, `a₀ = τ(0,0)`, `b_n = τ(n,0)`,
`D_{nm} = τ(n,m)`; `X = diag(n)`, `R = X⁻¹`, `r = Rη` (`r_n = 1/n`), `β = Xb`.

The P59 lattice node is `t_n := proposition59Pole L n = 2πn/L` (`Proposition59EntireTransform.lean`
line 13). By `proposition59PoleKernel_at_lattice_sign` and `proposition59RawTransform_at_zero_eq_sqrt`,

```
F(t_n) = √L · (−1)^n ξ_n ,      F(0) = √L · ξ_0 ,      so  F(t_n)/F(0) = (−1)^n x_n ,
```

with `x_n = ξ_n/ξ_0` the ground row. Therefore the target row is, **exactly**,

```
┌──────────────────────────────────────────────────────────────────────────────┐
│  y_n = (−1)^n · centeredXi(2πn/L) / centeredXi(0) ,   n ∈ M ,   y_0 = 1       │
│  centeredXi(z) = riemannXi(1/2 + i z)  (ClassicalXiInterface.lean:17)         │
│  centeredXi(0) = riemannXi(1/2) = ξ(1/2)                                      │
└──────────────────────────────────────────────────────────────────────────────┘
```

`y` is **even** (`Ξ` is even and `(−1)^{−n} = (−1)^n`), real on the real lattice, and
`Δ := x − y` is even with `|Δ_n| = |x_n − y_n| = |F(t_n)/F(0) − Ξ(t_n)/Ξ(0)|`, i.e. exactly the
`Δ_n` of the wall card records 9–10 and of verdict H1. The target of the atom is

```
‖RΔ‖²_+ := Σ_{n=1}^{N} |Δ_n|²/n²        ( = ½‖RΔ‖²_M on the symmetric carrier ).
```

Two facts about `y` that are used below and are not assumptions: `y_0 = 1` (common central
normalisation, the S3 fact), and `y_n → 0 superexponentially in n` once `t_n = 2πn/L ≳ 3`, so
`(η − y)_n = 1 − y_n → 1` on all but `O(L)` modes.

---

## 2. Item 2 — the exact residual `𝓡(y)` in source entries

For **any** even row `w` with `w_0 = 1`, put `ν(w) := (Kw)_0 = a₀ + 2Σ_{m≥1} b_m w_m` and
`𝓡(w)_n := (Kw)_n − w_n ν(w)`. Splitting the Loewner off-diagonal exactly,
`τ(n,m) = b_m + n(b_n − b_m)/(n − m)` (one line from `ccmWeilTau_structured_offdiag`), pairing
`±m`, and cancelling the two `w_n²` terms gives the raw-carrier form of LATTICE-1 — unconditional,
no eigenvector hypothesis, no `λ₁`:

```
┌──────────────────────────────────────────────────────────────────────────────┐
│ RAW-LATTICE-1                                                                │
│  𝓡(w)_n = (b_n + ν − a₀) + (τ(n,n) − b_n − ν)·w_n + Ω_n(w)                  │
│  Ω_n(w) := 2n² Σ_{m≥1, m≠n} (b_n − b_m) w_m /(n² − m²)                       │
└──────────────────────────────────────────────────────────────────────────────┘
```

(Multiplying by `√2` reproduces LATTICE-1 of the previous report verbatim; `τ(n,−n) = b_n` is the
`m = −n` term and contributes to `Σ b_m w_m`, not to `Ω`.) Substituting `w = y` and the literal
constructors:

```
𝓡(y)_n = b_n + 2Σ_{m≥1} b_m y_m + (τ(n,n) − b_n − a₀ − 2Σ_{m≥1} b_m y_m)·y_n
         + 2n² Σ_{m≥1,m≠n} (b_n − b_m) y_m/(n² − m²)
```

with, to the last literal (source dictionary of the previous preflight §1, re-derived):

```
d_n = L² + 16π²n² ,   A_L = 32 L sinh²(L/4) ,   L = ccmL m = log m
p_n = W02(n,0)  = A_L/d_n                                       ← ccmW02Entry(n,0)
a_n = (J_n + P_n)/(πn)                                          ← −ccmWREntry(n,0) − ccmPrimeEntryN1(n,0)
      J_n = ∫_{(0,L]} e^{x/2} sin(2πnx/L)/(2 sinh x) dx
      P_n = Σ_{k=2}^{m} Λ(k) k^{-1/2} sin(2πn log k/L)
b_n = p_n + a_n = τ(n,0)                                        ← ccmWeilTauN1 n 0
τ(n,n) = A_L(L²−16π²n²)/d_n² − W_ℝ(n,n) − Prime(n,n)
τ(0,0) = A_L/L² − W_ℝ(0,0) − Prime(0,0) = a₀
W_ℝ(n,n) = G_L + ∫_{(0,L]} [e^{x/2}(2(L−x)/L)cos(2πnx/L) − 2]/(2 sinh x) dx ,  G_L = γ + log(4π(e^L−1)/(e^L+1))
Prime(n,n) = Σ_{k=2}^{m} Λ(k) k^{-1/2}·2(1 − log k/L) cos(2πn log k/L)
```

`𝓡(y)` is computable from Ξ samples and source entries alone: it contains no eigenvector and no
`λ₁`. (`ν(y)` likewise.) The only spectral scalar that appears anywhere below is `λ₁`, and it
enters as one number with `0 < λ₁ ≤ a₀` by Rayleigh at `e₀` and `λ₁ ≈ 10^{−1.9m}` by relay.

`𝓡(x) = 0` is the ground eigen-equation; `ν(x) = λ₁`.

---

## 3. Item 3 — the identity. Attempts (a) and (b) converge to one object

### 3.1 The exact error equation (no inverse)

From `𝓡(x) = 0`, i.e. `(D − λ₁)x = −b`, and `Dy − ν y = 𝓡(y) − b`:

```
(EQ-1)   (D − λ₁)Δ = −𝓡(y) − (ν − λ₁) y ,        ν − λ₁ = −bᵀΔ .
```

Attempt **(b)** is the C5 coboundary applied to `Δ`. Multiply (EQ-1) by `R` and use the
reciprocal-mode displacement `DR − RD = b rᵀ − r bᵀ` (odd-Gram report §2, one `submatrix` from
`ccmWeilMatFinite_commutator`), together with the two parity facts `rᵀΔ = 0` (`r` odd, `Δ` even)
and `bᵀΔ = λ₁ − ν`:

```
┌──────────────────────────────────────────────────────────────────────────────┐
│ (COB)   (D − λ₁)·RΔ  =  −R𝓡(y)  +  (ν − λ₁)·R(η − y)                        │
└──────────────────────────────────────────────────────────────────────────────┘
```

This is the exact analogue of C5's `(D−λ₁)(Rx) = −Rb + (a₀−λ₁)r` for the **error** row: the
ground vector has been eliminated, the right side is Ξ-samples plus source entries, and no
resolvent has been written. At `y = η` (i.e. `Ξ` replaced by the constant 1) it degenerates to
`0 = −R𝓡(η)`, the correct trivial case.

Attempt **(a)** (expand `⟨R²Δ, (D−λ₁)Δ⟩` and commute `R` through) gives literally the same
equation: `R(D−λ₁) = (D−λ₁)R − brᵀ + rbᵀ`, and both rank-one terms die on `Δ` by the same two
parity facts. **(a) and (b) are one attempt, not two.**

### 3.2 The odd block in source coordinates — new normal form

Pairing `(COB)` with `RΔ` needs the odd block of `D`. From `τ(n,m) = (β_n−β_m)/(n−m)`,
`β_n = n b_n`, `β_{−n} = −β_n`:

```
┌──────────────────────────────────────────────────────────────────────────────┐
│  D^odd_{nn} = τ(n,n) − τ(n,−n) = τ(n,n) − b_n                                │
│  D^odd_{nm} = τ(n,m) − τ(n,−m) = 2nm (b_n − b_m)/(n² − m²)      (n ≠ m ≥ 1)   │
│  i.e.  D^odd_off = 2 X L[b] X ,   L[b]_{nm} := (b_n−b_m)/(n²−m²)             │
└──────────────────────────────────────────────────────────────────────────────┘
```

This is the odd companion of the even normal form `(★)` of the previous report
(`K̃_{nm} = 2(B_n−B_m)/(n²−m²)`, `B_n = n² b_n`): the **even** block is the Loewner matrix of
`u ↦ u·b(u)` at the squared nodes `u = n²`, the **odd** block is `2X ·` the Loewner matrix of
`b` itself at the same nodes. The reciprocal weight is the natural one here because
`X·(RΔ) = Δ`: the odd form evaluated at `u = RΔ` is a form in `Δ`.

### 3.3 The identity

Pair `(COB)` with `RΔ` and expand both sides over positive indices
(`⟨v,w⟩_M = 2Σ_{n≥1}v_nw_n` for `v,w` of equal parity):

```
┌──────────────────────────────────────────────────────────────────────────────┐
│ (MAIN)                                                                       │
│  Σ_{n=1}^{N} δ_n |Δ_n|²/n²  +  2 Σ_{n≠m≥1} (b_n−b_m) Δ_nΔ_m/(n²−m²)         │
│      =  − Σ_{n=1}^{N} Δ_n 𝓡(y)_n /n²  +  (ν−λ₁) Σ_{n=1}^{N} Δ_n(1−y_n)/n²   │
│                                                                              │
│  δ_n := τ(n,n) − b_n − λ₁            (odd-sector diagonal, source)           │
└──────────────────────────────────────────────────────────────────────────────┘
```

Both sides equal `½⟨RΔ,(D−λ₁)RΔ⟩_M`. Now extract the pole from `b = p + a`. Exactly,

```
(p_n − p_m)/(n² − m²) = −16π² A_L/(d_n d_m) ,     (τ(n,n) − b_n)_pole = −32π² A_L n²/d_n² ,
```

so the pole part of the bilinear form is `−32π²A_L[(Σ_nΔ_n/d_n)² − Σ_nΔ_n²/d_n²]` and the
excluded-diagonal correction `+32π²A_LΣΔ_n²/d_n²` **cancels the pole diagonal identically** —
the same cancellation as LATTICE-2, now at the quadratic level. With
`δ_n = D_n − 32π²A_L n²/d_n²` and `D_n := −W_ℝ(n,n) − Prime(n,n) − a_n − λ₁` (the previous
report's arch/prime diagonal defect, the object probe 10 measured):

```
┌══════════════════════════════════════════════════════════════════════════════┐
║ (MAIN-P)   exact, finite, no inverse, right side = Ξ-samples + source        ║
║                                                                              ║
║  Σ_{n=1}^{N} D_n |Δ_n|²/n²                                                   ║
║    −  32π² A_L ( Σ_{n=1}^{N} Δ_n/d_n )²                                      ║
║    +  2 Σ_{n≠m≥1} (a_n − a_m) Δ_nΔ_m/(n² − m²)                               ║
║  =  − Σ_{n=1}^{N} Δ_n 𝓡(y)_n/n²  +  (ν−λ₁) Σ_{n=1}^{N} Δ_n (1−y_n)/n²       ║
║                                                                              ║
║  A_L = 32 L sinh²(L/4),  d_n = L²+16π²n²,  a_n = (J_n+P_n)/(πn)              ║
╚══════════════════════════════════════════════════════════════════════════════┘
```

**What (MAIN-P) achieves.** The whole `W02` pole — the `e^{L/2}`-sized object that destroyed
probes 5–8 — enters the *energy* of the error row through exactly **one** scalar, squared:
`(Σ_nΔ_n/d_n)²`. Everything else is arch/prime. The target energy sits on the left with purely
source-computable weights `D_n`. Nothing on either side is an inverse, a norm of an inverse, a
gap, or a floor.

**One-sided companion (free, non-circular).** `D` is a principal submatrix of `K`, so Cauchy
interlacing gives `λ₁(K) ≤ λ_min(D)`, i.e. `(D − λ₁) ⪰ 0`. Hence the left side of (MAIN-P) is
`≥ 0`, giving the source inequality

```
(INEQ)   32π² A_L ( Σ_{n≤N} Δ_n/d_n )²  ≤  Σ_{n≤N} D_n|Δ_n|²/n²  +  2⟨Δ, L[a]Δ⟩ ,
```

an **upper** bound on the pole moment by the energy — the reverse of the direction the atom
needs, but a real by-product (see §10, by-product B1).

### 3.4 Why (MAIN-P) is nevertheless not the atom

To reach `Σ|Δ_n|²/n² ≤ …` from (MAIN-P) one must (i) divide by `min_n D_n`, (ii) dispose of the
arch/prime Loewner form `2⟨Δ,L[a]Δ⟩`, and (iii) **upper-bound the pole square**, which enters
with a minus on the left. Step (iii) is fatal on its own: writing
`1/d_n = (1 − L²/d_n)/(16π²n²)`,

```
16π² Σ_n Δ_n/d_n = 𝔐 − L² 𝔐₂ ,    𝔐 := Σ_{n≤N} Δ_n/n² ,   𝔐₂ := Σ_{n≤N} Δ_n/(n² d_n) ,
32π² A_L (Σ_nΔ_n/d_n)² = (A_L/8π²)(𝔐 − L²𝔐₂)² ,      |L²𝔐₂| ≤ Σ_n|Δ_n|/n² = W ,
```

so the term to be bounded is the **signed first moment of `Δ` squared** — the `W`-object of wall
card record 9 and the `N`-component that shell H1 was designed to *derive* from `‖RΔ‖`. The
identity therefore runs `moment² ⟹ energy`, i.e. backwards, with the amplification
`A_L/8π² ≈ L√m`. The single scalar `Σ_nΔ_n/d_n` can be isolated only by pairing `(COB)` with a
vector `u` solving `(D−λ₁)u = X·(1/d)` — a collapsed inverse. This is the same fixed point as
CURVBRIDGE, C5 and LATTICE-3, now at the quadratic level.

**Even-sector variant, checked and worse.** Symmetrising `R²(D−λ₁)` on the even block gives
pole part `2A_L L² [ 𝔐₂·(Σ_mΔ_m/d_m) − Σ_nΔ_n²/(n²d_n²) ]`: a *product* of two different
moments (not a square), a larger constant `2A_LL²`, and no diagonal cancellation. The odd /
reciprocal route of C5 is strictly the better representation, exactly as the judge predicted.

---

## 4. Attempt (c) — discrete Hardy / adjacent differences (verdict H2)

**Question.** Does the source equation give anything for `(Δ_n − Δ_{n−1})`?

**Answer: no, and the obstruction is structural, not quantitative.** Hardy runs
`Σ|∇Δ|² ⟹ Σ|Δ_n|²/n²`; it needs the gradient sum as an **input**, i.e. a strictly stronger
object than the target. Producing an equation for `∇Δ` requires an operator that shifts the mode
index. The algebra the source supplies is generated by `D`, by functions of `X`, and by rank-two
displacement terms; every commutator in it is another divided difference weighted by a function
of `X`. A shift is not in that algebra: `D` is dense and is not a Jacobi/band matrix, and there
is no three-term recurrence anywhere in the ledger.

Concretely, applying `∇` to (EQ-1) needs `[D,∇]`, whose entries are the **second divided
difference** of the source sequence `β` at the nodes `n−1, n, m`:

```
(∇D)_{nm} = D_{nm} − D_{n−1,m} = [β; n−1, n, m] ,
```

which is dense with only `|m−n|^{-2}` decay against a source sequence of size
`|β_m| ≤ A_L m/d_m + (|J_m|+|P_m|)/π`, `|P_m| ≤ Σ_{k≤m}Λ(k)k^{-1/2} = O(√m)`. The first
uncontrolled term of (c) is therefore `Σ_m [β;n−1,n,m]Δ_m`, an operator of source size `O(√m)`,
not a remainder. For the pole part this is explicit and rank-two:
`D^pole_{nm} = A_L(L² − 16π²nm)/(d_n d_m)`, whose `∇` is `O(A_L/L²)`.

(c) fails one step earlier than (a)/(b): it has no equation at all, not merely an uncontrolled
term in one.

---

## 5. Attempt (d) — the CONTRACTION reading (coordinator's request, after probe 10)

**The question, made precise.** Split the odd block of `D − λ₁` as
`diag(D_n) + [−32π²A_L ĝĝᵀ + Off^{ap}]`, where `ĝ_n := n/d_n` and
`Off^{ap}_{nm} := 2nm(a_n−a_m)/(n²−m²)` (this is exactly (MAIN-P) read as an operator). With
`u := RΔ`, the exact equation is

```
diag(D) u  =  h  +  32π² A_L ĝ (ĝᵀu)  −  Off^{ap} u ,     h := −R𝓡(y) + (ν−λ₁)R(η−y) ,
```

and the fixed-point/Jacobi reading closes **iff**

```
q := ‖ diag(D)^{-1}( 32π²A_L ĝĝᵀ − Off^{ap} ) ‖_{ℓ²→ℓ²}  <  1 ,
```

after which `‖RΔ‖ ≤ ‖diag(D)^{-1}h‖/(1−q)` with no inverse of `K−λ₁` anywhere. Two structural
points must be settled first, and both settle **in favour of the reading being well posed**:

1. `q` **is** an operator norm of pure source data. It does not need `y`, does not need the
   ground row, and does not need `λ₁` beyond the scalar shift. So the coordinator's question is
   answerable from source alone.
2. The rank-one term `(ν−λ₁)R(η−y)` is **not** an unknown: `ν = a₀ + 2Σ b_m y_m` is computable
   from Ξ-samples and source, and `λ₁ ≈ 10^{−1.9m}` is negligible against it. So the
   `y`-dependence sits entirely in the known right side `h`, not in the operator.

**Answer: reading (A). There is no contraction, and the failure is quantitative, from source
data alone.** The pole channel alone already exceeds 1. Its exact contribution is

```
q_pole = 32π² A_L · ‖ diag(D)^{-1} ĝ ‖ · ‖ ĝ ‖ ,       κ_n = 32π²A_L n ĝ_n , κ_n → 2A_L .
```

Arithmetic on probe 10's committed per-mode `D_n` (only `n ≤ 8` are measured, so every entry is a
**lower bound** for `q_pole`):

| m | L | A_L | 32π²A_L | ‖ĝ‖ | ‖diag(D)⁻¹ĝ‖ (n≤8) | **q_pole ≥** | 2A_L = max κ_n |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 13 | 2.5649 | 38.64 | 1.2202e4 | 7.719e-3 | 5.079e-2 | **4.78** | 77.3 |
| 23 | 3.1355 | 75.36 | 2.3801e4 | 7.700e-3 | 5.034e-2 | **9.23** | 150.7 |
| 43 | 3.7612 | 141.72 | 4.4759e4 | 7.625e-3 | 2.605e-2 | **8.89** | 283.4 |
| 83 | 4.4188 | 255.24 | 8.0612e4 | 7.507e-3 | 2.622e-2 | **15.87** | 510.5 |
| 163 | 5.0938 | 441.95 | 1.3958e5 | 7.360e-3 | 1.436e-2 | **14.75** | 883.9 |

`q_pole ≥ 4.8 … 15.9`, never below 1, and rising along the schedule (scaling
`32π²A_L‖ĝ‖² ≍ √m`, since `A_L ≍ 8L√m` and `‖ĝ‖² ≍ 1/(256π²L)`). **No contraction.**

**Why probe 10's 25 % closure does not contradict this — and this is the whole point.** The
observed near-closure is the *value* of this channel on one specific row, not its norm:
`Ŝ ≈ +1/(√2L²) ≈ 2·10⁻²` while `κ_n ≈ 2A_L ≈ 884` (m = 163), and `κ_nŜ` is then cancelled to
20–25 % by `√2[W_ℝ(0,0)+Prime(0,0)+a_n+μ]`. Both smallnesses are properties of the ground row:
by LATTICE-3 the functional value `Σ_j y_j/d_j` is affine in `E`, the target functional. **The
operator has norm ≥ 15; the row makes it small.** That is reading (A) verbatim, with the
mechanism named: a cancellation of relative depth `~ m^{-1/2}` on one vector.

**The one repair, and where it lands.** The pole term is *exactly* rank one, so it can be removed
by Sherman–Morrison instead of by norm, provided the arch/prime part alone contracts:

```
q_ap := ‖ diag(D)^{-1} Off^{ap} ‖ < 1     and    |1 − 32π²A_L ĝᵀ(diag(D)+Off^{ap})^{-1}ĝ| ≥ c .
```

Both are source-computable, and `q_ap` is the single cheapest decisive number this preflight can
name. But note where success would land: `q_ap < 1` plus a Neumann series **is a proof of odd-sector
coercivity for `D − λ₁` from source data** — i.e. exactly
`SELECTED_FERRERS_ODD_SECTOR_UNIFORM_SOURCE_COERCIVITY_AT_EXACT_RAYLEIGH_SHIFT`, the boundary
closed on 2026-08-30 (`KILL_…_ON_CURRENT_SOURCE_SHELF`, "not disproved; reentry requires genuinely
new mathematics") and named in this task's FORBIDDEN list as an odd-sector floor. So attempt (d)
has exactly two outcomes and both are terminal **for this task**: either `q_ap ≥ 1` (no
contraction) or the derivation's first quantitative step is an odd floor and must be routed to
the judge as a boundary reopening, not consumed here.

**And the odd floor is measurably small.** By interlacing `(D−λ₁)|_odd ⪰ 0`, so its diagonal
entries `δ_n = D_n − 32π²A_L n²/d_n²` are `≥ 0` — and arithmetic on probe 10's table gives
(all forty entries positive, a nontrivial cross-check of both this derivation and probe 10):

| m | δ₁ | δ₂ | δ₃ | δ₄ | D₁ | pole diag at n=1 | ratio |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 13 | 7.916e-4 | 3.630e-3 | 1.072e-2 | 3.228e-2 | 4.5177e-1 | 4.5098e-1 | 0.9982 |
| 23 | 2.296e-4 | 9.633e-4 | 2.359e-3 | 4.793e-3 | 8.4609e-1 | 8.4586e-1 | 0.9997 |
| 43 | 3.889e-4 | 1.677e-3 | 4.307e-3 | 9.415e-3 | 1.5123e+0 | 1.5119e+0 | 0.9997 |
| 83 | 5.884e-5 | 2.406e-4 | 5.633e-4 | 1.062e-3 | 2.5604e+0 | 2.5603e+0 | 1.0000 |
| 163 | 1.395e-4 | 5.830e-4 | 1.409e-3 | 2.785e-3 | 4.1292e+0 | 4.1291e+0 | 1.0000 |

Hence `λ_min((D−λ₁)|_odd) ≤ min_n δ_n ≈ 10⁻⁴`, from source data plus one measured column, with no
eigen-solve. Any coercive use of (MAIN-P) pays at least `1/δ ≈ 10⁴`. **Crucially this is not
`1/λ₂ ≈ 10^{300}`:** the C5 claim that the odd sector avoids the collapsed even pair is
*correct*, and the scale of what this route must buy is now measured for the first time.

**Plant.** For the two-by-two plant the previous report proved `D₁ = 0`, so `diag(D)^{-1}` does
not exist and the contraction fails at step one, by construction — the reading is therefore
non-generic in the right way (it uses `D_n ≠ 0`, which the plant forbids and probe 10 confirms
numerically). It fails anyway, on the source numbers, for a reason the plant cannot express.

---

## 6. Item 4 — the first uncontrolled source term, ranked

```
(U1)  T★ = 32π² A_L ( Σ_{n=1}^{N} Δ_n/d_n )²  =  (A_L/8π²)(𝔐 − L²𝔐₂)² ,
      A_L = 32 L sinh²(L/4) ≍ 8L√m ,   𝔐 = Σ_{n≤N}Δ_n/n²  (the wall-card W-object, signed).
```

**Classification (task taxonomy): the target under another name — a fixed point — amplified by
the exponentially large pole constant; and, as a repair, a collapsed inverse.** It is the signed
first moment of the error row squared, i.e. the very `N`-component that H1 derives *from*
`‖RΔ‖`; and it can be isolated out of (MAIN-P) only through `(D−λ₁)^{-1}X(1/d)`.

Equivalently, after the exact cancellation `δ_n = D_n − 32π²A_Ln²/d_n²`, (U1) has a second and
sharper form:

```
(U1')  the coercivity constant of the identity's own left side, λ_min((D−λ₁)|_odd),
       whose diagonal certificate is δ_n ≈ 1.4·10⁻⁴ (m=163, n=1) against constituents 4.129
       — a four-digit cancellation between the arch/prime diagonal D_n and the pole diagonal.
       This is an odd-sector floor: FORBIDDEN by the task, closed 2026-08-30 as NO_SOURCE.
```

```
(U2)  2⟨Δ, L[a]Δ⟩ = 2Σ_{n≠m}(a_n−a_m)Δ_nΔ_m/(n²−m²) — the arch/prime Loewner form at squared
      nodes. No source sign is proved; a sign would be H5's canonical Pick / complete-Bernstein
      extension of the arch/prime β-row, which the two-by-two plant already killed generically.
      Its contraction coefficient q_ap = ‖diag(D)^{-1}Off^{ap}‖ is the cheapest decisive number.
```

```
(U3)  a positive lower bound D_n ≥ δ_*(L) > 0 for 1 ≤ n ≤ N. Non-circular, purely source-side,
      registered as P59_ARCH_PRIME_DIAGONAL_DEFECT_NONDEGENERACY; probe 10 CONFIRMED it
      numerically for n ≤ 8 on five cells (min|D_n| = 4.7e-2 … 1.17e-1, no decay). Still a
      floor, still unproved, still exactly what the plant sets to zero.
```

The residual pairings on the right of (MAIN-P) are **not** uncontrolled: they are computable, and
Cauchy–Schwarz gives `|Σ_nΔ_n𝓡(y)_n/n²| ≤ ‖RΔ‖·‖R𝓡(y)‖` with the correct shape. The obstruction
is entirely on the left.

---

## 7. Plant check — what the two-by-two plant does to each attempt

`K_t = [[λ+b²/t, b],[b, λ+t]]` is the even block of a raw ±1 carrier: there
`D_{1,−1} = β_1 = b_1` is forced by the displacement law, so the even 2×2 is the plant and the
**odd** entry `τ(1,1) − b_1` is a free parameter. Ground pair: `λ`, `x_1 = −b/t`, unbounded as
`t → 0`.

| Attempt | Does the plant satisfy it? | Does it bound `‖RΔ‖` for the plant? | Verdict |
|---|---|---|---|
| (a)/(b) `(COB)`, `(MAIN)`, `(MAIN-P)` | yes, exactly (`N=1`: no cross term, no pole/arch split) | **no** — `δ_1 = τ(1,1)−b_1−λ` is free, so the left side may vanish while `Δ_1 → ∞` | non-generic identity, correct to keep; the *coercivity step* is generic and is rejected |
| (c) discrete Hardy | vacuous (`N = 1`, no adjacent modes); a two-mode plant makes `∇Δ` free as well | no | rejected before it starts |
| (d) contraction | `D₁ = 0` ⇒ `diag(D)^{-1}` undefined ⇒ contraction fails by construction | no | the reading is non-generic (it needs `D_n ≠ 0`); it fails on source numbers, not on the plant |

Rejected verbatim, because each holds for the plant while `‖RΔ‖` is unbounded: "the pole is rank
one, so low modes decouple"; "displacement rank 2 bounds the off-diagonal"; "the coefficient
decays like `n²/j²`, so the remainder is negligible"; "the diagonal dominates the row"; any use of
centrosymmetry, the squared-node interpolant, or the secular determinant alone; and — new here —
"the odd block is `2X L[b] X`, so Loewner positivity gives coercivity".

---

## 8. Lean-ready vs NEW_ANALYTIC

**Lean-ready** (finite algebra, no cofinal quantifier, no inverse, no eigenvector hypothesis
except where stated). Hypotheses: `2 ≤ mProject`, `1 ≤ N`, `L = ccmL mProject`, raw ±N carrier,
`K = ccmWeilMatFinite`, `x` the centre-normalised ground row, `y : M → ℝ` even with `y 0 = 1`.

1. `ccmOddBlock_squaredNode_loewner` : `D^odd_{nm} = 2nm(b_n−b_m)/(n²−m²)` for `n ≠ m ≥ 1`, and
   `D^odd_{nn} = τ(n,n) − b_n`. One `submatrix` + `ccmWeilTauN1_neg_neg` from
   `ccmWeilTau_structured_offdiag`. *(New normal form; companion of the even `(★)`.)*
2. `ccmRawLattice_centerNormalized_identity` (RAW-LATTICE-1, §2) — unconditional, `ring` after the
   split; the raw-carrier statement of the previous report's LATTICE-1, in one basis only.
3. `ccmErrorRow_reciprocal_coboundary` (COB, §3.1) : `(D−λ₁)(RΔ) = −R𝓡(y) + (ν−λ₁)R(η−y)`.
   Needs only `(D−λ₁)x = −b`, the commutator, and the two parity facts. **No invertibility.**
4. `ccmReciprocalMode_energy_identity` (MAIN, §3.3) and `ccmReciprocalMode_energy_identity_pole`
   (MAIN-P) — the pole extraction is `field_simp; ring` from `ccmW02Entry`, including the exact
   diagonal cancellation `δ_n = D_n − 32π²A_L n²/d_n²`.
5. `ccmOddSector_psd_of_interlacing` : `(D − λ₁(K)) ⪰ 0`, hence `δ_n ≥ 0` and
   `|D^odd_{nm} − λ₁δ_{nm}| ≤ √(δ_nδ_m)`. Cauchy interlacing for a bordered matrix; Mathlib API
   not pinned. Gives (INEQ) of §3.3 for free.

These five are honest theorems and worth having. **None of them bounds anything.**

**NEW_ANALYTIC** (no derivation in hand), in order of cheapness:

- `P59_ARCH_PRIME_LOEWNER_CONTRACTION` (new, non-circular, cheapest decisive):
  `q_ap = ‖diag(D)^{-1}·[2nm(a_n−a_m)/(n²−m²)]‖ < 1`. Source-only, measurable today. If true it
  supplies odd-sector coercivity and must be routed to the judge as a reopening of the
  2026-08-30 boundary, not consumed inside this task.
- `P59_ARCH_PRIME_DIAGONAL_DEFECT_NONDEGENERACY` (carried forward, non-circular):
  `|D_n| ≥ δ_*(L) > 0`, `1 ≤ n ≤ N`. Probe 10 CONFIRMED it for `n ≤ 8` on five cells.
- `P59_RECIPROCAL_POLE_MOMENT_BOUND` (**circular**): `|Σ_{n≤N}Δ_n/d_n| ≤ C/(√A_L L²)`. This is
  the signed `W`-moment under another name; it may not be assumed.

---

## 9. What the numerical companion should measure

One precommit, read-only, against the frozen production cells `m = N = 13, 23, 43, 83, 163` at the
existing precisions, reusing the already-resolved ground eigenpair and the unmodified
`CCMArbBuilder` — **no new solve.** Two lines of new construction only: the **odd** block
`odd[i,j] = k(i,j) − k(i,−j)` (`i,j ≥ 1`; `parity_blocks` currently builds the even block only),
and the Ξ-sample row `y_n = (−1)^n·centeredXi(2πn/L)/centeredXi(0)` at the same precision. **The
quadratic form to evaluate is `⟨u,(D^odd − λ₁)u⟩` at `u = RΔ`, `Δ_n = x_n − y_n`, computed twice:
once as the raw contraction with the odd block, once as the four terms of (MAIN-P)** — their
agreement to working precision validates §3 for free and is the cheapest possible check on this
report, exactly as probe 10's LATTICE-1/2 residual check was. Then print, for `n = 1..8` and
`n₀ ∈ {⌊L⌋, ⌊L²⌋}`: (i) that residual; (ii) the four terms of (MAIN-P) separately —
`Σ D_n Δ_n²/n²`, `32π²A_L(ΣΔ_n/d_n)²`, `2⟨Δ,L[a]Δ⟩`, and the two residual pairings; (iii) `δ_n`
and `min_n δ_n` directly from the odd block, against the prediction `δ_n = D_n − 32π²A_Ln²/d_n²`
of §5 (a four-digit cancellation — if it fails, either probe 10's `D_n` or this dictionary is
wrong, and everything downstream stops); (iv) the entrywise PSD certificate
`|D^odd_{nm}−λ₁δ_{nm}| ≤ √(δ_nδ_m)` at `(n,m) = (1,2)`, where the pole part alone is `−2.31` at
`m = 163` — this tests whether the arch/prime Loewner really cancels the pole rank-one to four
digits, and equivalently whether `b_n` is constant in `n` to `~10⁻⁴` at low modes (§10, S7);
(v) the operator norms `q_pole` and `q_ap` of §5. **The ratio that decides is
`ρ_stab := ‖RΔ‖ / ‖R𝓡(y)‖`** — the stability constant the H4 shell actually achieves. If
`ρ_stab` is `O(1)…O(10⁴)` and flat along the schedule, then `C_k` in H4 is the odd-sector floor
(`~10⁻⁴`) and **not** `1/λ₂ ≈ 10^{300}`, and a boundary-reopening request for
`SELECTED_FERRERS_ODD_SECTOR_UNIFORM_SOURCE_COERCIVITY` is justified with a measured scale; if it
grows like `√m` or faster, H4 is dead and the front goes to H2 (which §4 says has no equation) and
then H6. Second ratio, secondary: `q_ap` — `< 1` would make (d) close, `≥ 1` closes (d). Everything
here is `DIAGNOSTIC_NEVER_A_PROOF`: five cells license no cofinal quantifier, and a favourable
table changes only which NEW_ANALYTIC item is attacked first, never the code returned here.

---

## 10. Strange things, recorded before they are explained

**S7 — the arch/prime diagonal defect equals the pole diagonal to four digits.** `D_n` and
`32π²A_L n²/d_n²` are built from disjoint parts of the source (von Mangoldt sum + archimedean
integral versus the `W02` pole), yet their ratio is `0.9982, 0.9997, 0.9997, 1.0000, 1.0000` at
`n = 1` across `m = 13…163`, improving with `m` and degrading with `n` (0.74 at `n = 8`,
`m = 163`). Their difference `δ_n` is the odd-sector diagonal of `D − λ₁`, is `≥ 0` by
interlacing (all forty computed entries are positive — a genuine cross-check), and is
`≈ 10⁻⁴`. Two readings: **(A)** it is the shadow of a source identity — `δ_n ≥ 0` plus PSD
Cauchy–Schwarz forces the arch/prime Loewner form to cancel the pole rank-one throughout the odd
sector, which is equivalent to `b_n` being constant in `n` to relative `~10⁻⁴` at low modes;
**(B)** it is a numerical coincidence of two `O(1)` ratios at these five cells. **Distinguishing
measurement:** item (iv) of §9 — evaluate `D^odd_{12}` directly; reading (A) predicts
`|D^odd_{12}| ≤ 3·10⁻⁴` while its pole part alone is `−2.31`; reading (B) predicts the entry is
`O(1)` and then `δ_n ≥ 0` fails somewhere, breaking either probe 10's `D_n` or this dictionary.
Logged now, unexplained. If (A) holds, "the CCM centre column is nearly constant at low modes" is
a new source statement of independent value.

**S8 — the odd sector's floor is `10⁻⁴`, not `10⁻³⁰⁰`.** The measured `min_n δ_n ≈ 10⁻⁴` (upper
bound on `λ_min((D−λ₁)|_odd)`) hovers without a clean trend over five cells, while
`λ₁ ≈ 10^{−1.9m}` and `λ₂/λ₁ ≈ 10⁵…10⁸`. The C5 claim that the odd sector escapes the collapsed
second even pair is therefore correct, and the price of the forbidden step is now *measured*:
`10⁴`, not `10^{300}`. Whether `δ` has a floor in `L` is unknown; five cells decide nothing.

**By-product B1 — a free source inequality in the wrong direction.** (INEQ) of §3.3 gives
`|Σ_{n≤N}Δ_n/d_n| ≤ [(Σ D_n Δ_n²/n² + 2⟨Δ,L[a]Δ⟩)/(32π²A_L)]^{1/2}`, i.e. a gain of `A_L^{-1/2}`
(`≈ m^{-1/4}L^{-1/2}`) over Cauchy–Schwarz for the pole moment — non-circular, costing only
interlacing. It bounds the combination `𝔐 − L²𝔐₂`, not `𝔐`, and is conditional on (U2). Recorded
as a by-product, not used.

**Refutations of the previous report's own S-items by probe 10, accepted here.** S6
(`Ŝ ≈ −1/(√2L²)`, i.e. `κ_nŜ` exponentially dominant) is **REFUTED**: `Ŝ` is positive, carried by
its additive constant, and `|κ_nŜ|/|D_ny_n|` *falls* `13.7 → 2.86`. S4 (the pole-only shape
`x_n ≈ −d_n/(2L²)`) is **REFUTED** in favour of its own reading (A): `x_1 → −1`, not `−1/2`. And
the previous report's obstruction #2 (the `j > n₀` tail is the target's own tail) is **demoted**:
`|ρ_n(⌊L⌋)|/|D_ny_n| ≤ 0.254` and falling. Consequently the failure code returned here is the
**GAP** half, not the dense-tail half.

---

## 11. Boundaries

`HONESTY_STATE: CHALLENGER_NOT_RH`. `PX_RH_CLAIM: NOT_MADE`. No Lean file was edited, no numerical
run was performed, nothing under `phase5_scripts/`, no precommit, no queue, no verdict, no commit,
and `phase5_codex/lattice_equation.*` and `docs/cartographer/TOOLS.yaml` were not touched (a
concurrent agent owns them). `‖(K̃−λ₁)⁻¹‖`, `‖(D−λ₁)⁻¹‖`, an absolute or odd-sector floor, a
pole/Arch–Prime *split* of the source column, and the desired bound were used nowhere — where
they would have been needed, that is stated as the failure (§6). Probe-10 numbers are relay; the
`δ_n`, `q_pole` and `‖ĝ‖` tables are my arithmetic on those published numbers plus closed-form
source entries, and are for the companion to confirm. Five cells license no cofinal quantifier.

## Item 5 — code

```text
P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP
```

Fallback order stands as the judge set it: H2 is answered negatively at the level of *existence
of an equation* (§4), so the next re-representation is **H6**, the CCM projective-prolate shell
(`|A|L^{5/2}√p = O(1)`), carrying forward (COB), (MAIN), (MAIN-P) as the exact statement of what
the reciprocal-mode energy contains, `q_ap` as the one cheap decisive source number, and S7/S8 as
the two new unexplained source facts.

---

## §12 Correction 2026-09-04 — full re-derivation of the chain (owner challenge)

Owner assertion: an error in `(COB) → (MAIN) → (MAIN-P)`, §3.1–3.3. The chain was re-derived from
scratch, line by line, from `Kξ = λ₁ξ`, with every factor, sign and index range checked against
`docs/routeB_bus/phase5_scripts/edge_ledger_build.py` and not against §1.

**Result, stated exactly: the chain §3.1–3.3 is correct and unchanged — `(COB)`, `(MAIN)` and
`(MAIN-P)` stand as printed. Two errors were found elsewhere in the report (E1 in a §3.1
parenthetical sanity remark, E2 in the §5 quantitative deduction), plus two wording corrections
(E3, E4). E2 changes the mechanism statement of attempt (d); it does not change the code.**

### 12.1 Checks performed on the chain (all passed)

*Builder-level (against `edge_ledger_build.py`, lines 283–343, and `_alpha` line 227):*

| # | Check | Result |
|---|---|---|
| B1 | `w02(n,m) = 32L sinh²(L/4)(L²−16π²mn)/(d_m d_n)` ⟹ `w02(n,0) = A_L/d_n = p_n` | ✓ exact, verified numerically at `m=163`, `n = 1,2,3,7` |
| B2 | `w02(n,−n) = A_L(L²+16π²n²)/d_n² = A_L/d_n = p_n` — the pole half of `τ(n,−n) = b_n` | ✓ |
| B3 | `w02(n,n) − w02(n,0) = −32π²A_L n²/d_n²` | ✓ to 1e-16 |
| B4 | pole obeys the structured law `w02(n,m) = (β_n−β_m)/(n−m)`, `β_n = n·w02(n,0)`, **including signed `m` and `m = −n`** | ✓ at `(3,1), (5,−2), (4,−4)` |
| B5 | `wr(n,m) = (α_m−α_n)/(n−m)` with `α` odd and `α_0 = 0` ⟹ `−wr(n,0) = α_n/n` and `−wr(n,−n) = α_n/n` | ✓ read literally |
| B6 | `q_nm(n,m,y) = [sin(2πmy/L) − sin(2πny/L)]/(π(n−m))` ⟹ `−prime(n,0) = −prime(n,−n)·1 = P_n/(πn)` | ✓; `−prime(n,−n) = P_n/(πn)` by the `2n` denominator and the odd sine |
| B7 | therefore `τ(n,−n) = p_n + α_n/n + P_n/(πn) = τ(n,0) = b_n`, **derived from the literals, not from the structured law** | ✓ |
| B8 | `a_n := α_n/n + P_n/(πn)` is odd, `b_n = p_n + a_n` is even, `β_n = n b_n` is odd | ✓ |
| B9 | `even[0,0] = k(0,0)`, `even[0,j] = √2 k(0,j)`, `even[i,j] = k(i,j)+k(i,−j)`; the builder builds the **even block only** | ✓ lines 333–342 |
| B10 | the even block is the isometric parity reduction of the raw `K`: with `v_0 = c_0`, `v_i = √2 c_i` one has `(K̃v)_0 = (Kξ)_0` and `(K̃v)_i = √2 (Kξ)_i`, so `K̃v = λv ⟺ Kξ = λξ` | ✓ — working on the raw carrier is legitimate |
| B11 | the two residual conventions differ by exactly `√2`: `𝓡^even(v)_n = √2·𝓡^raw(x̂)_n`, both vanishing at the ground row | ✓ — §2's claim confirmed |
| B12 | `x` must be the **raw** ratio (no `√2`), because `F(t_n)/F(0) = (−1)^n ξ_n/ξ_0` needs `ξ_n/ξ_0`; feeding the raw `x` to the even block `K̃` would **not** give `𝓡(x) = 0` | ✓ — this is why the report works on the raw carrier throughout |

*Algebraic, re-derived from `Kξ = λ₁ξ`:*

| # | Check | Result |
|---|---|---|
| A1 | row 0: `a₀ + bᵀx = λ₁` with `bᵀx = Σ_{m∈M} b_mx_m = 2Σ_{m≥1}` | ✓ |
| A2 | rows `n≠0`: `(D−λ₁)x = −b` | ✓ |
| A3 | `ν(w) := (Kw)_0 = a₀ + 2Σ_{m≥1}b_mw_m`; `𝓡(w)_n := (Kw)_n − w_nν` | ✓ definition fixed once, used consistently |
| A4 | split `τ(n,m) = b_m + n(b_n−b_m)/(n−m)`; the `m = −n` term of the split returns `b_n + 0 = b_n`, i.e. it lands in `Σb_mw_m` and contributes **0** to `Ω` | ✓ — the index range of `Ω` is `m ≥ 1, m ≠ n`, and no term is lost |
| A5 | `±m` pairing: `n(b_n−b_m)w_m[1/(n−m)+1/(n+m)] = 2n²(b_n−b_m)w_m/(n²−m²)` — the factor `2n²` | ✓ |
| A6 | RAW-LATTICE-1 `𝓡(w)_n = (b_n+ν−a₀) + (τ(n,n)−b_n−ν)w_n + Ω_n(w)`; `×√2` reproduces the previous report's LATTICE-1 verbatim | ✓ |
| A7 | (EQ-1) `(D−λ₁)Δ = −𝓡(y) − (ν−λ₁)y`, `Δ = x−y`, and `ν−λ₁ = −bᵀΔ` | ✓ |
| A8 | `XD−DX = βηᵀ−ηβᵀ` entrywise `(n−m)τ(n,m) = β_n−β_m` (0 = 0 on the diagonal); `R(·)R` gives `DR−RD = brᵀ−rbᵀ` | ✓ |
| A9 | `(D−λ₁)R = R(D−λ₁) + (DR−RD)` (the `λ₁R` commutes) | ✓ |
| A10 | parity: `rᵀΔ = 0` (odd·even), `bᵀΔ ≠ 0`; hence exactly one of the two rank-one terms survives | ✓ |
| A11 | **(COB)** `(D−λ₁)RΔ = −R𝓡(y) + (ν−λ₁)R(η−y)`, `r − Ry = R(η−y)` | ✓ |
| A12 | odd reduction of the quadratic form: the four index pairs `(n,m),(n,−m),(−n,m),(−n,−m)` give `2(D_{nm}−D_{n,−m})u_nu_m`, and at `n=m` the same formula holds with all four pairs distinct — **no double counting, factor 2 correct** | ✓ |
| A13 | `D^odd_{nn} = τ(n,n) − τ(n,−n) = τ(n,n) − b_n`; `D^odd_{nm} = 2nm(b_n−b_m)/(n²−m²)` (numerator `2β_nm − 2β_mn = 2nm(b_n−b_m)`) | ✓ |
| A14 | `u = RΔ` ⟹ `u_nu_m·2nm = 2Δ_nΔ_m`, so the bilinear term of (MAIN) is `2Σ_{n≠m}(b_n−b_m)Δ_nΔ_m/(n²−m²)` — the factor 2, not 4 | ✓ |
| A15 | right side: `⟨RΔ,R𝓡(y)⟩_M = 2Σ_{n≥1}Δ_n𝓡(y)_n/n²`, same for `R(η−y)`; dividing both sides by 2 gives (MAIN), and **(MAIN)'s left side is `½⟨RΔ,(D−λ₁)RΔ⟩_M`** | ✓ |
| A16 | pole extraction: `(p_n−p_m)/(n²−m²) = −16π²A_L/(d_nd_m)`; off-diagonal sum `= −32π²A_L[(Σ_{n≥1}Δ_n/d_n)² − Σ_{n≥1}Δ_n²/d_n²]` — the **excluded-diagonal correction** `+32π²A_LΣΔ_n²/d_n²` | ✓ |
| A17 | `δ_n = D_n − 32π²A_L n²/d_n²` and `(n²/d_n²)(Δ_n²/n²) = Δ_n²/d_n²`, so the excluded-diagonal correction cancels the pole diagonal **identically**, leaving the full rank one | ✓ — and `δ_n = D_n + w02(n,n) − w02(n,0)` re-derived directly from `tau_entry`, independent of §1 |
| A18 | **(MAIN-P)**, all sums `Σ_{n=1}^{N}` over **positive** indices only | ✓ |
| A19 | `16π²Σ_{n≥1}Δ_n/d_n = 𝔐 − L²𝔐₂` and `32π²A_L(ΣΔ_n/d_n)² = (A_L/8π²)(𝔐−L²𝔐₂)²` | ✓ |
| A20 | `δ_n ≥ 0` from interlacing: `⟨e_n^-,(D−λ₁)e_n^-⟩ = D_{nn}−D_{n,−n}−λ₁ = δ_n` with `e_n^- = (e_n−e_{−n})/√2` — the `½·2` is correct | ✓ |

*Independent numerical validation of the whole chain* (synthetic `2N+1 = 13` centrosymmetric
matrix built from an arbitrary odd `β` and an arbitrary diagonal, so that it satisfies exactly the
structural laws B4/B7 and nothing else; true bottom eigenpair; arbitrary even target row `y`):
RAW-LATTICE-1 `3.6e-15`, (EQ-1) `1.3e-13`, `ν−λ₁+bᵀΔ` `7.1e-14`, displacement `2.2e-16`, **(COB)
`9.4e-14`**, `rᵀΔ = 1.0e-14`, **(MAIN) `L−R = −1.3e-12`**, `½⟨RΔ,(D−λ₁)RΔ⟩ − (MAIN)_L = 3e-13`,
**(MAIN-P) `L−R = −1.2e-12`**, odd-block form `3.1e-13`, `Gu − h` `5.1e-14`. Every factor of 2,
every sign and every index range is therefore confirmed independently of the analysis.

### 12.2 E1 — error in §3.1, last sentence (a sanity remark, outside the chain)

Wrong line, §3.1: *"At `y = η` (i.e. `Ξ` replaced by the constant 1) it degenerates to
`0 = −R𝓡(η)`, the correct trivial case."*

This is false: setting `y = η` kills the second term on the right but **not** the left, because
`Δ = x − η ≠ 0`. Numerically in the synthetic model `‖(D−λ₁)R(x−η)‖ = 15.18 = ‖R𝓡(η)‖`, not 0.

**Corrected line.** The trivial case of (COB) is `y = x` (then `Δ = 0`, `𝓡(x) = 0`, `ν = λ₁`,
`0 = 0`). At `y = η` (COB) instead reads `(D−λ₁)R(x−η) = −R𝓡(η)`, and this is a genuine
consistency check, which passes: expanding the left with C5's
`(D−λ₁)Rx = −Rb + (a₀−λ₁)r` and the right with the odd-Gram report's inverse-free
`Dr = R(Dη) − σ_b r` (`σ_b = bᵀη`) gives `−Rb + a₀r − Dr` on both sides. Nothing downstream
changes.

### 12.3 E2 — error in §5: `q_pole` does not lower-bound the contraction coefficient

Wrong step, §5: from the table of `q_pole = 32π²A_L‖diag(D)^{-1}ĝ‖‖ĝ‖ ≥ 4.78 … 15.87` the report
concludes *"The pole channel alone already exceeds 1 … No contraction."*

The `q_pole` values are arithmetically correct as the spectral norm of the **pole channel taken
alone** (`c(diag(D)^{-1}ĝ)ĝᵀ` is rank one, norm `‖v‖‖w‖`). But the splitting's coefficient is
`q = ‖diag(D)^{-1}(32π²A_Lĝĝᵀ − Off^{ap})‖`, and `q ≥ q_pole − q_{ap}` only — so a large `q_pole`
proves nothing when the two channels cancel. **They do cancel: that is exactly what §10 S7
reports.** The report used S7 in §6 and contradicted it in §5.

**Corrected analysis (E2').** Write `G := D^{odd} − λ₁I` (the exact `N×N` odd block; `diag G = δ_n`,
`G_{nm} = 2nm(b_n−b_m)/(n²−m²)`), so that (MAIN-P) is `⟨u,Gu⟩` and (COB) restricted to `n ≥ 1` is
`Gu = h`, `h_n = [−𝓡(y)_n + (ν−λ₁)(1−y_n)]/n`. Then, identically,

```
diag(D)^{-1}( 32π²A_L ĝĝᵀ − Off^{ap} )  =  I − diag(D)^{-1} G ,
```

so with `D_n > 0` (probe 10: positive for `n ≤ 8`, unknown above) and
`G̃ := diag(D)^{-1/2} G diag(D)^{-1/2} ⪰ 0` (interlacing),

```
┌──────────────────────────────────────────────────────────────────────────────┐
│  spectral radius of the iteration = max_k |1 − μ_k| ,   μ_k = eig(G̃) ⪰ 0     │
│  μ_min ≤ min_n G̃_nn = min_n δ_n/D_n                                          │
│  ⇒  a contraction DOES exist in the preconditioned spectral sense,           │
│      with constant  1/(1−q) ≥ 1/μ_min  =  the odd floor in disguise.         │
└──────────────────────────────────────────────────────────────────────────────┘
```

Arithmetic on probe 10's `D_n` (`n ≤ 8`, so each entry is an upper bound for `μ_min`, hence a
lower bound for the constant):

| m | min_n δ_n | argmin | min_n δ_n/D_n | 1/min_n δ_n | **1/μ_min ≥** |
|---:|---:|---:|---:|---:|---:|
| 13 | 7.916e-4 | 1 | 1.752e-3 | 1263 | **571** |
| 23 | 2.296e-4 | 1 | 2.714e-4 | 4355 | **3684** |
| 43 | 3.889e-4 | 1 | 2.572e-4 | 2571 | **3888** |
| 83 | 5.884e-5 | 1 | 2.298e-5 | 16996 | **43517** |
| 163 | 1.395e-4 | 1 | 3.378e-5 | 7169 | **29600** |

**What changes and what does not.** The verdict of attempt (d) is unchanged — **reading (A)**, and
the code is unchanged — but the mechanism is now stated correctly and, if anything, more sharply:
the iteration is not divergent, it is *degenerate*. Its contraction factor is `1 − μ_min` with
`μ_min ≲ 3·10⁻⁵`, so the constant it delivers is `1/μ_min ≈ 3·10⁴`, which is exactly
`≈ 1/(odd-sector floor)` — the forbidden object, reached by a different road. The
"operator norm versus value on the specific row" distinction of §5 survives verbatim: the best
constant in `‖RΔ‖ ≤ C‖R𝓡(y)‖` is `1/λ_min(G)`, and whether the actual `h` avoids the near-null
direction of `G` is a property of `y`, not of the source operator. The `q_pole` table stays in the
report as what it is — the norm of the pole channel alone, i.e. the size of the cancellation that
S7 asserts — and must **not** be read as a lower bound for `q`.

Downstream: §6 (U1)/(U1') unchanged; §7 plant row for (d) unchanged (`D₁ = 0` still kills the
preconditioner); §8 `P59_ARCH_PRIME_LOEWNER_CONTRACTION` is **restated** as: the decisive source
number is not `q_ap` in isolation but `μ_min = λ_min(diag(D)^{-1/2}(D^{odd}−λ₁)diag(D)^{-1/2})`,
with `q_ap` as its cheap upper-bound diagnostic; §9's deciding ratio `ρ_stab` unchanged, with
`μ_min` added as the second measured number.

### 12.4 E3 — wording, §5 / §10 S8 / the one-line summary

*"roughly flat over the five cells"* is wrong. `min_n δ_n` falls `7.92e-4 → 1.40e-4` (factor 5.7,
non-monotone) and the relative floor `min_n δ_n/D_n` falls `1.75e-3 → 3.38e-5` (factor 52) from
`m = 13` to `m = 163`. **Corrected:** the measured price rises along the schedule, from `≈10³` to
`≈3·10⁴`. This weakens, but does not overturn, S8's point: `10⁴` is still not `10^{300}`, and the
odd sector still escapes the collapsed second even pair.

### 12.5 E4 — §3.4, a strengthening, not a weakening

`𝔐 := Σ_{n≤N}Δ_n/n²` is described as *"the wall-card `W`-object, signed"*. That understates it.
Since `Δ_n = x_n − y_n = (−1)^n Δ^{wall}_n` with `Δ^{wall}_n = F(t_n)/F(0) − Ξ(t_n)/Ξ(0)`, the
moment `𝔐` is exactly `(4π²/L²)` times the **alternating** lattice sum of wall-card record 10, and

```
𝔐 = ( E − π²/6 )/2  −  Σ_{n=1}^{N} (−1)^n centeredXi(2πn/L)/(n² centeredXi(0)) ,
```

i.e. `𝔐` is affine in the target functional `E` with an explicitly computable `Ξ`-constant. The
fixed-point statement of §3.4 and (U1) is therefore not "bounded by the target" but "equal to the
target up to a computable constant and a factor 2".

### 12.6 Code

Unchanged: `P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP`, GAP half. E1 is inert, E2
replaces a wrong route to the same conclusion with a correct one, E3 is a trend correction that
makes the measured price worse, E4 strengthens the fixed-point argument.
