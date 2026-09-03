# Agent report — Goal 058: reciprocal-mode odd-Gram source preflight

Date: 2026-09-03 (night)
Executor: Linux-Claude subagent (Opus), standing in for Codex
Task: `docs/Codex/TASK_2026-09-03_goal058_reciprocal_mode_odd_gram_source_preflight.md`
Mode: PAPER_AND_SOURCE_READ_ONLY — no Lean edit, no numerics run, no commit

```yaml
TASK_ID: GOAL058_RECIPROCAL_MODE_ODD_GRAM_SOURCE_PREFLIGHT
CODE: C5_RECIPROCAL_COMMUTATOR_ONLY_RENAMES_CURVATURE
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
ROUTE_PROMOTION: false
```

**One line.** Items 1–5 of the judge's list all check out exactly, including the
restriction of the commutator; item 6 also succeeds — the odd defect **is** an exact
`(D−λ₁)`-coboundary with a fully explicit odd `s` and **no resolvent norm anywhere** —
but the unique preimage is `s = ½r + Rx` with `x = ξ/ξ₀` the tracked ground eigenvector,
and `⟨r,s⟩ + Σ_{n>N}n^{-2}` is *identically* `E`. The chain closes onto the CURVBRIDGE
formula that was already known before C5. Nothing is bounded that was not bounded before.

---

## 0. Verification status of each source statement

| Claim | Status |
|---|---|
| `ccmWeilMatFinite_commutator` (`XK − KX = βηᵀ − ηβᵀ`) | read in Lean source, `#print axioms` present in file; **not** re-run through `lake` here (read-only mode) |
| `ccmWeilMatFinite_centrosymmetric`, `ccmWeilTauN1_neg_neg`, `ccmWeilTauN1_symm` | read in Lean source |
| `proposition59SecondJetCoefficient` (`c₀=1/12`, `c_k=1/(2π²k²)`) | read in Lean source |
| `curvature_pairing_eq_half_borderedPhi_deriv` (`1/12 − ⟨c,Rb⟩ = ½Φ'(0)`) | read in Lean source |
| Probe-7 table, `κ_k = 0.0259…0.0245`, `λ₂/λ₁ = 3.6e5…3.6e8` | **relay, not re-verified** (no numerics run) |
| CURVBRIDGE formula `κ_k = (L²/2)[1/12 + (1/(2π²ξ₀))Σ ξ_n/n²]` | **relay** from `PROSHKA_REQUEST_…_NEW_MECHANISM_…txt` lines 30–32, quoted as stated there |

All algebra below is my own derivation and is checkable by hand.

---

## 1. Typed definitions on the ±N carrier

Lean carrier: `CCMModeFinite N := Fin (2N+1)`, `ccmModeFinite N i = i.1 − N ∈ {−N,…,N}`,
centre `ccmCenterFinite N = ⟨N,_⟩` (label `0`), reflection
`ccmNegFinite N i = ⟨2N − i.1,_⟩` (label `−n`).

| Symbol | Type | Definition | Lean anchor |
|---|---|---|---|
| `K` | `Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ` | `K_{ij} = τ(n_i,n_j)` | `ccmWeilMatFinite mProject N` |
| `𝕏` | same | `diagonal (fun i => (n_i : ℝ))`, `n_center = 0` | `ccmModeDiagFinite N` |
| `η_full` | `CCMModeFinite N → ℝ` | `≡ 1` | `ccmEtaFinite N` |
| `β_full` | same | `β_i = n_i · K_{i,center}`, `β_center = 0` | `ccmBetaFinite mProject N` |

Noncentral carrier `M := {−N,…,N} \ {0}`, `|M| = 2N`, obtained by deleting the centre
index. On `M`:

- `a₀ := K_{center,center} = τ(0,0)` (scalar);
- `b : M → ℝ`, `b_n := K_{n,center} = τ(n,0)` (centre column);
- `D : Matrix M M ℝ`, `D_{nm} := τ(n,m)` (noncentral block), so `K = [[a₀, bᵀ],[b, D]]`;
- `X := diag(n)_{n∈M}`, invertible since `0 ∉ M`;
- `R := X⁻¹ = diag(1/n)`, symmetric, diagonal;
- `η := (1,…,1)ᵀ ∈ ℝ^M`;
- `r := Rη`, i.e. `r_n = 1/n`;
- `β := (β_full)|_M`, i.e. `β_n = n·b_n`, so `β = X b` and `R β = b`, `R η = r`;
- `λ₁ := λ₁(K)` the simple bottom eigenvalue, `A := (D − λ₁ I)⁻¹` on `ℝ^M`;
- `c ∈ ℝ^M`, `c_n = 1/(2π²n²) = (1/2π²)(Rr)_n` — the noncentral part of
  `proposition59SecondJetCoefficient`; the centre coefficient is `1/12`.

Reversal `J` on `ℝ^M`: `(Jv)_n = v_{−n}` (`ccmReflectionEndFinite` restricted).
Parity classes: `JDJ = D` (even), `JXJ = −X` and `JRJ = −R` (odd operators),
`Jη = η`, `Jr = −r`.

---

## 2. `D R − R D = b rᵀ − r bᵀ` — proved, and the centre contributes nothing

The kernel-checked statement is on the **full** carrier:

```
ccmModeDiagFinite N * ccmWeilMatFinite − ccmWeilMatFinite * ccmModeDiagFinite
  = vecMulVec β_full η_full − vecMulVec η_full β_full
```

Its entrywise content, because `𝕏` is **diagonal** (`Matrix.diagonal_mul` /
`Matrix.mul_diagonal`, exactly the two rewrites used in the Lean proof), is

```
(n_i − n_j) · K_{ij} = β_i − β_j        for all i, j.            (★)
```

This is the whole point of the judge's caution, and it resolves in our favour: because
`𝕏` is diagonal, `𝕏K` and `K𝕏` scale rows resp. columns and **never mix indices**. The
`(i,j)` entry of the commutator therefore involves only `K_{ij}` — the central row/column
enters no noncentral entry. Consequently:

- **noncentral × noncentral** (`i,j ∈ M`): `(★)` reads `(n_i − n_j)D_{ij} = β_i − β_j`,
  i.e. `X D − D X = β ηᵀ − η βᵀ` on `ℝ^M`. **No central term appears.**
- **noncentral × centre** (`j = center`, `n_j = 0`): `(★)` reads `n_i·b_i = β_i − 0`.
  So `β = X b` on `M` is *not an extra assumption* — it is the same identity's centre
  column, matching `ccmBetaFinite` literally.
- **centre × noncentral**: the transpose of the previous line, `−β_j` on both sides.
- **centre × centre**: `0 = 0`.

Multiply `X D − D X = β ηᵀ − η βᵀ` by `R` on both sides. Using `RX = XR = I`, `Rᵀ = R`:

```
R(XD − DX)R = (RX)D R − R D (XR) = D R − R D,
R(βηᵀ − ηβᵀ)R = (Rβ)(Rη)ᵀ − (Rη)(Rβ)ᵀ = b rᵀ − r bᵀ.
```

```
┌──────────────────────────────┐
│   D R − R D = b rᵀ − r bᵀ    │   exact, finite, N ≥ 1, 2 ≤ mProject
└──────────────────────────────┘
```

**CONFIRMED, not refuted.** Parity cross-check: conjugating by `J` sends the left side to
`D(−R) − (−R)D = −(DR−RD)` and the right side to `b(−r)ᵀ − (−r)bᵀ = −(brᵀ − rbᵀ)`. ✔

Suggested Lean name (bookkeeping only, not written): `ccmReciprocalMode_commutator`.
It is one `Matrix.submatrix` of the existing theorem plus a `diagonal`-cancellation —
genuinely Lean-ready, low cost.

---

## 3. `rᵀ A b = 0` — parity proof

Source facts: `ccmWeilTauN1_symm` (`τ(n,m)=τ(m,n)`) and `ccmWeilTauN1_neg_neg`
(`τ(−n,−m)=τ(n,m)`), packaged as `ccmWeilMatFinite_centrosymmetric`. Hence `JKJ = K`,
and restricting to `M` (which `J` preserves) gives `JDJ = D`.

1. `b` is **even**: `b_{−n} = τ(−n,0) = τ(−n,−0) = τ(n,0) = b_n` by `ccmWeilTauN1_neg_neg`.
2. `r` is **odd**: `r_{−n} = 1/(−n) = −r_n`.
3. `D − λ₁I` commutes with `J`, therefore so does `A = (D−λ₁I)⁻¹`; `A` preserves the
   `±1` eigenspaces of `J` (the even and odd sectors). Hence `Ab` is even.
4. For `u` even and `v` odd, `vᵀu = Σ_n v_n u_n = Σ_n v_{−n}u_{−n} = −Σ_n v_n u_n`, so
   `vᵀu = 0`.

With `v = r` (odd) and `u = Ab` (even): **`rᵀ A b = 0`.** ✔

Corollary used below (same argument): `Rb` is **odd** (`R` odd operator on an even
vector), `Ar` is **odd**, `Rr` and `c` are **even**.

Schur root equation: the `λ₁`-eigenvector of `K` normalised at the centre is `(1, x)`
with `b + Dx = λ₁x`, i.e.

```
(D − λ₁I) x = −b,      x = −A b,      bᵀ A b = −bᵀx = a₀ − λ₁.
```

`x` is even (it is `−Ab`); it is the tracked object
`PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY` in coordinates `x_n = ξ_n/ξ_0`.

Judge's Step 2 then reproduces verbatim: from `RA − AR = A(brᵀ − rbᵀ)A`, pairing
`rᵀ(·)b`,

```
rᵀRAb − rᵀARb = (rᵀAb)² − (rᵀAr)(bᵀAb) = 0 − (a₀−λ₁)(rᵀAr),
```

```
┌──────────────────────────────────────────────┐
│   rᵀ R A b = rᵀ A R b − (a₀−λ₁) · rᵀ A r     │
└──────────────────────────────────────────────┘
```

**CONFIRMED.**

---

## 4. `κ = (L²/4π²) E` — exact derivation, and the `1/12` identity

Carrier identity (symmetric carrier, `M` closed under `n ↦ −n`):

```
½‖r‖² = ½ Σ_{0<|n|≤N} 1/n² = Σ_{n=1}^{N} 1/n²,
½‖r‖² + Σ_{n>N} 1/n² = Σ_{n=1}^{∞} 1/n² = π²/6,
```

hence `1/12 = (1/2π²)[ ½‖r‖² + Σ_{n>N} 1/n² ]`. ✔ (Item 4's stated identity.)

The second jet of the P59 transform at the origin is the functional
`proposition59SecondJetFunctional`, `ℓ(v) = Σ_{|k|≤N} c_k v_k` with `c_0 = 1/12`,
`c_k = 1/(2π²k²)`. Evaluated on the centre-normalised ground vector `(1,x)`:

```
ℓ(1,x) = 1/12 + Σ_{n≠0} x_n/(2π²n²) = 1/12 − ⟨c, A b⟩ = 1/12 − S,
```

using `x = −Ab` and `c = (1/2π²)Rr` (so `⟨c,Ab⟩ = (1/2π²) rᵀRAb`). This is exactly the
bracket that `curvature_pairing_eq_half_borderedPhi_deriv` computes as half the bordered
secular slope. Now, with `E := 2π²·ℓ(1,x)`:

```
E = π²/6 − rᵀRAb
  = ½‖r‖² + Σ_{n>N}1/n² − rᵀRAb                      (carrier identity)
  = ½‖r‖² − rᵀARb + (a₀−λ₁)rᵀAr + Σ_{n>N}1/n²        (Step-2 identity)
```

which is **literally the judge's `E`**. And the CURVBRIDGE definition (relay, request
lines 30–32)

```
κ_k = (L²/2)[ 1/12 + (1/(2π²ξ₀)) Σ_{n≠0} ξ_n/n² ] = (L²/2)·ℓ(1,x)
```

gives

```
┌──────────────────────────────┐
│   κ_k = (L_k²/4π²) · E_k     │
└──────────────────────────────┘
```

**CONFIRMED exactly**, with no convention slack: `(L²/2)·ℓ = (L²/2)·E/(2π²) = (L²/4π²)E`.

Two consequences worth stating in the open:

```
E = π²/6 + Σ_{n≠0} x_n/n²  =  Σ_{n=1}^{N} (1 + 2x_n)/n²  +  Σ_{n>N} 1/n².      (E-CLOSED)
```

`(E-CLOSED)` contains **no resolvent, no inverse, no norm**. The target `E ≤ C/L²` is,
verbatim, a statement about the low modes of the CCM ground eigenvector.

---

## 5. Full source expansion of `R b` (entries `b_n/n`)

From the literal Lean constructors (`ccmQKernel`, `ccmW02Entry`, `ccmWREntry`,
`ccmPrimeEntryN1`), with `L = ccmL m = log m`, `d_n := L² + 16π²n²`, and `n ≠ 0`:

**Kernel at the centre column.** `ccmQKernel L n 0 x = (sin(0) − sin(2πnx/L))/(π(n−0))`, so

```
Q(n,0,x) = − sin(2πnx/L)/(πn),        Q(n,0,0) = 0.
```

**Pole part (W02).** `ccmW02Entry L n 0 = 32L sinh²(L/4)·(L² − 0)/((L²+0)(L²+16π²n²))`:

```
W₀₂(n,0) = 32 L sinh²(L/4) / d_n.
```

**Arch part (W_R).** The `Q(n,0,0)/2·(γ + log(4π(e^L−1)/(e^L+1)))` constant term
**vanishes** (`Q(n,0,0)=0`), leaving only the integral, with `e^x − e^{−x} = 2 sinh x`:

```
W_ℝ(n,0) = ∫_{(0,L]} e^{x/2}·(−sin(2πnx/L)/(πn)) / (2 sinh x) dx = − I_n/(2πn),
I_n := ∫_{(0,L]} e^{x/2} sin(2πnx/L) / sinh(x) dx.
```

**Prime part.** With `x = log k`:

```
P(n,0) = Σ_{k=2}^{m} Λ(k) k^{-1/2} Q(n,0,log k) = − P_n/(πn),
P_n := Σ_{k=2}^{m} Λ(k) k^{-1/2} sin(2πn log k / L).
```

Since `τ = W₀₂ − W_ℝ − Prime`, the exact centre column on the raw `±N` carrier is

```
b_n = 32 L sinh²(L/4)/d_n  +  I_n/(2πn)  +  P_n/(πn),
```

which is the Codex-report formula stripped of its even-basis `√2` (that `√2` is the
`e_n^+ = (e_n+e_{−n})/√2` normalisation, not a source constant). Therefore

```
┌───────────────────────────────────────────────────────────────────────────┐
│ (R b)_n = b_n/n = 32 L sinh²(L/4)/(n·d_n) + I_n/(2πn²) + P_n/(πn²)        │
└───────────────────────────────────────────────────────────────────────────┘
```

- pole term `32 L sinh²(L/4)/(n·d_n)` — the `√2`-free form of the Codex-report
  `b_pole,n = 32√2 L sinh²(L/4)/d_n` divided by `n`;
- Arch term `I_n/(2πn²)` from `wr(0,n)`;
- prime term `P_n/(πn²)` from `prime(0,n)`.

All three are **odd** in `n` (`I_{−n} = −I_n`, `P_{−n} = −P_n`), confirming `Rb` odd and
`b` even. `β_n = n b_n = 32L sinh²(L/4)·n/d_n + I_n/(2π) + P_n/π` is odd, and
`Σ_{n≠0} β_n = 0`.

No pole/Arch–Prime **split** is used anywhere below (Probe 7's forbidden move); the full
`b_n` is carried as one object.

---

## 6. THE DECISIVE QUESTION — answered, and it kills C5

### 6.1 Reduction of `E` to the odd defect

Set `T := Σ_{n>N} 1/n²` and let `w := Ar` (odd). Since `D−λ₁I` is symmetric,

```
½‖r‖²   = ½⟨r,(D−λ₁)Ar⟩ = ⟨Ar, ½(D−λ₁)r⟩,
−rᵀARb  = ⟨Ar, −Rb⟩,
(a₀−λ₁)rᵀAr = ⟨Ar, (a₀−λ₁)r⟩,
```

so with the judge's odd defect vector

```
g := ½(D−λ₁I)r − R b + (a₀−λ₁) r        (odd),
```

we get exactly `E = ⟨A r, g⟩ + T`. If `g = (D−λ₁I)s` then
`⟨Ar,(D−λ₁)s⟩ = ⟨r,s⟩` and `E = ⟨r,s⟩ + T` — no inverse. This is the judge's success form,
correctly derived.

### 6.2 An exact coboundary EXISTS — and it is unique

Two independent source-side facts:

**(a) one-sided source form for `Dr`.** Apply the new commutator to `η`:
`(DR − RD)η = b(rᵀη) − r(bᵀη)`. On the symmetric carrier `rᵀη = Σ_{0<|n|≤N} 1/n = 0`, so
with `σ_b := bᵀη = Σ_{n≠0} b_n`,

```
D r = R(D η) − σ_b · r,     i.e.   (Dr)_n = (Σ_{m≠0} τ(n,m))/n − σ_b/n.
```

This is genuinely inverse-free and source-only. It rewrites the defect as

```
g = R·v,      v := ½ Dη − b + c₁ η   (even),   c₁ := a₀ − (3/2)λ₁ − ½σ_b.
```

**(b) the preimage.** Apply the commutator to the ground vector `x`, using
`(D−λ₁)x = −b`, `rᵀx = 0` (r odd, x even), `bᵀx = −(a₀−λ₁)`:

```
(D−λ₁I)(R x) = R(D−λ₁I)x + b(rᵀx) − r(bᵀx) = −R b + (a₀−λ₁) r.
```

Adding `(D−λ₁I)(½r)`:

```
┌────────────────────────────────────────────────────────────────┐
│  ½(D−λ₁)r − Rb + (a₀−λ₁)r  =  (D−λ₁)·s,     s = ½ r + R x      │
└────────────────────────────────────────────────────────────────┘
```

`s` is odd (`r` odd, `x` even so `Rx` odd). The coboundary is **exact**, and
`D−λ₁I` is invertible on the odd sector, so **`s = ½r + Rx` is the unique odd preimage**.

Consistency: `E = ⟨r,s⟩ + T = ½‖r‖² + Σ_{n≠0} x_n/n² + T`, which is `(E-CLOSED)`. ✔

### 6.3 Why this is FAILURE and not SUCCESS

The judge's success form demands `s` "constructed from source rows without inversion",
with `|⟨r,s⟩| + T ≤ C/L²`. Both halves fail, and they fail for the same reason:

1. **The preimage is the ground eigenvector, not a source row.** `s = ½r + Rx` with
   `x = −Ab = (ξ_n/ξ_0)_n`. `x` is an *inversion* — it is the tracked ground-family
   object, obtained from an eigenproblem, not from an entry formula of `K`. Since the odd
   preimage is unique, **any** admissible `s` must equal `½r + Rx`. So "find a source-row
   `s` without inversion" is equivalent to "write the CCM ground eigenvector in closed
   form from the source entries" — which is the entire open problem, not a step of it.

2. **The budget is the target.** `|⟨r,s⟩| + T = E` identically. The inequality
   `|⟨r,s⟩| + T ≤ C/L²` is not a sufficient condition for `E ≤ C/L²`; it **is**
   `E ≤ C/L²`. The derivation is a tautology `E = E`.

3. **The identity was already known in inverse-free form.** `(E-CLOSED)` is, term for
   term, the CURVBRIDGE bracket `κ = (L²/2)[1/12 + (1/(2π²ξ₀))Σ ξ_n/n²]` quoted in the
   request as already paper-proved. C5's Step 2 rewrites the *even-sector* pairing
   `rᵀRAb` as two *odd-sector* pairings `rᵀARb`, `rᵀAr`; the coboundary then folds them
   straight back into `Σ x_n/n²`. Net information gain over CURVBRIDGE: zero.

4. **Every remaining route hits the kill list.** Enumerated against the judge's own
   conditions:
   - *Cauchy–Schwarz on `E = ⟨Ar,g⟩`*: `|E| ≤ ‖Ar‖‖g‖` → starts with `‖(D−λ₁)⁻¹‖`. **KILL.**
   - *Bound `A` on the odd sector only* (the "the dangerous eigenpair is even, so the odd
     resolvent is safe" hope): this is precisely an **absolute odd floor**
     `λ₁^{odd}(D) − λ₁(K) ≥ c > 0`. Explicitly forbidden by the kill condition, and by
     CURVRITZ's dead-shape ledger. **KILL.**
   - *Solve for `s` by the ansatz `s = Rw`, `w` even*: `(D−λ₁)Rw = R(D−λ₁)w + (rᵀw)b − (bᵀw)r`;
     the even part vanishes automatically (`rᵀw = 0`), and the odd part forces
     `(D−λ₁)w = v + (bᵀw)η` — another inversion, self-referential in `bᵀw`. **Circular.**
   - *Expand `s` through `AR = RA − x(Ar)ᵀ + (Ar)xᵀ`* (the resolvent form of the same
     commutator): every term still carries `Ar` or `Av` — an **uncontrolled mixed
     resolvent pairing**. **KILL.**
   - *Finite-rank budget*: the displacement rank is exactly 2 (`brᵀ − rbᵀ`), but the
     judge's own §7 plant and Codex's `K_t = [[λ+b²/t, b],[b, λ+t]]` show rank-2
     displacement plus Loewner structure leaves the Gram defect free. No `L⁻²` budget is
     produced by the rank alone. **KILL.**

```text
C5_RECIPROCAL_COMMUTATOR_ONLY_RENAMES_CURVATURE
```

The judge's §7 "strongest attack" is the correct reading: the identity moves the same
mixed pairing from the even block to an odd block, and the odd block closes only onto the
ground eigenvector it started from.

---

## 7. First exact surviving term, and follow-up

**First exact surviving term.** After every cancellation the whole wall is one scalar
moment of the ground eigenvector:

```
E_k = Σ_{n=1}^{N} (1 + 2 ξ_{k,n}/ξ_{k,0}) / n²  +  Σ_{n>N} 1/n²,
κ_k = (L_k²/4π²) E_k,       target:  sup_k κ_k < ∞  ⟺  E_k = O(L_k^{-2}).
```

The surviving object is `⟨r, Rx⟩ = Σ_{n≠0} x_n/n²` — the `1/n²`-weighted low-mode moment
of `x_n = ξ_n/ξ_0`. No resolvent, no gap, no norm survives; only asymptotics of `x_n`.

**Follow-up class: NEW ANALYTIC, not Lean-ready.** The load-bearing statement is an
asymptotic law for the CCM ground eigenvector's low modes, of the shape

```
Σ_{n=1}^{N} (1 + 2x_{k,n})/n²  =  O(L_k^{-2}) − Σ_{n>N_k} 1/n²,
```

i.e. `x_{k,n} → −1/2` in the `1/n²`-weighted sense. Nothing in the source algebra
(displacement, Schur, Loewner, parity, reciprocal mode) supplies this; it needs the
arithmetic content of `b_n` — the pole/`I_n`/`P_n` triple of §5 — entering through the
eigenvector, not through an inverse-norm estimate.

**Lean-ready bookkeeping (cheap, safe, no cofinal quantifier).** Three finite-algebra
lemmas, all one `submatrix` step from theorems that already exist:

1. `ccmReciprocalMode_commutator` : `D R − R D = b rᵀ − r bᵀ` (§2);
2. `ccmOddSector_pairing_zero` : `rᵀ A b = 0` from centrosymmetry (§3);
3. `ccmOddDefect_isCoboundary` : `½(D−λ₁)r − Rb + (a₀−λ₁)r = (D−λ₁)(½r + Rx)` (§6.2),
   which needs only `(D−λ₁)x = −b` and the commutator — no invertibility of `D−λ₁`
   is needed for this *direction*.

They are honest theorems and worth having, but they are bookkeeping: none of them moves
`E_k`.

---

## 8. Strange things, recorded before they are explained

**S1 — `E_k·L_k² ≈ 1`, and `x_n ≈ −1/2`.** Combining the relayed numerics
(`κ_k = 0.0259, 0.0263, 0.0258, 0.0252, 0.0245` on `m = 13..163`, → `Σ_γ γ^{-2} = 0.0231`)
with `E = 4π²κ/L²` gives `E_k L_k² = 4π²κ_k ≈ 1.02, 1.04, 1.02, 0.995, 0.967`,
apparently → `4π²·0.0231 = 0.912`. Independently, Probe 7's `1/12 − S` column with
`L = log m` (Lean: `ccmL m = Real.log m`) gives
`(1/12−S)·L² = 0.0518, 0.0525, 0.0517, 0.0503` — flat, and `2π²·0.0507 ≈ 1`. The two
readings agree, which is a useful consistency check on `E = 2π²(1/12 − S)`.

Via `(E-CLOSED)` this says the ground eigenvector satisfies `x_n = ξ_n/ξ_0 ≈ −1/2` in the
`1/n²`-weighted low-mode sense, with a defect of size `≈ 1/L²`. Two readings:
(A) `x_n = −1/2 + O(1/L)` pointwise at low `n`, i.e. a genuine limit shape of the CCM
ground vector; (B) `x_n` is far from `−1/2` individually and only the weighted sum
conspires. **Distinguishing outcome, cheap, no new tooling:** print `x_n = ξ_n/ξ_0` for
`n = 1..8` on the already-computed cells `m = 13, 23, 43, 83, 163` from the existing
`CCMArbBuilder` run. If (A), the low-mode limit shape is the new source target and
replaces the whole resolvent apparatus; if (B), the cancellation is global and the target
stays a summed moment. `DIAGNOSTIC_NEVER_A_PROOF` — no cofinal quantifier either way.
Not run here (read-only mode); logged as the next cheap VOI probe.

**S2 — the `√2` in the judge's `b_pole,n`.** The judge's success form quotes
`(32√2 L sinh²(L/4))/(n·d_n)`, inherited from the Codex report's **even basis**
`e_n^+ = (e_n+e_{−n})/√2`. The C5 algebra (`X`, `R`, `η`, parity) lives on the **raw `±N`
carrier**, where the factor is absent (§5). Mixing the two bases would put a spurious
`√2` (and, for `D_pole`, a spurious `2`) into any Lean statement of the identity. Flagged
so the bookkeeping lemmas are written in one basis only — the raw `±N` one, which is what
`ccmWeilMatFinite` literally is.

**S3 — the centre-column constant term vanishes for free.** In `ccmWREntry` the
`γ + log(4π(e^L−1)/(e^L+1))` prefactor is multiplied by `Q(n,m,0)`, and `Q(n,0,0) = 0`
exactly. So the whole Euler–Mascheroni/`L`-dependent constant of the archimedean entry is
**absent** from the centre column `b`, and therefore from `Rb`, `β`, and `E`. It survives
only on the diagonal and in noncentral off-diagonal entries. This is a real structural
simplification of the source vector and does not seem to have been used anywhere; noted
in case it matters for the `x_n` asymptotics of S1.

---

## 9. Boundaries

`HONESTY_STATE: CHALLENGER_NOT_RH`. `PX_RH_CLAIM: NOT_MADE`. No Lean file was edited, no
numerics were run, no commit was made. Probe-7 and `κ_k` figures are relay from the
committed request and Codex report and were not re-verified here. Per the judge's
directive, C5 is closed with the failure code and the front moves to C1
(`P59DirectProjectiveSecondJetRate`, `|A_k|²L_k⁵p_k = O(1)`), with the `(E-CLOSED)`
low-mode moment of §7 carried forward as the exact statement of wall B.
