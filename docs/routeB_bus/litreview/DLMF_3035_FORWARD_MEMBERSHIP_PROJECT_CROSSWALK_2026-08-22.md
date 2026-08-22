# DLMF 30.3.5 forward membership — source acquisition and object lock

TASK: REQ_U_DLMF3035_FORWARD_SOURCE_TO_LEAN_OBJECT_LOCK (verdict `68e9cd78`)
MODE: READ_ONLY_SOURCE_ACQUISITION_AND_THEOREM_SHAPE — no Lean edited.
DATE: 2026-08-22
EXECUTOR: Linux body (Codex unavailable; standing owner grant)

## 0. Sources acquired

| Source | Where | Status |
|---|---|---|
| DLMF §30.3(i)/(iii), 30.3.5, 30.3.6, 30.3.7 | https://dlmf.nist.gov/30.3, fetched 2026-08-22 | read; project already holds audited TeX hashes for 30.3.E5 and 30.3.E7a–c in `D0Mode4DLMF3035EvenRightBranchCrosswalk.lean` (source lock v1.2.7) |
| Meixner–Schäfke 1954, §3.24 (Satz 6) | `/mnt/hdd01/Paper_to_read/978-3-662-00941-3.pdf`, printed pp. 238–240 = PDF 250–252 | pages rendered and read |
| Meixner–Schäfke 1954, §1.8 (Sätze 1–4) | same PDF, printed pp. 89–92 = PDF 101–104 | pages rendered and read |
| Meixner–Schäfke 1954, §3.23 | printed pp. 236–238 | read; carries normalization and eigenvalue-curve material, not load-bearing here |

DLMF §30.3 cites exactly «Meixner and Schäfke (1954), §3.23, §3.24, and §3.531»
as the provenance of all results in the section. §3.531 concerns the eigenvalue
functions Λ_n^m(γ²); it is recorded but not needed for the forward statement.

## 1. Exact one-way source statement (U2.0 lock)

### 1.1 DLMF 30.3(iii), version 1.2.7

Equation 30.3.5 (split at even p, Pringsheim notation):

```
β_p − λ − α_{p−2}γ_p/(β_{p−2}−λ) − α_{p−4}γ_{p−2}/(β_{p−4}−λ) − ⋯
  = α_p γ_{p+2}/(β_{p+2}−λ) − α_{p+2}γ_{p+4}/(β_{p+4}−λ) − ⋯
```

DLMF wording: the equation, with coefficients 30.3.6 or 30.3.7, «has the
solutions λ = λ_{m+2j}^m(γ²), j = 0,1,2,…» for even p. This is the printed
one-way membership: **every even eigenvalue solves the equation**. The lock
keeps this direction and does not promote it to an iff.

30.3.7 coefficients at order m = 0 (the project's audited instantiation):

```
α_k = γ² (k+1)(k+2) / ((2k+3)(2k+5))
β_k = k(k+1) − 2γ² (k(k+1)−1) / ((2k−1)(2k+3))
γ_k = γ² (k−1)k / ((2k−3)(2k−1))
```

### 1.2 Meixner–Schäfke §3.24, Satz 6 (printed p. 239) — the proof-bearing source

Setup (verbatim content): substitute `y(z) = (1−z²)^{m/2} u(z)` into the
spheroidal equation; the power series `u(z) = Σ u_p z^p` gives the three-term
recursion (7)

```
(p+1)(p+2) u_{p+2} + [λ* − (m+p)(m+p+1)] u_p − γ² u_{p−2} = 0,
λ* = λ + γ²,  u_{−1} = u_{−2} = 0,
```

which splits into an even and an odd recursion. Eigenvalues are characterized
by (7) plus condition (9): `|u_ρ|^{1/ρ} → 0 (ρ → +∞)` — the series is an
entire function. Every eigenfunction is even or odd, so either all odd or all
even `u_p` vanish. Then:

> Satz 6. Die Eigenwertpaare λ = λ_n^m(γ²), γ² bilden mit λ* = λ + γ² bei
> geradem n−m die Gesamtheit der Lösungspaare der Kettenbruchgleichung
> 0 = λ* − m(m+1) + 1·2·γ²/(λ*−(m+2)(m+3)| + 3·4·γ²/(λ*−(m+4)(m+5)| + ⋯
> bzw. der invertierten Gleichungen […]

Two facts the lock records:

1. The book proves **Gesamtheit** — set equality, i.e. both directions. The
   Lean target still consumes only the forward direction; the stronger book
   claim is documentation, not cargo. (The reverse direction is already
   kernel-carried independently by `regularEvenSpheroidal_of_mode4Root` and
   must not be re-imported from here.)
2. «bzw. der invertierten Gleichungen» — the book states the equation family
   projectively: when a denominator of the printed form vanishes, the claim
   is carried by the inverted equations. See § 3 (pole conditions).

Proof mechanism named by the book: «Durch Anwendung von 1.8. erkennt man so
Satz 6» — chapter §1.8 supplies the continued-fraction theory.

### 1.3 Meixner–Schäfke §1.8 (printed pp. 89–92) — the machinery

For `A_k z_{k+1} + B_k z_k + C_k z_{k−1} = 0` with `A_k ≠ 0 ≠ C_k`,
normalized by weights α_k (α_{k+1}A_k = α_{k−1}C_k, z_k = α_k y_k) to
`y_{k+1} − D_k y_k + y_{k−1} = 0`, under the Voraussetzung `|D_k| ≥ 2`:

- **Satz 1**: solution space is 2-dimensional; a solution is fixed by any
  consecutive pair.
- **Satz 2**: the determinant `δ(y, y*) = y_{k+1} y*_k − y_k y*_{k+1}` is
  constant in k (for the normalized recursion).
- **Satz 3**: trichotomy — trivial; Typ II (minimal: `|y_k| ≤ (|D_k|−1)^{−1}|y_{k−1}|`);
  Typ III (dominant: eventually `|y_{k+1}| > (|D_k|−1)|y_k|`, unbounded, `|T_k| ≥ k`).
- **Satz 4**: solutions of all three types exist; **no two linearly
  independent Typ-II solutions**; y is Typ II **iff**
  `y_1/y_0 = 1/D_1| − 1/D_2| − 1/D_3| − ⋯`, and then
  `y_i/y_{i−1} = 1/D_i| − 1/D_{i+1}| − ⋯` for every i.
- Convergence convention (printed p. 92): the infinite continued fraction is
  **defined** as `lim_{k→∞} S_k^{(i)} / T_k^{(i)}`, where S, T are the
  solutions of the recursion with initial data `S_{i−1} = −1, S_i = 0`,
  `T_{i−1} = 0, T_i = 1` — i.e. the limit of **terminal-zero finite
  truncations** (continuants). Convergence is proved by
  `S_{k+1}/T_{k+1} − S_k/T_k = 1/(T_k T_{k+1})` and `|T_k| ≥ k`.

This is Pincherle-type theory: minimal solution ⟺ continued fraction value.

## 2. Exact coefficient / split / convergence dictionary

Units and indexing, locked:

| Object | Book §3.24 | DLMF 30.3 | Project (kernel-green) |
|---|---|---|---|
| parameter | γ² | γ² | `G = mode4JacobiG mProject = (2π·mProject)²` |
| eigenvalue | λ (via λ* = λ+γ²) | λ | `Λ` (project Λ = DLMF λ) |
| order | m (here m = 0) | m = 0 | fixed by even predicate at order 0 |
| basis | power series u_p z^p | Legendre-coefficient recursion (30.3.7) | Legendre: `f = Σ c_k P_{2k}` (`lpv (2*k)`) |
| index | p (degree), even branch p even | k (degree) | `q` parity-compressed, degree `N = mode4JacobiIndex q = 2q` |
| recursion | (7) with λ*, raw coefficients (≙ 30.3.6) | 30.3.7 α, β, γ | `mode4JacobiUpper/Center/Lower`; identities `mode4DLMF3037Alpha_even_eq_mode4JacobiUpper`, `…Beta_even_sub_eq_mode4JacobiCenter`, `…Gamma_even_eq_mode4JacobiLower` |
| boundary | u_{−1} = u_{−2} = 0 | — | left pair `(a_{−1}, a_0) = (0, 1)`, `mode4DLMF3035EvenLeftPair` / `mode4LeftPair` |
| split | p = 0 (book Satz 6 prints the full one-sided CF) | any even p | `splitDegree = 2*(K−1)`, first right degree `2*K` |
| infinite CF | lim of continuants S/T (§1.8) | 30.3.5 right branch | `limUnder atTop` of terminal-zero `mode4DLMF3035EvenRightFiniteApprox` = `mode4RightTailLimit` (kernel: `mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit`) |
| pole handling | «bzw. der invertierten Gleichungen» | not addressed | cross-multiplied pair equality `y.2 = R · y.1` (division-free) |

Two convention facts that dissolve the registered obstruction (see § 5):

- The 30.3.6-form (book raw recursion, λ*) and the 30.3.7-form (project) are
  related by the §1.8 α_k-normalization (2),(3) — an explicit diagonal
  rescaling; both sides are explicit rational functions of the index, so each
  needed identity is finite `field_simp`/`ring` algebra. The project never
  needs the 30.3.6 form: its predicate is written directly in the audited
  30.3.7 coefficients.
- 30.3.7 is the recursion of **Legendre expansion coefficients**. Checked
  against the kernel-green expansion `legendre_even_expansion`
  ((1−x²)P_{2k} = jacA_k P_{2k+2} + jacB_k P_{2k} + jacC_k P_{2k−2}):
  the DLMF up-coefficient `α_k/γ² = (k+1)(k+2)/((2k+3)(2k+5))` is the
  P_k-content of (1−x²)P_{k+2}, and `γ_k/γ² = (k−1)k/((2k−3)(2k−1))` is the
  P_k-content of (1−x²)P_{k−2} — verified symbolically at even degree against
  `jacA/jacB/jacC` and the already-proved `mode4DLMF3037*_even_eq_*` bridges.
- Moment vs coefficient normalization: with `m_k = ∫_{−1}^1 f·P_{2k}` and
  `c_k = ((4k+1)/2)·m_k`, the Legendre self-adjointness symmetry
  `(4k+1)·jacA k = (4k+5)·jacC (k+1)` (a `field_simp` identity) converts the
  moment recursion into exactly the harvest/project coefficient recursion.

## 3. Every convergence and pole condition of the printed CF

1. **Voraussetzung |D_k| ≥ 2** (§1.8) after normalization; the book notes it
   suffices that it holds from some k₀ on, dropping k₀−1 equations. Project
   analogue: `hsep` on `q ≥ K` (tail separation `(31/24)·G ≤ N(N+1) − 20`)
   plus `Λ ≤ 20`, giving contraction of `mode4TailMap` on `Icc 0 (1/2)`.
2. **Definition of the infinite CF** = limit of terminal-zero continuant
   ratios S_k/T_k. Identical convention to the project's
   `limUnder atTop (mode4DLMF3035EvenRightFiniteApprox …)`; existence is
   already kernel-carried in the contraction domain
   (`mode4BackwardTail_cauchy` → `mode4RightTailLimit`).
3. **No poles beyond the split**: under |D_k| ≥ 2 the continuants satisfy
   |T_{k+1}| ≥ |T_k| + 1 ≥ 1, so no truncation denominator vanishes; project
   analogue: tail denominators are bounded away from 0 in the contraction
   domain (already inside the tail-map lemmas).
4. **Poles in the finite left part** (λ near a diagonal value): the printed
   equation can lose meaning; the book covers this case by the inverted
   equations («bzw. der invertierten Gleichungen»). The project's
   division-free cross-multiplied predicate
   `y.2 = mode4DLMF3035EvenRightRatio · y.1` on the left **pair** is the
   formalization of exactly this projective convention. No extra pole
   condition remains.
5. **Rate**: |S_{k+1}/T_{k+1} − S_k/T_k| = 1/|T_k T_{k+1}| ≤ 1/(k(k+1));
   not load-bearing (the project uses its own geometric contraction rate).

## 4. Are the production `hsep` hypotheses sufficient?

Yes, expected sufficient, with one flagged point.

- For everything the ratified U2.2 algebra already carries (finite-left
  identity, right-ratio = tail limit, iff with `mode4RootFunction = 0`):
  sufficiency is proven, not predicted — those theorems exist under exactly
  `hm, hK, hsep, hΛ` (`hΛ : Λ ≤ 20`; the U2.3 shape's `hcut : evenBranch r < 20`
  is strictly stronger).
- For the new forward content (§ 6, step W5): the argument needs, beyond the
  existing contraction, only (a) tail ratios `x_q ∈ Icc 0 (1/2)` for all
  `q ≥ K` — supplied by `hsep` being cofinal (`∀ q ≥ K`); (b) the
  determinant-transport factors `mode4JacobiLower/mode4JacobiUpper ≠ 0` for
  `q ≥ K` — true since `G > 0` (mProject ≥ 2) and `N = 2q ≥ 6` for
  `K ≥ 3`; (c) a positive lower bound on the partial products
  `Π (Lower_j / Upper_j)` — the factors are `1 + O(1/j²)` explicit rationals.
- **Flagged as first re-check in Lean**: the quantitative lower bound (c).
  It is elementary (log-comparison or telescoping against `Π (1 − c/j²)`),
  but it is the one place where a new estimate, not a ratified one, carries
  load. No new hypothesis on top of `hm/hK/hsep/hcut` is anticipated.

## 5. Resolution of the registered prediction (U2.2 obstruction)

The verdict predicted the first obstruction at «exact identification of the
printed infinite continued fraction with the project `limUnder` object at
poles and under the production convergence hypotheses». Finding:

- **Convention side — resolved.** The source's own definition of the infinite
  CF (§1.8, printed p. 92) is the limit of terminal-zero continuant ratios —
  literally the project's `limUnder` of terminal-zero approximants. There is
  no Cesàro/analytic-continuation/equivalence-class subtlety to bridge.
- **Pole side — resolved.** The source itself retreats to the inverted
  equations at poles; the project's cross-multiplied pair form is that
  convention, made division-free.
- **Lean side — already kernel-carried** in the contraction domain:
  `mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit` and
  `mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero`.

U2.2 therefore closes as a *convention audit* (this document) sitting on the
existing kernel identities; no additional Lean object is required for it.

## 6. The weakest theorem that gives U2.3, and its proof plan

### 6.1 Weakest new statement

Two lemmas, then U2.3 is composition with ratified pieces.

**(A) Spectral-to-sequence.** If `RegularEvenSpheroidalEigenvalue G Λ`, then
there exists `c : ℕ → ℝ` with:

```
(i)   c 0 ≠ 0        (equivalently: c ≠ 0; c 0 = 0 forces c ≡ 0)
(ii)  ∀ k, (specD G k − Λ) * c k = G * (specJL k * c (k−1) + specJR k * c (k+1))
(iii) ∀ k, |c k| ≤ (4*k+1) * Cf     (polynomial bound, Cf = sup |f|)
```

(harvest names; identical to the mode4 recursion via the kernel-green
`mode4DLMF3037*_even_eq_*` bridges at degree `2q`).

**(B) Bounded-solution ratio lock (Pincherle, special case).** In the
contraction domain (`hm, hK, hsep`, `Λ ≤ 20`): every solution `c` of (ii)
with at-most-polynomial growth satisfies the division-free pair equality at
K: `c K = mode4RightTailLimit mProject Λ K * c (K−1)`.

Then: c ∝ left-pair continuant (both solve the same second-order recursion
with the same q = 0 boundary equation, c 0 ≠ 0), so the left pair satisfies
`y.2 = R · y.1`; with `mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero`
this is `mode4RootFunction = 0`, and the U2.3 statement
`evenBranch_mode4DLMF3035EvenCharacteristic` follows in exactly the
verdict-fixed shape (source object, units, split `2*(K−1)`, one-way
direction all preserved; `hcut` is consumed only as `Λ ≤ 20`, never as a
mode selector).

### 6.2 Proof plan for (A) — all ingredients kernel-green in the port

Define `m_k := ∫ x in (−1)..1, f x * lpv (2*k) x`, `c_k := ((4k+1)/2)·m_k`.

- W1 (moment recursion): Lagrange/Green pairing of the eigen-equation
  `−((1−x²)f′)′ = (Λ + G(1−x²))·f` against the Legendre ODE
  `−((1−x²)P_{2k}′)′ = 2k(2k+1)·P_{2k}`; boundary terms die by the flux
  condition and boundedness (`spheroidal_wronskian_tendsto_one/_neg_one`
  machinery, as in `spheroidal_orthogonality` — same integral, different
  second function). Then `legendre_even_expansion` converts
  `∫ (1−x²) f P_{2k}` into `jacA·m_{k+1} + jacB·m_k + jacC·m_{k−1}`.
- W1′ (normalization): `(4k+1)·jacA k = (4k+5)·jacC (k+1)` (`field_simp`)
  turns the moment recursion into (ii).
- W2 (nontriviality): if all `m_k = 0` then, f being even, `∫ f·p = 0` for
  every polynomial p; Weierstrass approximation on `Icc (−1) 1` gives
  `∫ f² = 0`, contradicting the predicate's nonvanishing clause. Hence some
  `m_k ≠ 0`, and the k = 0 boundary equation propagates `c 0 = 0 ⇒ c ≡ 0`
  (uses `G ≠ 0`, `jacC (k+1) ≠ 0`), so `c 0 ≠ 0`.
- W3 (bound): `|m_k| ≤ 2·sup|f|` from `|P_{2k}| ≤ 1` on the interval.

### 6.3 Proof plan for (B) — Wronskian-vanishing, no growth trichotomy

Build the minimal comparison solution backwards from the tail:
`b_{K−1} := 1`, `b_q := x_q · b_{q−1}` for `q ≥ K` with
`x_q := mode4RightTailLimit … q` (exists for every `q ≥ K` since `hsep` is
cofinal); the tail fixed-point identity makes `b` a recursion solution with
`|b_q| ≤ (1/2)^{q−K+1}`. For the determinant
`δ_q := c_{q+1} b_q − c_q b_{q+1}`:

- transport: `Upper_q · δ_q = Lower_q · δ_{q−1}` (one line from the shared
  recursion), so `δ_q = δ_{K−1} · Π_{j} (Lower_j/Upper_j)` with the product
  bounded below away from 0 (§ 4, flagged point);
- collapse: `|δ_q| ≤ (4q+5)·Cf·(1/2)^{q−K}` → 0, hence `δ_{K−1} = 0`, i.e.
  `c K · b_{K−1} = c_{K−1} · b_K`, i.e. `c K = x_K · c_{K−1}` — the pair
  equality, division-free, poles never touched.

This is §1.8 Satz 2 + Satz 4 (uniqueness half), re-proved natively in the
special contraction domain; the full trichotomy (Satz 3) is not needed.

## 7. Precise proof source (not merely the DLMF statement)

- **Statement**: DLMF 30.3.5/30.3.7 (audited TeX hashes in the repo) ⟵
  Meixner–Schäfke 1954, §3.24 Satz 6 (printed p. 239).
- **Proof**: Meixner–Schäfke §1.8 (printed pp. 89–92), Sätze 1–4 —
  three-term recursions, minimal solutions, continuant convergence — applied
  through the entire-function condition (9) of §3.24. DLMF adds no proof of
  its own; §3.531 (eigenvalue functions) is auxiliary.
- **Lean realization**: not a citation port. The plan in § 6 re-proves the
  needed forward half natively (Legendre basis instead of the book's power
  series; equivalent by the §1.8 normalization transform), consuming only
  kernel-green project/harvest lemmas. **After U2.3, no paper verifier
  remains in the U2.3 chain** — the hard stop's demand that the source proof
  behind §30.3(iii) ultimately be formalized is met by construction for the
  forward direction, on the production domain.

## 8. Discipline checks (DO_NOT list)

- No Lean edited in this transaction. No axiom, no typed hole.
- Reverse crosswalk not used anywhere in § 6 (direction comes from the
  eigenfunction's own Legendre coefficients).
- DLMF statement not treated as iff; the book's stronger Gesamtheit is
  recorded as provenance only.
- `Λ < 20` used only as domain bound (`hΛ`), never as a mode selector.
- `splitDegree` nowhere identified with the source eigenvalue degree.
- DLMF branch nowhere defined via the project branch (the forward content is
  produced from the eigenfunction, not from the package enumeration; U2.1's
  crosswalk stays a separate later concern).

## RESULT

```
DLMF3035_FORWARD_SOURCE_AND_PROJECT_OBJECT_LOCKED
```

Next authorized step per verdict `68e9cd78`: write the forward module only
(`G6N1SpheroidalCrosswalkForward`), as its own transaction; range-equality
composition (U2.4) and selected-theta consumer replacement (U2.5) remain
separate transactions.
