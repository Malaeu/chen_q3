# R2 preflight: the exact source identity behind `P59_ZETA_ZERO_EVALUATION_RANGE_IDENTITY`

**Agent:** mathematics preflight agent (paper + source reading, READ-ONLY).
**Date:** 2026-09-04. **Branch:** `rh_clean`.
**Status:** DIAGNOSTIC / source audit. `PX_RH_CLAIM: NOT_MADE`. No Lean edit, no numerical run,
no route promotion. Sole write: this file.

**Target.** Judge's verdict
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_GROUND_TRANSFORM_ZERO_PINNING_AND_REAL_ZERO_IDENTIFICATION_2026-09-04.md`,
`Q2_ZERO_SUPPLIER.S9`, candidate `P59_ZETA_ZERO_EVALUATION_RANGE_IDENTITY`,
re-representation `R2_P59_EVALUATION_RANGE_IDENTITY` (CHEAPEST_SOURCE_TEST, kill 8/10, cost 4/10).

**Sources read (all on disk, no web):**

* `docs/routeB_bus/litreview/pdfs/2607.02828.pdf` — A. Groskin, *A finite Guinand–Weil dictionary
  and archimedean tail order for the truncated Weil quadratic form*, arXiv:2607.02828v1, 2 Jul 2026.
  Read in full (pp. 1–8 of the dictionary part).
* `docs/routeB_bus/litreview/pdfs/2511.22755.pdf` — Connes–Consani–Moscovici, *Zeta Spectral
  Triples*, arXiv:2511.22755v1. §3 (pp. 5–8), §5.6 (pp. 22–24), Thm 5.10, Lemma 7.3, §8.
* `docs/routeB_bus/phase5_scripts/edge_ledger_build.py` — `CCMArbBuilder`
  (`w02`, `wr`, `prime`, `q_nm`, `tau_entry`, `even_block`).
* `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean` (`ccmWeilTauN1`,
  `ccmWREntry`, `ccmW02Entry`, `ccmPrimeEntryN1`),
  `.../CCMFiniteWeilSourceCommutator.lean` (`ccmWeilTau_structured_offdiag`),
  `.../Proposition59EntireTransform.lean` (`proposition59RawTransform`).
* `docs/Progress_Log.md` entries of 2026-09-04 (S9 five-cell test; R2 hand test).
* Parent verdict `PROSHKA_VERDICT_GOAL058_SHELL_SEARCH_SOURCE_TO_LATTICE_ATOM_2026-09-03.md`
  (`99927f01`), lines 145–148 and 449.
* `./ask.sh "explicit formula"`, `./ask.sh Guinand`, `./ask.sh ccmWeilTau` (receipts: shelf
  INCOMPLETE on `q3_docs` semantic-index freshness only; Lean index and literature layers ran).

`Proposition59ExplicitProductCurvatureBridge.lean` and every other `.lean` file were **not**
edited (concurrent agent).

---

## 0. Notation

| symbol | meaning |
|---|---|
| `c = m`, `L = log m`, `Δ = L/2π`, `ρ = 2π/L` | window / cutoff (Groskin §2.1; CCM `L = 2 log λ`, `x = λ² = c`) |
| `V_k`, `\|k\| ≤ N` | CCM orthonormal window basis on `[λ⁻¹,λ]`, `V_k(u) = L^{-1/2} exp(2πi k log(λu)/L)` |
| `v ∈ ℝ^{N+1}` | even-sector Galerkin vector; symmetric embedding `u₀ = v₀`, `u_k = u_{−k} = v_k/√2` |
| `K = K(m,N)` | the project's even block: `even_block()` of `tau_entry = w02 − wr − prime`; Lean `ccmWeilTauN1` |
| `e(z)_k = L^{-1/2}·2 sin(zL/2)/(z − 2πk/L)`, `\|k\| ≤ N` | full-mode evaluation vector |
| `E(z)` | even-block evaluation vector: `E₀ = e₀`, `E_k = (e_k + e_{−k})/√2`, `k = 1..N`; `E(−z) = E(z)` |
| `F_v(z) = ⟨v, E(z)⟩` | the P59 transform of `v` |
| `Z*` | `{z ∈ ℂ : ζ(1/2 + iz) = 0, nontrivial}`, with multiplicity; `z ∈ Z* ⟹ −z, ±z̄ ∈ Z*` |
| `γ_j > 0` | the on-line elements of `Z*` in increasing order (`γ₁ = 14.1347…`) |
| `λ₁ ≤ λ₂ ≤ …`, `ξ = u₁` | eigenpairs of `K`, `ξ` unit-`ℓ²`, even ground state |
| `b(t) = K⁻¹E(t)` | the observer's vector; `b_i = F_{u_i}(t)/λ_i` in the eigenbasis |
| `R(t,s) = ⟨E(t), E(s)⟩` | reproducing kernel of the even window space |

Beware of a name collision inherited from the log: S9's `C_j := F_ξ(γ_j)/λ₁` is indexed by
**zeros**; the R2 hand test's "components `(C_1, −4.6, 1.0, −0.2, …)`" are `b_i = F_{u_i}(γ₁)/λ_i`,
indexed by **eigenvectors**. They agree only in the first slot (`u₁ = ξ`, `γ` fixed `= γ₁`).

---

## 1. The object is identified: `K` **is** Groskin's `Q∞`, and `e(z)` **is** CCM (5.25)

**1.1 Matrix.** Groskin §2.1 (p. 3) defines three source functions `ψ_p^{(c)}, ψ₀, ψ_{ℝ,T}` and the
divided-difference matrices `Q_ψ`; Lemma 2.1 (p. 4) proves entrywise

> `⟨v, Q∞ v⟩ = W_{0,2}(F_v) − W_ℝ(F_v) − W_p(F_v)`, `Q∞ := Q_prime^{(c)} + Q_pole + Q_arch,∞`,

i.e. `Q∞` **is** the Connes–Consani–Moscovici Galerkin matrix of the Weil form in the notation of
CCM (3.10)–(3.11), (3.16). The identification was checked term by term against the builder:

* pole: Groskin's proof of Lemma 2.1 derives
  `(Q_pole)_{mn} = 32L sinh²(L/4)(L² − 16π²mn) / ((L² + 16π²m²)(L² + 16π²n²))`
  — character-for-character `CCMArbBuilder.w02` (`edge_ledger_build.py`).
* prime: `ψ_p^{(c)}(x) = −(1/π) Σ_{q = p^a ≤ c} Λ(q) q^{-1/2} sin(2πx(1 − log q/L))`. Its divided
  difference is `−Σ Λ(q) q^{-1/2} · q_nm(n,m,log q)` with the builder's
  `q_nm(n,m,y) = (sin(2πmy/L) − sin(2πny/L))/(π(n−m))` — the sign flip `sin(2πm(1 − y/L)) =
  −sin(2πmy/L)` for integer `m` makes the two expressions identical, diagonal
  `q_nm(n,n,y) = 2(1 − y/L)cos(2πny/L)` included. So `CCMArbBuilder.prime = −Q_prime^{(c)}`.
* archimedean: `CCMArbBuilder.wr` is the CCM closed form (`alpha/beta/gamma` from `2F1`, digamma,
  polygamma, Lerch); Groskin Lemma 2.1 proves the entrywise `T → ∞` limit of `Q_arch,T` equals
  exactly that closed form, so `wr = −Q_arch,∞`. Independent numerical support already in the
  repo: Phase 0 matched the Zenodo 21146461 archimedean reference to `8.5e-20`
  (`edge_ledger_build.py` docstring).

Hence `tau_entry = w02 − wr − prime = (Q_pole) + (Q_arch,∞) + (Q_prime^{(c)}) = Q∞`. Same for the
Lean `ccmWeilTauN1 = ccmW02Entry − ccmWREntry − ccmPrimeEntryN1`. **The project's `K` is
literally the cutoff-free truncated Weil matrix of Groskin Thm 2.5, in its even sector, with the
same isometric even embedding `u₀ = v₀`, `u_k = v_k/√2` (Groskin p. 3 = `even_block()` docstring).**

**1.2 Evaluation vector.** CCM Proposition 5.9 (p. 23, eq. 5.25): for `ξ(u) = Σ_{|k|≤N} ξ_k V_k(u)`
extended by `0`,

> `ξ̂(z) = 2 L^{-1/2} sin(zL/2) Σ_{|j|≤N} ξ_j/(z − 2πj/L)`.

That is exactly `⟨ξ, e(z)⟩`. So **`e(z)_k = V̂_k(z)`: the evaluation vector is the Riesz representer
of the evaluation functional `f ↦ f̂(z)` on the window space `E_N`**, and `R(t,s) = ⟨E(t),E(s)⟩` is
its reproducing kernel. The project already has this in Lean:
`proposition59RawTransform_eq_paper_formula` (`Proposition59EntireTransform.lean:119`).

---

## 2. Deliverable (1): the finite explicit formula in project coordinates

**Theorem (Groskin 2607.02828, Thm 2.5, p. 6; with Lemma 2.1 p. 4 and Lemma 2.2 p. 4).**
For fixed `c > 1`, `N ≥ 0` and every real even `v ∈ ℝ^{N+1}`,

```
⟨v, Q∞ v⟩ = Σ_{z ∈ Z*} g_v(z),        Z* = { z : ζ(1/2 + iz) = 0 nontrivial },   with multiplicity
```

equivalently (same page)

```
⟨v, Q∞ v⟩ = −(1/π) Σ_{q = p^a ≤ c} Λ(q) q^{-1/2} ĝ_v(log q/2π) + 2 g_v(i/2) + (1/2π) ∫_ℝ h₊(r) g_v(r) dr,
h₊(r) = Re ψ_Γ(1/4 + ir/2) − log π,
```

with `g_v(z) = ∫_{−Δ}^{Δ} ĝ_v(ξ) e^{2πizξ} dξ`, `ĝ_v(ξ) = π K_v(1 − |ξ|/Δ)`,
`K_v(ω) = 2∫₀^ω T_v(t)T_v(ω−t)dt`, `T_v(t) = Σ_{|m|≤N} u_m e^{2πimt}`. The sum is absolutely
convergent (Lemma 2.2: `g_v` entire, type `≤ L`, `ĝ_v` supported in `[−Δ,Δ]`,
`g_v(z) = O((1+|Re z|)^{-2})` on strips; plus Riemann–von Mangoldt). No `N`-limit and no
archimedean cutoff enter. CCM's own statement of the same mechanism is (3.2) + (3.10)–(3.11)
(pp. 5–7), together with CCM's remark on p. 6 that they apply the explicit formula only to
convolutions `f* ∗ f` of compactly supported `L²` functions, "thus ensuring the absolute
convergence of the sum over the zeros".

**Closing the last gap: `g_v = F_v²`.** Groskin does not print `g_v` in the P59 coordinates. I
derived it (two independent routes, agreeing with no stray constant):

*Route A (from Groskin's own kernels).* `T_v` is real, even and 1-periodic (`u_m = u_{−m} ∈ ℝ`), so
`K_v(ω) = 2∫₀^ω T_v(t)T_v(t−ω)dt`, and with `λ = ξ/Δ`, `t' = t + λ`, periodicity `T_v(t'−1)=T_v(t')`:
`ĝ_v(ξ) = 2π ∫_λ^1 T_v(t')T_v(t'−λ) dt' = 2π (f ⋆ f̃)(ξ/Δ)` for `f = T_v·1_{[0,1]}`. Therefore
`g_v(z) = 2πΔ |f̂(zΔ)|² = L·|f̂(zΔ)|²` for real `z`. Expanding `f̂(zΔ) = Σ_m u_m ∫₀¹ e^{i(2πm − zL)t}dt`
and using `sin(πm − x) = −(−1)^m sin x`, `e^{iπm} = (−1)^m` (the `(−1)^m` cancels):
`f̂(zΔ) = e^{−izL/2} Σ_m u_m · 2 sin(zL/2)/(zL − 2πm) = e^{−izL/2} L^{-1/2} F_v(z)`. Hence
`g_v(z) = L · L^{-1}|F_v(z)|² = F_v(z)²`.

*Route B (from CCM).* `QW(f,f) = Ψ(f* ∗ f) = Σ_ρ (f*∗f)~(ρ)` (CCM (3.2), (3.10)); by the
convolution property the zero-side term is the squared Fourier–Mellin transform of `f`, and CCM
Prop 5.9 says that transform is exactly `F_v`. Same result, no constant.

### The identity in project coordinates

```
  ⟨v, K(m,N) v⟩  =  Σ_{z ∈ Z*}  F_v(z)² ,        F_v(z) = ⟨v, E(z)⟩ = 2 L^{-1/2} sin(zL/2) Σ_{|j|≤N} u_j /(z − 2πj/L)

  polarized:      K(m,N)  =  Σ_{z ∈ Z*}  E(z) E(z)ᵀ      (absolutely convergent, entrywise)

  under RH:       ⟨v, K v⟩ = 2 Σ_{j≥1} |F_v(γ_j)|²      (E even ⇒ ±γ contribute equally)
```

**Truncation / tail terms: there are none.** This is the point of Thm 2.5. Prime powers `q > c`
drop out because `supp ĝ_v ⊂ [−Δ,Δ] = [−L/2π, L/2π]` and `log q/2π > Δ ⟺ q > c`. The archimedean
`T`-cutoff is absent because the project uses the closed-form `wr`, i.e. `Q_arch,∞`. (Groskin's
second theorem, Thm 3.2 / Cor 3.3 pp. 8–11 with budget `B_T ≈ (2N+1)ρ(log(T/2π)+1)/(π²T)`, is
about the *other* assembly, the finite-`T` one; it does **not** apply to our `K` and is not
needed. Its content for us is only: a finite-`T` archimedean truncation would *lower* every
eigenvalue, so nothing in the project's numbers can be blamed on an archimedean cutoff.)

**Status of this identity: PAPER_PROVED, unconditional.** Groskin Thm 2.5 + Lemmas 2.1, 2.2. The
step `g_v = F_v²` in the P59 coordinates is my derivation, elementary, two independent routes.

---

## 3. Deliverable (2): what the range statement `e(γ) = K b(γ)` actually is

**3.1 As stated, the range identity is empty.** `K` is symmetric and (numerically) invertible, so
`b(γ) := K⁻¹E(γ)` exists for *every* `t`, zero or not, and `E(t) = K b(t)` holds trivially. The
range of `K` is all of `ℝ^{N+1}`. Nothing about `γ` is used. The candidate formula
`evaluationVector(m,N,γ) = K(m,N)·b(m,N,γ)` therefore carries **no** content; all the content is
in `REQUIRED_BOUND: b bounded on each fixed γ-compact`.

**3.2 The exact interpolation reading.** From `K = Σ_z E(z)E(z)ᵀ`:

```
K b = Σ_z F_b(z) E(z) ;        E(γ₁) = K b(γ₁)  ⟺  Σ_z F_{b}(z) E(z) = E(γ₁).
```

An *exact* solution with `F_b(γ₁) = 1/2` and `F_b(γ_j) = 0` for `j ≠ 1` would be a finite
band-limited function vanishing at every zeta zero but one. Impossible: `F_b(t) =
2L^{-1/2}sin(tL/2)·Σ u_j/(t − 2πj/L)` has, besides the lattice zeros `2πk/L` (`|k| > N`), only the
finitely many roots of the Cauchy numerator. So `b = K⁻¹E(γ₁)` is a *least-squares surrogate* for
an interpolation vector that does not exist.

**3.3 What IS uniform in `m`, exactly and provably.** Set `θ := F_b(γ₁) = ⟨E(γ₁), K⁻¹E(γ₁)⟩`
(`b = K⁻¹E(γ₁)`). Then `⟨b, K b⟩ = θ` and, by §2, `⟨b,Kb⟩ = Σ_z F_b(z)²`, whence under RH

```
  2 Σ_{j≥1} F_b(γ_j)²  =  θ   and   2 F_b(γ₁)² = 2θ² ≤ θ   ⟹   0 ≤ θ = ⟨b(γ), K b(γ)⟩ ≤ 1/2 ,
  Σ_{j ≥ 2} F_b(γ_j)² = θ/2 − θ² ≤ 1/8 .
```

Variationally, `θ = ½ · sup_{v ≠ 0} F_v(γ₁)² / Σ_{j≥1} F_v(γ_j)²` — a one-zero *concentration
ratio*, bounded by `1/2` uniformly in `m, N`. **This is a genuine uniform bound and it is the
honest core of R2 — but it is in the `K`-norm, not in `ℓ²`.**

**3.4 The `ℓ²` bound the candidate needs is not implied.** `‖b‖₂² = ⟨E(γ), K⁻²E(γ)⟩`. From `θ ≤ 1/2`
one gets only `‖b‖₂² ≤ θ/λ₁ ≤ 1/(2λ₁)`, i.e. `‖b‖₂ ≤ (2λ₁)^{-1/2}`. With `λ₁ ~ 10^{−1.9m}` that is
`~10¹²` at `m=13`, `~10²²` at `m=23`, `~10⁴¹` at `m=43` — against the observed `58, 58, 52`.
Equivalently, in eigencoordinates the source gives exactly

```
  |F_{u_i}(γ)| ≤ √(λ_i/2)   for every eigenvector u_i and every ON-LINE zero γ   (RH-conditional, §5)
  ⟹  |b_i| = |F_{u_i}(γ)|/λ_i ≤ (2λ_i)^{-1/2} .
```

For `i ≥ 2` (where `λ_i` is `O(1)`) this bound is of the observed order — `|b_2| ≤ (2λ_2)^{-1/2}`
against the observed `4.6` is plausible sharpness. For `i = 1` it is `27 orders` too weak.

**I tried and failed to close the gap from the dictionary alone.** Three attempts, all circular:

* pairing `Kξ = λ₁ξ` with `b` reproduces `F_ξ(γ₁) = 2Σ_j F_ξ(γ_j)F_b(γ_j)`, and Cauchy–Schwarz
  returns exactly `|F_ξ(γ₁)| ≤ √(λ₁/2)` again;
* eliminating the `j = 1` term gives `|F_ξ(γ₁)| ≤ √(2λ₁θ)/(2√δ)`, `δ = 1/2 − θ`, which **degrades**
  as `θ → 1/2` and never beats `√λ₁`;
* an approximate-interpolation vector `w` with `F_w(γ₁) = 1`, `‖(F_w(γ_j))_{j≥2}‖₂ = ‖ε‖₂` gives
  `|F_ξ(γ₁)| ≤ (λ₁/2)‖w‖ + √(λ₁/2)‖ε‖₂` — the `O(λ₁)` law needs `‖ε‖₂ = O(√λ₁)`, which is not a
  consequence of anything in the corpus.

> **FIRST MISSING STEP (stated exactly).** A uniform-in-`m` bound of the form
> `‖K(m,N)⁻¹E(γ)‖₂ ≤ C(γ)` — equivalently `|F_ξ(γ)| = O(λ₁)` rather than `O(√λ₁)` — i.e.
> **one full half-power of `λ₁` beyond the finite Guinand–Weil dictionary.** Concretely: a vector
> family `w_m` with `F_{w_m}(γ) = 1`, `Σ_{j: γ_j ≠ γ} F_{w_m}(γ_j)² = O(λ₁)`, `‖w_m‖₂ = O(1)`. No
> such statement exists in Groskin 2607.02828, in CCM 2511.22755, or on the project's shelf
> (`ask.sh` receipts above). **It is NEW_ANALYTIC, and it is not a corollary of the dictionary.**

**3.5 Hypotheses used.**

| step | needs `γ` on the critical line? | needs RH? |
|---|---|---|
| `⟨v,Kv⟩ = Σ_{z∈Z*} F_v(z)²` | no | no — unconditional, every zero, with multiplicity |
| `K = Σ_z E(z)E(z)ᵀ` | no | no |
| `b = K⁻¹E(t)` exists, `⟨b,ξ⟩ = F_ξ(t)/λ₁` | no | no (pure linear algebra) |
| `F_v(γ)² = |F_v(γ)|² ≥ 0` | **yes** (that zero real) | no |
| `2|F_v(γ)|² ≤ ⟨v,Kv⟩`, i.e. `θ ≤ 1/2`, `|F_ξ(γ)| ≤ √(λ₁/2)` | yes | **yes** — needs all *other* terms `≥ 0` |

At an **off-line** zero `ρ = β + iγ₀`, `β ≠ 1/2`, the parameter is `z = γ₀ − i(β − ½)`, non-real,
`|Im z| ≤ 1/2`, and the quadruple `ρ, 1−ρ, ρ̄, 1−ρ̄` contributes `4 Re F_v(z)²` — **sign
indefinite**. Consequently (i) no bound on `|F_v(z)|` follows, so an off-line zero is *invisible*
to the mechanism, and (ii) if that contribution is negative it destroys the on-line bound as well.
At a **complex non-zero point** (e.g. the planned `γ₁ + 0.1i`) there is no constraint at all.

---

## 4. Deliverable (3): `F_ground(γ) = λ₁⟨b(γ), ξ⟩`, and where `C₁·L → 205` comes from

**4.1 The consequence is a tautology.** `⟨b(t), ξ⟩ = ⟨K⁻¹E(t), ξ⟩ = ⟨E(t), K⁻¹ξ⟩ = F_ξ(t)/λ₁`, for
any symmetric invertible `K`, any eigenpair, any `t`. So `F_ground(t) = λ₁⟨b(t), ξ⟩` holds at
`t = 15` exactly as at `t = γ₁`, and it explains nothing by itself. The log's remark that "the
first component equals S9's `C₁`" is therefore a *convention check*, not a test:
`b₁ = F_ξ(γ₁)/λ₁ = C₁` by definition. **This is worth recording before addendum 15 spends cells on
it.**

**4.2 The 80-order contrast IS explained, and about half of it is source-derived.**
`‖b(t)‖₂ ≈ |F_ξ(t)|/λ₁` (the `i=1` term dominates: `58` vs `4.6, 1.0, 0.2`). Then:

* at `t = γ_j` (a zeta zero) the dictionary **constrains** `F_ξ`: `|F_ξ(γ)| ≤ √(λ₁/2)`, so
  `‖b(γ)‖₂ ≤ (2λ₁)^{-1/2}`;
* at `t = 15` (not a zeta zero) the dictionary constrains `F_ξ` **not at all**; `F_ξ(15)` takes a
  generic value and `‖b(15)‖₂ ≈ |F_ξ(15)|/λ₁ ~ 1/λ₁`.

So the source predicts a contrast of at least `(2λ₁)^{-1/2}` vs `~1/λ₁` — i.e. **half the observed
exponent gap, unconditionally-modulo-RH**. Observed: `8e26 / 58` at `m=13` (≈26 orders) against a
predicted `≥ 13` orders. The other half is the missing `√λ₁` of §3.4. This is a satisfying partial
explanation and it is the correct way to state R2 without overclaiming.

**4.3 Where the `1/L` in `C₁·L → 205` comes from — derived.** Apply the frame identity to the
eigen-equation. From `λ₁ξ = Kξ = Σ_z F_ξ(z)E(z)`, pair with `E(t)`:

```
      λ₁ F_ξ(t)  =  Σ_{z ∈ Z*} F_ξ(z) R(t, z) ,        R(t,s) = ⟨E(t), E(s)⟩ .
```

The even-block kernel is `R(t,s) = ½(R_full(t,s) + R_full(t,−s))`, `R_full(t,s) = Σ_{|k|≤N}
e_k(t)e_k(s)`, and for the production cells (`N = m`, `2πN/L ≫ γ₁`) `R_full` is the truncated sinc
kernel `2 sin((t−s)L/2)/(t−s)` up to `O(L/m)`. Hence `2R(γ₁,γ₁) = L + sin(γ₁L)/γ₁ + O(L/m) ≈ L`.
Splitting off `z = ±γ₁`:

```
      F_ξ(γ₁) · ( λ₁ − 2R(γ₁,γ₁) )  =  2 Σ_{j ≥ 2} F_ξ(γ_j) R(γ₁, γ_j)
  ⟹  F_ξ(γ₁)  ≈  −(2/L) Σ_{j ≥ 2} F_ξ(γ_j) R(γ₁, γ_j)          (λ₁ ≪ L)
  ⟹  C₁ · L    ≈  −2 Σ_{j ≥ 2} C_j R(γ₁, γ_j) .
```

**The factor `1/L` in the S9 law is exactly the reproducing-kernel norm `2R(γ,γ) ≈ L`.** That is
real, derived, source-based content, and it says the observed `C₁·√L` non-monotonicity vs `C₁·L`
monotonicity is not a coincidence. The *constant* `ℓ₁ ≈ 205` is `−2Σ_{j≥2}C_j R(γ₁,γ_j)`: the
identity does not predict its value, and the sum's convergence for fixed `m` is guaranteed only by
Cauchy–Schwarz against `Σ_{j≥2}C_j² ≤ 1/(2λ₁)`, which carries no uniform bound.

**Caution to record.** `R(γ₁,γ_j)` carries `sin(γ₁L/2)sin(γ_jL/2)`, and every `F_v` carries the
common factor `2L^{-1/2}sin(tL/2)`. The derived relation is therefore *oscillatory in `L`*, whereas
`C₁·L = 148.5, 182.1, 196.7, 201.1, 204.2` is monotone over `L = log m ∈ [2.56, 5.09]` — five
points, `L` varying by a factor of two. **A monotone five-point fit over one octave of `L` is weak
evidence for a limit**; the derived relation predicts the L-dependence is not a clean `1/L` unless
the oscillatory factors conspire. Extending to `m = 83, 163` (already in the schedule) only adds
`L = 4.42, 5.09`; a genuinely discriminating extension would vary `L` *independently of the prime
set*, which `edge_ledger_build.py` already supports (`L_override`, Probe 2).

---

## 5. Deliverable (4): RH-status

**The identity is unconditional; the inequality that makes it useful is not, and its failure mode
is exactly the not-RH branch.**

* `⟨v,Kv⟩ = Σ_{z∈Z*} F_v(z)²` holds for every nontrivial zero of `ζ`, real or not, with
  multiplicity, absolutely convergent (Groskin Thm 2.5 + Lemma 2.2). Unconditional.
* Split `⟨v,Kv⟩ = S_ℝ(v) + S_ℂ(v)`, `S_ℝ = Σ_{z real} F_v(z)² ≥ 0`, `S_ℂ = Σ_{z ∉ ℝ} F_v(z)²
  = Σ_{quadruples} 4 Re F_v(z)²` sign-indefinite. Then
  `2|F_v(γ)|² ≤ S_ℝ(v) = ⟨v,Kv⟩ − S_ℂ(v)`. The clean bound needs `S_ℂ(v) ≥ 0`, which RH supplies
  vacuously and nothing else supplies.
* **Not-RH branch.** With one off-line quadruple, taking `v = ξ` gives `S_ℂ(ξ) ≤ λ₁`, i.e.
  `4 Re F_ξ(z)² ≤ λ₁`: this constrains the *phase* of `F_ξ` at the off-line zero, not its modulus.
  `|F_ξ(z)|` may be `O(1)` with `Re F_ξ(z)² ≈ 0`. So a hypothetical off-line zero neither pins a
  zero of `F_ξ` nor shows up in the numbers. R2 supplies at best the **on-line half** of the
  divisor — precisely the `PARTIAL_TO_COMPLETE_DIVISOR_JUMP` the ZEROPIN verdict names as the
  first invalid step.

> **STANDING-KILL COLLISION — the most important finding of this preflight.**
> Written out exactly, R2's usable content is the implication
> *small Weil energy `⟨v,Kv⟩` ⟹ small `|F_v(γ)|` at zeta zeros.*
> That is verbatim the mechanism killed by the parent verdict `99927f01`
> (`PROSHKA_VERDICT_GOAL058_SHELL_SEARCH_SOURCE_TO_LATTICE_ATOM_2026-09-03.md`, line 449):
> *"Small Weil energy ⇒ values small at zeta zeros. This is false as an unconditional shell. The
> zero-side Hermitian sum is indefinite off the critical line; making it a sum of squares assumes
> the conclusion."* — code `KILL_SMALL_WEIL_ENERGY_TO_POINTWISE_ZERO_PINNING`,
> `KILL_EVIDENCE_KIND: INDEFINITE_HERMITIAN_ZERO_SUM` (lines 145–148), re-listed in the ZEROPIN
> verdict under `SCOPED_KILLS.SMALL_WEIL_ENERGY_TO_ZERO_PINNING`,
> `epistemic_status: MATHEMATICALLY_DEAD_WITHOUT_RH_SIGN`, and in the shell-search verdict's
> "what must not be tried again": *"a zero-side sum of squares without RH"* (line 634).
>
> The observer's own note of 2026-09-04 already flagged this ("механизм остаётся под вердиктом
> 99927f01"). This preflight upgrades that from a suspicion to a fact: **the exact source identity
> behind S9 exists, it is Groskin Thm 2.5, and its usable direction is under a standing kill.**
> R2 is therefore *not* an unconditional zero supplier and cannot become one. What it can still be
> is a **diagnostic instrument** and a **source-exact explanation of S9** — which is what §§2–4
> deliver.

---

## 6. Deliverable (5): what the DISCRIMINATOR needs beyond this identity

`DISCRIMINATOR: COMPLETE_ZERO_DIVISOR_TIGHTNESS_ON_COMPACTS` — "for every radius `R` whose boundary
avoids the target divisor, the positive P59 zero multiset inside `[0,R]` matches the target with
multiplicity for all large indices, and the unmatched reciprocal-square mass tends to zero."

The identity supplies **none of the three inputs**, and one third of one of them:

1. **Local multiset convergence with multiplicity.** Identity gives a *value* bound at each on-line
   zero, at best `|F_ξ(γ)| ≤ √(λ₁/2)`. A small value is not a nearby zero. Still needed:
   (a) a **normalization lower bound** — `F_ξ(0) = √L·ξ₀`, so the normalized quantity is
   `|F_ξ(γ)/F_ξ(0)| ≤ √(λ₁/2)/(√L |ξ₀|)`, and this needs a **uniform lower bound on the ground
   state's mode-0 weight `|ξ₀|`**; (b) a **slope lower bound** `inf|F_ξ'|` on a neighbourhood of `γ`,
   or a Rouché boundary lower bound, uniform in `m`; (c) **multiplicity and separation** control.
   The judge already says this ("a small value at `γ` alone does not prove a nearby zero").
2. **Escape of every unmatched bounded root.** The identity says nothing about zeros of `F_ξ` that
   are not near zeta zeros. The P59 numerator has `N` real roots; the identity constrains their
   *values-at-zeta-zeros*, never their locations.
3. **Vanishing unmatched reciprocal-square mass `Σ 1/ρ²`.** Completely outside the identity.
4. **Completeness.** By §5 the identity is blind to off-line zeros. Even a perfect version of (1)
   would give tightness only against the on-line part of `Z(Ξ)`, i.e. exactly the partial divisor
   the ZEROPIN verdict rejected as an identification hypothesis.
5. **Target crosswalk.** CCM Thm 5.10(ii) says `det_reg(D_log^{(λ,N)} − z) = −i λ^{−iz} ξ̂(z)`; Lemma
   7.3 (p. ~1731 of the text dump) gives the *trial* transform → `Ξ`; §8 explicitly leaves
   ground → trial open. Unchanged by this preflight.

**Net.** R2's kill-power against `COMPLETE_ZERO_DIVISOR_TIGHTNESS` is `0`, not `8/10`: it cannot
pass or fail the discriminator, because it says nothing about zero *locations* and nothing about
off-line zeros. Its actual value is (a) it identifies the exact source of S9, (b) it explains the
`1/L`, (c) it converts the S9 numbers into two falsifiable checks (§8).

---

## 7. Deliverable (6): Lean-ready vs NEW_ANALYTIC

**NEW_ANALYTIC (large):**

* The Guinand–Weil explicit formula itself. Mathlib has no explicit formula, no sums over
  nontrivial zeros, no `Λ`-weighted zero-side transport; `./ask.sh Guinand` returns **zero** Lean
  declarations (only literature rows). Formalizing Groskin Thm 2.5 means formalizing Weil's
  explicit formula for a band-limited class — out of scale for this front. It would enter as an
  **imported hypothesis**, not a proved lemma.
* The missing `√λ₁` of §3.4 (uniform `‖K⁻¹E(γ)‖₂` bound / near-interpolation family).
* The uniform lower bound on `|ξ₀|` needed to normalize `F_ξ(γ)/F_ξ(0)`.

**LEAN-READY (finite linear algebra, `Matrix` + `InnerProductSpace`, given the identity as a
hypothesis):** a clean conditional theorem, no analysis:

```
hypothesis  (S : Set ℝ)  (hK : K = Σ_{γ ∈ S} E γ ⊗ E γ)      -- summable, S ⊂ ℝ
conclusion  ∀ γ ∈ S, ∀ eigenpair (λ, u) of K with ‖u‖ = 1 :
              |⟨u, E γ⟩| ≤ √(λ/2)                                        -- (i)
              ⟨K⁻¹ (E γ), u⟩ = ⟨u, E γ⟩ / λ                              -- (ii)  spectral tautology
              ⟨K⁻¹ (E γ), K (K⁻¹ (E γ))⟩ = ⟨E γ, K⁻¹ (E γ)⟩ ≤ 1/2        -- (iii)
              λ ⟨u, E t⟩ = Σ_{γ ∈ S} ⟨u, E γ⟩ ⟨E t, E γ⟩                 -- (iv)  kernel relation
```

This is honest, small, and **closes nothing about RH** — the hypothesis `S ⊂ ℝ` *is* RH restricted
to the window. It should be labelled as such if it is ever entered. `Proposition59EntireTransform`
already supplies the `E`-side formula. Given the standing kill of §5, my recommendation is **not**
to spend a Lean node on it; the verdict's own `FIRST_LEAN_LOCAL_TARGET` (`QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND`)
is the better spend.

---

## 8. Two falsifiable checks the identity produces (for addendum 15) — and one non-check

**NON-CHECK.** `b₁ = C₁` (S9's first coefficient) is a definition, not a prediction (§4.1). Do not
count it as confirmation.

**CHECK P2 — eigenvector value bound (cheap, decisive on conventions and on RH-consistency).**
For every `i` and every on-line zeta zero `γ`:
`|F_{u_i}(γ)| ≤ √(λ_i/2)`, equivalently `|b_i(γ)| ≤ (2λ_i)^{-1/2}`.
Data already in hand at `m = 13, 23, 43` for `i = 1..6`. A violation means: either the project's
`K` is not `Q∞` (convention error somewhere in `w02/wr/prime` or the `√2` embedding), or the `e(t)`
normalization is off, or `S_ℂ < 0` (off-line zeros). Cost: arithmetic on stored numbers.

**CHECK P3 — the exact sum rule (the real test).** Under RH, with `C_j = F_ξ(γ_j)/λ₁`:

```
        Σ_{j ≥ 1} C_j²  =  1 / (2 λ₁)        exactly.
```

Every partial sum must be `≤ 1/(2λ₁)`; the deficit is the tail over high zeros. If a partial sum
*exceeds* `1/(2λ₁)`, the identity, the conventions, or `S_ℂ ≥ 0` fails. This is consistent with the
observed growth `C₁ = 58, C₂ ≈ −8e3, C₃ ≈ 2.6e5` (the mass `1/(2λ₁) ~ 10²⁵` lives at large `j`) and
it is the cheapest *quantitative* use of the dictionary the project has. It needs `F_ξ(γ_j)` at
many zeros — the same computation S9 already runs, extended in `j`.

**CHECK P4 — the `1/L` relation of §4.3.** `C₁ · (2R(γ₁,γ₁) − λ₁)/2 = −Σ_{j≥2} C_j R(γ₁,γ_j)` with
`R` the explicit truncated kernel. Same data as P3. This is what would turn `ℓ₁ ≈ 205` from a fit
into an identity.

**Prediction P5 (off-target point).** At `t = γ₁ + 0.1i` and at `t = 15`, `‖b(t)‖₂ ≈ |F_ξ(t)|/λ₁`
with **no** upper bound from any source; the identity predicts blow-up, not boundedness. If
`b(γ₁ + 0.1i)` came out *bounded*, the whole reading of §4.2 would be wrong and that would be the
interesting outcome.

---

## 9. Answers, compressed

1. **Identity:** `⟨v, K(m,N) v⟩ = Σ_{z: ζ(1/2+iz)=0} F_v(z)²`, `F_v(z) = ⟨v, E(z)⟩` the P59
   transform; polarized `K = Σ_z E(z)E(z)ᵀ`. Exact, **no truncation and no tail terms** (primes
   `> c` die on `supp ĝ_v`; the archimedean cutoff is absent because `wr` is the closed form
   `Q_arch,∞`). Source: Groskin arXiv:2607.02828 **Theorem 2.5, p. 6**, with **Lemma 2.1, p. 4**
   (`K = Q∞`, and the `w02` closed form derived in its proof) and **Lemma 2.2, p. 4**
   (admissibility / absolute convergence); CCM arXiv:2511.22755 **(3.2), (3.10)–(3.11), pp. 5–7**
   and **Prop. 5.9 eq. (5.25), p. 23** (`e(z)` is the vector of `V̂_k`).
2. **Range identity:** empty as stated (`K` invertible). Real content: `⟨b(γ),Kb(γ)⟩ =
   ⟨E(γ),K⁻¹E(γ)⟩ ≤ 1/2` uniformly in `m,N`, hence `|F_{u_i}(γ)| ≤ √(λ_i/2)` — but only in the
   `K`-norm. The `ℓ²` bound `‖b‖₂ = O(1)` is **not derivable**; the gap is exactly one half-power
   of `λ₁`. Hypotheses: the identity is unconditional; the bound needs `γ` real **and** all other
   zeros on the line.
3. **Consequence:** `F_ground(γ) = λ₁⟨b(γ),ξ⟩` is a spectral tautology, true at non-zeros too. The
   `1/L` in `C₁·L → 205` **is** explained — it is `2R(γ,γ) ≈ L`, the reproducing-kernel norm, via
   `λ₁F_ξ(t) = Σ_z F_ξ(z)R(t,z)`. The constant `205` is not predicted, and the five-point monotone
   fit over one octave of `L` is weak.
4. **RH-status:** identity unconditional (all zeros, real or not, with multiplicity); the useful
   inequality requires the off-line contribution `Σ 4Re F_v(z)² ≥ 0`, i.e. RH. In the not-RH branch
   an off-line zero is invisible (only its phase is constrained) and the on-line bound is destroyed.
   **The usable direction is the standing kill `KILL_SMALL_WEIL_ENERGY_TO_POINTWISE_ZERO_PINNING`
   of verdict `99927f01`.**
5. **Discriminator:** R2 gives no zero *locations*, no excess-zero escape, no reciprocal-square
   mass, and nothing off-line. Still needed: uniform `|ξ₀|` lower bound (normalization), uniform
   slope/Rouché lower bound near `γ`, multiplicity + separation, excess-zero mass, and the
   ground→trial→`Ξ` crosswalk (CCM §8, open).
6. **Lean:** the explicit formula is NEW_ANALYTIC and absent from Mathlib and from the project's
   Lean shelf; only the finite-dimensional consequences (i)–(iv) of §7 are Lean-ready, and they are
   RH-conditional by construction. Recommendation: do not spend a Lean node here.

---

`DIAGNOSTIC_NEVER_A_PROOF`. `PX_RH_CLAIM: NOT_MADE`. `RH_CLAIM: false`. `ROUTE_PROMOTION: false`.
`LEAN_EDIT_PERFORMED: false`. `NUMERICAL_RUN_PERFORMED: false`.
