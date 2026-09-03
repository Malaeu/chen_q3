# Agent report — Goal 058: source-specific real-zero quasi-eigenvector selector, source preflight

**Basis line (convention card rule).** Every row in this report is a **FULL mode row**
`v : [-N, N] → ℝ`, `v_{-n} = v_n`, in the raw-ratio scaling `x_n = ξ_n/ξ_0` of
`docs/routeB_bus/CONVENTION_CARD_GOAL058.md`. The EVEN-coordinate row of the card is
`v^{even}_n = √2 v_n` (`n ≥ 1`), `v^{even}_0 = v_0`; the P59 sample ratio carries **no** `√2`.
`R` is `(Rc)_n = c_n/n`, `(Rc)_0 = 0`, even → odd. `L = log m`, `N = m`, nodes `λ_n = n`,
`η ≡ 1` (`ccmEtaFinite`, verified: `CCMFiniteWeilSourceMatrix.lean:51-53`).

Date: 2026-09-04
Executor: Linux-Claude subagent (Opus), owner-authorized under verdict `9b822624`
Task: `docs/Codex/TASK_2026-09-04_goal058_realzero_quasieigen_selector_source_preflight.md`
Verdict acted on: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_XI_ROW_QUASI_EIGENVECTOR_AND_COLLAPSE_THEOREM_2026-09-04.md`
Mode: PAPER_AND_SOURCE_READ_ONLY — no Lean edit, no numerical run, no commit, nothing under
`phase5_scripts/`, no precommit, no queue, no verdict, no resolvent norm, no floor.

```yaml
TASK_ID: GOAL058_P59_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT
CODE: P59_REALZERO_CONE_NOT_SELECTIVE
JUDGE_PREDICTION_SCORED: [P_SOURCE_SPECIFIC_REALZERO_COMPONENT_IS_SELECTIVE, 0.30, REFUTED]
FIRST_FAILURE_POINT: CCM_THM_5_10_i_INNER_PRODUCT_IS_MANUFACTURED_FROM_THE_OPERATOR
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
ROUTE_PROMOTION: false
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
FALSIFIER_ROW_EXHIBITED: false        # see §7 — the kill is structural, not by witness
```

**One line.** Theorem 5.10(i) builds its inner product **out of the operator itself**
(`QW_λ^N − ε_N⟨·|·⟩` restricted to `E_N/ℂξ`), and a real matrix is self-adjoint for *some*
positive form exactly when it is diagonalizable over `ℝ` — so, once the form is detached from
the unknown ground row, the whole "self-adjoint characteristic determinant + displacement"
package is **provably equivalent to `ZerosRealOn` plus semisimplicity** (Theorem A, §1.3), while
keeping the form pinned to `QW_λ^N − ε_N` makes the predicate read *"`v` is the simple even
bottom eigenvector of `QW`"*, which is exactly the circularity the verdict's STRONGEST ATTACK
forbids. Neither horn supplies a selector: the unpinned admissible set is an **open** subset of
row space around any row with `2N` simple real roots, and an open set cannot cut the dimension
of a near-null slab whose width at the registered residual scale exceeds `λ₂` by 14 / 29 / 59 /
114 orders on `m = 13 / 23 / 43 / 83` (§5.2). All separating power sits in the residual, none in
the real-zero cone.

---

## 0. What was read

| Object | Locator | Used for |
|---|---|---|
| Judge verdict, §3 Q2, §6, STRONGEST ATTACK, CODEX DIRECTIVE | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_XI_ROW_QUASI_EIGENVECTOR_AND_COLLAPSE_THEOREM_2026-09-04.md` | the five required outputs, `ω_m`, (SEL), the plants |
| Bases and pairings | `docs/routeB_bus/CONVENTION_CARD_GOAL058.md` | basis line above |
| P59 transform, pole kernel, paper formula | `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean` | §2.1 |
| Ground zero-set bridge, `-Lz/(2π)` coordinate | `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean` | §1.1, §2 |
| The exact hypothesis bundle of the real-zero weld | `.../CCMFiniteWeilRealZeros.lean`, `.../CCMFiniteWeilBottomSpectral.lean`, `.../CCMFiniteWeilParity.lean`, `.../RankOneCorrectionLagrangeRealZeros.lean`, `.../RankOneCorrectionLagrangeRadicalCharpoly.lean`, `.../RankOneCorrectionWeightedSymmetry.lean` | §1.2, Theorem A |
| `sourceLagrangePolynomial`, charpoly factorization | `q3.lean.aristotle/Q3/Proofs/RouteB/RankOneCorrectionLagrangePolynomial.lean` | §2.2 |
| `ZerosRealOn` | `q3.lean.aristotle/Q3/Proofs/RouteB/ZeroEscapeLogic.lean:13` | §1 |
| Source displacement identity and `β` | `.../CCMFiniteWeilSourceCommutator.lean`, `.../CCMFiniteWeilShiftedRankOne.lean:103,136` | §1.3 |
| CCM Thm 5.10 verbatim card | `docs/routeB_bus/litreview/CCM_ZST_USAGE_CARDS.md`, `docs/routeB_bus/imports/THM510_ZETA_SPECTRAL_TRIPLES_2026-07-31.md` | §1.1 |
| Probe 12 + ERRATUM + S9 | `docs/routeB_bus/phase5_codex/out/xi_row_zeros.md`; `docs/Progress_Log.md` 2026-09-04 entries | §3, §5 |
| `λ₂` of the even block, five cells | `docs/routeB_bus/phase5_codex/out/odd_gram.md` | §5.2 |

`./ask.sh` was used for `sourceLagrangePolynomial`, `ZerosRealOn`, `rankOneCorrection`,
`ccmEtaFinite`, `proposition59CCMTransform`. No new object was created; nothing outside the one
report path was written.

---

## 1. Output (1) — the exact source predicate, and why it is not stronger

### 1.1 What Theorem 5.10 literally says

Verbatim from the pinned card (`CCM_ZST_USAGE_CARDS.md`, arXiv:2511.22755v1 p. 23, e-print
SHA-256 `96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a`):

> "Let `ε_N` be the smallest eigenvalue of `QW_λ^N` assumed simple and `ξ` the corresponding
> eigenvector assumed even, normalized by `δ_N(ξ) = 1`.
> (i) The operator `D_log^{(λ,N)}` is selfadjoint in the direct sum `E'_N ⊕ E_N^⊥` **where on the
> subspace `E'_N = E_N/ℂξ` the inner product is given by the restriction of the quadratic form
> `QW_λ^N − ε_N⟨·|·⟩`.**
> (ii) `det_reg(D_log^{(λ,N)} − z) = −i λ^{−iz} ξ̂(z)`.
> (iii) `ξ̂` is entire, all its zeros are on the real line and coincide with the spectrum of
> `D_log^{(λ,N)}`."

The bolded clause is the whole story. The metric is **not** an independently given structure: it
is manufactured from the very form whose bottom eigenvector is the object to be identified.

### 1.2 The project's faithful transcription of that predicate

The project transcribes it exactly, as the hypothesis bundle of
`sourceLagrangePolynomial_complex_zerosRealOn_of_radical_nonneg`
(`RankOneCorrectionLagrangeRealZeros.lean:41`), instantiated at
`T := ccmShiftedWeilMatFinite m N ε = K_m − ε·I`, `D := ccmModeDiagFinite N = diag(λ)`,
`η := ccmEtaFinite N ≡ 1`, `β := ccmBetaFinite m N`:

```
hT      : Tᵀ = T
hpos    : ∀ x, 0 ≤ xᵀ T x                       (PSD — from the bottom Rayleigh bound)
hker1   : dim ker T = 1                          (from the simple eigenspace)
hTxi    : T v = 0                                (v spans that kernel)
hcomm   : T D − D T = −β ηᵀ + η βᵀ               (displacement rank 2)
hTDxi   : T (D v) = −β
hnorm   : η · v = 1
```

and the conclusion is `ZerosRealOn Set.univ (Q_v ⊗ ℂ)` for the source Lagrange polynomial `Q_v`
of §2.2. The mechanism, in the project's own files, is: `A_v := D − (Dv)ηᵀ`
(`rankOneCorrection`, `RankOneCorrectionWeightedSymmetry.lean:9`) is `T`-self-adjoint, it kills
`v`, it descends to `(ℝ^n)/rad(T)` where `T` is a genuine inner product, and
`sourceLagrangePolynomial_eq_signed_radical_quotient_charpoly` identifies `Q_v` with `±` the
characteristic polynomial of that descended self-adjoint operator. This is exactly Thm 5.10(i)+(ii).

So the **candidate source predicate on an arbitrary center-normalized even row `v`** is

> **SRC(v):** `∃ T ∈ Sym_n(ℝ)` with `T ⪰ 0`, `dim ker T = 1`, `T v = 0`, and
> `[T, D] = −β ηᵀ + η βᵀ` where `β := −T D v`.

(`hTDxi` is then true by definition of `β`, and the compatibility `β·v = 0` is automatic:
`β·v = −(Dv)ᵀ T v = 0` by symmetry of `T` and `T v = 0`. No hidden extra condition.)

SRC is stated in the project's objects, mentions **only** `v`, the fixed node diagonal `D` and an
existentially quantified `T`. It never mentions the ground row, `K_m`, `ε`, or any distance.
It is therefore *formally* independently checkable. That is the good news and it is the end of it.

### 1.3 Theorem A — SRC collapses onto `ZerosRealOn`

> **Theorem A.** Let `n = 2N+1`, `D = diag(−N, …, N)`, `η ≡ 1`, and let `v ∈ ℝ^n` satisfy
> `v_0 ≠ 0` and `η·v ≠ 0`; normalize `η·v = 1`. Put `A_v := D − (Dv)ηᵀ` and let
> `Q_v(X) := Σ_k v_k ∏_{j≠k}(λ_j − X)` be the source Lagrange polynomial. Then
>
> **(a) SRC(v)** ⟺ **(b) `A_v` is diagonalizable over `ℝ`** ⟺ **(c) `Q_v` has `2N` real roots
> and `A_v` is semisimple.** In particular, whenever `Q_v` has `2N` **distinct** real roots,
>
> ```
>            SRC(v)  ⟺  ZerosRealOn ℂ (Q_v ⊗ ℂ).
> ```

*Proof.* Degrees and the zero eigenvalue first. The coefficient of `X^{n−1}` in `Q_v` is
`(−1)^{n−1}(η·v) = (−1)^{n−1} ≠ 0`, so `deg Q_v = n − 1 = 2N` exactly (this is why the source
insists on `δ_N(ξ)=1`). Because the nodes are the integers, `Q_v(0) = v_0 ∏_{j≠0} j ≠ 0`. By
`sourceLagrangePolynomial_charpoly_factor` (`RankOneCorrectionLagrangePolynomial.lean:48`),
`charpoly(A_v) = ± X · Q_v(X)`; hence `0` is an eigenvalue of `A_v` of algebraic multiplicity
exactly `1`, with eigenvector `v` (`rankOneCorrection_kills_vector`, uses `η·v = 1`), and the
remaining `2N` eigenvalues are the roots of `Q_v`.

(a) ⇒ (b) is the project's own chain: `hpos`+`hker1` make `T` an inner product on
`(ℝ^n)/ker T`, `A_v` descends and is self-adjoint there, so it is `ℝ`-diagonalizable on the
quotient; together with the eigenvector `v` in the kernel direction it is `ℝ`-diagonalizable on
`ℝ^n`.

(b) ⇒ (a) — this is the direction that kills the route. Write `A_v = S Λ S^{-1}` with `Λ` real
diagonal, `Λ_{00} = 0`, `S e_0 = v`. For a real diagonal `g = (g_0, …, g_{n−1})` set

```
        T := S^{-T} diag(g) S^{-1}.
```

`T` is symmetric; `Sᵀ T S = diag(g)` commutes with `Λ` (any diagonal does), which is precisely
`T A_v = A_vᵀ T`. Choose `g_0 = 0` and `g_j > 0` for `j ≥ 1`: then `T ⪰ 0` and
`ker T = span{S e_0} = span{v}`, one-dimensional. Finally expand `T A_v = A_vᵀ T` with
`A_v = D − (Dv)ηᵀ` and `Dᵀ = D`:

```
   T D − T(Dv)ηᵀ = D T − η (Dv)ᵀ T  ⇒  [T, D] = T(Dv)ηᵀ − η (T Dv)ᵀ = −β ηᵀ + η βᵀ,
   β := −T (D v),
```

which is `hcomm` and `hTDxi` simultaneously. So SRC(v) holds. ∎

**Reading.** The `g_j > 0` are *free*. The displacement identity, which looks like a strong
source constraint, is a **consequence** of `T`-self-adjointness, not an extra hypothesis. So
Theorem 5.10's "self-adjoint characteristic determinant with a modified inner product" is the
classical statement *"a real matrix is self-adjoint for some positive definite form iff it is
`ℝ`-diagonalizable"*, dressed in source clothing. It supplies **no** predicate stronger than
`ZerosRealOn` + semisimplicity, and for rows with simple real roots it supplies nothing at all.

### 1.4 The two genuinely stronger candidates, and their fates

| Candidate | Statement in project objects | Fate |
|---|---|---|
| **Strict interlacing** | the `2N` roots of `Q_v` separate the `2N+1` nodes `−N…N` | **FALSE for the ground row.** Interlacing ⟺ all `v_n` of one sign (`Φ_v(s) = Σ v_n/(n−s)` is then strictly monotone between poles). Probe 12's committed sign table gives the ground row **5 / 9 / 20 sign changes** at `m = 13 / 23 / 43` (`xi_row_zeros.md`, line "sign flips: ground […]"). Also directly visible in the zero list: at `m=13` the transform has zeros at `s = ±Lγ_j/2π` up to `γ ≈ 43.9`, i.e. `|s| ≈ 17.9 > N = 13`, so roots leave the node interval. |
| **Positive norming data** | residues of `1/Φ_v` at its poles all of one sign, i.e. `Φ_v` (up to sign) Herglotz with poles at the nodes | Same object as interlacing; **FALSE for the ground row** for the same reason. In the *modified* metric the norming constants are positive by construction (the `g_j` of Theorem A), which is exactly why they carry no information. |
| **Pinned metric** | `SRC_pinned(v)`: `∃ ε`, `T = K_m − ε I` PSD with `ker T = span{v}` | **Circular.** It says "`v` is the simple even bottom eigenvector of `K_m`", i.e. `v = x_m`. Then `ω_m(ε_m) = ‖R(x_m − y_m)‖` identically — the modulus *is* the unknown, the exact failure mode named in the verdict's STRONGEST ATTACK ("`admissible = real-rooted rows in the same component as the ground row` is useless unless 'same component' is independently decidable"). Forbidden. |

**Answer to output (1).** Theorem 5.10 gives the ground row the property "its `P59`/Lagrange
numerator is the characteristic polynomial of an operator self-adjoint in a metric built from
`QW − ε`". Written as a predicate on an arbitrary center-normalized even row it is `SRC(v)`
above; it **is** checkable independently of knowing the eigenvector, and it is **exactly**
`ZerosRealOn(Q_v)` + semisimplicity (Theorem A). Not simplicity of zeros, not interlacing, not
positive norming constants in any fixed metric — the last two are false for the ground row.

---

## 2. Output (2) — the exact P59/Lagrange numerator of the Xi-sample row, and why it fails

### 2.1 The transform

For a FULL even row `v` on `[−N, N]`, `L = log m` (`ccmL`), the project's transform is
`proposition59CCMTransform L N v` with the source's pole ordering "mode `n` ↦ pole `−n`"
(`Proposition59GroundLagrangeZeroSetBridge.lean:97-110`). Off the lattice
(`proposition59RawTransform_eq_paper_formula`):

```
        F_v(z) = L^(−1/2) · 2 sin(Lz/2) · Σ_{n=−N}^{N}  v_n / (z − 2πn/L)          (evenness of v)
        F_v(2πj/L) = √L · (−1)^j · v_j                      for every |j| ≤ N.
```

With the locked coordinate `s = −Lz/(2π)` (`proposition59_denominator_coordinate`) and
`P(X) := ∏_{j=−N}^{N}(j − X)`,

```
        F_v(z) = (2/√L) · sin(Lz/2) · (L/2π) · Q_v(s) / P(s),
        Q_v(X) = Σ_{k=−N}^{N} v_k ∏_{j≠k}(j − X)  =  sourceLagrangePolynomial (λ = id) v,
        deg Q_v = 2N.
```

Off the lattice, `zeros(F_v) = zeros(Q_v)` in the `s` variable. This is the polynomial the whole
question is about.

### 2.2 The Xi-sample row and its numerator

```
        y_{m,0} = 1,      y_{m,n} = (−1)^n · centeredXi(2πn/L) / centeredXi(0),   |n| ≤ N = m,
```
in FULL ratios (EVEN-coordinate row `= √2 y_{m,n}` for `n ≥ 1`; the sign `(−1)^n` is present so
that `F_{y_m}(2πj/L) = √L · Ξ(2πj/L)/Ξ(0)`, i.e. the transform interpolates the `Ξ` samples on
the whole carrier). Its numerator is

```
   Q_{y_m}(X) = Σ_{k=−N}^{N} (−1)^k (Ξ(2πk/L)/Ξ(0)) · ∏_{j≠k} (j − X),      deg = 2N = 2m.
```

The residual it is measured against (verdict §2.1) is
`𝓡_m(v)_n = (K_m v)_n − v_n (K_m v)_0`, with `R_m 𝓡_m(y_m)` the odd-sector vector of the
convention card.

### 2.3 Why it fails the predicate

Probe 12 (observer, by hand; `phase5_codex/out/xi_row_zeros.md`, and the 2026-09-04
Progress_Log entry plus its ERRATUM):

| `m = N` | `deg Q = 2N` | ground non-real | Xi-row non-real | fraction |
|---:|---:|---:|---:|---:|
| 13 | 26 | 0 | **16** | 0.615 |
| 23 | 46 | 0 | **28** | 0.609 |
| 43 | 86 | 0 | **50** | 0.581 |

and the ERRATUM confirms one of them independently, by Newton on `F_y` rather than by
`acb_poly.roots`: `z = −18.8595 + 24.6602 i`, `|F_y(z)| = 0` (the earlier `roots()` output was
accurate to only `10^{−8}` and was retracted; the non-real zeros survived that retraction).

Hence `Q_{y_m}` is **not hyperbolic**, so by Theorem A **no** PSD `T` exists for `y_m`: the
Xi-sample row is not source-admissible, and not marginally so — roughly **60 % of its zeros are
non-real, stably across the three cells**. `y_m` is deep outside the cone, not near its boundary.

Two consequences, both load-bearing:

* the verdict's Q2 line `xi_row_transform_real_zero_status: UNKNOWN_NOT_IMPLIED_BY_RH` is now
  resolved in the **negative** — it is FALSE, not unknown (this is Probe 12's answer, obtained
  before the verdict; `P_XI_ROW_TRANSFORM_REAL_ZEROS 0.50 REFUTED`);
* `ω_m` compares admissible rows to a row that is itself inadmissible, so no continuity or
  perturbation argument can be run "from `y_m` outward". Whatever bounds `ω_m` must bound the
  cone around `x_m` and then transport across a Θ(1)-fraction-of-zeros discontinuity in the
  predicate. See §5.3.

---

## 3. Output (3) — the Robin-cosine plant in the project's objects: **it does not instantiate**

The plant (verdict §3.1) is, for `h > 0`, `a > 0`,
`F_h(z) = cos(πz/h)`, `G_{h,a}(z) = cos(πz/h) − a(πz/h) sin(πz/h)`, both even, real entire, type
`π/h`, value `1` at `0`, both with only real zeros (`G` is the characteristic function of the
nonnegative self-adjoint Robin problem `−u'' = λu`, `u'(0)=0`, `u'(1)+a^{-1}u(1)=0`), and
`F_h(nh) = G_{h,a}(nh) = (−1)^n` for all `n ∈ ℤ`, yet `F ≠ G`.

**Match to the project.** The P59 Nyquist spacing is `h = 2π/L`, so `πz/h = Lz/2` and the plant's
cosine is built on the *same* argument as the P59 sine numerator
`proposition59Numerator L z = 2 sin(Lz/2)`. The plant's node values are exactly the `(−1)^n`
pattern of `proposition59PoleKernel_at_lattice_sign`.

**Row-level verdict — the plant collapses to one row.** By §2.1,
`F_v(2πj/L) = √L (−1)^j v_j`, so a row is *determined* by the transform's lattice values. `F_h`
and `G_{h,a}` have the same lattice values, hence they define **the same** center-normalized even
source row, namely the constant row

```
        v^{Robin}_n ≡ 1        (n ∈ [−N, N]),     Q_{v^Robin}(X) = Σ_k ∏_{j≠k}(j − X) = ±P′(X).
```

Moreover the difference `G_{h,a} − F_h = −a(Lz/2)·sin(Lz/2)` vanishes at every carrier lattice
point, and the finite P59 family contains **no** nonzero element vanishing on the whole carrier
(again by `proposition59PoleKernel_at_lattice_sign`: `F_v ≡ 0` on the carrier forces `v = 0`);
the extra factor `z` is not in the span of the finite pole kernels. So the plant's second branch
is not a P59 transform of any finite row at all.

**What this does and does not kill.**
* It kills, correctly and finally, the *function-level* rigidity shape "even + real zeros + equal
  type + agreement on the full Nyquist lattice ⇒ same entire function". That shape is dead
  (`KILL_GENERIC_REALZERO_LATTICE_RIGIDITY`), and no argument here revives it.
* It is **inert against `ω_m`**, which is a distance between *rows*, and the plant supplies one
  row, not two. Formally a point FOR selectivity.
* But the point is worthless, and the reason is the finding of §1.3. Under `SRC`, the plant's row
  is itself **admissible**: `Q_{v^Robin} = ±P′` is real-rooted with simple roots strictly
  interlacing the integers (Rolle), so `SRC(v^Robin)` holds by Theorem A. The predicate does not
  separate the plant's row from the ground row at all; what excludes `v^Robin` is only its
  Θ(1) residual `‖R 𝓡_m(v^Robin)‖`. **All separating power is in the residual, none in the
  predicate.** That is the sentence the verdict's STRONGEST ATTACK asked for, with the sign
  reversed from what it hoped: the "source predicate unavailable to the plant" does not exist,
  because the plant's row satisfies it.

The other two plants behave the same way and need no re-derivation: the `2×2` collapsed plant
(`K_ε = diag(0,ε)`, `x = (1,0)`, `y = (1,1)`) shows minimality without a modulus is dead; the
confluent-Hermite plant shows same-node Loewner structure forces no spectral profile. Neither is
a row on the CCM lattice; both are already `MATHEMATICALLY_DEAD` verdicts and are not reopened.

---

## 4. Output (4) — a noncircular selector modulus `ω_m(ε)`

Fix `m`, `N = m`, `L = log m`, `D = diag(−N…N)`, `η ≡ 1`, `K_m = ccmWeilMatFinite m N`,
`R = diag(1/n)` (`R_0 = 0`).

```
  Admissible class (no reference to x_m, to y_m, or to any distance):

     A_m(ε) := { v : [−N,N] → ℝ  |  (N1) v_{−n} = v_n              (even)
                                     (N2) v_0 = 1                   (center-normalized)
                                     (N3) η·v ≠ 0                   (degree-exactness of Q_v)
                                     (N4) ‖ R 𝓡_m(v) ‖₂ ≤ ε ,   𝓡_m(v)_n = (K_m v)_n − v_n (K_m v)_0
                                     (N5) SRC(v)  —  §1.2                                   }

  Selector modulus:

     ω_m(ε) := sup { ‖ R (v − y_m) ‖₂  :  v ∈ A_m(ε) } .

  Target (SEL):

     ω_m(ε_m) = O( (log m)^{−2} ),      ε_m = C m^A exp( −π² m / (2 log m) ) .
```

**Noncircularity audit against the verdict's four prohibitions.**

| Forbidden ingredient | Present? | Why not |
|---|---|---|
| `‖R(v − y_m)‖` small as an assumption | no | it is the *objective*, never a constraint; `y_m` occurs only inside the `sup` |
| absolute / relative / odd-sector complement floor | no | (N4) is a forward residual, no inverse, no `1/λ₂`, no `1/δ_odd` |
| the desired locally uniform convergence | no | (N1)–(N5) are finite algebraic/semialgebraic conditions on `v` at fixed `m` |
| bounded curvature as a selector | no | curvature does not appear; per verdict §3.4 it may re-enter only as a normality supplier elsewhere |
| the ground row / "same component as `x_m`" | no | `SRC` quantifies `T` existentially; `K_m` enters only through (N4) |

By Theorem A, (N5) may be replaced, with no loss and no gain, by the *fully explicit* condition

```
     (N5′)   Q_v(X) = Σ_k v_k ∏_{j≠k}(j − X)  has 2N real roots (and A_v is semisimple),
```

which is decidable by a Sturm sequence or by the signature of the Hermite quadratic form —
no root finding, no eigenvector, no `T`. **This is the honest form of `ω_m`, and it is the form
in which the route dies:** `ω_m` is the `R`-radius of the hyperbolicity region of the linear map
`v ↦ Q_v`, intersected with a residual slab, measured from a point outside that region.

**Structural inequality (free, and worth stating).** The ground row `x_m` satisfies (N1)–(N5)
with residual `0`, so `x_m ∈ A_m(ε)` for every `ε ≥ 0` and

```
     ω_m(ε)  ≥  ‖ R (x_m − y_m) ‖₂     for all ε ≥ 0.
```

Hence (SEL) ⇒ the Input-A target, as intended — but also: **(SEL) is strictly harder than the
target**, since any proof of it must in particular prove `‖R(x_m − y_m)‖ = O(log^{−2} m)` and, on
top of that, control every other admissible row. The representation is not a reduction of the
problem; it is the problem plus a hyperbolicity-radius theorem.

---

## 5. Why the cone cannot be the selector — the three measurements

### 5.1 The cone is open, hence dimension-preserving

`v ↦ Q_v` is **linear** and `deg Q_v = 2N` exactly on (N2)+(N3). If `Q_{x_m}` has `2N` **simple**
real roots — Probe 12 reports `NONREAL = 0` on all three cells; simplicity is the one bit not
yet certified, see §6 — then by continuity of simple roots there is `r_m > 0` with

```
     ‖v − x_m‖ < r_m   ⟹   Q_v has 2N simple real roots   ⟹   SRC(v).
```

So `A_m(ε) ⊇ B(x_m, r_m) ∩ {slab (N4)} ∩ {(N1),(N2)}`, and

```
     ω_m(ε) ≥ R-radius of that ball  ≥  r_m / N .
```

The real-rooted set is a **full-dimensional** semialgebraic region, not a variety: it can shrink a
near-null set by *size*, never by *dimension*. The verdict's own §3.4 argument against curvature
("its level set has codimension at most one; it cannot identify one row inside a high-dimensional
near-null space") applies here with the codimension improved from one to **zero**.

### 5.2 The residual slab at the registered scale is astronomically wide

The registered residual budget is `ε_m = C m^A exp(−π² m/(2 log m))`, i.e.
`log₁₀ ε_m ≈ −2.1433 · m/log m` up to the polynomial factor. Against the committed second
eigenvalue of the even block (`phase5_codex/out/odd_gram.md`, column `lambda2`, five cells,
`DIAGNOSTIC_NEVER_A_PROOF`):

| `m = N` | `ε_m` (leading scale) | `λ₂` (committed) | `ε_m / λ₂` |
|---:|---:|---:|---:|
| 13 | `≈ 1.4·10^{−11}` | `2.842·10^{−25}` | `≈ 10^{14}` |
| 23 | `≈ 1.9·10^{−16}` | `1.251·10^{−45}` | `≈ 10^{29}` |
| 43 | `≈ 3.2·10^{−25}` | `7.605·10^{−84}` | `≈ 10^{59}` |
| 83 | `≈ 5.6·10^{−41}` | `1.256·10^{−154}` | `≈ 10^{114}` |

The polynomial prefactor `C m^A` cannot touch a gap that grows by ~30 orders per cell. So the
slab (N4) is, in the bottom eigendirections, effectively **the whole space**: moving from `x_m`
along the second even eigenvector `u₂` by `t` costs residual `≈ |λ₂ − λ₁|·t·‖R u₂‖`, so `t` may
run to `~10^{14} … 10^{114}` before (N4) bites. This is the same collapse that killed H1/H2/H6,
restated in the coordinates where it matters for `ω_m`.

Combining §5.1 and §5.2: near `x_m`, `A_m(ε_m)` **is** the hyperbolicity region — the residual
constraint is inactive there. Therefore

```
     ω_m(ε_m)  ≈  R-diameter of the hyperbolicity component of x_m   (locally, in the free
                  directions with λ_j ≤ ε_m),
```

and (SEL) is *equivalent*, at this scale, to the statement `r_m = O(log^{−2} m)` — a brand-new
analytic theorem about the hyperbolicity radius of the Lagrange map at the CCM ground row, for
which no source supplier exists in CCM, in Groskin, or in the project. A "selector" that reduces
to proving a sharper unknown is not a selector.

### 5.3 The Xi row sits on the wrong side, uniformly in `m`

`y_m ∉ A_m(ε)` for any `ε` (§2.3, ~60 % non-real zeros on all three cells). So `ω_m` measures a
distance from an inadmissible point to a full-dimensional set that does not contain it, with the
known interior point `x_m` at distance `‖R(x_m − y_m)‖ ~ 1/log² m` (Probe 9 scale) and with
`r_m ≤ ‖x_m − y_m‖` (the ball cannot cross the non-hyperbolic point). The upper bound on `r_m` is
of the *right order* but is not a theorem, and no lower bound on `r_m` is available either. The
whole content of (SEL) has migrated into a quantity that no source result addresses.

---

## 6. Output (5) — interval-test design for the `R`-diameter of `A_m(ε_m)`

Purpose: convert §5.1's `ω_m ≥ r_m/N` into either a certified **lower** bound on the `R`-diameter
(the judge's falsifier, KILL) or a certified **upper** bound (SUPPORT). Design only; no run was
performed and none is authorized by this task.

**D0. Precision and comparison discipline (ERRATUM lesson).** All quantities as `arb`/`acb`
balls; every comparison a *containment* predicate, never a strict threshold. Working precision
`dps ≥ 3 · 2N · log₁₀(max|coeff Q_v|)`; the ground numerator coefficients already reach `10^{29}`
at `m = 13`, so `dps ≥ 240 / 320 / 480 / 900` at `m = 13 / 23 / 43 / 83 / 163`, matching the
existing precommit ladder. **No `acb_poly.roots()` anywhere in the decision path** — it was the
source of the retracted Probe-12 point 4.

**D1. Hyperbolicity certificate without root finding.** For a row `v` with interval coefficients,
build `Q_v` (linear in `v`, so interval coefficients are exact rational combinations) and form the
**Hermite quadratic form** `H(Q_v)` — the `2N × 2N` Hankel matrix of Newton power sums of the
roots, computed from the coefficients by the Newton identities. Certify by interval `LDLᵀ`:
`H ≻ 0` ⟹ all `2N` roots real and simple ⟹ `SRC(v)` (Theorem A). A certified negative pivot
⟹ at least one non-real pair ⟹ `¬SRC(v)`. Cost `O(N³)` per row, deterministic, no root
localization. (Sturm sequence on `Q_v` is the equivalent fallback; Hermite is preferred because
its output is a signature, i.e. a *count*, which the diameter search needs.)

**D2. Residual certificate.** Evaluate `𝓡_m(v)_n = (K_m v)_n − v_n (K_m v)_0` **exactly** on the
interval row (not the linearization), then `‖R 𝓡_m(v)‖₂`. Admissible iff the upper endpoint of
that ball is `≤` the lower endpoint of the `ε_m` ball. `ε_m`'s unknown `C, m^A`: run the test at
three declared budgets `ε ∈ {10^{−2.14 m/L}, 10^{−1 · m/L}, λ₂ · 10^{3}}` and report the diameter
as a function of the budget; a kill at the *smallest* budget is the strongest.

**D3. Free-direction frame.** Compute certified enclosures of the bottom even eigenpairs
`(λ₁, x_m), (λ₂, u₂), …, (λ_J, u_J)` with `J := max{ j : λ_j ≤ ε_m }` (only `λ₁, λ₂` are currently
committed; `λ₃ …` is the one genuinely new number this design requires). Search directions:
`u₂, …, u_J`, plus two adversarial directions — `d_Ξ := y_m − x_m` (towards the inadmissible Xi
row) and `d_R := v^{Robin} − x_m` (towards the plant's row, §3), both re-evenized and
re-center-normalized.

**D4. The diameter search.** For each direction `d`, bisect on `t > 0` over
`v(t) := renorm(x_m + t d)` to find the certified `t*` = last `t` passing D1 **and** D2. Report
`ρ(d) := ‖R(v(t*) − x_m)‖₂` and `‖R(v(t*) − y_m)‖₂`.

* **KILL** (issue the falsifier) if some direction yields, on `m = 13, 23, 43, 83` with a
  non-decreasing trend, `‖R(v(t*) − y_m)‖₂ ≥ c > 0` with `c` independent of `m`. That row is
  exactly the verdict's falsifier: center-normalized, even, at Xi residual scale, with the same
  real-zero/characteristic property as the ground row, at `R`-distance bounded below.
* **SUPPORT** if `max_d ρ(d) · (1 + o(1)) ≤ C / log² m` with `C` stable over the four cells.
  Support only; a cofinal theorem still requires an analytic hyperbolicity-radius bound.

**D5. Mandatory plant controls (each run must print all four).**
1. *Positive control:* `v^{Robin} ≡ 1` must be certified hyperbolic by D1 (`Q = ±P′`, simple,
   interlacing). If D1 rejects it, D1 is broken.
2. *Negative control:* `y_m` must be certified NON-hyperbolic by D1, reproducing the counts
   `16/26`, `28/46`, `50/86`. If D1 accepts it, D1 is broken.
3. *Residual-scale control:* the `2×2` collapsed plant (`K_ε = diag(0,ε)`, `x = (1,0)`,
   `y = (1,1)`) must return "residual `ε`, distance `1`" through the D2 code path.
4. *Inapplicability control:* the Robin plant's second branch `G_{h,a}` must be **rejected as
   not a row** by the harness (§3: no finite P59 element vanishes on the full carrier). It must
   never be entered as an input row; a harness that silently accepts it is measuring the wrong
   object.

**D6. What the test cannot do.** Any outcome is `FINITE_CELL` and `DIAGNOSTIC_NEVER_A_PROOF`. A
SUPPORT outcome does not supply (SEL); it only fails to refute it. Only a KILL outcome is
decisive, and §5.1 predicts KILL unless `r_m` collapses at exactly the `log^{−2} m` rate.

---

## 7. Verdict, first failure point, and what is honestly not established

```
CODE: P59_REALZERO_CONE_NOT_SELECTIVE
```

**The predicate, in one display** (the answer to "what is the strongest thing Theorem 5.10 gives",
with its collapse):

```
   SRC(v):  ∃ T = Tᵀ ⪰ 0,  dim ker T = 1,  T v = 0,  [T, D] = −β ηᵀ + η βᵀ  with β = −T D v

                      ⟺   D − (Dv)ηᵀ  is ℝ-diagonalizable
                      ⟺   Q_v(X) = Σ_k v_k ∏_{j≠k}(j − X)  has 2N real semisimple roots
                      ⟺   ZerosRealOn(Q_v)                    (when the roots are distinct)
```

**Plant verdict, in one sentence.** The Robin-cosine plant does not instantiate as two rows on
the CCM lattice — both branches carry the same lattice values and therefore the same
center-normalized even row `v ≡ 1`, whose second branch is not even a finite P59 transform — so
the plant is inert against `ω_m`; but that row *satisfies* `SRC` (its numerator is `±P′`, real
and interlacing), which shows the predicate never separated it from the ground row in the first
place and that all separating power lies in the residual.

**First failure point, named exactly.** Theorem 5.10 **(i)**, the clause *"where on the subspace
`E'_N = E_N/ℂξ` the inner product is given by the restriction of the quadratic form
`QW_λ^N − ε_N⟨·|·⟩`"*. The metric is manufactured from the operator. Detach it — the only way to
get a predicate on an arbitrary row — and Theorem A shows self-adjointness becomes free, i.e.
equivalent to real-rootedness; keep it pinned and the predicate becomes "`v` is the simple even
bottom eigenvector of `QW`", the forbidden circularity. There is no third reading. Consequently
the "source-specific real-zero component" of the verdict's `NEW_ATOM` is not source-specific: it
is the bare hyperbolicity cone of the Lagrange map, an **open** set, which cannot reduce the
dimension of a near-null slab that exceeds `λ₂` by 14–114 orders on the committed cells.

**What is NOT established (stated so it is not read as more than it is).**

1. **No falsifier row was exhibited.** The verdict's kill trigger has two conjuncts; the first
   ("the source theorem supplies only `ZerosRealOn`") is now a *theorem* (Theorem A), strictly
   stronger than the verdict anticipated. The second ("an interval test finds a second source row
   at Xi residual scale with real-rooted transform and non-vanishing `R`-distance") was **not**
   executed — numerical runs are forbidden for this task. The kill is issued on the first
   conjunct plus the openness argument of §5.1, which shows the second conjunct's *existence* at
   radius `r_m` but supplies no `Θ(1)` lower bound on `r_m`. **This is the residual risk of the
   code.** If a later interval run (§6) certifies `r_m = O(log^{−2} m)`, (SEL) is not refuted —
   but even then it is not a selector, because §5.1 shows it would have become a new analytic
   theorem about the hyperbolicity radius, not a consequence of the source.
2. **Simplicity of the ground numerator's roots** is used in §5.1 and is not certified: Probe 12
   reports `NONREAL = 0`, not "simple". D1 of §6 certifies it as a by-product (`H ≻ 0`).
3. `ε_m`'s constants `C, A` are unknown; §5.2 compares leading scales only. The conclusion is
   robust because the gap grows ~30 orders per cell, but the table is a scale statement, not a
   bound.
4. All numerics cited are the observer's committed five-cell diagnostics
   (`xi_row_zeros.md`, `odd_gram.md`, `lattice_equation.md`) — `FINITE_CELL`,
   `DIAGNOSTIC_NEVER_A_PROOF`, no cofinal claim.

**Where the front should go (not a decision — the judge's ranking already names it).** The
verdict's route 2, `P59_POLARIZED_ZERO_SIDE_VECTOR_RESIDUAL`, is untouched by this report: it does
not use a selector and would prove the repaired residual rate `(Q1-stretch)` directly through the
exact finite Guinand–Weil dictionary. Independently, the observer's zero-side observation (Probe
12 ERRATUM + S9: `F_ground(γ_j) = C_j λ₁` with `C₁·L → ≈ 205` over five cells, and the certified
zero-shift `~10^{−26}` at `m = 13`) is a *zeros* statement, not a *rows* statement, and the
Robin-cosine plant does not touch it either — `cos` and the Robin function have different zeros.
That is the `ZEROPIN` draft, and nothing here weakens it.

```yaml
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
FILES_WRITTEN: [docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT.md]
COMMIT_PERFORMED: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```
