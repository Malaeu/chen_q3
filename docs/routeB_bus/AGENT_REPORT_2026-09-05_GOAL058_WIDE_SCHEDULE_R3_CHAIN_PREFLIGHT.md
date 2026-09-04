# AGENT REPORT — GOAL 058 / Route B — R3 "wide schedule" chain preflight

**Date:** 2026-09-05 · **Mode:** READ-ONLY paper-and-Lean preflight · **Branch:** `rh_clean`
**Scope:** type the R3 chain (`R3_WIDE_SCHEDULE_PROJECTIVE_RATE`) step by step from the CCM
paper and the Lean tree. No Lean edit, no numerical run, no commit. Every number below is
quoted from an existing record; nothing was recomputed except the two closed-form
comparisons in §5 (D2), which are pure arithmetic on published constants.

`DIAGNOSTIC_NEVER_A_PROOF` · `PX_RH_CLAIM: NOT_MADE` · `RH_CLAIM: false`

---

## 0. Sources actually read

| object | locator |
|---|---|
| CCM paper | `docs/routeB_bus/litreview/pdfs/2511.22755.pdf` (34 pp.), text layer read for §3.1, §3.2, §5.3, §7, §8 |
| CCM usage cards | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/CCM_ZST_USAGE_CARDS.md` |
| Weil-positivity object card | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/WEIL_POSITIVITY_OBJECT_CARD_2026-09-04.md` (read in full) |
| FULLCHAIN verdict | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FULL_CLOSURE_CHAIN_2026-09-04.md` |
| NEWMECH verdict | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_NEW_MECHANISM_FOR_CURVATURE_WALL_2026-09-03.md` |
| Lean roof | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean` |
| Lean schedule instantiation | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/D0CanonicalApproximation.lean` |
| Lean terminal consumer | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/Goal058DirectGroundZeroEscape.lean` |
| Lean guard carrier | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/SoftL2Round13Integration.lean` |
| measured numbers | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/Progress_Log.md` (Probe 11, Probe 12, Probe 22 blocks, 2026-09-04/05) |
| trial-jet crosswalk | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_FINITE_PROJECTED_TRIAL_JET_CROSSWALK_PREFLIGHT.md` |

Coordinate crosswalk used throughout: the project's window parameter `m` and CCM's `λ`
are related by `L_m = log m = 2 log λ`, i.e. **`λ_m = √m`, `µ = λ² = m`**
(`D0CanonicalApproximation.lean:23` `logLength = Real.log i.m`, comment at line 44
"`L_m = 2 log lambda_m`"). CCM's Figure 4 abscissa `µ = λ²` is our `m` directly.

---

## 1. What CCM actually PROVES about the bottom of the Weil form

### 1.1 Proved (upper part of the ladder)

| # | statement | locator | type |
|---|---|---|---|
| P1 | `QW_λ` is lower bounded and lower semi-continuous | Prop. 3.3, p. 9 (imported from [4, §2] = Connes–Consani, Enseign. Math. 69 (2023)) | THEOREM (external) |
| P2 | `E = span{V_n}` is a core; `QW_λ(f,f) = liminf_{g_n→f} QW_λ(g_n,g_n)` (3.22) | Prop. 3.4, p. 9 (imported from [4, Prop. 2.3]) | THEOREM (external) |
| P3 | **"the lower bound of `QW_λ` is the limit, when `N → ∞`, of the smallest eigenvalue of the restriction of `QW_λ` to the linear span `E_N` of the functions `V_k` with `|k| ≤ N`"** | Prop. 3.4, immediately after (3.22), p. 9 | THEOREM (corollary of P2) |
| P4 | `A_λ` has discrete lower-bounded spectrum | Thm 3.6, p. 9 | THEOREM |
| P5 | a minimizer exists: `A_λ φ = µ_λ φ`, `µ_λ = inf spec A_λ`; **"we cannot assert that `µ_λ ≥ 0`"**; `λ > λ' ⇒ µ_λ ≤ µ_λ'` (3.27) | Cor. 3.7, p. 11 | THEOREM |
| P6 | **"If the limit when `λ → ∞` of the decreasing function `µ_λ` is equal to 0 then RH holds"** | Cor. 3.8, p. 11 | THEOREM |
| P7 | prolate → Hermite rate `max_{[−λ,λ]}|h_{n,λ} − h_n| ≤ cλ^{−2}` (`n = 0,4`), and the same for the combination `h_λ` vs `h` | Lemma 7.2 (7.7)/(7.8), p. 29 | THEOREM (rests on Meixner–Schäfke Satz 9, Fuchs Thm 1) |
| P8 | Fourier transform of `k_λ` → `Ξ`, uniformly on closed substrips of `|Im z| < 1/2` | Lemma 7.3, pp. 31–32 | THEOREM |
| P9 | determinant / real-zero bridge | Thm 5.10, p. 23 | THEOREM **conditional on** "`ε_N` simple, `ξ` even" stated inside its own head |

### 1.2 NOT in the paper — stated negatively, on purpose

* **There is no upper bound of the form `ε_λ ≤ QW_λ(k_λ,k_λ)/‖k_λ‖²` proved anywhere,
  and no `e^{−cλ²}` rate for `ε_λ`.** What the paper contains is the *prolate* defect rate,
  quoted from Fuchs, for the wrong object:
  > "for `n = 4`, by [8], Theorem 1, one has `1 − χ(λ) ∼ (2^14/3) √2 π^5 e^{−4πλ² + 9 log λ}`"
  > — CCM p. 30, top.
  `1 − χ(λ)` is the *prolate concentration defect* of `PW_λ`, not the Weil bottom. The only
  link between `ε_λ` and `1 − χ(λ)` in the paper is **Figure 4**, a plot of
  `log(ε_λ)` and `log(1 − χ(λ))` against `µ = λ²`, offered in §8 as "indication (2)".
  A picture. Connes' 2026 survey repeats it as an observation, not a theorem
  (`2602.04022` §6: "*The numerical computation … shows that `ε(λ)` tends exponentially fast
  to 0 … a careful analysis reveals a striking similarity (Figure 1)*").
* **There is no lower bound on `ε_N` or `µ_λ` of any kind.** P5 says the opposite in as many
  words: `µ_λ ≥ 0` is not assertable.
* **There is no "`k_λ` is a near-minimizer" theorem.** CCM, p. 28, verbatim:
  > "We refer to [4], Section 3, for … the numerical evidence showing that it gives an
  > approximation of a scalar multiple of `ξ_λ`. **Justifying rigorously this step is the
  > main remaining obstacle to our approach to RH.**"
  and §8, p. 32: the second of "two essential steps still missing".
* **CCM do not assume `λ₁ > 0` anywhere.** Their standing hypothesis is `even simple`
  (Def. 5.3), and Thm 5.10 is applied to the *shifted* form `T := QW_λ^N − ε_N·id`, which is
  `≥ 0` by construction whatever the sign of `ε_N` (proof of Thm 5.10, p. 23). Confirmed
  independently in `WEIL_POSITIVITY_OBJECT_CARD_2026-09-04.md` §4.1.

**Verdict on question (1): the paper contains no bound on `λ_min` in either direction
beyond "it exists and is finite". The `e^{−cλ²}` rate that Route B has been treating as the
size of the bottom belongs to a different operator (`PW_λ`) and reaches `ε_λ` only through
a figure.**

---

## 2. The finite truncation, the "saturation" step, and what the Lean roof demands

### 2.1 Continuum object and monotonicity — proved

The continuum object *is* what R3 needs: `µ_λ = inf spec A_λ` = the bottom of `QW_λ` on the
whole of `L²([λ^{-1}, λ], d*u)`; `E_N` = span of `V_k`, `|k| ≤ N` — exactly the finite
Fourier sector the project calls `K(m,N)`. Since `E_N ⊂ E_{N+1}`, Rayleigh–Ritz gives

```
λ₁(m,N)  non-increasing in N,   λ₁(m,N) ↓ λ₁(m,∞) = µ_{√m}   (CCM Prop. 3.4, P3 above)
```

* Monotonicity: **THEOREM**, elementary from `E_N ⊂ E_{N+1}` (and Lean-ready).
* Convergence `λ₁(m,N) → λ₁(m,∞)`: **THEOREM** (CCM P3), no hypothesis, no RH.
* **A rate — any `N*(m)` making `λ₁(m,N*) ≤ 2 λ₁(m,∞)` — is NOT in CCM and not in the
  cited literature. This is the saturation step and it is NEW-MATH.**

Two further caveats that must not be lost:

1. `µ_λ` is the bottom on the **full** space. The project measures the **even block**;
   `λ₁^even ≥ λ₁^full`. On existing caches the even bottom *is* the full bottom
   (`Progress_Log` 2026-09-04, second-channel check: full-matrix minimum = even `λ₁`
   `7.9e-31, 7.3e-52, 1.0e-90` at `m = 13,23,43`, `N = m`; the odd minimum sits
   `6.409e-28, 1.511e-48, 3.649e-87` above). That is a finite fact, not a theorem.
2. `µ_λ` is **decreasing** in `λ` (CCM (3.27)). This matters in §3c below and is the reason
   a *cofinal* family is not a weakening.

### 2.2 What the Lean consumer requires of a schedule `N(m)` — exact hypothesis names

Read directly, not paraphrased:

* `CanonicalRHRouteSkeleton.lean:34–41` — `structure CanonicalApproximation (Index : Type*)`
  with fields `parent : ℕ → Index`, **`parentCofinal : Prop`**, `parentCofinalProof : parentCofinal`,
  `extract : ℕ → ℕ`, `extractStrictMono : StrictMono extract`. `parentCofinal` is an
  *arbitrary proposition supplied together with its own proof*: at this level cofinality has
  **no arithmetic content whatsoever**.
* `CanonicalRHRouteSkeleton.lean:69–78` — `def sameCofinalGuard` merely *transports*
  `SlotH2a`/`SlotS1` into `SoftSameCofinalSubsequence` (`SoftL2Round13Integration.lean:14–21`,
  same abstract `parentCofinal : Prop` field). It is bookkeeping: it fixes that S2 consumes
  `parent ∘ extract` and nothing else. It imposes **zero** constraint on `m ↦ N`.
* The only place cofinality acquires content is
  `D0CanonicalApproximation.lean:67–69`:
  ```lean
  def PairCofinal {D : CoefficientFamily} (p : ℕ → CentralIndex D) : Prop :=
    Tendsto (fun k => (p k).1.m) atTop atTop ∧
      Tendsto (fun k => (p k).1.N) atTop atTop
  ```
  i.e. **`m → ∞` and `N → ∞`, independently. No relation between them.**
* The terminal consumer `Goal058DirectGroundZeroEscape.lean:27–33`
  `rh_of_real_zero_family_tendsto_centeredXi (F : ℕ → ℂ → ℂ) …` takes an *arbitrary*
  sequence of entire functions. No index type, no schedule.

**Answer to question (2): `N(m) = 6m` and `N(m) = c·m·log m` are both admissible exactly as
written, with a one-line `PairCofinal` proof. Nothing in the Lean tree fixes `N = m`;
a repository-wide grep for a hypothesis binding `i.N` to `i.m` returns nothing.
`N = m` is a production convention of the numerics, and the judge already typed it so:
`SCHEDULE_AUDIT: N_EQUALS_M: ONE_REPRESENTATION_NOT_A_THEOREM`.**

Corollary, and it is the uncomfortable half: since the guard constrains nothing, it also
*supplies* nothing. The judge's own line —
`WIDE_MISSING_SUPPLIER: … sameCofinalGuard bookkeeping alone supplies no spectral rate` —
is confirmed by reading the file. R3's whole content sits in the analytic premise, not in
the schedule.

---

## 3. The epistemic firewall around `ε_∞(m) = R(k_λ)/λ₁(m,∞) ≤ C`

The premise is, written out, a **quantitative lower bound for the Weil bottom**:
`λ₁(m,∞) ≥ R(q_m)/C` with `R(q_m)` the explicit, computable energy of the prolate trial.

### (a) Under ¬RH, does `λ₁(m,∞)` go negative for large `m`?

**Yes — for the full-space bottom, and the chain of citations is complete.**

* Weil's criterion in the localized form: RH ⟺ `( , )|C(a)` positive definite **for every
  `a > 0`**, `C(a) = {φ ∈ C_c^∞(ℝ) : supp φ ⊆ [−a,a]}` — Yoshida 1992, p. 282; and
  Yoshida Thm 2, p. 321 (non-degeneracy for every `a`).
* `λ_a` is continuous in `a` without assuming RH, and `λ_a > 0` for small `a`; hence ¬RH
  ⟹ `λ_a < 0` for some `a` — Suzuki `arXiv:2606.09096` Thm 1.3 (p. 4), Thm 1.4 (p. 5).
* CCM's `µ_λ` **is** that object (`a = (log m)/2`, `λ = √m`), and it is **monotone
  decreasing** in `λ` (CCM (3.27)). So once negative it stays negative: ¬RH ⟹ there is
  `m₀` with `λ₁(m,∞) < 0` for all `m ≥ m₀`.
* Test-function class: `C_c^∞` with support in the window / the core `E` of `QW_λ`. The
  CCM finite even-block form is a Rayleigh–Ritz restriction of the same form on the same
  window, so the *window* matches exactly.

**But the even block does not fall under those theorems without one extra step.**
Yoshida 1992 Prop. 1, p. 285: `T_k` **oddly** positive definite ⟺ RH; `T_k` **evenly**
positive definite ⟺ RH *"with possible exceptions of real zeros"*. CCM live in the even
sector by construction (`γξ = ξ`, Def. 5.3), and so does the project's block. For `ζ` over
`ℚ` the exception is empty (`ζ(s) < 0` on `(0,1)`, classical), but the step must be cited,
not waved through. Second gap in the same direction: at a **fixed** `m`, ¬RH gives
*nothing* — negativity is only guaranteed eventually, and the eventual `m₀` is Yoshida's
open threshold `a₀`, known only to satisfy `a₀ ≥ (log 2)/2` since 1992.

### (b) Under RH, is `λ₁ ≥ c·Q(k_λ)` known or provable?

**No. Nothing of the kind exists, at any rate, at our windows.**

* RH ⟹ positivity, with no rate: Connes `arXiv:2602.04022` §6.4 verbatim — *"RH implies
  that `QW_λ` is strictly positive and that its radical is `{0}`"*. Strict positivity,
  no lower bound.
* The exact unconditional identity on the finite object is Groskin `arXiv:2607.02828`
  Thm 2.5: `⟨v, Q_∞ v⟩ = Σ_{z ∈ Z*_ζ} g_v(z)`. Under RH all `z` are real and every term is
  `≥ 0` — again positivity, no floor.
* The only **quantitative** lower bound in the literature is Bombieri 2000 Thm 12, p. 226:
  `T[F * F(−·)] ≥ (log(1/|I|) − log log(1/|I|) − O(1)) ‖F‖²` — and it holds **only for
  `|I| < log 2`**, because the proof works precisely where the `Λ(n)` sum is empty
  (Bombieri's own sentence at the start of that proof). Our smallest cell is `m = 13`,
  `L = log 13 ≈ 2.565`, i.e. `3.7×` past that boundary, with nine prime powers inside the
  window. Yoshida 1992 Thm 1 (p. 310) and Connes–Consani `2006.13771` Thm 1 stop at the
  same `log 2`. Suzuki Thm 1.4 gives an asymptotic as `a → 0+` with an unquantified
  `µ₁ > 0` and no threshold.
* Order-of-magnitude mismatch, independent of the boundary: Bombieri's bound is of size
  `log(1/|I|)·‖F‖²`, i.e. `O(1)`. The object R3 needs is of size `e^{−4πm}`. Nothing in
  the literature is even the right shape.

Connes' own 2026 verdict on the method that reached `log 2` (`2602.04022` §4.1):
*"it does not provide any conceptual reason for this positivity that would have a chance to
continue to hold when primes are involved."*

### (c) Can R3 avoid an RH-conditional step? — No, and it is worse than "conditional"

Chain the two facts already established:

1. `ε_∞(m) ≤ C` for a cofinal set of `m` ⟹ `λ₁(m,∞) ≥ R(q_m)/C > 0` cofinally.
2. `µ_λ` decreasing in `λ` (CCM (3.27)) ⟹ positivity on a **cofinal** set of `λ` propagates
   *downward* to **all** `λ`.
3. Positivity for all `λ` ⟹ RH (Weil's criterion in the localized form; Yoshida 1992 Thm 2;
   with the even-sector footnote of Prop. 1(2) plus "`ζ` has no real zero in `(0,1)`").

So **the R3 premise implies RH by itself**, through CCM's own monotonicity corollary. The
honest typing is therefore not "R3 has an RH-conditional step" but:

> **R3 relocates the whole of RH into one inequality with an explicit computable right-hand
> side. It does not reduce RH to anything weaker. The cofinal restriction buys nothing,
> because `µ_λ` is monotone: a cofinal family of windows is not a proper sub-family in the
> only direction that matters.**

Is *that* implication ("positivity on a non-exhaustive family ⟹ RH") new? **No, and this is
the one genuinely good news of the preflight**: the project's own litreview already
adjudicated it (`WEIL_POSITIVITY_OBJECT_CARD_2026-09-04.md` §3.1, §3.4). "For all `a`" is
Weil's criterion with the quantifier moved outside — a reformulation, not a strengthening;
the cofinal version follows from monotonicity. What **is** strictly weaker, and what the
card also settles, is positivity at **fixed `N`**: `λ₁(m,N)` only majorizes `λ₁(m,∞)`
(CCM Prop. 3.4), and the generated test family does not exhaust the admissible class
(Groskin Rem. 2.6, explicit non-claim). **The `N → ∞` quantifier cannot be dropped.**

Consequence for R3's design: the schedule `N(m)` must be proved to *reach* saturation,
because a schedule that does not saturate proves a strictly weaker statement that implies
nothing about RH.

---

## 4. The typed chain

Notation: `q_{m,N} = P_N f_λ` (projected prolate trial), `R(q)` its Rayleigh quotient,
`λ₁ ≤ λ₂` the bottom two even eigenvalues of `K(m,N)`, `g = λ₂/λ₁`, `ε = R(q)/λ₁`,
`p = 1 − ⟨ξ,q⟩²`, `F_ground`/`F_trial` the anchored Proposition-59 transforms,
`K` a compact of the open centered critical strip.

| # | step | TYPE | FIRST_FAILURE |
|---|---|---|---|
| **S0** | precommit `N(m) ≥ m`, e.g. `N(m) = 6m` or `⌈c·m log m⌉` | **LEAN-READY** — a definition; `PairCofinal` is a two-line `Tendsto` proof | none |
| **S1** | the path is accepted by `sameCofinalGuard` | **THEOREM (Lean, hole-free)** — `CanonicalRHRouteSkeleton.lean:69`, `#print axioms sameCofinalGuard_s2Sequence` at :219 | the guard is *pure bookkeeping*: `parentCofinal : Prop` carries its own proof, so acceptance conveys no spectral information |
| **S2** | `λ₁(m,N)` non-increasing in `N`, `→ λ₁(m,∞)` | **THEOREM** — CCM Prop. 3.4 corollary, p. 9; monotone half elementary | existence of the limit only |
| **S3** | **saturation rate**: `∃c: λ₁(m,N(m)) ≤ 2λ₁(m,∞)` on the precommitted schedule | **NEW-MATH (named: `CCMFiniteBottomSaturationRate`)** | CCM prove convergence with **no rate**. Measured `N*/m`: `4.6` at `m=13`, `6.3` at `m=23` — *growing*, so linear `N(m)=cm` is not evidently sufficient |
| **S4** | **`ε_∞(m) = R(q_m)/λ₁(m,∞) ≤ C` cofinally** | **NEW-MATH (named: `CofinalQuantitativeWeilBottomFloor`) — and RH-hard: it implies RH by §3c** | it is a lower bound for the Weil bottom past `L = log 2`; the entire literature stops at `log 2` (Yoshida Thm 1, Bombieri Thm 12, CC `2006.13771` Thm 1, Suzuki Thm 1.4) |
| **S5** | relative gap: `g(m) ≥ g₀ > 1`, ideally `g → ∞` | **NEW-MATH** | a second trial gives an **upper** bound for `λ₂` by min–max, not the lower bound needed — NEWMECH §4 verbatim; needs complement coercivity or an exclusion theorem |
| **S6** | `p ≤ (ε−1)/(g−1)` when `0 < λ₁ < λ₂`, `R(q) ≤ Cλ₁` | **THEOREM, LEAN-READY** — elementary Rayleigh–Ritz; retained by NEWMECH as `C3_RELATIVE_RITZ_CONDITIONAL_SUPPLIER` | conditional on S4+S5; NEWMECH killed it as a *single unconditional mechanism* (`POSITIVITY_TYPE_PREMISE` + `WRONG_MINMAX_DIRECTION`) |
| **S7** | `p → 0` ⟹ `sup_K |F_ground − F_trial| → 0` | **NEW-MATH (the judge's atom, `FiniteGroundTransformToCCMTrialLocallyUniform`)** | `p` is an `ℓ²` angle in `ℝ^{2N+1}`; the consumer wants a **compact sup-norm** on the P59 transform. Missing: the source factorization `F_ground − F_trial = E_source` with `sup_K|E_source| ≤ ε_m(K) → 0` built from `K_{m,N}`, its bottom projector and the literal trial **before** any inverse-gap operator-norm bound |
| **S8** | trial leg: transform of `k_λ` → `Ξ` locally uniformly on the strip | **THEOREM** — CCM Lemma 7.3, pp. 31–32, with Lemma 7.2 rate `cλ^{−2}` | Lemma 7.3 is about the **continuum** `k_λ`, not the finite projection `q_{m,N}`; the `k_λ ↔ P_N k_λ` crosswalk is the project's own tail estimate, not CCM's, and its constant `c` in (7.7)/(7.8) is non-explicit |
| **S9** | real zeros of `F_ground`, then roof ⟹ RH | **THEOREM (Lean, hole-free)** for the roof — `rh_of_real_zero_family_tendsto_centeredXi`; **CONDITIONAL** for the real zeros — CCM Thm 5.10 assumes `ε_N` simple and `ξ` even | CCM §8 first missing step: even-simple is unproved for `QW_λ`. Numerically simple on our cells (§5, D6), which proves nothing |

**Load-bearing NEW-MATH step: S4.** S3, S5 and S7 are hard; S4 is not merely hard, it is
RH-equivalent-or-stronger by CCM's own Cor. 3.7 (3.27) + Weil/Yoshida. Any presentation of
R3 that shows S4 as "one more estimate" is misreading its own chain.

---

## 5. Discriminators on the existing caches, with pre-registered numbers

Existing caches: `(13, N ≤ 120)` dps 110 certified; `(23, N ≤ 160)` dps 220 quad 512
`MAX_DEGREE = 180` (trial coefficients floored at `~1e-43`; rerun `q3-wide-23d` with
`MAX_DEGREE = 600` pending); `(43, N ≤ 86)` dps 110; `(83, 83)` dps 110, `MAX_DEGREE = 600`.

**Precision reality check, stated before any discriminator.** The Fuchs law below predicts
`λ₁(43,∞) ≈ 10^{−219}` and `λ₁(83,∞) ≈ 10^{−436}`. The `(43,86)` and `(83,83)` caches are
dps 110. **They cannot see the bottom at all** — consistent with the recorded
`‖(I−P_N)f‖² = 0.0 (below dps 110)` at `(83,83)`. Every discriminator that needs `λ₁`
beyond `m = 23` needs a new run at dps ≥ 260 / dps ≥ 520. Saying otherwise would be a
fabricated measurement.

### D1 — S3, saturation rate `N*(m)/m` · needs a new run
Measured: `N*(13)/13 = 4.6`, `N*(23)/23 = 6.3` (Probe 22).
**Pre-register:** if the first saturated `m = 43` run (dps ≥ 260, `MAX_DEGREE ≥ 600`) gives
`N*(43)/43 ≥ 9.0`, the linear schedule model `N(m) = c·m` is **REFUTED** and R3 must
precommit a superlinear `N(m)` (first candidate `c·m·log m`, since
`4.6/log 13 = 1.79`, `6.3/log 23 = 2.01` — nearly constant).
If `N*(43)/43 ≤ 7.5`, linear survives with `c ≥ 8`.

### D2 — S4, the Figure-4 law · computable **now** on `(13,120)` and `(23,160)`
Define `r(m) = log₁₀ λ₁(m,∞) − log₁₀[(2^14/3)·√2·π⁵ · m^{4.5} · e^{−4πm}]`
(CCM p. 30 constant, `λ² = m`; `log₁₀` of the constant is `6.3736`).

| m | predicted `log₁₀(1−χ₄)` | measured `log₁₀ λ₁(m,∞)` | `r(m)` |
|---|---|---|---|
| 13 | `−59.561` | `−58.458` (`3.484e-59`, `N=120`) | **`+1.103`** |
| 23 | `−113.021` | `−111.745` (`1.8e-112`, `N=160`) | **`+1.277`** |
| 43 | `−220.949` | — (precision-floored) | predicted `+1.47 ± 0.25` |
| 83 | `−437.964` | — (precision-floored) | predicted `+1.67 ± 0.45` |

The saturated bottom decays at `5.33` decades per unit `m` between 13 and 23, against the
Fuchs exponent `4π/ln 10 = 5.46` — CCM's Figure 4 reproduced numerically on our object for
the first time in this project.
**Pre-register:** a saturated `λ₁(43,∞)` with `r(43) ∉ [1.2, 1.9]` **REFUTES**
"`λ₁ ≍ (1−χ₄)` up to a slowly varying factor" at our windows, i.e. removes the only
quantitative reason to expect a uniform `C` in S4. Point prediction: `λ₁(43,∞) = 10^{−219.5}`.

**Companion check available with zero new computation:** at `N = m` the bottom decays at
`2.10` decades per unit `m` (`7.9e-31 → 7.3e-52 → 1.0e-90` at `m = 13,23,43`), i.e.
**less than 40 % of the saturated slope**. `N = m` is not measuring the continuum object at
all — a second, independent confirmation of the judge's `N_EQUALS_M: ONE_REPRESENTATION_NOT_A_THEOREM`.

### D3 — S4, boundedness of `C` · needs the `MAX_DEGREE = 600` rerun of `(23,160)`
Measured: `ε_∞(13) = 1.355` (saturated, `N = 120`). `ε(23)` is not measurable in the
current cache — `R(q)` plateaus at `7e-84` from a Legendre–Galerkin truncation floor
(`MAX_DEGREE = 180`), which is the recorded strangeness.
**Pre-register:** `ε_∞(23) ∈ [1.0, 2.0]` ⟹ `C` looks `m`-independent (`C ≈ 1.5`), S4 stays a
plausible target; `ε_∞(23) > 10` ⟹ on 2 of 2 measurable cells `C` is not uniform and S4
should be re-typed as implausible, not merely unproved.
**Standing caveat (the judge's `EXACT_REFUTER`):** no finite set of cells can refute a
cofinal existential, and no finite set can establish it. D3 is a plausibility instrument.

### D4 — S5, the gap
Measured: `g(13,∞) = 3.77e7` (saturated); `g(23,110) ≈ 1.87e8` (unsaturated cell, indicative
only). Growth `13 → 23` is a factor `4.9`, close to `(23/13)³ = 5.5`.
**Pre-register:** `g(43, saturated) ≥ 1.0e9`. Adverse: `g(43) ≤ 2·g(23)` weakens the
"`g → ∞` fast" leg on which S6 depends.
Equivalent, already-satisfied consistency check: the C3 bound `(ε−1)/(g−1)` at `m = 13` is
`9.4e-9` against `p = 4.7e-9`; at `(23,160)` `p = 4.8e-10` — the lemma holds on every cell
measured, as recorded.

### D5 — S7, the judge's own compact defect · computable **now** from existing caches
On `K₀ = {|Re z| ≤ 1, |Im z| ≤ 1/4}`, the anchored P59 difference `E_{m}` from cached ground
and trial rows at `(13,13), (23,23), (43,43), (83,83), (13,120)`.
**Pre-registered by the judge, relayed unchanged:** `COMPACT_DEFECT_NONDECAY` if the
precision-stable values at `N = m` obey `E_43 ≥ 0.90·E_23` **and** `E_83 ≥ 0.90·E_43`.
This kills the `N = m` representation only, never the existential schedule atom.
**This is the one discriminator that runs on the caches as they stand and it has not been
run.** It is the cheapest decisive probe currently available on R3's atom.

### D6 — S9, even-simple
Second-channel verified (`Progress_Log` 2026-09-04): full-matrix minimum = even `λ₁`; odd
minimum above it by `6.409e-28, 1.511e-48, 3.649e-87` at `m = 13,23,43`; full-matrix relative
gap `≈ 800, 2000, 3600`. Even-simple holds on every computed cell.
**Pre-register:** `λ₁^odd(m,N) ≤ λ₁^even(m,N)` at any cell **REFUTES** CCM's Def. 5.3
hypothesis on our object. Not observed so far. A finite certificate at fixed `(m,N)` is not
a theorem about `QW_λ`; CCM's §8 first missing step remains open regardless.

---

## 6. Friction, honestly

* **The R3 label flatters the step.** "Wide schedule + `sameCofinalGuard` + a saturation
  estimate" reads as three engineering tasks. Reading the Lean shows the first two are free
  and empty; reading CCM shows the third has no literature at our window at all, and the
  premise it serves implies RH. R3's `estimated_cost: 9/10` is, if anything, low.
* **What R3 genuinely buys** and should be stated as its actual value: it moves the wall
  from an *eigenvector* statement without a mechanism (second-mode overlap `d₂`) to an
  *eigenvalue* statement in classical form (`λ₁ ≥ R(q)/C`) that admits a finite interval
  certificate on every cell. That is the `FINITE_CERTIFICATE_PRINCIPLE` shape, and it is a
  real gain in *legibility* — the judge's `HARDNESS_MOVED_TO_FEWER_HIDING_PLACES: plausible_not_proved`
  at 0.72. It is not a gain in *difficulty*.
* **Cheapest next action is D5, not more caches.** It runs on existing data, it is the
  judge's own pre-registration, and it is the only probe that touches the atom itself rather
  than its inputs. D2's `m = 13`/`m = 23` half is already done above and cost nothing.
* **Bookkeeping debt found in passing:** the `WIDE_MISSING_SUPPLIER` line and the object card
  §3.2 say the same thing from two directions (the guard supplies no rate; fixed-`N`
  positivity is strictly weaker). Worth one cross-reference in `docs/GENEALOGY.md` so the
  next reader does not rediscover it a third time.

## CLOSES / OPENS

**CLOSES**
1. "Does CCM bound `λ_min` from below?" — **No**, and Cor. 3.7 says `µ_λ ≥ 0` is not
   assertable. Verified statement, not a guess.
2. "Does CCM prove `ε_λ ≤ Q(k_λ)` at rate `e^{−cλ²}`?" — **No.** The `e^{−4πλ²+9log λ}` rate
   is Fuchs Thm 1 for the prolate defect `1−χ₄`; the link to `ε_λ` is Figure 4.
3. "Does the Lean consumer fix `N = m`?" — **No.** Only `PairCofinal` (`m→∞ ∧ N→∞`).
   `N(m) = 6m` and `c·m log m` are admissible as written.
4. "Is the R3 premise weaker than RH?" — **No.** It implies RH via CCM (3.27) + Weil/Yoshida.
5. First numerical confirmation on our own object that the *saturated* bottom follows the
   Fuchs exponent (`5.33` vs `5.46` decades per unit `m`), and that `N = m` does not
   (`2.10`).

**OPENS**
1. `CCMFiniteBottomSaturationRate` (S3) — an `N*(m)` bound. Nothing in CCM.
2. `CofinalQuantitativeWeilBottomFloor` (S4) — the RH-hard premise, named.
3. The even-sector citation step (Yoshida Prop. 1(2) + "no real zeros of `ζ` in `(0,1)`")
   is currently implicit in Route B and should be an explicit link in the chain.

