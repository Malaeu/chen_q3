# STATUS: OPEN — 034 ABSTRACT REDUCTION CLOSED; TWO SUPPLIERS EXACTLY NAMED

```yaml
PRIMARY_STATUS: OPEN
ROUTE_STATE: CHALLENGER_NOT_RH

TRANSACTION_034:
  primary: COFINAL_EDGE_SLIVER_REDUCTION_PROVED
  scope: ABSTRACT_REDUCTION_PLUS_M257_REGRESSION
  verifier: PAPER_PROOF_PLUS_EXACT_RATIONAL_SYMBOLIC_CHECKER
  lean_status: STANDALONE_TASK_EMITTED_NOT_BUILT   # no repo in this cell
  secondary_flags:
    - A_EDGE_FOUR_THIRDS_ACCEPTED            # m=257 regression, exact margin 1/65
    - TOOTH_LEDGER_IRRELEVANT_TO_LEBESGUE_CONSUMER
  flags_withheld:
    - CERTIFICATE_CUTOFF_RADIUS_DRIVEN       # requires plant P1 on 033 backend (repo)
    - SCALED_JACOBI_PROFILE_IDENTITY_PROVED  # 031 identity consumed, not re-proved
    - PSI_LAST_ZERO_SUFFICIENT_BARRIER_PROVED

CURRENT_SMALLEST_GAP: ScaledOuterSignBarrierFourThirds
NEXT_GAP: RelativeBoundaryCellProductBound

EXECUTION_CELL: cloud session 2026-07-29, no repository checkout.
SOURCE_MIRROR_DECLARED: 7d86020a01f1923b61eaef17c480b1cf752b2246   # unverified here
SOURCE_COMMIT_DECLARED: fdfec3b89d72eba1e9132e79def01719e9d7ca78   # unverified here

INPUT_HASHES:
  PROSHKA_033_AND_MUNTZ_POLE_SUBTRACTED_v2.md: aad7e9de123c42d989a53ed6b10d4bd2f66fc6915e46e0e1d4c46a72087dfcf2
  proshka_answer.md (034 contract): f18c9a6d3b712fa7cea07bd19b31858fc99d82ae61143cdecd34ffa8c51d0362

FORBIDDEN_HONORED:
  - no finite-cell to cofinal promotion (all cofinal statements conditional on named suppliers)
  - r=195 used only as certificate profile in regression, never as intrinsic object
  - no tooth values inside the Lebesgue budget
  - no new K/depth/precision ladder; no enumeration of any kind
  - no pointwise DualTheta claim; no S1 claim; no RH claim
  - STATE untouched; Bus 010 void; next gate NOT self-selected
```

---

## 0. What this cell did and did not do

Executed here: STEP 0 (object lock), STEP 1 (abstract reduction — full proof),
STEP 3 (m=257 regression, exact arithmetic), the exact statements and
jump-targets of the two STEP 2 suppliers, the runnable subset of plants
P1–P11, and one standalone Aristotle task that formalizes the reduction.
Also emitted: the repaired pole-subtracted Müntz task v3 (REQUEST_2 of the
033 handoff), since the project copy `ARISTOTLE_TASK_EStarMuntzContinuation.md`
is still the stale raw-product version whose T4 is false at the pole.

Not executed here (no repo): re-verification of 030/031/033 certificate
hashes; plants P1, P5, P7-backend, P2-coverage against the real backend;
`lake build` of the Lean artifact; STATE history line + git add (operator
action in the repo).

## 1. Import ledger (K7 classification; nothing below is re-proved here)

| Import | Content used | Class | Where verified |
|---|---|---|---|
| 032 / RiemannBoundaryCellBridge (T2,T3) | for zero-mass, [0,b]-supported, Ico-Lipschitz h: for u∈(0,1), ‖Σ'ₙ h(nu)‖ ≤ K·b + (‖h(0)‖+K·b) + ‖h(b)‖ and ‖E⋆(h,u)‖ ≤ B√u with the same explicit B | THEOREM (Lean, axiom-clean) | 032 reverification, per 033 source locks; parametric in (h,b,K) |
| 030/031 Theorem C crosswalk | E⋆(h_λ, λz) = −(I₀I₄/D)·√(z/λ)·S_λ(z), C_λ := I₀I₄/D > 0; tooth-alias identity; du/u = dz/z | THEOREM (Arb+exact-rational certificates) | 030/031 certificates, hashes declared in 033 contract; only C_λ > 0 and the exponent lock are consumed below |
| 031 Jacobi divided-difference | S_m = ((Θ₄,ₘ−Θ₀,ₘ)/2)·D_m with full Green boundary ledger; spectral difference positive | THEOREM (per 031 answer) | repo; consumed only to phrase Supplier A's discriminator form |
| 033 band profile | ε_r > 0 exactly for r=195..256; ε_r = 0 (i.e. certified L_r ≥ 0) for r=16..194; teeth: lower envelope ≥ 0 for r=17..195, zero-compatible r=196..257 | THEOREM (finite cell m=257) | 033 answer + FULL_WINDOW_POSITIVE_PART_CERT.json (hash-locked in repo) |
| 027 outer-lobe gate | E⋆(h_λ,u) ≤ 0 on u ∈ [1,λ] | THEOREM at m=257; cofinal scope **UNVERIFIED here** — flagged everywhere it is used | 027 answer (repo) |
| max ε_r vs 030 remainder | 2.241863561…e−237 vs 2.24186222…e−237, gap 1.33e−243 | MEASUREMENT (evidence for radius-driven cutoff; not a theorem) | proshka_answer; P1 required before any flag |

## 2. STEP 0 — object lock (registered before any derivation)

Coordinates, frozen by the 034 contract:

```text
lambda_m = sqrt(m),   z = u / lambda_m,   a := m z = lambda_m u
window u ∈ [1/lambda_m, lambda_m]  ⇔  z ∈ [1/m, 1]  ⇔  a ∈ [1, m]
lower half u ∈ [1/lambda_m, 1]     ⇔  a ∈ [1, lambda_m]
tooth z = 1/r                       ⇔  a = m/r,  u = lambda_m/r
r_m(a) = floor(m/a)
```

Crosswalk, both source forms pinned (P4 lock):

```text
033-contract form:  E⋆(h_λ, λz) = −(I₀I₄/D)·sqrt(z/λ)·S_λ(z)
034 scaled form:    E⋆(h_{λ_m}, a/λ_m) = −C_m·sqrt(a)/λ_m^{3/2}·𝒮_m(a)
consistency:        z = a/m, m = λ² ⇒ sqrt(z/λ) = sqrt(a)·λ^{−3/2}   [checker C13, exact]
equivalent u-form:  E(u) := E⋆(h_{λ_m}, u) = −(C_m/λ_m)·sqrt(u)·𝒮_m(λ_m u)
```

Consequence used everywhere: since C_m > 0 and √a > 0, off teeth

```text
E⋆ ≤ 0  ⇔  𝒮_m ≥ 0        (and E⋆ > 0 ⇔ 𝒮_m < 0)
```

Only the SIGN of the prefactor and the exponent lock are consumed by the
reduction; a normalization error in C_m cannot corrupt STEP 1 — it would
surface later as `SCALED_EDGE_OBJECT_MISMATCH` at supplier consumption.

Mutant guard (P4): the mutant a = r/λ fails the object lock twice — the
window edge u = 1/λ_m must map to a = 1 (it maps to nothing r-independent),
and a tooth alias must depend on position only through m/r. Registered as a
statement-level kill; the exponent identity itself is checker-verified (C13).

## 3. STEP 1 — the abstract reduction, proved

Standing hypotheses for one cell m ≥ 2, λ = λ_m = √m ≥ √2 > 4/3.
E : (0, λ] → ℝ, E(u) = E⋆(h_λ, u). Constants B_m ≥ 0, C_m > 0,
A_m ∈ [1, λ].

```text
(H0)  E is Lebesgue-measurable on (0, λ].
      [Supplied: bridge T0 gives the finite-sum representation
       Σ_{n=1}^{ceil(b/u)} h(nu); finite sums of measurable functions,
       times sqrt(u). THEOREM-class.]

(H1)  |E(u)| ≤ B_m·sqrt(u) for all u ∈ (0,1).
      [Supplied: bridge T3 with b := λ, B_m := K_m λ + (‖h_λ(0)‖ + K_m λ) + ‖h_λ(λ)‖.
       THEOREM-class, parametric in m. Requires the h_λ package facts:
       support ⊂ [0,λ], Lipschitz on [0,λ), measurable, zero mass —
       all locked package properties.]

(H2)  E(u) ≤ 0 for a.e. u ∈ [A_m/λ, λ].            ["scaled outer sign" (S)]
      [THE NAMED SUPPLIER — see §5. Not assumed proved.]
```

Target functional (contract form):

```text
Δ⁺_{m,σ} := ∫_{1/λ}^{λ} max(E(u),0) · u^{−σ} · du/u,     0 ≤ σ < 1/2.
```

### Theorem 034-R (scaled edge-sliver reduction)

Under (H0)–(H2), for every σ ∈ [0, 1/2):

```text
Δ⁺_{m,σ}  ≤  B_m · λ^{σ−1/2} · (A_m^{1/2−σ} − 1) / (1/2 − σ),
```

equivalently, dividing by C_m > 0, exactly the boxed (034-edge):

```text
Δ⁺_{m,σ}/C_m  ≤  (B_m/C_m) · λ_m^{σ−1/2} · (A_m^{1/2−σ} − 1) / (1/2 − σ).
```

Moreover the right side is strictly increasing in A_m
(∂_A RHS = B_m λ^{σ−1/2} A^{−σ−1/2} > 0; checker C11a), so any certified
A_m ≤ A_edge may be replaced by the frozen conservative A_edge = 4/3,
PROVIDED (H2) holds at A_m (then it holds at every A' ≥ A_m, since
[A'/λ, λ] ⊂ [A_m/λ, λ] — both monotonicities point the same way).

**Proof.** The integrand f(u) := max(E(u),0)·u^{−σ−1} is measurable (H0) and
nonnegative, so all integrals below are well-defined in [0, ∞] and the
splitting is legitimate for nonnegative integrands.

Geometry of the split: 1 ≤ A_m gives 1/λ ≤ A_m/λ; A_m ≤ λ gives
A_m/λ ≤ 1 ≤ λ. So, up to the single shared endpoint (measure zero),

```text
[1/λ, λ] = [1/λ, A_m/λ) ⊔ [A_m/λ, λ].
```

Outer part. By (H2), E ≤ 0 a.e. on [A_m/λ, λ], hence max(E,0) = 0 a.e.
there, hence ∫_{[A_m/λ, λ]} f = 0 (nonnegative integrand vanishing a.e.).
This is where the entire upper half u ∈ [1, λ] and the outer lower part
u ∈ [A_m/λ, 1] disappear.

Sliver part. [1/λ, A_m/λ) ⊂ (0,1) because 1/λ > 0 and A_m/λ ≤ 1.
So (H1) applies pointwise: max(E(u),0) ≤ |E(u)| ≤ B_m √u, hence

```text
f(u) ≤ B_m · u^{1/2} · u^{−σ−1} = B_m · u^{−σ−1/2}.
```

The majorant is continuous on the compact closure of the sliver, hence
integrable; by monotonicity of the Lebesgue integral and the fundamental
theorem of calculus with antiderivative u ↦ u^{1/2−σ}/(1/2−σ)
(valid: the exponent −σ−1/2 ≠ −1 since 1/2−σ > 0; checker C8a):

```text
Δ⁺_{m,σ} ≤ B_m ∫_{1/λ}^{A_m/λ} u^{−σ−1/2} du
         = B_m · [(A_m/λ)^{1/2−σ} − (1/λ)^{1/2−σ}] / (1/2−σ)
         = B_m · λ^{σ−1/2} · (A_m^{1/2−σ} − 1) / (1/2−σ).          ∎
```

(The last algebra step is checker-verified symbolically, C8b. As a byproduct
Δ⁺_{m,σ} < ∞ under (H0)–(H2); indeed the majorant is integrable even down to
u = 0+ since −σ−1/2 > −1.)

Edge cases. A_m = 1: RHS = 0 and the sign hypothesis covers the whole
window, so Δ⁺ = 0 — consistent. σ → 1/2−: RHS → B_m ln A_m (finite); the
theorem is stated per σ < 1/2, the limit is a remark, not a claim at σ=1/2.

**Sharpness (E0-identity, K1).** The witness E₀(u) := B_m√u for
u ∈ (0, A_m/λ), 0 otherwise, satisfies (H0)–(H2) and attains the bound with
EQUALITY at every σ (checker C14). The constant is optimal; there is no
hidden slack in the reduction to absorb supplier weaknesses later.

### Corollary 034-P (product condition ⇒ cofinal moment bound)

Let 𝓜 be any family of admissible cells, each with constants
(A_m, B_m, C_m) such that (H0)–(H2) hold. Fix σ ∈ [0,1/2) and suppose the
exact all-σ condition (034-product):

```text
Π_σ := sup_{m∈𝓜} [ (B_m/C_m) · λ_m^{σ−1/2} · (A_m^{1/2−σ} − 1)/(1/2−σ) ] < ∞.
```

Then sup_{m∈𝓜} Δ⁺_{m,σ}/C_m ≤ Π_σ < ∞. If this holds for every
σ ∈ [0,1/2), the statement `CofinalFullWindowPositivePartMomentBound`
holds on 𝓜. Immediate from 034-R; the quantifier over m enters ONLY
through the hypotheses — no finite cell occupies it (plant P10).

### Corollary 034-S (simple sufficient form)

If cofinally A_m ≤ 4/3 (with (H2) at A_m) and B_m ≤ B₀·C_m, then for all
such m and ALL σ ∈ [0,1/2) simultaneously:

```text
Δ⁺_{m,σ}/C_m ≤ B₀ · ((4/3)^{1/2−σ} − 1)/(1/2−σ) ≤ B₀ · 2(2/√3 − 1) < 0.3094011 · B₀,
```

using λ_m^{σ−1/2} ≤ 1 (λ_m ≥ 1, exponent ≤ 0), A-monotonicity, and:
g(x) := ((4/3)^x − 1)/x is increasing on (0, 1/2] because
φ(x) := x c^x ln c − c^x + 1 has φ(0) = 0 and φ'(x) = x c^x (ln c)² ≥ 0
(checker C11b), so sup over σ ∈ [0,1/2) is g(1/2) = 2(2/√3 − 1), attained
at σ = 0 (checker C11c). Note the bound is uniform in σ — strictly more
than the contract's per-σ requirement. Failure of either sufficient
hypothesis does NOT kill (034-product): explicit counterexamples in both
directions are checker-verified (C12a: A_m ≡ 2 works; C12b: B_m/C_m = 1+ln λ_m
works). This is plant P11 discharged.

### Lemma 034-D (domain shrink — CONDITIONAL on 027's cofinal scope)

(H2) concerns u ∈ [A_m/λ, λ], i.e. a ∈ [A_m, m]. If additionally the
027-type outer-lobe gate holds at m (E ≤ 0 a.e. on u ∈ [1, λ], i.e.
a ∈ [λ_m, m] = [√m, m]), then (H2) reduces to

```text
E ≤ 0 a.e. on u ∈ [A_m/λ, 1]   ⇔   𝒮_m(a) ≥ 0 a.e. on a ∈ [A_m, √m].
```

So IF the outer-lobe gate is available on the same cofinal family (import
status: THEOREM at m=257; cofinal scope OPEN — must be checked in the repo
before use), Supplier A's obligation shrinks from a ∈ [4/3, m] to
a ∈ [4/3, √m] — a quadratic domain compression. Flag this lemma's use with
the 027-scope check; do not consume it silently.

### Exact shape of the product supplier (K8 compression of Supplier B)

With A_m ≤ 4/3 frozen, (034-product) for every σ < 1/2 is equivalent to:

```text
∀σ ∈ [0,1/2):  sup_{m∈𝓜} (B_m/C_m)·λ_m^{σ−1/2} < ∞
⇔  B_m/C_m grows slower than any positive power of λ_m on 𝓜.
```

(If B_m/C_m ~ λ^β with β > 0, the condition holds for σ < 1/2−β and fails
for σ ∈ (1/2−β, 1/2): the ∀σ form demands subpolynomial growth — exactly.)
With the explicit bridge constant B_m = K_m λ_m + (‖h_λ(0)‖ + K_m λ_m) + ‖h_λ(λ_m)‖,
Supplier B reduces to growth control of the Lipschitz constant, the value at
0, and the endpoint value of h_{λ_m}, against a LOWER bound for
C_m = I₀,ₘI₄,ₘ/D_m. The missing lower bound on C_m is the analogue of the
b_λ two-sided-bound slot in the α-thread (NORMALIZATION_DEGENERACY risk
class) — it must be a slot in the supplier task, not an afterthought.

## 4. STEP 3 — m=257 regression (exact arithmetic; no bands regenerated)

All facts below are integer/rational identities, machine-checked
(checker C1–C7); 033/027 verdicts enter as declared imports.

```text
conservativity:   3·257 = 771 < 780 = 4·195  ⇒  257/195 < 4/3
exact margin:     4/3 − 257/195 = 9/585 = 1/65  (in a-units)
crossing band:    257/193 < 4/3 < 257/192  ⇒  a = 4/3 lies inside band r=192
buffer:           bands r = 193, 194 (both ε=0) lie strictly below 4/3
positive bands:   r = 195..256 ⇒ a ∈ [257/256, 257/195] ⊂ [1, 4/3)   ✓ all inside sliver
zero-compat teeth: r = 196..257 ⇒ a = 257/r ∈ [1, 257/196] ⊂ [1, 4/3) ✓ all inside sliver
planted violation: A_edge = 5/4 FAILS (4·257 = 1028 > 975 = 5·195) — judge fires ✓
domain guard:     16/9 < 2 ≤ m ⇒ 4/3 < λ_m for every m ≥ 2 ✓
```

Assembly of the m=257 instance of (H2) at A = 4/3 (imports 033 + 027):
033's ε_r = 0 for r = 16..194 certifies 𝒮₂₅₇ ≥ 0 on every such band, i.e. on
a ∈ [257/195, √257] minus teeth (measure zero); since 257/195 < 4/3, this
covers a ∈ [4/3, √257] a.e.; 027 covers a ∈ [√257, 257]; junction exact.
**Hence (H2) holds at (m=257, A=4/3), and the m=257 instance of (034-edge)
is unconditional given the 033/027 imports:**

```text
Δ⁺_{257,σ} ≤ B₂₅₇ · 257^{(σ−1/2)/2} · ((4/3)^{1/2−σ} − 1)/(1/2−σ),   σ ∈ [0,1/2).
```

First cell where the edge-sliver reduction is fully realized. (033's own
ε-ledger bound ~1e−237 is astronomically tighter AT m=257; no conflict —
both are upper bounds, and only the 034 form generalizes cofinally.)

NOT claimed: that r=195 is intrinsic (the 1.33e−243 gap between max ε_r and
the 030 remainder stays MEASUREMENT-class until plant P1 runs on the
backend); that any of this covers m ≠ 257; that teeth affect Δ⁺
(measure zero — flag TOOTH_LEDGER_IRRELEVANT_TO_LEBESGUE_CONSUMER, trivially
by null-set invariance of the Lebesgue integral, plant P6).

## 5. STEP 2 — the two suppliers: exact statements, routes, jump-targets

### Supplier A — `ScaledOuterSignBarrierFourThirds`  [CURRENT_SMALLEST_GAP]

```text
Statement (unconditional form):   for m ∈ 𝓜:  𝒮_m(a) ≥ 0 a.e. on a ∈ [4/3, m].
Statement (027-shrunk form):      𝒮_m(a) ≥ 0 a.e. on a ∈ [4/3, √m]
                                  + cofinal 027 outer-lobe gate (scope check!).
m=257 instance: CLOSED (033 bands 16..194 + 027; §4).
```

Primary route (contract): the 031 Jacobi divided-difference identity in the
scaled variable — 𝒮_m = ((Θ₄,ₘ−Θ₀,ₘ)/2)·𝒟_m with positive spectral factor,
so the JUMP-TARGET is one sign statement for one explicit object:

```text
JUMP-TARGET A:  𝒟_m(a) ≥ 0 a.e. on a ∈ [4/3, √m]  (parametric in m; no r-enumeration)
```

Permitted stronger route: Ψ_m(t) ≥ 0 for t ∈ [4/(3m), 1] ⇒ every active
sample nz ≥ z ≥ 4/(3m) lands in the nonnegative region ⇒ 𝒮_m ≥ 0 pointwise
on a ≥ 4/3. WARNING (plant P3, checker C10): this route is sufficient, NOT
necessary — Ψ(t) = t² − 1/3 has an interior sign change and zero mass, yet
S*_r = (r+1)/(6r) > 0 for every r. A failure of Ψ_m-positivity is NOT a kill
of Supplier A (direction semantics, P11-analogue for signs).

Required repo inputs to run this supplier: 031 answer + certificate pair
(Jacobi identity, exact 𝒟_m definition), Ψ_m coefficient structure
(δ_q ledger), 027 answer (exact scope of the outer-lobe gate).

### Supplier B — `RelativeBoundaryCellProductBound`  [NEXT_GAP]

```text
Statement: ∀σ ∈ [0,1/2): sup_{m∈𝓜} (B_m/C_m)·λ_m^{σ−1/2}·(A_m^{1/2−σ}−1)/(1/2−σ) < ∞
Frozen-A form (A_m ≤ 4/3): ⇔ B_m/C_m = O(λ_m^ε) for every ε > 0.
JUMP-TARGET B:  one two-sided ledger —
   upper: K_m, ‖h_{λ_m}(0)‖, ‖h_{λ_m}(λ_m)‖ growth (explicit from the h-package);
   lower: C_m = I₀,ₘI₄,ₘ/D_m ≥ c·λ_m^{−q}  for some fixed q  (the missing slot).
```

Do not prove stronger separate bounds unless needed (contract line). The
C_m lower bound is the single genuinely new estimate; everything else is
bookkeeping on locked package constants.

## 6. Plants P1–P11 — ledger (RUN here vs EMITTED to repo)

| Plant | Status | Result / task |
|---|---|---|
| P1 radius mutation | EMITTED | needs 033 backend; ×1/2, ×2 outward radius; r_cert must move if resolution-driven. Prerequisite for CERTIFICATE_CUTOFF_RADIUS_DRIVEN flag. |
| P2 intrinsic-object lock | RUN — PASS | definitional audit: no hypothesis or step of 034-R/P/S/D references q=700, τ_response, box widths, or Bernstein subdivision (§3 is the full inventory: H0, H1, H2, m≥2, σ<1/2 — nothing else). |
| P3 Ψ-root trap | RUN — PASS | checker C10: zero mass ✓, interior sign change ✓, S*_r = (r+1)/(6r) exactly ✓. Sampled sign ≠ Ψ sign; guards Supplier A's route semantics. |
| P4 scaled-variable mutation | RUN — PASS | a = mz = λu passes (C13 exponent lock + window/tooth aliases §2); mutant a = r/λ killed at statement level (§2). |
| P5 crossing-band deletion | EMITTED | coverage checker lives with certificates; crossing band identified exactly here: r=192 (C3). |
| P6 tooth mutation | RUN — PASS | null-set invariance: changing E on finitely many points changes no integral; tooth ledger is a separate pointwise object. |
| P7 sign flip | RUN (semantics) / EMITTED (backend) | Ψ → −Ψ ⇒ 𝒮 → −𝒮 ⇒ E → −E: positive part migrates from sliver to outer region, (H2) fails, 034-R inapplicable — the reduction is NOT sign-symmetric, as it must be. Backend δ₀-lock check emitted. |
| P8 Jacobian/weight | RUN — PASS | checker C8 + C9: dropping du/u or the λ^{σ−1/2} factor changes the closed form with exact rational separation (plants fire). |
| P9 scalar rescaling | RUN — PASS (abstract) | the inequality is 1-homogeneous under (Δ⁺, B, C) → c·(Δ⁺, B, C); normalized statement invariant. Whether the concrete (E⋆, B_m, C_m) realize the joint scaling under h → c·h is a repo-level residual (declared, not assumed). |
| P10 finite-to-cofinal guard | RUN — PASS | quantifier audit: m=257 data appears only in §4; Theorems in §3 quantify over 𝓜 only through named hypotheses. No promotion anywhere. |
| P11 direction semantics | RUN — PASS | checker C12: A_m ≡ 2 (violates A≤4/3) and B_m/C_m = 1+ln λ (violates B≤B₀C) both still satisfy per-σ (034-product). Simple-corollary failures are not kills. |
| extra: regression plant | RUN — PASS | A_edge = 5/4 planted: judge fires (C5). |
| extra: sharpness E0 | RUN — PASS | witness attains equality (C14): constant optimal. |

## 7. Artifacts + ACTIONS LOG

```text
Artifacts of this cell:
  034_cofinal_scaled_edge_sliver_moment.answer.md      (this file)
  034_REGISTRATION.md                                   (pre-run predictions)
      sha256 00ad87dac777367e5954ac105c1434aa72f70f59d68185c8b8c5d85cef4e596b
  check_034_edge_sliver_reduction.py                    (independent judge)
  CHECK_034_RUN.log                                     (26/26 PASS, plants fired)
  ARISTOTLE_TASK_EdgeSliverMomentReduction.md           (Lean target for 034-R, standalone)
  ARISTOTLE_TASK_EStarMuntzContinuation_v3_PoleSubtracted.md
                                                        (repaired Müntz target, REQUEST_2)

ACTIONS LOG:
  2026-07-29T23:07:02Z  registered predictions (034_REGISTRATION.md), sha256 above;
                        input hashes recorded (see YAML header)
  2026-07-29T23:08Z     checker built and run once: 26/26 PASS on first run;
                        no check edited after the run; registered wording unchanged
  (repo actions NOT performed here: hash re-verification, lake build,
   ROUTE_B_STATE.md history line, git add — operator/next cell)

Artifact hashes (this file's own hash to be recorded by the operator in STATE):
  8fba7657164fd16411e6356f018cf661e2cc843b7f01777353a3ddacd5f3f79b  check_034_edge_sliver_reduction.py
  49a965798b1be4a802ddc144ae51bd2e9c287c9c323b68dea7ec2221ba277969  CHECK_034_RUN.log
  5b9a7fba98626aca3ab6d0bf1443bcd15b829bab2426c1f08a04ffac6ff1ac7d  ARISTOTLE_TASK_EdgeSliverMomentReduction.md
  90af30037ec0340bca1ea7d530a37aca3f48342d856d02bd5717cc6d3c627c95  ARISTOTLE_TASK_EStarMuntzContinuation_v3_PoleSubtracted.md
  00ad87dac777367e5954ac105c1434aa72f70f59d68185c8b8c5d85cef4e596b  034_REGISTRATION.md
```

## 8. Registered predictions — scored

Mine (034_REGISTRATION.md, pre-run):

```text
R034-1  CONFIRMED   (P2 audit §6; hypothesis inventory §3)
R034-2  CONFIRMED   (C1b margin 1/65; C3 crossing r=192; C5 plant fires)
R034-3  CONFIRMED   (ledger §6; P1/P5/P7-backend emitted as predicted)
R034-4  CONFIRMED   (C14 equality)
R034-5  CONFIRMED   (C11c: 2(2/√3−1) = 0.3094011… at σ=0; ln(4/3) limit)
R034-6  CONFIRMED   (§4 assembly; conditional ONLY on declared 033/027 imports)
```

Proshka's P034-1..5 (from the 034 contract), current state:

```text
P034-1 (r_cert radius-driven)          UNSCORED — requires plant P1 (repo). Evidence noted, no flag.
P034-2 (intrinsic transition = sampled response, not bare Ψ-zero)
                                       SUPPORTED, not decided — P3 trap validated exactly (C10);
                                       the real Ψ_m case needs Supplier A work.
P034-3 (A_edge = 4/3 survives cofinal audit)
                                       PARTIAL — m=257 instance certified (§4); cofinal audit open.
P034-4 (reduction closes; remaining wall = cofinal product bound)
                                       HALF-CONFIRMED — reduction closed (§3). Correction to the
                                       second half: TWO walls remain, and Supplier A (sign barrier)
                                       is the deeper one; Supplier B is a two-sided constants ledger.
P034-5 (tooth sign inconclusive and irrelevant to the moment)
                                       CONFIRMED on irrelevance (P6); tooth sign untouched.
```

## 9. PRIMARY VERDICT

```text
COFINAL_EDGE_SLIVER_REDUCTION_PROVED
```

— formula (034-edge) is closed (Theorem 034-R with full proof, sharp
constant, machine-checked algebra and regression; standalone Lean task
emitted), and the source suppliers remain exactly named:
`ScaledOuterSignBarrierFourThirds` (a ∈ [4/3, m]; shrinks to [4/3, √m]
under cofinal 027), then `RelativeBoundaryCellProductBound`
(⇔ B_m/C_m subpolynomial, needs the C_m lower-bound slot).

Not returned: `COFINAL_EDGE_SLIVER_MOMENT_BOUND_PROVED` (suppliers open),
`SCALED_OUTER_SIGN_BARRIER_KILLED` (no negative certificate),
`RELATIVE_BOUNDARY_CELL_PRODUCT_GAP` (sign supplier not yet proved — the
gap sequencing has not been reached), `SCALED_EDGE_OBJECT_MISMATCH`
(C13 + §2: forms agree exactly).

What would change the verdict: (i) a repo hash mismatch on 030/031/033
certificates or a different 027 statement → downgrade §4 assembly and
re-audit; (ii) failure of the emitted Lean task on a named API gap → the
paper proof stands, the Lean layer reports its gap code; (iii) a certified
strict-negative 𝒮_m interval inside a ≥ 4/3 on an admissible family →
SCALED_OUTER_SIGN_BARRIER_KILLED and the route pivots to the Jacobi
fallback as sign supplier.

## 10. Route map + meta closeout

```text
034 (this):  abstract reduction CLOSED + m=257 instance realized
             → Supplier A: 𝒟_m(a) ≥ 0 a.e. on [4/3, √m] (one sign, one object, one interval)
             → Supplier B: one two-sided constants ledger (C_m lower bound is the only new slot)
Jacobi:      reserve → PRIMARY route for Supplier A (031 identity, scaled variable, no r-enumeration)
Müntz:       repaired v3 pole-subtracted task emitted (T4 raw-product falsehood removed)
```

- **Became smaller:** `CofinalFullWindowPositivePartMomentBound` →
  (034-edge, PROVED) + one sign barrier on one explicit interval + one
  subpolynomial constants ratio. Both survivors have named jump-targets.
- **Killed:** any slack in the reduction constant (sharpness witness);
  Jacobian/weight drift (exact separation plants); A-cutoff misreadings
  (5/4 plant); Ψ-zero as a necessary mechanism (P3 trap, exact).
- **Do not try again:** proving (034-edge) with certificate parameters in
  the hypotheses; treating simple-corollary failures as kills of
  (034-product); consuming 034-D without the 027 scope check.
- **Current smallest named gaps:** `ScaledOuterSignBarrierFourThirds`,
  then `RelativeBoundaryCellProductBound`.
- **Next cheapest decisive tests:** (1) repo: read 031's exact 𝒟_m and check
  its sign structure on [4/3, √m] symbolically before any computation;
  (2) repo: plant P1 radius mutation to score P034-1; (3) run the emitted
  Lean task. This is test-ordering within 034's own STEP 2, not a
  self-selected next gate.
- **Progress class:** `PROOF_PROGRESS + REPRESENTATION_PROGRESS`.
- **Route score:** 5/5 for the reduction layer; suppliers untouched by design.
