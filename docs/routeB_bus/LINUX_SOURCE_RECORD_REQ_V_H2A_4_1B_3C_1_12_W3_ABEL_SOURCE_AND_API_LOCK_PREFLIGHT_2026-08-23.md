```yaml
BASE_HEAD: 51bc40a9220b748b4df2d5a760938f47f8fb707b
TASK_ID: H2A_4_1B_3C_1_12_W3_ABEL_SOURCE_AND_API_LOCK_PREFLIGHT
MODE: READ_ONLY_MATH_AND_API_PREFLIGHT
LEAN_EDIT: false
LEAN_PATH: null
LEAN_GIT_BLOB: null
SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_12_W3_ABEL_SOURCE_AND_API_LOCK_PREFLIGHT_2026-08-23.md
PUBLIC_SURFACE: []
EXPECTED_AXIOM_PROFILES: {}

CLOSES:
  - W3_ABEL_LIMIT_PINNED_SUPPLIER_STATUS
  - W3_FIRST_DECISIVE_TEST_MATHEMATICAL_CLOSURE
  - W3_PERIODIZATION_SUPPLIER_STATUS
  - W3_POISSON_KERNEL_SUPPLIER_STATUS
OPENS:
  - W3_DIRECTIVE_CONFLICT_BETWEEN_TWO_ADMISSION_VERDICTS

VERIFICATION_HANDOFF: []          # read-only preflight, no gate to run

NEXT_LOAD_BEARING_GAP: W3_DIRECTIVE_CONFLICT_BETWEEN_TWO_ADMISSION_VERDICTS

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
ARISTOTLE: false
```

# W3 preflight — source and API lock

## 0. Two admission verdicts disagree about W3, recorded before it is explained

Both verdicts adjudicate the same task and both admit W2. They then give
different next transactions.

| | `d4cd2e46` (23:15:59) | `7b6f9b9e` (23:24:39) |
|---|---|---|
| file | `..._W3_ABEL_POISSON_L2_AUTHORIZATION_...` | `..._SEMANTIC_ADMISSION_...` |
| next task | `H2A_4_1B_3C_1_12_SELECTED_FERRERS_ABEL_POISSON_L2_LOCK_LEAN` | `H2A_4_1B_3C_1_12_W3_ABEL_SOURCE_AND_API_LOCK_PREFLIGHT` |
| mode | `ONE_GOAL_ONE_COMMIT_LEAN_SOURCE_TRANSACTION`, `LEAN_EDIT: true` | `READ_ONLY_MATH_AND_API_PREFLIGHT` |
| named gap | `W3_SELECTED_FERRERS_ABEL_REFLECTED_L2_LOCK` | `W3_DIRICHLET_JORDAN_SINE_HARMONIC_AND_MIDPOINT_SOURCE_LOCK` |
| Dirichlet–Jordan | explicitly FORBIDDEN in the primary route | named inside the gap |

**Two readings, and the outcome that separates them.**

Reading A — `7b6f9b9e` is later on the clock but earlier in knowledge: it does
not mention the pinned `AbelLimit.lean` supplier and still names the gap
through Dirichlet–Jordan, which `d4cd2e46` had already retired via its
`PINNED_MATHLIB_CORRECTION` and `REPRESENTATION_SHIFT` sections. Under this
reading `d4cd2e46` governs.

Reading B — `7b6f9b9e` is a deliberate revision pulling W3 back to a read-only
preflight before any Lean is written.

The separating outcome is the judge's own answer, not my inference. It is
queued.

**What I did about it.** I executed the intersection: this file is exactly the
read-only preflight `7b6f9b9e` demands, and it is also step 1 of the proof
route `d4cd2e46` mandates ("Run `./ask.sh` for the final public names, Poisson
kernel, finite periodization, Abel limit and seam-set suppliers"). No Lean
source was written and no route was mutated, so neither reading is foreclosed.

## 1. Pinned Abel supplier — CONFIRMED, and my earlier claim was wrong

My earlier preflight called Abel's limit theorem external. That was false.
Pinned at `2df2f015`, file `Mathlib/Analysis/Complex/AbelLimit.lean`:

```lean
Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) ((𝓝[<] 1).map ofReal) (𝓝 l)

Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) :
    Tendsto (fun x ↦ ∑' n, f n * x ^ n) (𝓝[<] 1) (𝓝 l)
```

Both pasted from the pinned source, lines 247 and 263. Retained as the
runner-up tool only; the primary route does not consume them.

## 2. First decisive test — closed mathematically before any Lean

The judge required `REFLECTED_ABEL_EQUALS_SQRT_U_OVER_TWO_TIMES_POISSON_AVERAGE`
to close literally, with a stop order if it did not.

Symbolic derivation, with `p_{k,u}(x) = Σ_m f_k(u(m+x))` of period 1:

```
p̂(n) = ∫_0^1 p(x) e^{-2πinx} dx = ∫_ℝ f(ux) e^{-2πinx} dx = u⁻¹ · 𝓕f(n/u)
```

`f_k` is even and real, so `p̂(-n) = p̂(n)`, and with the period-1 Poisson
kernel `P_r(x) = Σ_{n∈ℤ} r^{|n|} e^{2πinx}`:

```
(P_r * p)(0) = Σ_{n∈ℤ} r^{|n|} p̂(n) = p̂(0) + 2 Σ_{n≥1} r^n u⁻¹ 𝓕f(n/u)
```

Zero mass kills `p̂(0) = u⁻¹𝓕f(0)`, and the factor 2 cancels the ½:

```
(√u/2)(P_r * p)(0) = u^{-1/2} Σ_{n≥1} r^n 𝓕f(n/u) = E^∨_{r,k}(u)
```

The Fourier sign, the 2π normalization, the positive-index ½, the zero-mass
term and the reflection orientation all close with **no fitted scalar**.

Zero-mass is load-bearing exactly as the mandated plant says: without
`𝓕f(0) = 0` the identity carries the extra `−½ 𝓕f(0) u^{-1/2}`.

The `r → 1` limit: `(P_r*p)(0) → p(0) = f(0) + 2Σ_{m≥1} f(um)`, hence

```
(√u/2)p(0) = ½f(0)√u + √u Σ_{m≥1} f(um) = E_star(f)(u) + ½ f(0) √u
```

which is `selectedFerrersAbelLimit` literally.

### Numerical probe (reconnaissance only — not a certificate, not committed)

Run against an even, compactly supported, zero-mass toy with analytic Fourier
transform and an independent grid convolution:

```
u=2.3 r=0.9   Abel=+0.254020330  Poisson=+0.254020189  diff=1.42e-07
u=0.8 r=0.95  Abel=-0.221093138  Poisson=-0.221092759  diff=3.79e-07
u=3.1 r=0.7   Abel=+0.237836571  Poisson=+0.237836098  diff=4.73e-07
```

`r → 1` against `E_star + ½f(0)√u`, at `u = 0.55` where `E_star = -0.3438` is
genuinely nonzero against a half-jump of `+0.1347`:

```
r=0.99   diff=2.68e-03
r=0.999  diff=2.67e-04
r=0.9999 diff=2.67e-05
```

Linear in `(1-r)`, as an approximate identity against a jump should be.

**Recorded symptom, resolved.** The first probe run used `u = 2.3 > λ`, where
every `f(nu)` vanishes and `E_star = 0`. It agreed with the target while
testing only the half-jump term — a green light for the wrong reason. Rerunning
at `u < λ` was what made the `E_star` branch load-bearing. Written down here
because a check that passes for a suspicious reason is worse than one that
fails.

## 3. Supplier status — what the pin has and what it does not

| Object | Pinned supplier | Status |
|---|---|---|
| Abel limit | `Real/Complex.tendsto_tsum_powerSeries_nhdsWithin_lt` | EXISTS (runner-up only) |
| Fourier coefficient on a circle | `fourierCoeff`, `fourierCoeffOn`, `fourierCoeff_eq_intervalIntegral` (`Analysis/Fourier/AddCircle.lean`) | EXISTS |
| periodization coefficient | `Real.fourierCoeff_tsum_comp_add` (`Analysis/Fourier/PoissonSummation.lean:51`) | **EXISTS BUT UNUSABLE — see below** |
| unit-circle Poisson kernel | — | **ABSENT from the whole pin** |
| project `E_star`, `dStar`, `I_m` | `D0KTrialStage1.lean:33,40`, `D0KTrialStage2.lean:24` | EXIST |

### The periodization supplier does not apply to our packet

```lean
theorem Real.fourierCoeff_tsum_comp_add {f : C(ℝ, ℂ)} ...
```

It is stated for `f : C(ℝ, ℂ)` — a **continuous** map. The W2 packet is
deliberately discontinuous: it carries two production endpoint jumps, and W2's
entire variation ledger is built on paying them. So this row cannot discharge
our consumer.

This is not a blocker. The coefficient identity for our object is elementary
for a different reason than continuity: the packet has compact support, so the
periodization is a **finite** sum on any bounded set, and the coefficient
integral does not see the two jumps at all. It must be proved locally.

`grep` over the entire pinned Mathlib returns no `poissonKernel` or
`PoissonKernel` declaration. The kernel is defined locally too, by its closed
form, as the verdict's step 4 anticipates.

## 4. What this preflight closes and what it opens

```
CLOSES: W3_ABEL_LIMIT_PINNED_SUPPLIER_STATUS
        W3_FIRST_DECISIVE_TEST_MATHEMATICAL_CLOSURE
        W3_PERIODIZATION_SUPPLIER_STATUS
        W3_POISSON_KERNEL_SUPPLIER_STATUS
OPENS:  W3_DIRECTIVE_CONFLICT_BETWEEN_TWO_ADMISSION_VERDICTS
```

The one thing it opens is a question to the judge, not a mathematical input.

## 5. Held, pending the judge

I am not opening `G6N1SelectedFerrersAbelPoissonL2.lean` until the directive
conflict is resolved. Under reading A the Lean transaction is authorized and I
proceed immediately; under reading B this file is the whole deliverable. Both
are one message away, and writing Lean now would foreclose the choice for the
judge rather than for me.
