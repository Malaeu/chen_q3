```yaml
BASE_HEAD: 961cbeecda9849883f10c5b25b09e61107b35e9b
TASK_ID: H2A_4_1B_3C_1_13_W4_FIXED_K_SHIFTED_ROOT_ENERGY_SOURCE_AND_API_PREFLIGHT
AUTHORIZED_BY: PROSHKA_VERDICT_REQ_2026_08_24_X_W3_ABEL_POISSON_L2_SEMANTIC_ADMISSION_2026-08-24.md
AUTHORIZING_COMMIT: 8fa01d82
MODE: READ_ONLY_MATH_AND_API_PREFLIGHT
LEAN_EDIT: false
NUMERICS: false
ARISTOTLE: false
EXECUTED_BY: LINUX_CLAUDE

OUTCOME: W4_ROUTE_VIABLE_ONE_NAMED_MISSING_LEMMA
CANDIDATE_SELECTED: A_LOG_COORDINATE_FINITE_JUMP_FOURIER_DECAY

CLOSES:
  - W4_DOWNSTREAM_CONSUMER_TYPE_LOCK
  - W4_ADDITIVE_LOG_SOURCE_OBJECT_IDENTIFICATION
  - W4_DISCONTINUITY_ENUMERATION
  - W4_SYMBOL_WEIGHT_CROSSWALK
OPENS:
  - W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA

NEXT_LOAD_BEARING_GAP: W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

# W4 preflight — fixed-`k` shifted root energy

Read-only. No Lean written, no numerics run, no route mutated.

## AUDIT 1 — the exact downstream consumer type, copied not paraphrased

`D0PstarShiftedArchFormDomain.lean:22`:

```lean
noncomputable def sourceArchimedeanShiftedFormDomain
    (i : PairIndex) : Submodule ℂ (H_m i) where
  carrier :=
    {x | MemLp (sourceArchimedeanShiftedWeightedImage i x) 2 volume}
```

with, at line 11 of the same file (private):

```lean
private noncomputable def sourceArchimedeanShiftedWeightedImage
    (i : PairIndex) (x : H_m i) : ℝ → ℂ :=
  fun t : ℝ =>
    (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
      ((sourceLogWindowFourierL2Isometry i x : Lp ℂ 2 volume) : ℝ → ℂ) t
```

So membership is exactly this and nothing else:

```
∫_ℝ  W(t) · |(𝓘_i x)(t)|²  dt  <  ∞ ,      W(t) := sqrtWeight(t)²
```

where `𝓘_i` is the **synthesized** isometry, not an ordinary Fourier integral.
That distinction is the whole content of W1 and is plant 3 below.

## AUDIT 2 — the exact additive-log function

`D0PstarSourceLogWindowFourierIntegralCrosswalk.lean`, public surface:

```lean
noncomputable def sourceLogWindowZeroExtension (i : PairIndex) (x : H_m i) : ℝ → ℂ :=
  Set.indicator (Set.Icc (0 : ℝ) (L_m i))
    (((logWindowL2Equiv i).symm x : Lp ℂ 2 (volume.restrict (Set.Icc 0 (L_m i)))) : ℝ → ℂ)

theorem coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension :
  ⇑(𝓘_i x) =ᵐ[volume] fun t => 𝓕 (sourceLogWindowZeroExtension i x) t
```

The coordinate change is `D0LogWindowVNMCompletenessBridge.lean:148`:

```lean
phi : ℝ → ℝ := fun u => Real.log (lambda_m i * u)
psi : ℝ → ℝ := fun x => Real.exp x / lambda_m i
```

So the W4 object is fixed, with no freedom left:

```
g_k := sourceLogWindowZeroExtension i_k (A_k)     on [0, L_m]
A_k := the W3 limit  selectedFerrersAbelLimit k   pulled into H_m
g_k(x) = A_k(e^x / λ_m) · (Jacobian of the measure-preserving map)
```

`g_k` is the additive-log representative; its **ordinary** Fourier transform
is a.e. the synthesized image, by W1.

## AUDIT 3 — every discontinuity of `g_k`, enumerated

`A_k(u) = E_star(f_k)(u) + ½ f_k(0) √u` on the multiplicative window
`I_m = [λ_m⁻¹, λ_m]`, and `E_star(h)(u) = √u · Σ'_{n≥1} h(n·u)`.

| # | Location | Source | Jump size |
|---|---|---|---|
| 1 | `x = 0` (i.e. `u = λ_m⁻¹`) | window endpoint of the zero extension | `\|A_k(λ_m⁻¹)\|` |
| 2 | `x = L_m` (i.e. `u = λ_m`) | window endpoint of the zero extension | `\|A_k(λ_m)\|` |
| 3 | `u = λ_k / n`, `n ∈ ℕ⁺`, inside `I_m` | `E_star` seam: `f_k(n·u)` crosses the packet endpoint `±λ_k` | `√u · \|f_k(λ_k⁻)\|` |
| 4 | — | shadow term `½ f_k(0) √u` | **none**: `√u` is continuous on `I_m`, `f_k(0)` is a constant |

Row 4 matters and is easy to miss: the C13 shadow contributes **no** new
discontinuity. Every jump comes from the window ends or from `E_star` seams.

The seam set is finite: `n·u = λ_k` with `u ∈ [λ_m⁻¹, λ_m]` forces
`n ∈ [λ_k/λ_m, λ_k·λ_m]`, a bounded integer range. This is the same finiteness
W3 already proved (`selectedSeamIndices`, `selectedSeamSet`); W4 reuses it and
does not reprove it.

**Count for fixed `k`: two endpoint jumps plus finitely many seam jumps.**
Nothing else.

## AUDIT 4 — piecewise absolute continuity, and the one missing lemma

Between consecutive seams the situation is good: on each open subinterval the
sum defining `E_star` is a **finite** sum of translates `f_k(n·u)`, and W2
already proved each translate has bounded variation with the derivative
majorant behind it. Multiplication by `√u` is smooth and bounded on `I_m`,
`λ_m⁻¹ > 0`. The coordinate change `u = e^x/λ_m` is a diffeomorphism on the
compact window with bounded derivative. So on each piece `g_k` is a finite sum
of `C¹`-transported BV pieces.

What W2 gives is `BoundedVariationOn`, which is **not** literally absolute
continuity: a BV function may carry a singular part. For our packet it does not
— it is built from Legendre series with the closed derivative majorant
`|P_n'| ≤ n(n+1)` and weighted summable coefficients, so the derivative exists
pointwise on each piece and is integrable there. But that step is not currently
a theorem in the tree.

Hence the single named gap:

```
W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA

  statement: on each open seam-free subinterval of the selected window, the
  exact packet derivative is integrable, so the packet is absolutely
  continuous there — not merely of bounded variation.

  why not free: BoundedVariationOn allows a singular part; W2 does not exclude
  it. C04: same coordinates, two different laws.

  why cheap: the derivative majorant and the weighted coefficient summability
  are already kernel-green inside W2
  (mode4OrdinaryLegendrePolynomial_derivative_abs_le_closed,
   selected_weighted_summable). What is missing is the assembly, not new
  analysis.
```

This is the honest answer to mandatory audit step 4: **name the smallest
missing derivative-integrability lemma**, which is what this is.

## AUDIT 5 — the fixed-`k` decay bound

With piecewise AC plus finitely many jumps, one integration by parts on each
piece gives, for `t ≠ 0`:

```
𝓕g_k(t) = (1/(2πit)) · [ Σ_j (jump_j) e^{-2πi t x_j}  +  𝓕(g_k')(t) ]
```

`g_k'` is integrable by the lemma above, so `|𝓕(g_k')(t)| ≤ ‖g_k'‖_{L¹}`, and
the jump sum is bounded by the total jump mass. Both are finite and depend on
`k` only. Together with the trivial bound `|𝓕g_k(t)| ≤ ‖g_k‖_{L¹}` near `t = 0`:

```
|𝓕g_k(t)|  ≤  C_k / (1 + |t|),
C_k := max( ‖g_k‖_{L¹},  (Σ_j |jump_j| + ‖g_k'‖_{L¹}) / (2π) ) · 2
```

The constant is explicit in objects that already exist. It is **not** uniform
in `k`, and nothing here claims it is.

## AUDIT 6 — matching the exact project symbol

Do not substitute a nameless logarithmic surrogate. The exact chain is:

`D0PstarShiftedArchSqrtWeight.lean:23`

```lean
noncomputable def sourceArchimedeanShiftedSqrtWeight (t : ℝ) : ℝ :=
  Real.sqrt (sourceArchimedeanMultiplier t + (|Real.log Real.pi| + Real.log 4 + 6))
```

`D0PstarExactArchSymbolLogDomination.lean:30` and `:156`

```lean
def sourceArchimedeanMultiplier (t : ℝ) : ℝ :=
  -Real.log Real.pi + (Q3.digamma ((1/4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ))).re

theorem abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope (t : ℝ) :
    |sourceArchimedeanMultiplier t| ≤
      (|Real.log Real.pi| + Real.log 4 + 7) * vModeLogGrowthEnvelope t
```

`D0PstarVModeLogWeightedL2.lean:21`

```lean
def vModeLogGrowthEnvelope (t : ℝ) : ℝ := 1 + Real.log (2 + |t|)
```

So the weight `W = sqrtWeight²` is dominated by an explicit constant times
`1 + log(2+|t|)`. The consumer integral is therefore majorized by

```
∫_ℝ (1 + log(2+|t|)) · C_k² / (1+|t|)²  dt   <   ∞
```

which converges, because `log` is beaten by any positive power of `(1+|t|)`.

**This is the load-bearing arithmetic of W4, so state where it is tight.** The
`1/(1+|t|)` decay is exactly what a jump discontinuity gives and no better.
Squared it is `1/(1+|t|)²`, integrable with room to spare for a logarithmic
weight — but with **no** room for a weight of order `(1+|t|)^{2s}`, `s ≥ 1/2`.
The archimedean symbol is logarithmic, so W4 passes. A polynomial shifted
weight would not, and the jumps would have to be removed first.

## AUDIT 7 — fixed `k` is not a cofinal rate

`C_k` above contains `‖g_k'‖_{L¹}` and the jump mass, both of which depend on
the packet at index `k` and on `λ_k`. Nothing in W1–W4 controls their growth
in `k`. The judge's own prediction `P_W4_3` at 0.99 says the same, and this
preflight confirms it as a route boundary, not as a defect.

W5 remains the only place a cofinal rate may be claimed.

## MANDATORY PLANTS

```
L2_WITHOUT_LOG_WEIGHTED_ENERGY
  f(t) = 1/((1+|t|) · log(2+|t|)) lies in L² but ∫ log(2+|t|)·|f|² diverges.
  So W3's L² conclusion does not, by itself, give the form-domain membership.
  This is exactly the objection the verdict raises at line 349.

FULL_ENDPOINT_VS_MIDPOINT_SEAM
  At u = λ_k/n the production E_star takes the full endpoint value while the
  midpoint convention takes half. The two differ pointwise on a finite set;
  their L² classes agree. W4 must never identify them pointwise — the jump
  ledger of AUDIT 3 counts full-endpoint jumps.

ORDINARY_FOURIER_VS_SYNTHESIZED_ISOMETRY
  The consumer is stated with the synthesized isometry 𝓘_i, the decay bound is
  proved for the ordinary Fourier integral 𝓕. They are equal only a.e., and
  only by the W1 crosswalk theorem. Since the consumer is an L²/MemLp
  predicate, a.e. equality suffices — but the crosswalk must be cited, not
  assumed. A pointwise consumer would not be dischargeable this way (C04/C10).

FIXED_K_FINITE_NOT_COFINAL_RATE
  C_k is finite for each k and unbounded as far as W1–W4 know. Any statement
  of the form "∃C ∀k" is outside this packet.
```

## VERDICT OF THIS PREFLIGHT

Candidate A (`LOG_COORDINATE_FINITE_JUMP_FOURIER_DECAY`) is viable. Every
input exists in the tree except one named assembly lemma, and the arithmetic
that decides the route — logarithmic weight against `1/(1+|t|)` decay —
converges with margin.

Candidate B (`DIRECT_PIECEWISE_AC_WEIGHTED_ROOT_ENERGY`) is not needed: it
would prove the weighted integral directly in the multiplicative coordinate,
duplicating the coordinate transport that W1 already owns.

Recommended next transaction: close
`W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA` first, as its own small Lean
node, then assemble W4 on top of it. Splitting it out keeps the failing case
visible: if the derivative is not integrable on some piece, the route dies
there and not inside a large file.

## ADDENDUM — pinned API reconnaissance for the named lemma

Added after the main body, in the same read-only tact. No Lean written.

### The pinned IBP theorem does not apply to our object

`Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:822`:

```lean
theorem fourier_deriv {f : ℝ → E}
    (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    𝓕 (deriv f) = fun x ↦ (2 * π * I * x) • (𝓕 f x)
```

`h'f : Differentiable ℝ f` is **everywhere** differentiability. Our `g_k` is
discontinuous by construction — two window-endpoint jumps plus the finite seam
set of AUDIT 3 — so this row cannot discharge our consumer.

**This is the same wall as in W3**, where `Real.fourierCoeff_tsum_comp_add`
required `f : C(ℝ, ℂ)` and the production packet had jumps. The pattern is now
twice observed and worth naming: the pinned Fourier API is stated for the
smooth case, and every production object on this rope carries jumps on purpose,
because the full-endpoint convention is load-bearing.

Consequence for cost: the integration by parts of AUDIT 5 must be done
**piecewise and by hand**, exactly as the periodization coefficient was in W3.
It is not free, but it is the known shape of work, not new analysis.

### What the pin does offer

`Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean` supplies
`AbsolutelyContinuousOnInterval` with a usable algebra: `fun_add`, `fun_neg`,
`fun_sub`, `const_smul`, `const_mul`, `fun_smul`, `fun_mul`, `mono`, `symm`,
and the `ε`-`δ` characterization `absolutelyContinuousOnInterval_iff`.

That closure under sums and products is what the named lemma needs: on a
seam-free subinterval `g_k` is a finite sum of `C¹`-transported packet
translates times `√u`, and each operation in that description has a pinned
closure lemma.

### Revised cost of the named lemma

```
W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA
  previous estimate: assembly only
  revised:           assembly plus a hand-written piecewise IBP, because the
                     pinned fourier_deriv is unusable on a jumping source
  still not:         new analysis; the derivative majorant and the weighted
                     summability remain kernel-green inside W2
```

The recommendation of the main body stands and is strengthened: close this
lemma as its own small node before W4. The hand-written IBP is precisely the
place where a hidden non-integrability would surface, and it should surface in
a small file.
