# Step 1.3 source check — Proposition 5.9 agreement set

```yaml
TASK_ID: MYTHOS_2026-09-03_KILLPLAN_BIND_AND_STEP1_3
DATE: 2026-09-03
REPO: Malaeu/chen_q3
BRANCH: rh_clean
SOURCE_BASE_COMMIT: 2bb8db37baf532b41a502269a2e2d420cb41ca6c
FETCH_HEAD: 2bb8db37baf532b41a502269a2e2d420cb41ca6c
SCOPE: READ_ONLY_SOURCE_CHECK
NO_LEAN_SOURCE: true
NO_NUMERICS: true
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE

NO_AGREEMENT_SET: No checked Lean declaration or cited source statement makes proposition59CCMTransform (ccmL m) N xiR agree with centeredXi on any set having a limit point in centeredCriticalStrip. The only centeredXi occurrence in the direct finite-transform bridge is the scalar anchor centeredXi 0 used to normalize a different tracked transform; equality with centeredXi as a function is not supplied.

P_STEP1_3_NO_STRUCTURAL_AGREEMENT:
  probability: 0.65
  fate: CONFIRMED_WITHIN_CHECKED_SOURCE_SURFACE
  scoring_note: The checked repository revision and primary paper provide no exact finite agreement set. This scores the source-check prediction, not a theorem that no future construction can produce such a set.
```

## 1. Exact repository search

The requested command was run against the refreshed `FETCH_HEAD`:

```text
git grep -n "proposition59CCMTransform" FETCH_HEAD -- q3.lean.aristotle/Q3
```

### Definition and inputs

The definition is at
`q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean:125`:

```lean
def proposition59CCMTransform
    (L : ℝ) (N : ℕ) (xi : CCMModeFinite N → ℝ) : ℂ → ℂ :=
  proposition59RawTransform L (Finset.Icc (-(N : ℤ)) N)
    (proposition59CCMCoefficient N xi)
```

Thus its data are a real length `L`, a finite cutoff `N`, and a real coefficient row
`xi : CCMModeFinite N → ℝ`. For the object in the question, `L = ccmL m` and
`xi = ξ_ℝ` is the finite real ground-eigenvector row. Neither `centeredXi` nor values
of `centeredXi` at interpolation nodes are inputs.

### All direct relations found

The six files returned by the exact symbol search contain these relations:

1. `Proposition59GroundLagrangeZeroSetBridge.lean`
   - `proposition59CCMTransform_eq_mode_sum` (`:130`): exact finite pole-kernel sum.
   - `proposition59CCMTransform_zerosRealOn_of_lagrange` (`:231`): transfers real zeros from `sourceLagrangePolynomial`; it is a zero-set implication, not value agreement with that polynomial or with `centeredXi`.
   - `differentiable_proposition59CCMTransform` (`:329`): the transform is entire.
   - `Proposition59GroundLagrangeZeroSetBridge` (`:341`): under the finite bottom/simple/normalized hypotheses, its zeros are real.
2. `CCMProposition59SourceTrialFeshbachPreflight.lean`
   - `proposition59CCMTransform_eq_phase_mul_complexTransform` (`:214`): conditional pointwise equality to a phase multiple of `proposition59CCMComplexTransform` for the same coefficient row.
   - `sourceCCMProposition59Transform_eq_phase_mul_complexTransform` (`:229`): source-specialized version of that equality.
3. `CCMProposition59ComplexHermitianConnector.lean`
   - `proposition59CCMTransform_sub_sourceProjection_le` (`:198`): a pointwise error bound against a projection-scaled complex source transform.
4. `D0RawTransformRowScaling.lean`
   - `rawFplus_eq_smul_ccmTransform_of_row` (`:62`): conditional pointwise scalar equality between `rawFplus` and the reflected finite ground transform when their coefficient rows agree.
5. `G6N1SelectedFerrersGroundProposition59RealZeros.lean`
   - `selectedFerrersGround_exists_proposition59_zerosRealOn_of_sectorFloors` (`:32`): existence of a real normalized ground representative whose Proposition-59 transform has only real zeros.
6. `G6N1SelectedFerrersTrackedGroundTransform.lean`
   - private `gtt_transform_crosswalk` (`:286`): equality between `sourceOrderedCCMRawTransform` and the reflected Proposition-59 transform for an even row.
   - `selectedFerrersTrackedGroundTransform_realZeros_and_pointwiseTracking_of_sectorFloors` (`:399`) and its pointwise-floor version (`:775`): the tracked transform is a nonzero scalar multiple of the reflected Proposition-59 transform and is bounded pointwise against `centeredPstar`.

The last pair contains `centeredXi 0` only in the normalization scalar

```text
centeredXi 0 / rawFplus k 0
```

and in the resulting error bound. It does not assert equality to `centeredXi z` at
`z = 0`, at interpolation nodes, on a sequence, or on any subset of
`centeredCriticalStrip`.

No theorem found by the requested `FETCH_HEAD` search relates
`proposition59CCMTransform` directly to `centeredXi`, the Riemann `xi`/`Xi` function,
or an agreement set with a limit point. `sourceLagrangePolynomial` is used only to
transfer the property that zeros are real.

### Imported interpolation-lattice suppliers

The exact-symbol results above depend on the following node-evaluation lemmas in
`Proposition59EntireTransform.lean`; they are part of the complete interpolation-node
inventory even though their statements mention the underlying raw transform rather
than the specialized `proposition59CCMTransform` name:

- `proposition59PoleKernel_at_lattice` (`:88`): at a lattice point, only the diagonal
  pole kernel survives;
- `proposition59PoleKernel_at_lattice_sign` (`:104`): the surviving value is
  `L * (-1)^j`;
- `proposition59PoleKernel_sum_at_lattice` (`:114`): the finite kernel sum samples
  exactly the coefficient `v j`, with the same normalization and sign factor;
- `proposition59RawTransform_at_zero` (`:184`): the central raw-transform value is
  `sqrt(L)⁻¹ * (L * v 0)`;
- `proposition59RawTransform_at_zero_eq_sqrt` (`:195`): for `0 < L`, that value
  simplifies to `sqrt(L) * v 0`.

These lemmas establish coefficient-row sampling at the removable Fourier lattice.
They do not identify any sampled coefficient with `centeredXi`, Riemann `xi`/`Xi`,
or values of those functions at the lattice nodes. Thus they supply no agreement set
for the two analytic functions in the question.

## 2. Primary paper: arXiv:2511.22755v1

Primary source checked:
`docs/routeB_bus/litreview/pdfs/2511.22755.pdf`.

Proposition 5.9 is on printed pages 22–23. It defines a compactly supported finite
Fourier-mode function from coefficients `ξ_j` and computes its Fourier transform in
equation (5.25):

```text
ξ̂(z) = 2 L^(-1/2) sin(zL/2) Σ_{j=-N}^N ξ_j / (z - 2πj/L).
```

In Proposition 5.9 itself the coefficients `ξ_j ∈ ℂ` are arbitrary. The removable
lattice values of the Fourier transform are determined by those coefficients, but
the proposition does not identify them with samples of Riemann `ξ`, `Ξ`, or
`centeredXi`.

Classification of the requested alternatives:

- (a) interpolant of Riemann `ξ` at nodes: **no**. Equation (5.25) reconstructs the
  Fourier transform of the finite Fourier-mode expansion; it gives no Riemann-xi
  sampling identity.
- (b) moment-matched object: **no moment-matching statement is made** in Proposition
  5.9 or the ground-vector construction around it.
- (c) operator-defined object with no explicit equality to Riemann `ξ`: **yes, after
  the ground-state specialization**. Theorem 5.10, printed pages 23–24, equations
  (5.26)–(5.27), specializes the coefficient row to an even, normalized eigenvector
  for a simple smallest eigenvalue of the finite Weil matrix. Under those assumptions
  it gives the exact relation
  `detreg(Dlog^(λ,N) - z) = -i λ^(-iz) ξ̂(z)` and concludes that the zeros are real.
  The multiplier `-i λ^(-iz)` is nonconstant in `z`, entire, and zero-free (and has
  unit modulus on the real axis). Those assumptions and conclusions belong to
  Theorem 5.10, not to generic Proposition 5.9.

The later route to Riemann `Ξ` is explicitly asymptotic, not an agreement-set
identity:

- printed page 27 states the proposed two-limit program: first `N → ∞` at fixed
  `λ`, then suitably normalized transforms as `λ → ∞` should converge uniformly on
  closed substrips to Riemann `Ξ`;
- equations (7.5)–(7.6), printed pages 28–29, construct the prolate trial `k_λ`, not
  the actual finite ground eigenvector;
- Lemma 7.3, printed pages 31–32, proves convergence of the Fourier transform of
  `k_λ` to `Ξ` on closed substrips;
- Section 8, printed page 32, says the missing second essential step is to prove that
  `k_λ` approximates a scalar multiple of the true ground eigenvector `ξ_λ`
  sufficiently well to transfer convergence of zeros.

Therefore Lemma 7.3 does not create an exact agreement set for the finite
`proposition59CCMTransform`; it applies to the separate prolate trial object and feeds
an unclosed approximation bridge.

## 3. Identity theorem available in the pinned toolchain

The requested repository grep

```text
git grep -n -i "eqOn_of_preconnected_of_frequently_eq\|AnalyticOn.*eqOn" FETCH_HEAD -- q3.lean.aristotle/Q3
```

returned project uses of the identity-theorem family, including
`CenteredXiZeroNonzero.lean:265`,
`G6N1ExplicitCCMLimitMellinNormalization.lean:720`, and
`MuntzV3/Core.lean:204`. These use the `eventuallyEq` sibling rather than the exact
`frequently_eq` identifier queried in the first alternand.

The pinned Mathlib revision in `q3.lean.aristotle/lake-manifest.json` is
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`inputRev: v4.26.0`). At that exact
revision, `Mathlib/Analysis/Analytic/IsolatedZeros.lean:243` provides:

```lean
AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
```

Its conclusion is `Set.EqOn f g U` from analyticity of both functions on `U`,
`IsPreconnected U`, a point `z₀ ∈ U`, and frequent equality in the punctured
neighborhood `𝓝[≠] z₀`. The closure-set variant immediately below is:

```lean
AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
```

The project separately proves `isPreconnected_centeredCriticalStrip` in
`MontelCenteredCriticalStrip.lean:17`.

These lemmas show that a genuine accumulation agreement set would be decisive. The
missing input is precisely such an equality hypothesis for the finite ground
transform and `centeredXi`; analyticity and preconnectedness alone cannot manufacture
it.

## Verdict

`P_STEP1_3_NO_STRUCTURAL_AGREEMENT` at the preregistered probability `0.65` is
**CONFIRMED_WITHIN_CHECKED_SOURCE_SURFACE**. The finite Proposition-59 transform is
linked to its coefficient row, a Lagrange zero-set transfer, other finite transforms,
and `centeredPstar` through a quantitative tracking bound. It is not linked by exact
values to `centeredXi` on an accumulating set. The identity theorem cannot be applied
without a new exact agreement premise.

This is a source-surface conclusion only. It does not kill the fixed ground family,
promote Route B, or make an RH claim.
