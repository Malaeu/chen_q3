# STATUS: OPEN — TWO SOURCE-FAITHFUL FRONTS IDENTIFIED; NO EXECUTION OR CLOSURE AUTHORIZED
```yaml
MEMORANDUM: GOAL058_TWO_FRONT_PROOF_ARCHITECTURE
DATE: 2026-08-14

ROLE: MYTHOS_PROOF_ARCHITECTURE_ONLY
ACCEPTANCE_JUDGMENT: false
CODEX_EXECUTION_AUTHORIZED: false
ARISTOTLE_AUTHORIZED: false
G1_CLOSED: false
G3_CLOSED: false
ROUTE_B_PROMOTED: false
RH_CLAIMED: false
ROUTE_STATE: CHALLENGER_NOT_RH
BUS_010: VOID

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  BASE_PROOF_COMMIT: d727e128186bd9506b55d2c3c4e08075bed6fbd0
  DISPATCH_COMMIT: c49171559bb4836c05627cefe98935a784a9f2b8
  DISPATCH_DATE: 2026-08-14

ARSENAL_MANDATE_ACCEPTED: true
ARSENAL_DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839
ARSENAL_CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C12_BOUNDED_POTENTIAL_EXCLUSION

G3:
  ARCHITECTURE_RECOMMENDATION: ROUTE_C_PRIMARY_PSWF_SOURCE_PLUS_EXACT_COEFFICIENT_CROSSWALK
  ROUTE_A_ROLE: SECONDARY_CONSTRUCTIVE_CONTROL
  ROUTE_B_ROLE: FULL_FORMALIZATION_FALLBACK
  FIRST_EXECUTABLE_LEAF: MODE4_FERRERS_PHYSICAL_SCALE_CROSSWALK
  FIRST_MISSING_SOURCE_FACT:
    CLASSICAL_PSWF4_REGULAR_SOLUTION_MATCHES_CURRENT_MINIMAL_LEGENDRE_TAIL_AND_PLUS_PHASE
  CURRENT_STOP: MODE4_FERRERS_ODE_PROVED_MODE0_SELECTION_FOURIER_AND_LEMMA72_MISSING

G1:
  ARCHITECTURE_RECOMMENDATION: LITERAL_COMPLEX_TRIAL_LINE_COMPLEMENT_FLOOR
  PRIMARY_REPRESENTATION: FESHBACH_COMPLEMENT_COERCIVITY
  KRYLOV_ROLE: SECONDARY_MULTIPLICITY_DIAGNOSTIC
  FIRST_EXECUTABLE_LEAF: SOURCE_CCM_COMPLEMENT_FLOOR_FROM_EXACT_GRAM_CERTIFICATE
  UNIFORM_TARGET: SOURCE_CCM_COMPLEMENT_FLOOR_ON_PRECOMMITTED_SCHEDULE
  SAME_TRIAL_CONNECTOR: RESIDUAL_OVER_FLOOR_PLUS_ETA_MARGIN
  CURRENT_STOP: LITERAL_CCM_QUANTITATIVE_SIMPLE_EVEN_GROUND_AND_TRACKING_MISSING

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## 0. Scope and source pins

This memorandum is a **candidate architecture**, not an acceptance verdict. It does not authorize a repository write, a cloud-prover job, a route-state change, or any mathematical closure. `[ABSTRACT][PAPER]`

The authoritative dispatch is pinned at:

- `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/proshka/GOAL058_JOINT_SOURCE_REVIEW_DISPATCH_2026-08-14.txt`
- commit `c49171559bb4836c05627cefe98935a784a9f2b8`.

The authoritative context pack is pinned at:

- `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/proshka/PROSHKA_BRIEF_GOAL058_G1_G3_NEXT_SOURCE_JUDGE_2026-08-14.txt`
- commit `c49171559bb4836c05627cefe98935a784a9f2b8`.

The proof state being reviewed is pinned at:

- branch `rh_clean`;
- commit `d727e128186bd9506b55d2c3c4e08075bed6fbd0`.

The dispatch explicitly fixes two independent open fronts:

```text
G3:
  MODE4_FERRERS_ODE_PROVED_MODE0_SELECTION_FOURIER_AND_LEMMA72_MISSING

G1:
  LITERAL_CCM_QUANTITATIVE_SIMPLE_EVEN_GROUND_AND_TRACKING_MISSING
```

`[ABSTRACT][PAPER]`

### Exact project pins used below

| Object | Exact project pin | Status | Tags |
|---|---|---:|---|
| Mode-four Ferrers ODE constructor | `Q3/Proofs/RouteB/D0Mode4FerrersProlateDifferentialEquation.lean` at `d727e128`; theorem `exists_mode4MatchedNormalizedProlateFerrersRow_of_root` | kernel checked | `[ABSTRACT][LEAN]` |
| Root receiver | `Q3/Proofs/RouteB/D0Mode4HermitianSchurTailEnvelopes.lean` at `d727e128`; theorem `exists_mode4RootFunction_eq_zero_at_four_mul_of_finiteLeft_envelopes` | kernel checked, conditional on two strict envelope signs | `[ABSTRACT][LEAN]` |
| Root function | `Q3/Proofs/RouteB/D0Mode4JacobiRootFunction.lean` at `d727e128`; object `mode4RootFunction` | kernel checked | `[ABSTRACT][LEAN]` |
| Actual-pair boundary | `Q3.RouteB.D0Pstar.IsActualProlateModePair`; target head `exists_actualProlateModePair` | predicate exists; constructor absent | `[ABSTRACT][LEAN]` |
| Literal complex trial line | `Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean` at `d727e128` | kernel checked | `[FINITE_CELL][LEAN]` |
| Exact Feshbach identity | theorem `sourceCCMFiniteMatrix_sub_rayleigh_eq_complexTrialFeshbach` | kernel checked | `[FINITE_CELL][LEAN]` |
| Source-row preflight | `Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean` | real/even phase remains an explicit source obligation | `[FINITE_CELL][LEAN]` |
| Literal CCM matrix | `ccmWeilMatFinite m N` on `CCMModeFinite N` | kernel checked source object | `[FINITE_CELL][LEAN]` |

### Exact external source pins used below

1. **Bonami–Karoui PSWF source package**: A. Bonami and A. Karoui, *Uniform approximation and explicit estimates for the prolate spheroidal wave functions*, arXiv:1405.3676 / Constructive Approximation 43. The paper fixes
   \[
   \mathcal F_c f(x)=\int_{-1}^{1}e^{icxy}f(y)\,dy,
   \qquad
   \mathcal L_c\psi=-\frac d{dx}\bigl((1-x^2)\psi'\bigr)+c^2x^2\psi,
   \]
   and records the PSWF basis, strict eigenvalue ordering, parity, and the fact that \(\psi_n\) has exactly \(n\) interior zeros. `[ABSTRACT][PAPER]`

2. **Slepian–Pollak finite-Fourier source**: D. Slepian and H. O. Pollak, *Prolate Spheroidal Wave Functions, Fourier Analysis and Uncertainty — I*, Bell System Technical Journal 40 (1961), 43–63. The project source dossier pins the finite-Fourier integral equation and nonzero eigenvalue statements at equations (26)–(28), with plus-phase kernel \(e^{icxy}\). `[ABSTRACT][PAPER]`

3. **CCM physical normalization and rate**: Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755, §7. The physical operator is
   \[
   PW_\lambda
   =
   -\partial_u\bigl((\lambda^2-u^2)\partial_u\bigr)
   +(2\pi\lambda u)^2,
   \]
   the dimensionless PSWF parameter is
   \[
   c=2\pi\lambda^2,
   \]
   the selected modes are \(h_{0,\lambda}\) and \(h_{4,\lambda}\), Lemma 7.2 supplies the \(O(\lambda^{-2})\) source comparison, and Lemma 7.3 supplies trial-transform convergence to \(\Xi\). `[COFINAL_FAMILY][PAPER]`

## 1. Registered predictions before new tests

```text
P-G3-1:
  The physical-window rescaling of the already-proved Ferrers ODE is a small,
  non-circular Lean leaf. It should require only chain-rule identities,
  sqrt(m)^2=m, and the definition of mode4JacobiG.

P-G3-2:
  A degree-2 substitute will survive evenness and the ODE but fail the required
  degree-4 zero count and the plus-phase sign. This must be caught by a plant.

P-G3-3:
  The first real source obstruction after physical scaling will be the exact
  identification of the current minimal Jacobi tail with the classical
  regular degree-4 PSWF coefficient row, not another interior-ODE calculation.

P-G1-1:
  The existing exact 3x3 commutator counterexample cannot admit any positive
  literal trial-line complement floor. If a proposed certificate accepts it,
  the certificate is proving a surrogate.

P-G1-2:
  A literal complement-floor certificate is strictly more informative than a
  sector Krylov determinant: it can simultaneously supply simplicity, a
  quantitative gap, and source-line tracking.

P-G1-3:
  The hardest cofinal step will be the uniform analytic reduction from the
  infinite/source arithmetic to replayable finite head certificates, not the
  finite-dimensional min-max consequence.
```

These predictions are registered now. They must be scored without retroactive repair. `[ABSTRACT][CONDITIONAL]`

---

# FRONT G3 — actual degree-0/degree-4 prolate pair

## 2. Route comparison

### Route A — prove source-defined finite-left envelope signs

This route reuses the current root receiver:

```lean
exists_mode4RootFunction_eq_zero_at_four_mul_of_finiteLeft_envelopes
```

It is source-faithful only after the endpoints are fixed from the actual degree-four spectral source. The old diagnostic endpoints
\[
-G+8\sqrt G,\qquad -G+10\sqrt G
\]
are not authorized and must not return. `[ABSTRACT][LEAN]`

**Benefit:** it gives a constructive root inside the current coefficient backend.

**Limit:** even a root does not prove endpoint realization, degree-four selection, mode zero, or the finite-Fourier eigenrelation.

**Role in the proposed architecture:** secondary independent control, not the shortest complete source chain.

### Route B — formalize singular Sturm–Liouville and oscillation theory

This route would construct the finite-interval self-adjoint prolate realization, prove compact/discrete simple spectrum, parity, exact zero count, and simultaneous finite-Fourier diagonalization inside Lean.

**Benefit:** strongest self-contained formal route.

**Cost:** pinned Mathlib does not currently supply the needed infinite-dimensional compact self-adjoint eigenbasis theorem, and the repository has no singular Sturm–Liouville/oscillation library. The route would build a major library before reaching the current local theorem. `[ABSTRACT][LEAN]`

**Role in the proposed architecture:** fallback if the source crosswalk cannot be formalized without recreating the whole spectral theory.

### Route C — pinned primary PSWF theorem plus exact coefficient crosswalk

This is the shortest source-faithful paper chain:

```text
classical PSWF existence/order/parity/zero count/Fourier phase
    ↓ exact scale c = 2πλ²
classical degree-4 Legendre coefficient row
    ↓ exact recurrence + minimal-tail branch crosswalk
current mode4RootFunction root
    ↓ current kernel-checked constructor
current normalized Ferrers function
    ↓ uniqueness and source normalization
classical ψ4 on [-1,1]
    ↓ physical scaling
h4 on [-λ,λ]
```

The same chain is required for degree zero. The two physical modes then populate the unchanged `ProlatePair` and discharge `IsActualProlateModePair`. `[ABSTRACT][PAPER]`

### Architecture recommendation

Use **Route C** as the primary proof architecture. Keep **Route A** as a constructive independent check on the degree-four root. Hold **Route B** as the formalization fallback. This is a recommendation for Proshka’s adjudication, not an acceptance verdict. `[ABSTRACT][CONDITIONAL]`

## 3. Exact source dictionary for G3

The dictionary must be frozen before any theorem is written.

### 3.1 Scale

Let
\[
\lambda=\sqrt m,\qquad
c=2\pi\lambda^2=2\pi m,\qquad
G=c^2=(2\pi m)^2.
\]

The current dimensionless ODE has the form
\[
-(1-x^2)f''(x)+2xf'(x)+Gx^2f(x)
=
(\Lambda+G)f(x).
\]

Therefore the classical degree-four eigenvalue is
\[
\chi_4(c)=\Lambda+G,
\qquad
\Lambda=\chi_4(c)-G.
\]

The analogous degree-zero shift is
\[
\Lambda_0=\chi_0(c)-G.
\]

`[ABSTRACT][PAPER]`

### 3.2 Physical window

For
\[
h(u)=f(u/\lambda),
\qquad |u|<\lambda,
\]
the chain rule gives
\[
h'(u)=\lambda^{-1}f'(u/\lambda),
\qquad
h''(u)=\lambda^{-2}f''(u/\lambda).
\]

Hence
\[
-\bigl(\lambda^2-u^2\bigr)h''(u)
+2uh'(u)
+(2\pi\lambda u)^2h(u)
=
(\Lambda+G)h(u).
\]

This is exactly the expanded CCM operator
\[
-\partial_u\bigl((\lambda^2-u^2)\partial_u\bigr)
+(2\pi\lambda u)^2.
\]

`[ABSTRACT][PAPER]`

### 3.3 Index map

The classical PSWF index is the number of zeros in \((-1,1)\).

```text
ψ0:
  zero interior zeros;
  even;
  first even mode.

ψ2:
  two interior zeros;
  even;
  second even mode.

ψ4:
  four interior zeros;
  even;
  third even mode.
```

Therefore “degree four” means \(\psi_4\), the **third even mode**, never “the second even mode”. `[ABSTRACT][PAPER]`

The project’s concentration-eigenvalue indexing is even-sector indexing:

```text
h0 ↔ chi0
h4 ↔ chi2
```

That map is source locked and must not be changed. `[ABSTRACT][PAPER]`

### 3.4 Plus-phase convention

The finite-Fourier kernel is
\[
\mathcal F_c f(x)=\int_{-1}^{1}e^{icxy}f(y)\,dy.
\]

For the classical phase convention,
\[
\mathcal F_c\psi_n=\mu_n(c)\psi_n,
\qquad
\mu_n(c)=i^n|\mu_n(c)|.
\]

Thus:

```text
n = 0:
  phase +1.

n = 4:
  phase +1.

n = 2:
  phase -1.
```

The degree-2 mode is therefore an exact phase falsifier for a mistakenly selected degree-four mode. `[ABSTRACT][PAPER]`

### 3.5 Normalization

The existing mode-four constructor fixes:

- \(a_0>0\);
- \(\sum_q a_q^2/(4q+1)=1\);
- an exact recurrence row;
- the exact geometric right-tail splice.

The classical mode must be rescaled and signed to this same normalization before equality is asserted. ODE equality “up to scalar” is not enough for `ProlatePair`. `[ABSTRACT][LEAN]`

## 4. G3 theorem chain

### G3.0 — local physical scaling leaf

This is the first theorem small enough to be executable without importing the missing spectral theorem.

Suggested owned file:

```text
Q3/Proofs/RouteB/D0Mode4FerrersPhysicalProlateScaling.lean
```

Suggested definitions:

```lean
noncomputable def mode4PhysicalFerrersSeries
    (mProject : ℕ) (a : ℕ → ℝ) (u : ℝ) : ℝ :=
  mode4FerrersSeries a (u / Real.sqrt mProject)

noncomputable def mode4PhysicalFerrersFirstDerivativeSeries
    (mProject : ℕ) (a : ℕ → ℝ) (u : ℝ) : ℝ :=
  (Real.sqrt mProject)⁻¹ *
    mode4FerrersFirstDerivativeSeries a (u / Real.sqrt mProject)

noncomputable def mode4PhysicalFerrersSecondDerivativeSeries
    (mProject : ℕ) (a : ℕ → ℝ) (u : ℝ) : ℝ :=
  (mProject : ℝ)⁻¹ *
    mode4FerrersSecondDerivativeSeries a (u / Real.sqrt mProject)
```

Suggested theorem head:

```lean
theorem exists_mode4MatchedNormalizedPhysicalProlateRow_of_root
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    ∃ a : ℕ → ℝ,
      0 < a 0 ∧
      Summable (fun q => |a q|) ∧
      Summable (fun q => (a q)^2) ∧
      HasSum (fun q => (a q)^2 / (4 * (q : ℝ) + 1)) 1 ∧
      ContDiffOn ℝ 2
        (mode4PhysicalFerrersSeries mProject a)
        (Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) ∧
      ∀ u ∈ Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        -((mProject : ℝ) - u^2) *
              mode4PhysicalFerrersSecondDerivativeSeries mProject a u +
            2 * u *
              mode4PhysicalFerrersFirstDerivativeSeries mProject a u +
            (2 * Real.pi * Real.sqrt mProject * u)^2 *
              mode4PhysicalFerrersSeries mProject a u =
          (Λ + mode4JacobiG mProject) *
            mode4PhysicalFerrersSeries mProject a u
```

The exact final syntax should be adjusted to the existing derivative API, but the mathematical contract must not change. This theorem consumes an already-existing exact root and proves only the physical scaling. It does not claim root existence, endpoint flux, mode selection, Fourier diagonalization, Lemma 7.2, or G3. `[ABSTRACT][CONDITIONAL]`

### G3.1 — primary-source package head

This is the exact source theorem needed by Route C. It is not currently a bounded Lean task.

```lean
theorem exists_classicalPSWFModes_zero_four
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ (h0 h4 : ℝ → ℝ)
      (chi0 chi4 : ℝ)
      (mu0 mu4 : ℂ),
      -- regular physical-window realization
      ContDiffOn ℝ 2 h0 (Set.Ioo (-lambda) lambda) ∧
      ContDiffOn ℝ 2 h4 (Set.Ioo (-lambda) lambda) ∧
      -- exact physical prolate ODEs
      physicalProlateEigenmode lambda chi0 h0 ∧
      physicalProlateEigenmode lambda chi4 h4 ∧
      -- endpoint realization
      zeroFluxAtEndpoints lambda h0 ∧
      zeroFluxAtEndpoints lambda h4 ∧
      -- source ordering
      zeroCountOn h0 (Set.Ioo (-lambda) lambda) = 0 ∧
      zeroCountOn h4 (Set.Ioo (-lambda) lambda) = 4 ∧
      -- parity and normalization
      Even h0 ∧ Even h4 ∧
      0 < ∫ u in (-lambda)..lambda, h0 u ∧
      0 < ∫ u in (-lambda)..lambda, h4 u ∧
      -- plus-phase finite Fourier
      restrictedPlusFourier lambda h0 = mu0 • h0 ∧
      restrictedPlusFourier lambda h4 = mu4 • h4 ∧
      0 < mu0.re ∧ mu0.im = 0 ∧
      0 < mu4.re ∧ mu4.im = 0
```

This is a **statement-level source package**, not a theorem on disk. Formalizing it from first principles is Route B. Using it in a paper proof requires explicit citations to the pinned primary source chain and does not convert it into Lean evidence. `[ABSTRACT][PAPER]`

### G3.2 — exact coefficient/root crosswalk

This is the central Route-C bridge:

```lean
theorem classicalPSWF4_coefficients_force_mode4Root
    (mProject : ℕ) (hm : 2 ≤ mProject)
    (psi4 : ℝ → ℝ) (chi4 : ℝ)
    (hpsi4 : classicalDegreeFourPSWF
      (2 * Real.pi * (mProject : ℝ)) psi4 chi4) :
    let Λ := chi4 - mode4JacobiG mProject
    mode4RootFunction mProject (4 * mProject) Λ = 0
```

Required proof content:

1. expand \(\psi_4\) in the even Legendre basis;
2. prove the exact current three-term recurrence;
3. prove the classical regular \(L^2\) coefficient row enters the same current minimal right-tail branch;
4. prove the splice coefficient at \(K-1\) is nonzero;
5. prove the finite-left/current-tail matching equation;
6. conclude `mode4RootFunction = 0`.

The smallest missing primary-source fact is therefore not “PSWFs exist”. It is:

```text
CLASSICAL_PSWF4_REGULAR_SOLUTION_MATCHES_CURRENT_MINIMAL_LEGENDRE_TAIL
```

together with the exact plus-phase normalization. `[ABSTRACT][CONDITIONAL]`

### G3.3 — uniqueness identification

```lean
theorem mode4MatchedFerrers_eq_classicalPSWF4
    (mProject K : ℕ) (Λ : ℝ)
    (a : ℕ → ℝ)
    (psi4 : ℝ → ℝ)
    (hCurrent : currentMode4MatchedNormalizedRow mProject K Λ a)
    (hSource : classicalDegreeFourPSWF
      (2 * Real.pi * (mProject : ℝ))
      psi4 (Λ + mode4JacobiG mProject))
    (hSourceNorm : sourceNormalization psi4 a) :
    mode4FerrersSeries a = psi4
```

The equality must use a uniqueness theorem for the regular degree-four solution with the exact source normalization. ODE equality alone is insufficient because the second-order equation has a two-dimensional local solution space. `[ABSTRACT][CONDITIONAL]`

### G3.4 — mode-zero companion

A symmetric source package is required for degree zero. It should not be forced through the mode-four root backend unless the recurrence and tail definitions genuinely specialize.

```lean
theorem exists_mode0MatchedNormalizedPhysicalProlate
    (mProject : ℕ) (hm : 2 ≤ mProject) :
    ∃ (Λ0 : ℝ) (a0 : ℕ → ℝ),
      currentMode0MatchedNormalizedRow mProject Λ0 a0 ∧
      zeroCountOn
        (mode0PhysicalFerrersSeries mProject a0)
        (Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) = 0 ∧
      restrictedPlusFourier ...
```

No theorem currently on disk supplies this object. `[ABSTRACT][CONDITIONAL]`

### G3.5 — unchanged production pair

The final constructor head remains exactly:

```lean
theorem exists_actualProlateModePair
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ P : ProlatePair,
      P.pw.lambda = lambda ∧ IsActualProlateModePair P
```

This theorem must construct the existing record. It must not add fields to `ProlatePair`, and it must not take `IsActualProlateModePair P` as a hypothesis. `[ABSTRACT][CONDITIONAL]`

### G3.6 — CCM rate consumer

After the exact pair exists, consume the source theorem:

```lean
theorem prolateCombination_sub_explicitCCMLimitH_supNorm_le
    (lambda : ℝ) (hlambda : lambda0 ≤ lambda)
    (P : ProlatePair)
    (hP : P.pw.lambda = lambda)
    (hActual : IsActualProlateModePair P) :
    Set.EqOn
      -- exact source interval and normalization
      ... ∧
    ‖prolateCombination P - explicitCCMLimitH‖∞
      ≤ C / lambda^2
```

The constants, window, and exact normalization must be copied from CCM Lemma 7.2. They must not be reconstructed from asymptotic notation. `[COFINAL_FAMILY][PAPER]`

## 5. G3 planted falsifiers and controls

| Plant | Mutation | Expected failure | Discriminator | Tags |
|---|---|---|---|---|
| `G3_SCALE_LINEAR_NOT_QUADRATIC` | replace \(c=2\pi\lambda^2\) by \(2\pi\lambda\) | physical potential fails for \(m\ne1\) | symbolic coefficient comparison of \(u^2h(u)\) | `[ABSTRACT][LEAN]` |
| `G3_DEGREE2_AS_DEGREE4` | substitute \(\psi_2\) | evenness and ODE survive; degree-four selection fails | exact interior zero count \(2\ne4\) and phase \(i^2=-1\) | `[ABSTRACT][PAPER]` |
| `G3_SIGN_FLIP` | replace \(\psi_4\) by \(-\psi_4\) | ODE/zeros/Fourier eigenspace survive; source normalization fails | positive-integral or positive-leading-coefficient normalization | `[ABSTRACT][LEAN]` |
| `G3_EIGENVALUE_SHIFT` | set \(\Lambda=\chi_4\), omitting \(-G\) | current recurrence residual is nonzero | evaluate the \(q=0\) recurrence row or the ODE coefficient | `[ABSTRACT][LEAN]` |
| `G3_LOOSE_PAIR` | fill all old record fields but miss source meaning | old structure passes while actual predicate fails | existing `looseProlatePairPlant_not_actual` | `[ABSTRACT][LEAN]` |
| `G3_TAIL_BRANCH` | use a nonminimal recurrence solution with same local recurrence | interior recurrence passes; regular endpoint branch fails | weighted \(\ell^2\) tail / current Riccati minimality | `[ABSTRACT][CONDITIONAL]` |

## 6. G3 re-representations if Route C is inconclusive

| Representation | Kill power | Cost | What changes | Discriminator |
|---|---:|---:|---|---|
| Primary-source PSWF package + coefficient uniqueness | 5 | 3 | changes from endpoint-sign search to exact source object | exact `classicalPSWF4_coefficients_force_mode4Root` |
| Source-defined envelope signs | 4 | 4 | keeps current root backend and proves a bracket from spectral source bounds | certified lower \(L>0\) and upper \(U<0\) at precommitted endpoints |
| Full singular Sturm–Liouville formalization | 5 | 8 | constructs spectrum, parity, oscillation and Fourier commutation internally | compiled `exists_actualProlateModePair` with no project axioms |

A zero-consistent numerical root result is not a discriminator. The discriminator is exact source identification: zero count, endpoint regularity, minimal-tail branch, and plus-phase eigenrelation. `[ABSTRACT][CONDITIONAL]`

---

# FRONT G1 — literal CCM simple-even ground, gap and tracking

## 7. Choosing the right object

The exact on-disk identity is:

\[
K-aI
=
|q\rangle\langle r|
+
|r\rangle\langle q|
+
Q(K-aI)Q,
\]
where:

```text
q = sourceCCMComplexRow S i
K = sourceCCMFiniteMatrix i
a = sourceCCMFiniteRayleigh S i
r = sourceCCMFiniteResidual S i
Q = I - |q><q|
```

This is theorem:

```lean
sourceCCMFiniteMatrix_sub_rayleigh_eq_complexTrialFeshbach
```

in:

```text
Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean
```

`[FINITE_CELL][LEAN]`

The exact decomposition isolates two independent quantities:

1. **Residual** \(r\): the off-diagonal coupling of the source line.
2. **Complement floor**: coercivity of \(Q(K-aI)Q\) on \(q^\perp\).

That is the correct G1 computing object. `[FINITE_CELL][LEAN]`

### Why the sector Krylov determinant is not the primary object

A nonzero sector Krylov determinant can certify cyclicity or simplicity inside one sector. It does not, by itself, give:

- strict even/odd ground ordering;
- a numerical lower gap;
- source-row overlap with the ground;
- the cofinal ratio needed for tracking.

It remains useful as a secondary multiplicity diagnostic. `[FINITE_CELL][PAPER]`

### Why a discriminant/resultant is not primary

A resultant detects eigenvalue collisions. It does not identify the ground order or provide a quantitative lower separation without additional root-location bounds. Its degree and interval arithmetic cost grow badly with \(N\). `[FINITE_CELL][PAPER]`

### Why Perron/oscillation is not source-faithful here

The literal CCM matrix is not a positive Jacobi matrix. The beta/sign diagnostic already forbids treating the whole object as a Perron matrix without a proved similarity or sign-regular reduction. `[FINITE_CELL][LEAN]`

### Architecture recommendation

Use the **literal complex trial-line complement floor** as the primary object:

\[
\boxed{
Q(K-aI)Q\ge\beta Q,\qquad \beta>0.
}
\]

Here **complement floor** means a positive lower bound for the shifted matrix on vectors orthogonal to the exact source line. It is not the final spectral gap assumed as a hypothesis; it must be produced by a replayable certificate for the literal block. `[FINITE_CELL][CONDITIONAL]`

## 8. Why the complement floor supplies the right consequences

Let \(A=K-aI\), let \(q\) be unit, and let \(Q=I-|q\rangle\langle q|\).

Assume a proved literal inequality
\[
\langle x,Q A Qx\rangle\ge\beta\|Qx\|^2,
\qquad \beta>0.
\]

The compression of \(A\) to \(q^\perp\) has minimum at least \(\beta\). By codimension-one interlacing,
\[
\lambda_2(A)\ge\beta.
\]

Since
\[
\langle q,Aq\rangle=0,
\]
the min-max principle gives
\[
\lambda_1(A)\le0.
\]

Therefore the ground is simple and
\[
\lambda_2(A)-\lambda_1(A)\ge\beta.
\]

If \(\xi_0\) is the normalized ground vector and \(r=Aq\), spectral expansion gives
\[
1-|\langle\xi_0,q\rangle|^2
\le
\frac{\|r\|^2}{\beta^2}.
\]

Thus the same literal source line supplies:

```text
simple ground;
quantitative gap;
ground-to-source-line tracking.
```

`[FINITE_CELL][PAPER]`

This is stronger and more directly aligned with Goal 058 than a bare Krylov determinant.

## 9. G1 exact theorem heads

### G1.0 — define the literal floor predicate

Suggested owned file:

```text
Q3/Proofs/RouteB/CCMProposition59ComplexTrialComplementFloor.lean
```

```lean
def sourceCCMComplexTrialComplementFloor
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (beta : ℝ) : Prop :=
  0 < beta ∧
  ∀ x : CCMModeFinite i.N → ℂ,
    beta *
        ((star (complexTrialLineComplement
            (D0Pstar.sourceCCMComplexRow S i) *ᵥ x)) ⬝ᵥ
          (complexTrialLineComplement
            (D0Pstar.sourceCCMComplexRow S i) *ᵥ x)).re
      ≤
    ((star (complexTrialLineComplement
        (D0Pstar.sourceCCMComplexRow S i) *ᵥ x)) ⬝ᵥ
      (sourceCCMComplexTrialComplementBlock S i *ᵥ x)).re
```

This is a name for the target inequality, not a proof of it. It must not be used as an arbitrary binder in a theorem claimed to close G1. `[FINITE_CELL][CONDITIONAL]`

### G1.1 — first executable leaf: exact Gram-certificate soundness

The first non-circular executable leaf should bind explicit certificate data, not the desired gap/order.

```lean
theorem sourceCCMComplexTrialComplementFloor_of_gramCertificate
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (beta : ℝ)
    (R :
      Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)
    (hbeta : 0 < beta)
    (hgram :
      sourceCCMComplexTrialComplementBlock S i -
          (beta : ℂ) •
            complexTrialLineComplement
              (D0Pstar.sourceCCMComplexRow S i)
        = Rᴴ * R) :
    sourceCCMComplexTrialComplementFloor S i beta
```

This proves a lower envelope from an exact Gram factorization. It does not assume a ground vector, eigenvalue order, gap, or tracking estimate. `[FINITE_CELL][CONDITIONAL]`

For interval data, the exact equality can be replaced by a project-standard replayable lower-envelope certificate:

```lean
theorem sourceCCMComplexTrialComplementFloor_of_verifiedIntervalLDL
    (C : SourceCCMComplementIntervalLDLCertificate S i beta)
    (hC : C.checks = true) :
    sourceCCMComplexTrialComplementFloor S i beta
```

The certificate object must contain the literal source matrix/block enclosures and an exact checker. A numerical eigensolver result is not enough. `[FINITE_CELL][CONDITIONAL]`

### G1.2 — finite-cell spectral consequence

```lean
theorem hermitian_unit_trialLine_complementFloor_gives_ground_gap_tracking
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ)
    (q r : ι → ℂ)
    (a beta : ℝ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (ha : (a : ℂ) = star q ⬝ᵥ (K *ᵥ q))
    (hr : r = K *ᵥ q - (a : ℂ) • q)
    (hbeta : 0 < beta)
    (hfloor :
      ∀ x : ι → ℂ,
        beta *
            ((star (complexTrialLineComplement q *ᵥ x)) ⬝ᵥ
              (complexTrialLineComplement q *ᵥ x)).re
          ≤
        ((star (complexTrialLineComplement q *ᵥ x)) ⬝ᵥ
          ((complexTrialLineComplement q *
              (K - (a : ℂ) • 1) *
              complexTrialLineComplement q) *ᵥ x)).re) :
    ∃ (epsilon : ℝ) (xi0 : ι → ℂ),
      star xi0 ⬝ᵥ xi0 = 1 ∧
      K *ᵥ xi0 = (epsilon : ℂ) • xi0 ∧
      (∀ x : ι → ℂ,
        epsilon * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ (K *ᵥ x)).re) ∧
      (∀ x : ι → ℂ,
        star xi0 ⬝ᵥ x = 0 →
        (epsilon + beta) * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ (K *ᵥ x)).re) ∧
      1 - Complex.normSq (star xi0 ⬝ᵥ q)
        ≤ (star r ⬝ᵥ r).re / beta^2
```

This is a generic finite-dimensional receiver. It is not the arithmetic G1 theorem. Its role is to freeze the exact direction of the needed certificate. `[ABSTRACT][CONDITIONAL]`

### G1.3 — literal specialization

```lean
theorem sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (beta : ℝ)
    (hfloor : sourceCCMComplexTrialComplementFloor S i beta) :
    ∃ (epsilon : ℝ)
      (xi0 : CCMModeFinite i.N → ℂ),
      -- unit lowest eigenvector
      star xi0 ⬝ᵥ xi0 = 1 ∧
      D0Pstar.sourceCCMFiniteMatrix i *ᵥ xi0 =
        (epsilon : ℂ) • xi0 ∧
      -- quantitative spectral isolation
      sourceCCMGroundGapAtLeast
        (D0Pstar.sourceCCMFiniteMatrix i) epsilon beta ∧
      -- exact source-line projective tracking
      1 - Complex.normSq
          (star xi0 ⬝ᵥ D0Pstar.sourceCCMComplexRow S i)
        ≤
      (star (D0Pstar.sourceCCMFiniteResidual S i) ⬝ᵥ
        D0Pstar.sourceCCMFiniteResidual S i).re / beta^2
```

The helper proposition `sourceCCMGroundGapAtLeast` should be defined in terms of the Rayleigh inequality on \(\xi_0^\perp\), not by importing an ordered-eigenvalue API that changes the object. `[FINITE_CELL][CONDITIONAL]`

### G1.4 — evenness from the same source line

Simplicity plus reflection commutation gives a parity eigenvector, but not automatically the even sign. The same trial must exclude the odd branch.

A sufficient connector is:

```lean
theorem sourceCCMFinite_ground_even_of_tracking_etaMargin
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (beta : ℝ)
    (hfloor : sourceCCMComplexTrialComplementFloor S i beta)
    (hmargin :
      Real.sqrt 2 *
          ‖(ccmEtaFinite i.N : CCMModeFinite i.N → ℂ)‖ *
          Real.sqrt
            ((star (D0Pstar.sourceCCMFiniteResidual S i)) ⬝ᵥ
              D0Pstar.sourceCCMFiniteResidual S i).re
        <
      beta *
        Complex.abs
          (star (ccmEtaFinite i.N : CCMModeFinite i.N → ℂ) ⬝ᵥ
            D0Pstar.sourceCCMComplexRow S i)) :
    ∃ (epsilon : ℝ)
      (xi0 : CCMModeFinite i.N → ℝ),
      -- lowest, simple, even, eta-normalizable
      sourceCCMRealEvenNormalizedGroundPackage S i epsilon xi0
```

The exact constant may be sharpened during formalization. The invariant is non-negotiable:

```text
same q;
same residual;
same beta;
eta overlap stays nonzero;
odd ground is therefore impossible.
```

No independently selected real part or fitted phase is allowed. `[FINITE_CELL][CONDITIONAL]`

### G1.5 — cofinal arithmetic target

The true G1 arithmetic theorem must not take the floor as a hypothesis.

```lean
theorem sourceCCMComplementFloor_on_precommitted_schedule
    (S : D0Pstar.ProlateCanonicalSourceData)
    (schedule : ℕ → D0Pstar.PairIndex)
    (hschedule_m :
      Tendsto (fun j => (schedule j).m) atTop atTop)
    (hschedule_N :
      Tendsto (fun j => (schedule j).N) atTop atTop)
    (hschedule_locked :
      Goal058PrecommittedSchedule schedule) :
    ∃ beta : ℕ → ℝ,
      (∀ᶠ j in atTop, 0 < beta j) ∧
      (∀ᶠ j in atTop,
        sourceCCMComplexTrialComplementFloor
          S (schedule j) (beta j)) ∧
      Tendsto
        (fun j =>
          Real.sqrt
            ((star (D0Pstar.sourceCCMFiniteResidual
              S (schedule j))) ⬝ᵥ
              D0Pstar.sourceCCMFiniteResidual
                S (schedule j)).re /
          beta j)
        atTop (𝓝 0)
```

`Goal058PrecommittedSchedule` is a placeholder name for a source-defined schedule contract; the actual project type must be used. The theorem must prove its floor from literal CCM arithmetic, replayable finite head certificates, and a Lean-checked uniform tail reduction. `[COFINAL_FAMILY][CONDITIONAL]`

## 10. Certificate architecture for the cofinal floor

The proposed certificate path is:

```text
literal complement block
    ↓ exact parity/source-preserving unitary or Gram crosswalk
finite head + infinite/large-mode tail
    ↓ analytic tail lower bound
finite corrected Schur/Feshbach head
    ↓ exact Arb/interval LDL lower envelope
positive complement floor beta(j)
```

The finite certificate must use the exact source row and exact complement projector. Replacing \(Q\) by a convenient basis projector without an exact unitary/Gram crosswalk is a **C10 surrogate failure**. `[COFINAL_FAMILY][CONDITIONAL]`

### Verdict semantics

```text
PASS:
  only from a certified lower envelope L >= 0
  for the exact literal corrected matrix.

KILL:
  only from a certified upper envelope U < 0
  for the exact same target inequality.

INCONCLUSIVE:
  failure of LDL, failure of a sufficient penalty, or a zero-straddling
  interval does not prove the floor false.
```

`[FINITE_CELL][ARB_INTERVAL]`

## 11. G1 planted falsifiers and controls

| Plant | Mutation | Required behavior | Discriminator | Tags |
|---|---|---|---|---|
| Existing 3x3 commutator collapse | rank-two commutator holds; ground kernel dimension is two | every \(\beta>0\) floor certificate must fail | exact nonzero vector in \(q^\perp\) with zero quadratic value | `[FINITE_CELL][LEAN]` |
| `goal058FeshbachOrientationPlant_orientation_matters` | reverse `q q*` to `star q ⊗ q` | projection equality must fail | off-diagonal sign | `[FINITE_CELL][LEAN]` |
| `goal058FeshbachResidualSignPlant_mutant_fails` | use \(a q-Kq\) instead of \(Kq-aq\) | Feshbach identity must fail | exact Fin-2 matrix entry | `[FINITE_CELL][LEAN]` |
| Nonunit row plant | omit \(\langle q,q\rangle=1\) | \(Qq=0\) must fail | existing nonunit complement plant | `[FINITE_CELL][LEAN]` |
| Post-hoc trial optimization | change \(q\) with \(N\) after seeing the gap | result must be quarantined as moving-witness diagnostic | precommitted source-row identity | `[COFINAL_FAMILY][PAPER]` |
| Surrogate Gram | certify a basis matrix without exact crosswalk to literal block | certificate must not discharge source floor | equality of quadratic forms for all vectors | `[FINITE_CELL][LEAN]` |
| Sufficient-certificate failure | LDL/penalty checker returns false or straddles zero | classify INCONCLUSIVE, never KILL | independent upper envelope on exact target | `[FINITE_CELL][ARB_INTERVAL]` |

## 12. G1 re-representations if the direct floor is inconclusive

| Representation | Kill power | Cost | What it can prove | Main risk |
|---|---:|---:|---|---|
| Literal trial-line Gram/LDL certificate | 5 | 3 | finite-cell floor, simplicity, gap, tracking | certificate may not stabilize with \(N\) |
| Parity-resolved head/tail Feshbach | 5 | 5 | cofinal floor with exact even/odd structure | difficult analytic tail/coupling estimate |
| Sector Krylov + strict sector order | 3 | 4 | simplicity and parity ordering | still needs separate quantitative gap/tracking |
| Discriminant/resultant | 2 | 5 | collision exclusion | high degree, poor quantitative content |
| Perron/oscillation | 1 | 4 | possible ordering after a new similarity theorem | literal beta signs do not currently support it |

The discriminator for a zero-consistent floor experiment is:

\[
\inf_{\substack{x\perp q\\\|x\|=1}}
\langle x,(K-aI)x\rangle.
\]

A useful computation must produce a certified one-sided envelope for this exact quantity or a mathematically equivalent Schur complement. `[FINITE_CELL][CONDITIONAL]`

---

# 13. Interface between G3 and G1

The two fronts meet at one object only:

\[
q_{m,N}
=
\texttt{sourceCCMComplexRow}\;S\;(m,N).
\]

G3 must prove that this row is produced from the actual source degree-0/degree-4 prolate pair with the exact physical scale, phase, normalization, and finite projection. `[COFINAL_FAMILY][CONDITIONAL]`

G1 must prove, for that same row:

\[
\frac{\|r_{m,N}\|}{\beta_{m,N}}\to0
\]
on one precommitted cofinal schedule, where:

\[
r_{m,N}=(K_{m,N}-a_{m,N}I)q_{m,N},
\]
and \(\beta_{m,N}\) is the literal complement floor. `[COFINAL_FAMILY][CONDITIONAL]`

This gives the clean coupling:

```text
G3:
  proves q is the right source trial and supplies its source convergence/rate.

G1:
  proves the actual finite ground tracks that exact q.

P59:
  transports ground-vector tracking to the entire real-zero approximants.
```

No theorem may use the CCM trial in G3 and a separately optimized trial in G1. That would violate the same-family invariant. `[COFINAL_FAMILY][PAPER]`

---

# 14. Final proposal

## G3

Primary architecture:

```text
pinned classical PSWF source package
→ exact c = 2πλ² physical scaling
→ exact degree-4 Legendre coefficient/minimal-tail crosswalk
→ current root-conditioned Ferrers constructor
→ uniqueness/normalization identification with ψ4
→ degree-zero companion
→ plus-phase finite-Fourier relations
→ unchanged ProlatePair
→ IsActualProlateModePair
→ CCM Lemma 7.2
```

First executable local leaf:

```text
MODE4_FERRERS_PHYSICAL_SCALE_CROSSWALK
```

Exact missing source bridge:

```text
CLASSICAL_PSWF4_REGULAR_SOLUTION_MATCHES_CURRENT_MINIMAL_LEGENDRE_TAIL_AND_PLUS_PHASE
```

`[ABSTRACT][CONDITIONAL]`

## G1

Primary architecture:

```text
exact literal Feshbach decomposition
→ replayable lower-envelope certificate for Q(K-aI)Q on q⊥
→ codimension-one min-max
→ simple ground + gap beta
→ residual/beta projective tracking
→ eta margin + reflection
→ even real normalized ground
→ one cofinal schedule
```

First executable local leaf:

```text
SOURCE_CCM_COMPLEMENT_FLOOR_FROM_EXACT_GRAM_CERTIFICATE
```

Exact cofinal missing theorem:

```text
SOURCE_CCM_COMPLEMENT_FLOOR_ON_PRECOMMITTED_SCHEDULE
```

`[COFINAL_FAMILY][CONDITIONAL]`

No execution is authorized by this memorandum. Proshka must decide whether either proposed leaf is source-faithful and bounded enough for implementation. `[ABSTRACT][PAPER]`

---

# 15. Strongest attacks

## Attack on G3

> A citation to classical PSWF existence does not prove that the current `mode4RootFunction` selects the same coefficient row.

Correct. This is the central Route-C risk. The repair is not another ODE theorem. It is the exact coefficient/minimal-tail theorem:

```text
classical regular ψ4
→ current even Legendre recurrence
→ current minimal right-tail branch
→ current root equation
→ exact source normalization.
```

If this crosswalk cannot be proved without rebuilding singular Sturm–Liouville theory, Route C loses its cost advantage and Route B becomes the honest path. `[ABSTRACT][CONDITIONAL]`

## Attack on G1

> A positive complement floor is just the desired gap rewritten.

Not if the proof object is an exact lower-envelope certificate for the literal block. It becomes circular only if `hfloor` is taken as an unexplained source hypothesis or derived from the desired eigenvalue order. The certificate must come from:

```text
literal entries
+ exact source projection
+ exact head/tail reduction
+ replayable one-sided arithmetic.
```

That is an independent form inequality. `[COFINAL_FAMILY][CONDITIONAL]`

## Attack on the coupled route

> G3 may identify the continuum prolate trial, while G1 certifies a different finite row.

This is fatal. The only legal connector is the literal `sourceCCMComplexRow S i`, with one normalization and one precommitted schedule. No “up to a convenient phase”, real-part replacement, or moving optimized probe is allowed without an exact theorem. `[COFINAL_FAMILY][PAPER]`

---

# 16. Code/agent boundary

```text
CODEX:
  no execution directive from Mythos.

ARISTOTLE:
  not authorized.

PROSHKA:
  may accept, repair, reject, or hold each proposed leaf;
  must retain all nonclaims.

REPOSITORY:
  no write authorized by this memorandum.
```

---

# 17. Meta closeout

**What became smaller?**

```text
G3:
  “construct actual prolate modes”
  became
  “physical scale leaf”
  plus one exact source coefficient/minimal-tail crosswalk.

G1:
  “prove simple-even ground and tracking”
  became
  “certify one literal complement floor”
  plus a residual/floor ratio and eta margin.
```

**What was killed?**

```text
- commutator-only simplicity/gap;
- beta-only determinant as a complete G1 supplier;
- a bare Krylov determinant as a quantitative tracking theorem;
- ψ4 called the second even mode;
- c = 2πλ instead of c = 2πλ²;
- root-conditioned ODE treated as actual-mode existence;
- a source floor replaced by a convenient surrogate matrix.
```

**What must not be tried again?**

```text
- add fields to ProlatePair;
- assume the missing root/order/Fourier/gap as a closure binder;
- optimize the trial after seeing the gap;
- infer KILL from failure of a sufficient certificate;
- combine real-zero facts and convergence facts from different families.
```

**Current smallest named gaps**

```text
G3:
  MODE4_FERRERS_PHYSICAL_SCALE_CROSSWALK

G1:
  SOURCE_CCM_COMPLEMENT_FLOOR_FROM_EXACT_GRAM_CERTIFICATE
```

**Next cheapest decisive tests**

```text
G3:
  symbolic scale plant and degree-2 phase/zero-count plant.

G1:
  run the exact 3x3 commutator-collapse plant through the proposed
  floor checker; it must fail for every beta > 0.
```

**Fate of prior predictions**

```text
Not yet scored.
No new theorem or computation was run in this architecture review.
```

```yaml
iteration:
  target: GOAL058_G1_G3_NEXT_SOURCE_ARCHITECTURE
  status: PROGRESS
  failed_strategy:
    - G3_ROOT_CONDITIONED_ODE_AS_MODE_EXISTENCE
    - G1_COMMUTATOR_ONLY_GAP
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name:
    G3: CLASSICAL_PSWF4_TO_CURRENT_MINIMAL_TAIL_CROSSWALK
    G1: SOURCE_CCM_LITERAL_COMPLEMENT_FLOOR
  invariant_learned:
    - same_source_trial
    - exact_physical_scale
    - exact_plus_phase
    - exact_literal_complement_block
  forbidden_future_move:
    - source_surrogate_swap
    - missing_result_as_closure_binder
    - post_hoc_trial_optimization
  next_decisive_test:
    G3: PHYSICAL_SCALE_AND_DEGREE2_PLANTS
    G1: COMMUTATOR_COLLAPSE_FLOOR_PLANT
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
