# STATUS: OPEN — THE CCM LEMMA 7.3 PORT IS NOT A STRUCTURE FILL; IT HAS ONE SOURCE-NORMALIZATION CROSSWALK, ONE TRUE LEMMA-7.2 WALL, AND SIX EXACT ASSEMBLY FLOORS

```yaml
PRIMARY: CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT_FLOOR_DECOMPOSITION
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-20-D

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: 45fbe6f0dfb1568d9617711d0913d1c1561a8fe3
  TARGET_LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  TARGET_STRUCTURE: CCMLemma73PreAnchorPort
  CODEX_TASK: docs/Codex/TASK_2026-08-20_return_briefing_and_preanchor_inhabitant.md
  PAPER_KEY: CCM-ZST-2025
  PAPER_ID: arXiv:2511.22755
  LOCAL_PDF: docs/routeB_bus/litreview/pdfs/2511.22755.pdf
  USAGE_CARD: docs/routeB_bus/litreview/CCM_ZST_USAGE_CARDS.md
  USAGE_CARD_BLOB: 3013b18024d91e1f39ed188d359ba3f2f0debc15

DELIVERY:
  DOC_ONLY: true
  LEAN_WRITTEN: false
  CODEX_REDIRECTED: false
  ARISTOTLE_CALLED: false

CLOSES:
  - CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT_DECOMPOSITION
  - ARBITRARY_PREANCHOR_DATA_LEMMA73_SURROGATE_ROUTE
OPENS: []

TOP_LEVEL_ADJUDICATION:
  INVALID_TARGET: forall D : SelectedProlatePreAnchorData, CCMLemma73PreAnchorPort D
  VALID_TARGET: CCMLemma73PreAnchorPort selectedFerrersPreAnchorData
  VALID_TARGET_DEPENDS_ON_CODEX_OBJECT: true
  FIELD_P_CONVERGENCE_MUST_BE_PROVED: true
  FIELD_P_CONVERGENCE_MAY_BE_RESTATED_AS_INPUT: false
  PAPER_LEMMA_7_3_STATUS: PAPER_PROVED
  PROJECT_INHABITANT_STATUS: OPEN

CODEX_PACKAGE_CONTRACT:
  REQUIRED:
    - one named selectedFerrersPreAnchorData inhabitant
    - exact index formula and precommitted schedule
    - exact pair formula at every k
    - pair provenance back to exists_modeZero_modeFour_selectedFerrersProductionProlatePair
    - lambda_eq and mCofinal
    - reducible definitions or pair_spec theorems exposing the Ferrers witnesses
  NOT_LOAD_BEARING_FOR_LEMMA73:
    - nCofinal
  BARE_OPAQUE_STRUCTURE_VALUE_SUFFICIENT: false

FLOOR_ORDER:
  - L73_0_SELECTED_FERRERS_PREANCHOR_PROVENANCE
  - L73_1_PROJECT_PAPER_ZERO_MASS_NORMALIZATION
  - L73_2_SELECTED_FERRERS_LEMMA72_RATE
  - L73_3_GWIN_ERROR_DECOMPOSITION
  - L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
  - L73_5_EXPLICIT_LIMIT_MELLIN_EQ_CENTERED_XI
  - L73_6_CLOSED_SUBSTRIP_ERROR_BOUND
  - L73_7_LOCALLY_UNIFORM_TOPOLOGY_PROMOTION
  - L73_8_PORT_INHABITANT_ASSEMBLY

FIRST_BY_COST_AFTER_CODEX: L73_0_SELECTED_FERRERS_PREANCHOR_PROVENANCE
FIRST_GENUINE_ANALYTIC_WALL: L73_2_SELECTED_FERRERS_LEMMA72_RATE
INDEPENDENT_FLOOR_AVAILABLE_NOW: L73_5_EXPLICIT_LIMIT_MELLIN_EQ_CENTERED_XI

MINIMAL_MISSING_IDENTITY:
  name: SELECTED_FERRERS_SCALED_GWIN_ERROR_DECOMPOSITION
  formula: >-
    sourceScale_k * Gwin(h_k, lambda_k, -i z) - centeredXi(z)
    = integral_[lambda_k^-1,lambda_k]
        (E(sourceScale_k*h_k)-E(h))(u) u^(-i z-1) du
      - integral_outside_[lambda_k^-1,lambda_k]
        E(h)(u) u^(-i z-1) du
  exact_source: h_k = prolateCombination (selectedFerrersPreAnchorData.pair k)
  exact_target: h = explicitCCMLimitH

PAPER_TO_PROJECT_RESULT:
  NEW_MATHEMATICAL_HYPOTHESIS_REQUIRED: false
  NEW_PROJECT_THEOREMS_REQUIRED: true
  MAIN_MISSING_PROOF_INFRASTRUCTURE:
    - source-locked formal port of CCM Lemma 7.2 / Meixner-Schaefke Satz 9
    - exact paper/project normalization scalar
    - exact Mellin identification of E(explicitCCMLimitH) with centeredXi
    - explicit zero-extension target-tail term
  PAPER_ALONE_DETERMINES_PROJECT_SOURCE_SCALE: false

CURRENT_COUNTER:
  CLASSICAL_ROUTE: 14
  ROUTE_058: 14
  DELTA_FROM_THIS_VERDICT: 0
  ASSEMBLY_ROW_12: RED

CANDIDATE_REPRESENTATIONS:
  R1_LEMMA72_UNIFORM_SOURCE_RATE:
    rank: PRIMARY
    kill_power: 10/10
    cost: 8/10
    route: formalize the selected n=0/4 spheroidal-to-Hermite O(lambda^-2) rate, then reproduce Lemma 7.3
  R2_DIRECT_WEIGHTED_MELLIN_CONVERGENCE:
    rank: RUNNER_UP
    kill_power: 8/10
    cost: 7/10
    route: bypass sup-norm Lemma 7.2 and prove the exact weighted E/Mellin error tends to zero directly from the Ferrers coefficient representation

DISCRIMINATOR:
  name: STRICT_CLOSED_SUBSTRIP_MELLIN_ERROR
  pass: for every sigma < 1/2, an explicit upper bound tends to zero uniformly on abs(im z) <= sigma
  pointwise_only: INCONCLUSIVE
  bounded_only: INCONCLUSIVE
  sourceScale_chosen_from_desired_limit: REJECT_CIRCULAR

REGISTERED_PREDICTIONS:
  P_L73_1:
    statement: the Codex inhabitant will need one additional pair_spec/provenance theorem before the paper port can unfold cleanly
    probability: 0.72
    fate: PENDING
  P_L73_2:
    statement: sourceScale can be chosen as a fixed nonzero real scalar after exact L2 normalization and positive-integral orientation are exposed
    probability: 0.76
    fate: PENDING
  P_L73_3:
    statement: the dominant formal cost will be the selected Ferrers Lemma-7.2 rate, not the locally-uniform topology assembly
    probability: 0.86
    fate: PENDING
  P_L73_4:
    statement: the literal zero-extended project source requires an explicit beyond-window target-tail term absent from the one-line paper estimate
    probability: 0.82
    fate: PENDING

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

NEXT_LOAD_BEARING_GAP: L73_2_SELECTED_FERRERS_LEMMA72_RATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## ROUTE MAP

### Exact target and the first kill

The current production type is:

```lean
structure CCMLemma73PreAnchorPort
    (D : SelectedProlatePreAnchorData) where
  sourceScale : ℕ → ℂ
  sourceScale_ne : ∀ k, sourceScale k ≠ 0
  convergence :
    TendstoLocallyUniformlyOn
      (fun k z =>
        sourceScale k *
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) z)
      centeredXi atTop centeredCriticalStrip
```

`SelectedProlatePreAnchorData` stores an index, a `ProlatePair`, two cofinality facts, `lambda_eq`, and `MemLp`. It stores no asymptotic relation to the Hermite modes and no transform limit. Therefore a theorem for arbitrary `D` cannot follow from this type. The valid target must mention the exact Ferrers inhabitant constructed from the mode-zero/mode-four production witnesses.

This kills the generic theorem shape

```lean
∀ D : SelectedProlatePreAnchorData,
  CCMLemma73PreAnchorPort D
```

as a **C04/C10 object substitution**. Two values may inhabit the same record while carrying different asymptotic laws. A structure with a `convergence` field is also not evidence that the field has an inhabitant.

The valid final theorem has the shape

```lean
theorem selectedFerrersCCMLemma73PreAnchorPort :
    CCMLemma73PreAnchorPort selectedFerrersPreAnchorData := by
  ...
```

where the exact exported name is taken from the Codex package.

### What the paper actually supplies

The paper gives the following chain.

1. Equation (7.1) defines the explicit packet
   
   \[
   h(x)=\frac{\pi}{2}x^2(2\pi x^2-3)e^{-\pi x^2}.
   \]

2. Equation (7.2) defines
   
   \[
   \mathcal E(f)(u)=u^{1/2}\sum_{n\ge1}f(nu).
   \]

3. Lemma 7.1 identifies the Fourier transform of `k = E(h)` with Riemann's `Xi` and writes `h` as a specific nonzero combination of normalized Hermite modes `h0,h4`.

4. Equations (7.5)--(7.6) define the prolate operator and the trial
   
   \[
   k_\lambda=\mathcal E(h_\lambda),
   \]
   
   where `h_lambda` is the zero-integral line in the span of the prolate modes `h0_lambda,h4_lambda`.

5. Lemma 7.2 proves, after a suitable normalization,
   
   \[
   \sup_{[-\lambda,\lambda]}|h_\lambda-h|\le C\lambda^{-2}.
   \]

6. Lemma 7.3 proves locally uniform convergence of the Fourier transform of `k_lambda` to `Xi` on closed substrips of `|Im z|<1/2`.

The paper explicitly says `h_lambda` is determined only up to a nonzero scalar before the suitable normalization is selected. The project has already selected a different concrete representative:

\[
\operatorname{prolateCombination}(P)
 =\frac{I_4h_0-I_0h_4}{\sqrt{I_0^2+I_4^2}}.
\]

Consequently `sourceScale` is load-bearing. It must be computed from the exact normalization and orientation; it cannot be defined as a scalar whose existence is inferred from the desired convergence.

## FLOOR LEDGER

### L73.0 — `SelectedFerrersPreAnchorProvenance`

```yaml
CHARACTER: PORT_AND_OBJECT_LOCK
CLOSES:
  - SELECTED_FERRERS_PREANCHOR_TO_PRODUCTION_MODE_PAIR
OPENS: []
DEPENDS_ON_CODEX: HARD
STATUS: WAITING_CODEX
PAPER_DERIVABLE_WITHOUT_PROJECT_DATA: false
NEW_INDEPENDENT_PREMISE: false
COST: 1/10
```

Required output:

```text
D_Ferrers.index k = the precommitted production PairIndex;
D_Ferrers.pair k = the exact P returned by
  exists_modeZero_modeFour_selectedFerrersProductionProlatePair;
P.h0 and P.h4 are the selected normalized zero-extended Ferrers modes;
P.pw.lambda = sqrt(m_k) = lambda_m(D_Ferrers.index k).
```

The Codex object must be reducible or expose a theorem such as

```lean
selectedFerrersPreAnchorData_pair_spec
```

for every `k`. An opaque record inhabitant erases the exact witnesses needed by Lemma 7.2 and is insufficient for the next floor.

This floor uses `mCofinal`; `nCofinal` is not consumed by Lemma 7.3. The latter remains cargo for the later Galerkin/selected-family layers.

### L73.1 — `ProjectPaperZeroMassNormalization`

```yaml
CHARACTER: SOURCE_NORMALIZATION_PORT
CLOSES:
  - CCM_LEMMA_7_3_SOURCE_SCALE_DEFINITION
  - CCM_LEMMA_7_3_SOURCE_SCALE_NONZERO
OPENS: []
DEPENDS_ON_CODEX: HARD
STATUS: OPEN_AFTER_L73_0
PAPER_DERIVABLE_WITHOUT_PROJECT_DATA: false
NEW_INDEPENDENT_PREMISE: false
COST: 3/10
```

Define a source-derived scalar

```lean
selectedFerrersLemma73SourceScale : ℕ → ℂ
```

and prove it is nonzero. The proof must use:

- the exact project `I4*h0-I0*h4` orientation;
- `I0>0`, `I4>0`;
- normalization and orthogonality of the selected Ferrers modes;
- the explicit Hermite combination in CCM Lemma 7.1 / equation (7.4).

The likely result is a fixed negative real scalar, but that is a registered prediction, not a locked fact. A `k`-dependent source scale remains legal if it is forced by the exact normalization crosswalk.

Forbidden definition:

```text
choose sourceScale k so that the desired convergence holds.
```

That would define the supplier by its conclusion and instantiate C10.

### L73.2 — `SelectedFerrersLemma72UniformRate`

```yaml
CHARACTER: PAPER_PORT_AND_MAIN_ANALYTIC_WALL
CLOSES:
  - CCM_LEMMA_7_2_SELECTED_FERRERS_UNIFORM_RATE
OPENS: []
DEPENDS_ON_CODEX: HARD
STATUS: OPEN_MAIN_WALL
PAPER_SUPPORT: Lemma_7_2_plus_Meixner_Schaefke_Satz_9
NEW_INDEPENDENT_PREMISE: false_if_formalized
MAY_BE_ADDED_AS_STRUCTURE_FIELD: false
COST: 9/10
```

The exact project statement should be eventual and source-locked:

```lean
∃ C : ℝ, 0 ≤ C ∧
  ∀ᶠ k in atTop,
    ∀ x ∈ Icc
        (-lambda_m (D_Ferrers.index k))
        ( lambda_m (D_Ferrers.index k)),
      ‖selectedFerrersLemma73SourceScale k *
          prolateCombination (D_Ferrers.pair k) x -
        explicitCCMLimitH x‖
      ≤ C * (lambda_m (D_Ferrers.index k))⁻²
```

The existing Ferrers constructor explicitly does not prove CCM Lemma 7.2. Thus the Codex inhabitant does not close this floor.

No new mathematical assumption is needed if the paper theorem and its cited spheroidal asymptotics are formalized. But this is not bookkeeping. The current Lean tree has the exact Ferrers modes and the exact target packet; it does not have the uniform large-`lambda` asymptotic connecting them.

This is the first genuine wall.

### L73.3 — `SelectedFerrersEstarWindowMainError`

```yaml
CHARACTER: ANALYTIC_ASSEMBLY
CLOSES:
  - SELECTED_FERRERS_ESTAR_FINITE_SUM_ERROR
OPENS: []
DEPENDS_ON_CODEX: FULL_SOURCE_AND_LAMBDA
STATUS: OPEN_AFTER_L73_2
NEW_INDEPENDENT_PREMISE: false
COST: 3/10
```

Use linearity of `Gwin` and the Lemma-7.2 rate to control the terms with `n*u <= lambda_k`:

\[
\left|
 u^{1/2}\sum_{nu\le\lambda_k}
   (a_k h_k(nu)-h(nu))
\right|
\le
u^{1/2}\,\delta_k\,\frac{\lambda_k}{u}.
\]

Here `a_k = sourceScale k`, `h_k` is the exact project `prolateCombination`, and `delta_k <= C lambda_k^-2` comes from L73.2.

This floor is elementary after the rate exists. It must not reintroduce a free `Estar`-error hypothesis.

### L73.4 — `ExplicitLimitBeyondSourceWindowTail`

```yaml
CHARACTER: SOURCE_SUPPORT_REPAIR_LEMMA
CLOSES:
  - EXPLICIT_CCM_LIMIT_ESTAR_BEYOND_PROLATE_WINDOW_TAIL
OPENS: []
DEPENDS_ON_CODEX: INDEX_LAMBDA_ONLY
STATUS: OPEN
NEW_INDEPENDENT_PREMISE: false
COST: 4/10
```

The project Ferrers modes are literally zero-extended outside `[-lambda_k,lambda_k]`, whereas `explicitCCMLimitH` is a full Gaussian packet. Therefore the exact difference contains the additional term

\[
 u^{1/2}\sum_{nu>\lambda_k}h(nu).
\]

The printed one-line estimate in Lemma 7.3 does not syntactically display this term under the project's zero-extension convention. The formal port must do one of two things:

1. prove that the paper convention already removes it; or
2. bound it explicitly from the polynomial-Gaussian formula.

The second route is available. The repository already proves strong decay of `explicitCCMLimitH` internally for Poisson summation, but the required moving-threshold `E_star` tail theorem is not exported.

This is a repair lemma, not a new hypothesis and not a claim that Lemma 7.3 is false.

### L73.5 — `ExplicitLimitMellinEqualsCenteredXi`

```yaml
CHARACTER: PAPER_PORT_AND_EXACT_TARGET_CROSSWALK
CLOSES:
  - EXPLICIT_CCM_LIMIT_MELLIN_TO_CENTERED_XI
OPENS: []
DEPENDS_ON_CODEX: NONE
STATUS: PARTIAL_OPEN
PAPER_SUPPORT: Lemma_7_1
NEW_INDEPENDENT_PREMISE: false
COST: 7/10
```

Required identity:

```text
full Mellin transform of E_star explicitCCMLimitH at s = -I*z
= centeredXi z.
```

Already kernel-checked in the project:

- the literal CCM equation-(7.1) packet;
- its plus-phase Fourier invariance;
- Poisson inversion
  `E_star h (u^-1) = E_star h u`;
- strict positivity of its starred sum on `u >= 1`;
- the exact definition of `centeredXi`.

Not found in the audited production tree:

- the final full Mellin/Fourier identity equating this exact `E_star` target to the project `centeredXi`.

Therefore this floor is partially built but not closed. It is independent of the Codex source packet and can be attacked in parallel.

### L73.6 — `ExplicitLimitClosedSubstripOuterTail`

```yaml
CHARACTER: ANALYTIC_TARGET_TAIL
CLOSES:
  - EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
OPENS: []
DEPENDS_ON_CODEX: MCOFINAL_AND_LAMBDA_ONLY
STATUS: OPEN
NEW_INDEPENDENT_PREMISE: false
COST: 5/10
```

For every `sigma < 1/2`, prove uniformly for `|Im z| <= sigma`:

\[
\int_{(0,\lambda_k^{-1})\cup(\lambda_k,\infty)}
  \mathcal E(h)(u)u^{-iz-1}\,du
\longrightarrow 0.
\]

The paper uses Poisson symmetry `k(u)=k(u^-1)` and convergence of the outer integral. The project already has the exact inversion theorem. The missing formal content is uniformity over an entire closed substrip, not merely convergence at one fixed exponent.

No new premise is needed; `mCofinal` and `lambda_eq` provide `lambda_k -> infinity`.

### L73.7 — `SelectedFerrersClosedSubstripMellinConvergence`

```yaml
CHARACTER: QUANTITATIVE_ASSEMBLY
CLOSES:
  - CCM_LEMMA_7_3_SELECTED_FERRERS_CLOSED_SUBSTRIP_CONVERGENCE
OPENS: []
DEPENDS_ON_CODEX: HARD
STATUS: WAITING_ON_L73_2_TO_L73_6
NEW_INDEPENDENT_PREMISE: false
COST: 4/10
```

For `|Im z| <= sigma < 1/2`, the exact project coordinate is

\[
s=-iz,
\qquad
\Re(s)=\Im(z).
\]

The paper estimate then has worst exponent

\[
O(\lambda_k^{-1/2+\sigma}),
\]

which tends to zero. Combine:

- the finite `E_star` main error from L73.3;
- the zero-extension repair from L73.4;
- the exact target identity from L73.5;
- the target outer tail from L73.6.

The result must be a strict uniform estimate on the complete closed substrip, not pointwise convergence for each `z`.

### L73.8 — `SelectedFerrersCCMLemma73PreAnchorPort`

```yaml
CHARACTER: STRICT_TOPOLOGICAL_AND_STRUCTURE_ASSEMBLY
CLOSES:
  - CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT
OPENS: []
DEPENDS_ON_CODEX: HARD
STATUS: WAITING_ON_ALL_PRIOR_FLOORS
NEW_INDEPENDENT_PREMISE: false
COST: 2/10
```

Use compactness to place every compact subset of `centeredCriticalStrip` inside one closed substrip. Promote L73.7 to

```lean
TendstoLocallyUniformlyOn
  (fun k z =>
    selectedFerrersLemma73SourceScale k *
      preAnchorGwinTransformCoordinate
        (D_Ferrers.index k)
        (prolateCombination (D_Ferrers.pair k)) z)
  centeredXi atTop centeredCriticalStrip
```

and construct the record:

```lean
{
  sourceScale := selectedFerrersLemma73SourceScale
  sourceScale_ne := ...
  convergence := ...
}
```

This floor is cheap only after the theorem-bearing floors are complete. Writing it first would merely relocate the target into a structure field and repeat the morning overclaim.

## Does any floor need a new premise not present in the paper?

### Mathematical answer

No additional analytic hypothesis is presently identified.

The paper supplies:

- the exact target packet and target transform;
- the normalized prolate asymptotic through Lemma 7.2;
- the closed-substrip convergence theorem through Lemma 7.3.

The project must still prove that its selected Ferrers objects are those paper objects and must formalize the cited asymptotics. Those are theorems, not hypotheses.

### Formal-project answer

The port does **not** follow from the Codex `D` package alone.

The following are missing theorem suppliers:

```text
project/paper mode normalization;
selected Ferrers Lemma-7.2 rate;
full Mellin identity to centeredXi;
zero-extension target-tail repair;
uniform closed-substrip outer-tail control.
```

If L73.2 is replaced by a field or axiom, the public axiom profile will no longer be the standard triple and the transaction fails.

## Two admissible representations

### R1 — uniform source-rate route

```yaml
KILL_POWER: 10/10
COST: 8/10
```

Port Lemma 7.2 on the exact Ferrers modes, then reproduce the quantitative proof of Lemma 7.3. This is the primary route because it follows the source and exposes every normalization.

### R2 — direct weighted Mellin route

```yaml
KILL_POWER: 8/10
COST: 7/10
```

Use the exact Ferrers coefficient representation to prove directly that

\[
\sup_{z\in K}
|a_kGwin(h_k,\lambda_k,-iz)-\Xi(z)|\to0
\]

without first proving a global sup-norm `O(lambda^-2)` estimate for `h_k-h`. This route is admissible only if it derives the weighted error from source coefficients and does not assume the desired Mellin convergence.

The discriminator for both routes is the same: a strict closed-substrip upper bound tending to zero.

## FINAL PROPOSAL

1. Keep Codex on `SelectedProlatePreAnchorData`; do not redirect it.
2. Require the returned package to expose `pair_spec` provenance. A bare opaque record is not enough.
3. After the Codex gate, close L73.0 and L73.1 first.
4. Attack L73.2 as the first genuine wall.
5. In parallel, formalize L73.5 because it is independent of Codex and already has most of its analytic ingredients in Lean.
6. Do not write the final port record until L73.2, L73.5 and the closed-substrip error ledger are theorems.

The assembly count remains `14/14`. Row 12 turns green only after L73.8 is kernel-green with the standard axiom triple.

## STRONGEST ATTACK

### Objection

> Lemma 7.3 is already proved in the paper. Why not instantiate `P.convergence` immediately and cite it?

### Answer

Because the paper theorem is about a suitably normalized `h_lambda`, defined only up to scalar before normalization. The project expression is the exact source-locked

```text
prolateCombination (D.pair k)
```

with a different explicit normalization and literal zero extension. The paper does not mention `SelectedProlatePreAnchorData`, the project Ferrers constructors, or the project's `centeredXi` definition.

The missing work is precisely the source-to-source crosswalk:

```text
paper h_lambda
= sourceScale_k * project prolateCombination_k,
```

followed by the exact coordinate and target identity. Treating equal theorem interfaces as equal objects is C04. Treating the `convergence` field as its own proof is C10.

A second objection is that the zero-extension tail is negligible and need not be named. Negligible is not zero. The project source is compactly supported while the explicit Gaussian target is not. The exact error decomposition must carry that term before any estimate can erase it.

## CODEX DIRECTIVE

```text
CONTINUE THE CURRENT CODEX TASK ONLY:
  docs/Codex/TASK_2026-08-20_return_briefing_and_preanchor_inhabitant.md

ADD TO THE RETURN REPORT, WITHOUT STARTING LEMMA 7.3:
  - exact exported name of the D inhabitant;
  - exact formulas for D.index and D.pair;
  - one per-index pair_spec theorem or reducibility statement;
  - exact theorem showing the pair comes from
      exists_modeZero_modeFour_selectedFerrersProductionProlatePair;
  - direct Lean command, target build, q3_check and all printed axiom profiles.

DO NOT:
  - add CCMLemma73PreAnchorPort as a field of the data packet;
  - assume the Lemma-7.2 rate;
  - define sourceScale from the desired limit;
  - start N2;
  - alter the precommitted schedule.
```

## META CLOSEOUT

**What became smaller?**

One opaque paper-port red is now nine ordered floors. Only L73.2 is a genuinely new source-asymptotic wall; L73.5 is a classical target crosswalk, and the rest are exact transport or topology.

**What was killed?**

- a generic Lemma-7.3 port for arbitrary `SelectedProlatePreAnchorData`;
- counting a record field as a theorem;
- an unspecified `up to scalar` normalization;
- silently dropping the target tail created by project zero extension.

**What must not be tried again?**

Do not define `P` by copying the paper conclusion into `P.convergence`. Do not call the selected Ferrers pair the paper pair without the normalization theorem. Do not start N2 before both actual inhabitants exist.

**Current smallest named gap:**

```text
L73_0_SELECTED_FERRERS_PREANCHOR_PROVENANCE
```

immediately after the Codex package, followed by the true wall

```text
L73_2_SELECTED_FERRERS_LEMMA72_RATE.
```

**Next cheapest decisive test:**

Inspect the Codex inhabitant's exact reducibility and typecheck the L73.2 theorem statement without proving it. If the pair provenance is erased, repair the package before analytic work.

**Fate of prior predictions:**

The morning prediction that a kernel-green conditional composer did not supply its own `D` and `P` arguments is confirmed. The four predictions registered in this verdict concern future implementation and remain pending.

```yaml
iteration:
  target: CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT
  status: PROGRESS
  failed_strategy: treat_paper_convergence_field_as_project_inhabitant
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_LEMMA72_UNIFORM_RATE
  invariant_learned: paper object, project object, normalization and zero-extension convention are cargo
  forbidden_future_move: generic_D_port_or_convergence_field_restatement
  next_decisive_test: Codex_pair_provenance_then_typecheck_L73_2_statement
```
