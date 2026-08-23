# H2A.4.1B.3C.1.5 — selected Ferrers full-source dual/radical preflight (READ-ONLY)

```yaml
PRIMARY: H2A_4_1B_3C_1_5_SELECTED_FERRERS_FULL_SOURCE_DUAL_RADICAL_PREFLIGHT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict f66a05cd — CODEX DIRECTIVE (REQ-2026-08-22-V)
MODE: READ_ONLY
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: f66a05cd06821e1a04a20ffa6f8b17a75e46be51

OUTCOME_CODE: FULL_SOURCE_DUAL_DEFECT_FOUND_GLOBAL_RADICAL_THEOREM_OPEN

PREFLIGHT_ASK:
  - "./ask.sh \"factor four target radical source Weil form\" — only finite-dimensional finrank-one kernel lemmas (MatrixBilinFormRadical.lean:40, SimpleRadicalSpan.lean:12); nothing about the unwindowed target"
  - "./ask.sh \"explicitCCMLimitH Weil pairing zero\" — only decay/Fourier properties of explicitCCMLimitH; no radical membership theorem"

SOURCE_LOCKS_READ:
  - "sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis (D0PstarSourceWeilSesquilinearForm.lean:88): W_i(S(c), S(d)) = sum_j sum_k star(c_j) * ccmWeilMatFinite(j,k) * d_k — the exact finite source-form crosswalk, star-first convention, NO ambient operator"
  - "sourceCCMFiniteRieszOperator_apply_sourceTrial (D0PstarCCMFiniteRieszOperator.lean:127): finite-carrier semantics only, asserts no compression"
  - "ccmW02Entry_structured_mul / ccmWREntry_structured_mul (via ccmWRIntegrand_structured_mul) / ccmPrimeEntry_structured_mul / ccmQKernel_structured_mul — all PRIVATE, CCMFiniteWeilSourceCommutator.lean:50-183, confirming the verdict's source correction (noted: my 3C.1.4 ask.sh missed them because they are private; private lemmas must be grepped in-file)"
  - "radical machinery on disk: MatrixBilinRadicalQuotientEquiv, QuotientByRadical*, SimpleRadicalSpan, RankOneCorrectionQuotient* — ALL finite-dimensional quotient mechanics; none states radical membership of the unwindowed factor-four target"

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## TEST 1 — EXACT FULL-SOURCE DUAL DEFECT IDENTITY

Claim, for every finite `v : CCMModeFinite N -> C`:

```text
< v , Gamma_k > = W_{i_k}( S(D_k v), S(q_k) ) - a_k * < D_k v , q_k >.
```

Derivation from disk theorems only:

1. `Gamma_k = D_k (M_k - a_k I) q_k` (3B, kernel-checked).
2. `D_k` is the literal REAL mode diagonal, hence self-adjoint for the
   mathlib inner product (conjugate-linear first slot):
   `< v, D_k w > = < D_k v, w >` — coordinate computation, `n_j` real.
3. `< D_k v, M_k q_k > = sum_j sum_k star((D v)_j) * ccmWeilMatFinite(j,k) * (q)_k`
   — and by `sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis` this IS
   `W_{i_k}(S(D_k v), S(q_k))`.  The identifying theorem is named; it lives
   at the finite synthesis level; no ambient associated operator and no
   compression is invoked anywhere (the Riesz-operator file states this
   boundary explicitly in its own docstring).
4. The `a_k` term is the plain inner product.

Star convention checked: `ccmWeilMatFinite` is real symmetric; the star
sits on the first argument in both the crosswalk theorem and the mathlib
inner product — consistent.  P_FULL_SOURCE_1 = 0.99: CONFIRMED — the dual
defect identity closes from existing theorems (a Lean proof would be
assembly, not analysis).

Dual-norm recovery, exact statement:

```text
||Gamma_k|| = sup_{v != 0} |< v, Gamma_k >| / ||v||
```

(finite-dimensional inner-product space; attained at `v = Gamma_k`).

## TEST 2 — EXACT SELECTED VECTOR IDENTITY INSERTED

Using `s_k q_k = t_k (eE_k + gE_k)` WITHOUT division (no `s_k != 0` needed
for the identity itself), linearity of `D_k (M_k - a_k I)` and second-slot
linearity of the mathlib inner product:

```text
s_k * < v, Gamma_k >
  = < v, D_k (M_k - a_k I) (s_k q_k) >
  = t_k * [ W_{i_k}( S(D_k v), S(eE_k + gE_k) ) - a_k * < D_k v, eE_k + gE_k > ].
```

Cast audit: `s_k` is the complex source scale and multiplies inside the
second (linear) slot — no stray conjugation; `t_k` enters as `((sTrial : R) : C)`
exactly as in the 4.1A identity — real positive, so it commutes with the
star convention.  Division by `s_k` is legal only where `s_k != 0` is in
scope (it is, from the ratified chain), giving the dual-norm consequence

```text
||Gamma_k|| = (t_k/|s_k|) * sup_{||v||=1} | W(S(D_k v), S(eE_k + gE_k)) - a_k <D_k v, eE_k + gE_k> |.
```

## TEST 3 — GLOBAL RADICAL PROVENANCE

Searched: both ask.sh sweeps above, the radical-machinery file list, and
the explicitCCMLimitH usage sites.  Result: **there is NO theorem, in the
production tree, stating that the unwindowed factor-four target
`G = E_star(4 * explicitCCMLimitH)` lies in the radical of the full source
Weil sesquilinear form on any specified domain.**

What exists and is NOT accepted (per the directive's own exclusion list):
`Mellin`-level identities (`spectralCCMLimitH_eq_explicitCCMLimitH`,
transform crosswalks), inversion-evenness and two-sided decay
(`E_star_explicitCCMLimitH_inv`, `E_star_norm_bound`), Muntz/E-star image
structure, and physical proximity of the selected trial.  None of these is
a radical statement about the form's nullspace.

The disk radical machinery (`SimpleRadicalSpan`, `MatrixBilinFormRadical`,
`QuotientByRadical*`, `RankOneCorrectionQuotient*`) is finite-dimensional
quotient mechanics parameterized by an ASSUMED kernel structure; it
consumes radical facts, it does not supply this one.

RADICAL INPUT: ABSENT.  P_FULL_SOURCE_2 = 0.80: CONFIRMED.

## TEST 4 — WINDOW/PROJECTION RADICAL DEFECT

Not derivable: there is no global radical theorem to transport (Test 3).
For the record, the four defect sources named by the directive
(restriction to `I_m`; projection `P_m_N`; mode differentiation `D_k`;
zero extension / boundary seams) are each nontrivial, and the mandatory
plant below shows projection alone already breaks radicality in a
two-dimensional example — so even a future global radical theorem arrives
with a load-bearing finite defect ledger (consistent with
P_FULL_SOURCE_3 = 0.90, untested here).

## TEST 5 — FULL SIGNED ERROR CHANNEL UNDER THE 3C.1.2 CONTRACT

Question: is `W(S(D_k v), S(eE_k))` subcritical under the hypothetical
derivative contract WITHOUT splitting into W02/WR/Prime norms?

Honest answer: the full form admits no direct Cauchy–Schwarz — it is not
semidefinite (only bounded below on the shifted domain,
`sourceWeilSesquilinearForm_re_self_lowerBound`), and every disk bound on
the full form routes through the three component continuous forms, i.e.
through exactly the split the directive forbids as a positive route.  The
non-splitting alternative is the spectral meaning of the source Weil form
(the explicit-formula pairing over the zero set); estimating the single
signed pairing on `eE_k` there requires control of the spectral mass of
`S(D_k v)` against `S(eE_k)` — an explicit-formula-grade input that is the
same wall as the prime oscillation estimate, now stated for the ONE
combined form instead of the prime component.  Required functional, named
exactly:

```text
SPECTRAL_OR_OSCILLATORY_BOUND_FOR_THE_FULL_SOURCE_WEIL_PAIRING
  |W_{i_k}(S(D_k v), S(eE_k))| <= C(v) * o(m^{1/4}/L^{3/2})-scale
  uniformly over ||v|| = 1  (the rate that makes Test 6 close),
```

with no component split.  Whether the radical/window-defect route (Test
3/4, once supplied) can bypass it is exactly the open fork of
P_FULL_SOURCE_4 = 0.60 — undecidable from disk facts today.  This
preflight cannot confirm the bypass; it records the dual identity that
makes the question precise.

## TEST 6 — FINAL RATE LEDGER

From Test 2, with the anchor ratio (`t_k^2/normSq(s_k) <= L_k/b^2`
eventually, private kernel-checked helper of H2A.3 — used once):

```text
GammaEnergy_k = ||Gamma_k||^2
  <= (L_k/b^2) * ( sup_{||v||=1} | W(S(D_k v), S(eE_k + gE_k)) - a_k <D_k v, eE_k + gE_k> | )^2.
```

Required threshold `GammaEnergy_k = o(sqrt(m_k)/L_k^2)` therefore reduces
to the dual-sup bound

```text
sup_{||v||=1} | ... | = o( m_k^{1/4} / L_k^{3/2} ).
```

`eta_k` is NOT used in this ledger (it enters only later, in the already
ratified consumer `L*eta*GammaEnergy -> 0`) — no double counting.  The
signed pairing is never replaced by a component sum anywhere above.

## MANDATORY PLANTS

**mellin_target_is_not_a_radical_certificate_plant.**  Take `G = e_0 != 0`
and the identity Hermitian form `B(v,w) = <v,w>`.  Attach to `G` any
transform label whatsoever (call its Mellin image `Xi`).  Then
`B(G,G) = 1 != 0`: the label does not put `G` in the radical.  Inference
from `Mellin(G) = Xi` to radical membership is dead.

**global_radical_not_preserved_by_projection_plant.**  `B = diag(0,1)`,
`G = e_0`: for every `v`, `B(v,G) = conj(v_1)*1*0 + conj(v_0)*0*1 = 0` —
`G` is radical.  Project orthogonally onto `span(e_0+e_1)`:
`P G = (e_0+e_1)/2`.  Then `B(e_0+e_1, P G) = 1/2 != 0` — the projected
vector is NOT radical.  The finite window/projection defect is
load-bearing for any future radical transport.

**component_majorant_is_not_the_full_consumer_plant.**  Reused from the
kernel-checked 4.1A plant family: the combined defect can vanish while
separated action terms remain nonzero (and the 3C.1.4 falsifier gives the
corrected-vs-raw instance).  No component-norm sum is relabeled `Gamma`
anywhere in this report.

## FORBIDDEN CHECK

```yaml
radical_from_mellin_or_evenness: not inferred (Test 3 exclusion list applied; plant 1)
projected_radical_from_global: not inferred (Test 4 deferred; plant 2)
ambient_operator_or_compression: not used (Riesz docstring boundary quoted)
full_pairing_replaced_by_component_opNorms: no (Test 5 names the non-split functional)
gamma_decay_radicality_or_oscillation_as_hypothesis: none added (Test 5 marks them OPEN)
selected_row_schedule_target_scale_rayleigh_altered: no
lean_numerics_aristotle: none
sector_floors_ground_510_RH_bundling: none
```

## PREDICTION CHECK

```text
P_FULL_SOURCE_1 = 0.99: CONFIRMED — dual defect identity closes from
  sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis + real mode diagonal.
P_FULL_SOURCE_2 = 0.80: CONFIRMED — no radical theorem for the factor-four
  target exists on disk; the radical machinery is consumer-side only.
P_FULL_SOURCE_3 = 0.90: NOT TESTED (no global radical to transport); the
  projection plant independently shows the defect would be load-bearing.
P_FULL_SOURCE_4 = 0.60: UNDECIDED — the dual representation is now exact,
  but whether it reduces the prime wall to a window defect needs the
  radical input first; without it the single-pairing bound is
  explicit-formula-grade (Test 5).
LIKELIEST_FAILURE (GLOBAL_RADICAL_DOMAIN_OR_FINITE_WINDOW_PROJECTION_
  DEFECT_GAP): OBSERVED — the radical input is absent, which is exactly
  the named gap.
```

## SUMMARY FOR THE NEXT DIRECTIVE

The dual identity chain (Tests 1-2) is assembly-ready: every ingredient is
an existing kernel-checked theorem, and the reduction of the Gamma
threshold to the dual-sup bound `o(m^{1/4}/L^{3/2})` (Test 6) is exact.
The single missing analytic input on this route is the smallest named gap:

```text
FACTOR_FOUR_TARGET_FULL_SOURCE_RADICAL_OR_WINDOW_DEFECT_IDENTITY
```

— either supplied from the primary source (CCM's own Weil-pairing
statement about the limit target, if one exists with exact domain and
quantifiers: a bounded paper acquisition candidate), or replaced by the
spectral/oscillatory bound of Test 5.

SUCCESS_CODE_RETURNED: FULL_SOURCE_DUAL_DEFECT_FOUND_GLOBAL_RADICAL_THEOREM_OPEN
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
