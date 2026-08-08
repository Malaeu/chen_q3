# PROSHKA REQUEST — Goal 057 B3.0G source W02 mode-pairing audit

## 0. Requested decision

Choose exactly one operative next atom after closed B3.0F:

```text
GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY
```

The audit result is deliberately asymmetric:

- the primary source defines the exact endpoint/pole functional
  `W_{0,2}` and proves that its ordered mode entries are the rank-two matrix
  given by equation (4.2);
- production Lean defines the exact scalar formula `ccmW02Entry` from (4.2);
- production Lean does **not** define `W_{0,2}`, `W_{0,2}#`, an endpoint
  moment, or an independent `sourceW02ModePairing` object.

Therefore the source mathematics is present, but the source-side production
object is missing.  Do not accept

```lean
def sourceW02ModePairing i n r :=
  (Q3.RouteB.ccmW02Entry (L_m i) n r : ℂ)
```

as a source construction: that would make the requested crosswalk true by
definition and trigger C10, surrogate-by-formula.

Return exactly one `TRY_`, `KILL_`, or `WALL_` primary code and either release
one smallest production child or name the first missing analytic theorem.
This is one `DELEGATED_STRATEGIC_REVIEW` in the same living Goal-057 phase and
chat.  It is not an owner boundary.

## 1. Immutable control state

```yaml
repo: /Users/emalam/GitHub/rh_lean_01_2026
branch: rh_clean
head: dc2968ccb4302cd8001564868ca54a2453cee3c7
origin_rh_clean: dc2968ccb4302cd8001564868ca54a2453cee3c7
active_goal: 057
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
aristotle_submission: NONE
route_promotion: false
px_rh_claim: NOT_MADE
owner_gate: PX_RH_CLAIM_ONLY
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
parent_transaction: GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
parent_success: GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED
parent_production_sha256: b075be90e7ae6f3cf484e8868683bc642a88be77919a29e9dfafcd63bf5d3d2f
```

Do not implement the prime pairing or complete source Weil form, add an
operator wrapper, decrement the checkpoint ledger, invoke H4a1b, create Bus
010, release Goal 055, unfreeze G2/CCM, submit Aristotle, promote Route B, or
claim PX/RH.

## 2. Primary-source lock

Primary source:

Connes--Consani--Moscovici, *Zeta Spectral Triples*,
arXiv:2511.22755v1:

https://arxiv.org/abs/2511.22755

Pinned e-print:

```text
tmp/pdfs/source_audit/2511.22755v1.eprint
SHA-256 96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a
```

The source fixes all four layers needed by this audit.

### 2.1 Functional

Equations (3.10)--(3.11):

```text
QW(f,g) = Psi(f* * g)
Psi(F) = W_0,2(F) - W_R(F) - sum_p W_p(F)
W_0,2(F) = Fhat(i/2) + Fhat(-i/2)
```

The form is antilinear in the first slot and linear in the second.

### 2.2 One-sided source object

Equations (3.12)--(3.14):

```text
W_0,2#(F) = integral_[1,infinity) F(x) (x^(1/2)+x^(-1/2)) d*x.
```

For production modes, Proposition 3.2 and equation (4.1) use

```text
F(x) = q(U_n,U_m)(log x).
```

Since this mode correlation is supported in `0 <= log x <= L`, the exact
log-coordinate expression is

```text
integral_[0,L] q(U_n,U_m)(y) (exp(y/2)+exp(-y/2)) dy.
```

There is no extra factor two: the one-sided `W_0,2#` is already the object in
equation (4.1).

### 2.3 Exact ordered mode entry

Lemma 4.1, equation (4.2):

```text
W_0,2(V_n,V_m) = W_0,2#(q(U_n,U_m) o log)

  = 32 L sinh(L/4)^2 (L^2 - 16 pi^2 m n)
      / ((L^2 + 16 pi^2 m^2) (L^2 + 16 pi^2 n^2)).
```

The paper explicitly says this contribution is a rank-two matrix.  Symmetry
of the closed real formula does not erase the ordered sesquilinear convention
from which it arose.

### 2.4 Normalization

The source uses

```text
lambda = sqrt(mProject)
L = 2 log(lambda) = log(mProject)
U_n(x) = L^(-1/2) exp(2 pi i n x / L).
```

Production `lambda_m`, `L_m`, `V_n_m` and
`logWindowZeroExtendedMode` use the same normalization.  In particular,
`L_m i = log i.m` and the source mode order remains the literal integer pair
`(n,m)` before the finite map `ccmModeFinite N j = j-N` is applied.

## 3. Exact production inventory

### 3.1 Existing scalar entry

`Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean`

```text
SHA-256 f2f9d248a6f2ad703428c624ccbaf5a75b340655e4b4ebbbe3f1d77355523815
```

defines exactly:

```lean
noncomputable def ccmW02Entry (L : ℝ) (n m : ℤ) : ℝ :=
  32 * L * Real.sinh (L / 4) ^ 2 *
      (L ^ 2 - 16 * Real.pi ^ 2 * (m : ℝ) * (n : ℝ)) /
    ((L ^ 2 + 16 * Real.pi ^ 2 * (m : ℝ) ^ 2) *
      (L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2))
```

This is a literal transcription of source equation (4.2), with codomain
`ℝ`.  The eventual source crosswalk must therefore conclude

```lean
sourceW02ModePairing i n r =
  (Q3.RouteB.ccmW02Entry (L_m i) n r : ℂ)
```

with a positive sign.

### 3.2 Existing source mode construction

`Q3/Proofs/RouteB/D0PstarSourceModeCosineCCMQKernel.lean`

```text
SHA-256 1c39c60492931150d98e25e87e1e4762d4509edd725bd68b68c64c8504cc56a4
```

already constructs the zero-extended normalized modes and their convolution
correlation.  Its public theorem proves, for `0 <= x`,

```lean
2 * integral_t
      conj(Fourier(mode n)(t)) * cos(2*pi*t*x) * Fourier(mode r)(t)
  = if x <= L_m i then
      (ccmQKernel (L_m i) n r x : ℂ)
    else 0.
```

Thus the source `q(U_n,U_r)` profile is already connected to the literal CCM
kernel.  However, the underlying `sourceModeCorrelation` is private and no
public endpoint/pole functional consumes it.

### 3.3 Exact negative inventory result

An exact Route-B declaration scan finds only:

```text
ccmW02Entry
ccmW02Entry_symm
ccmW02Entry_neg_neg
ccmW02Entry_neg_one_one_eq_neg_one_zero
ccmW02Entry_13_seven_class_normal_form
```

There is no production declaration for any of:

```text
W02 functional
W02# functional
sourceW02ModePairing
source endpoint moments at +/- i/2
source W02 finite sesquilinear form
source W02 rank-two factorization
```

Therefore the exact audit stop is:

```text
SOURCE_W02_FUNCTIONAL_PRODUCTION_OBJECT_MISSING
```

and the current route-level stop remains:

```text
GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY_MISSING
```

This is a missing Lean materialization, not a missing primary-source theorem.

## 4. Candidate A — one-sided source-integral pairing

```text
TRY_GOAL057_B3_0G_ONE_SIDED_W02_MODE_PAIRING_PREFLIGHT
```

Materialize one independent source object from (3.14)/(4.1), for example:

```lean
noncomputable def sourceW02ModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ) *
      ((Real.exp (x / 2) + Real.exp (-x / 2) : ℝ) : ℂ)
```

and prove exactly one public crosswalk:

```lean
theorem sourceW02ModePairing_eq_ccmW02Entry
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      (Q3.RouteB.ccmW02Entry (L_m i) n r : ℂ)
```

This is the cheapest visible construction, but Proshka must decide whether
using public `ccmQKernel` in the definition preserves enough source
provenance or merely moves the CCM formula one layer upward.  If selected,
the proof must consume the already-proved source-mode/cosine crosswalk or
otherwise retain a demonstrable source parent.

## 5. Candidate B — rank-two endpoint moments

```text
TRY_GOAL057_B3_0G_RANK_TWO_ENDPOINT_MOMENT_PREFLIGHT
```

Materialize the two source endpoint evaluations of the normalized production
modes, including the center shift from `u` to `x = log(lambda*u)`, then define
the mode pairing as the exact conjugate-first sum of the two outer products.
This construction makes the source's rank-two statement structural rather
than a later algebraic observation.

Proshka must supply or correct the exact Lean definitions and signs.  The
required mathematical content is:

```text
endpointPlus_n  = integral V_n(u) u^(+1/2) d*u
endpointMinus_n = integral V_n(u) u^(-1/2) d*u

W02(V_n,V_r) =
  conjugate(endpointMinus_n) * endpointPlus_r
  + conjugate(endpointPlus_n) * endpointMinus_r
```

This cross orientation follows from
`widehat(f* * g)(s) = conj(widehat f(conj s)) * widehat g(s)` and must still be
checked against the exact Lean endpoint-moment definitions.  Candidate B is
more source-transparent but may require more analytic support than Candidate
A.

## 6. Candidate C — stop the current materialization route

```text
WALL_GOAL057_B3_0G_SOURCE_W02_PAIRING_CONSTRUCTION_NOT_YET_EXECUTABLE
```

Select this only if neither A nor B can be made source-exact with the current
production API.  Name the first missing theorem and one dependency-aware
replacement atom.  Do not replace the source object by an equality premise,
a direct alias of `ccmW02Entry`, or a finite matrix wrapper.

## 7. Mandatory attacks

At minimum adjudicate these errors:

1. direct alias `sourceW02ModePairing := ccmW02Entry`:
   `SURROGATE_BY_FORMULA_NOT_SOURCE_CONSTRUCTION` (`C10`);
2. use `W_0,2` where the mode matrix requires the one-sided `W_0,2#`, thereby
   doubling the entry: `SOURCE_W02_FULL_VS_SHARP_FACTOR_MISMATCH`;
3. omit either `exp(x/2)` or `exp(-x/2)`:
   `SOURCE_W02_ENDPOINT_WEIGHT_MISSING`;
4. replace `L = 2 log lambda` by `log lambda`:
   `SOURCE_W02_LOG_LENGTH_NORMALIZATION_MISMATCH`;
5. collapse the rank-two contribution to rank one:
   `SOURCE_W02_RANK_TWO_STRUCTURE_LOST`;
6. move conjugation away from the first coefficient slot:
   `SOURCE_W02_SESQUILINEAR_SLOT_MISMATCH`;
7. project the source value to `re` instead of proving the explicit
   `ℝ -> ℂ` crosswalk: `SOURCE_W02_COMPLEX_COERCION_MISMATCH`;
8. use symmetry of `ccmW02Entry` as proof of ordered source-slot fidelity:
   `SOURCE_W02_ORDER_DETECTOR_MISSING` (`C04`);
9. infer positivity, the complete Weil form, or an associated operator:
   `SOURCE_W02_COMPONENT_ONLY_BOUNDARY_VIOLATED`;
10. import generated PSD/Step33 support:
    `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`.

The global `n/r` swap of the final closed formula is symmetry-blind and must
not be counted as an orientation plant.  If orientation is tested, use an
independent nonsymmetric endpoint-moment harness or another source object
whose slots remain observable.

## 8. Recommended ruling

Codex recommends Candidate A **only if** the released definition is tied to
the existing source-mode correlation parent and not accepted as an isolated
`ccmQKernel` integral by naming alone.  It is the smallest executable bridge
from source equation (3.14) to the already-pinned equation (4.2).

If that provenance cannot be made load-bearing in one child, choose Candidate
B and release only the first endpoint-moment theorem, not the whole crosswalk.
Candidate C is preferable to a tautological alias.

## 9. Required response schema

```yaml
STATUS: OPEN
PRIMARY: TRY_|KILL_|WALL_
SELECTED_CANDIDATE: A|B|C
RELEASED_ATOM:
FIRST_MISSING_SOURCE_THEOREM:
OWNED_FILE:
EXACT_IMPORTS:
PUBLIC_SURFACE:
PRIVATE_SURFACE:
SOURCE_PARENT_CONSUMED:
RANK_TWO_CONTRACT:
COEFFICIENT_ORDER:
REAL_TO_COMPLEX_CROSSWALK:
MANDATORY_PLANTS:
STOP:
SUCCESS:
NEXT_GAP_AFTER_SUCCESS:
CHECKPOINTS_CLOSED_AFTER_SUCCESS: 0
CHECKPOINTS_REMAINING_AFTER_SUCCESS: 10
PHASE_KEY_CHANGE: false
REUSE_SAME_LIVING_CHAT: true
OWNER_ACTION_REQUIRED: false
SOLE_OWNER_GATE: PX_RH_CLAIM
```

Return a complete `CODEX DIRECTIVE` only if one production child is genuinely
released.  Otherwise return a precise wall and the next discriminator.

## 10. Boundaries

```yaml
FORBIDDEN:
  - define_sourceW02ModePairing_as_ccmW02Entry_alias
  - hide_the_crosswalk_as_a_structure_field_or_premise
  - treat_formula_symmetry_as_ordered_slot_evidence
  - drop_the_one_sided_W02_sharp_normalization
  - collapse_rank_two_to_rank_one
  - alter_L_or_mode_normalization
  - project_the_complex_form_to_its_real_part
  - define_prime_source_pairing
  - define_complete_source_Weil_form
  - add_matrix_or_operator_wrapper
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
  - create_Bus_010
  - release_Goal_055
  - unfreeze_G2_CCM
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_fresh_chat

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```
