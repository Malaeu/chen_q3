STATUS: OPEN
YAML
PRIMARY: SELECT_B_EXACT_WEIGHTED_SUM_NORMAL_FORM
STATUS_CODE: G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM_SELECTED

PIN_VERIFIED: true
REPO: Malaeu/chen_q3
BRANCH: rh_clean
PIN_FULL_SHA: d3d939bfc02947933d2e0588eb4c335b13b22706
BRANCH_HEAD_EQUALS_PIN: true
COMMIT_MESSAGE: "[MacOS][rh_clean][RouteB] Prove CCM seven-class layout consumer"

CONTEXT_PACK_AUDIT: PASS_FOR_RELEVANT_GATE
CONTEXT_PACK_SHA256: 327425c5b29ee6b8d34c70fa75961d4bde72f1e90d5d0cb9fc4f8b76ff81edde
CONTEXT_PACK_TRUNCATED_AFTER_1200_LINES: true
LAYOUT_SOURCE_SHA256_VERIFIED: 734d65982687768421730bb0277fa9add357d5c520672dbd2224e36dc2592b0f

BOOTSTRAP_FETCHED: true
ARSENAL_MANDATE_ACCEPTED: true
ARSENAL_DUAL_USED:
  - C10_FUNCTIONAL_NOT_SURROGATE

MATHLIB_REV: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
MATHLIB_VERSION: v4.26.0
JUDGE_RERAN_LEAN: false
SCRATCH_PREFLIGHT_SHA256_CLAIMED: e2ea1169ab23ebd306fc1c12db825d765937d05cdbfff018e4e67254e97efde9
SCRATCH_BYTES_AVAILABLE_TO_JUDGE: false

FINITE_VON_MANGOLDT_MATHEMATICS: CLOSED
REUSABLE_PRODUCTION_NORMAL_FORM: OPEN

SELECTED_CANDIDATE: B
TRANSACTION: G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM
STOP: G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM_MISSING
SUCCESS: G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM_PROVED

OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2VonMangoldtNormalForm.lean
SOLE_IMPORT: Q3.Proofs.RouteB.CCMFiniteWeilCell13N2SevenClassLayout
NAMESPACE: Q3.RouteB
PRIMARY_THEOREM: Q3.RouteB.ccmVonMangoldt_sum_Icc_2_13
PUBLIC_THEOREMS: 1
PUBLIC_DEFINITIONS: 0
PRIVATE_HELPERS_PERMITTED: true
PRIVATE_PLANTS_REQUIRED: 3

DIRECT_DOWNSTREAM_CONSUMER: Q3.RouteB.ccmCell13N2_wr_enclosures
RUNNER_UP_LEAF: G2_CCM_054_1_PRIME_ENTRY_13_EXACT_NORMAL_FORM
RUNNER_UP_AUTHORIZED: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 5

REPO_WRITE_AUTHORIZED: false
ARISTOTLE_SUBMISSION_AUTHORIZED: false
GOAL_055: HOLD_055_RATIFIED
GOAL_055_MATERIALIZATION_AUTHORIZED: false
H2A_CLOSED: false
G2_CLOSED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
Evidence audit

The GitHub branch reference rh_clean currently resolves exactly to d3d939bfc02947933d2e0588eb4c335b13b22706. The commit exists with the stated message and parent. [ABSTRACT][PAPER]

The uploaded context pack begins with the expected repository, branch, and short HEAD and records the transition from the seven-class transaction to the finite von-Mangoldt theorem-shape stop. Its full byte SHA-256 is:

327425c5b29ee6b8d34c70fa75961d4bde72f1e90d5d0cb9fc4f8b76ff81edde

The pack is an explicitly truncated 1,200-line capture, not a complete repository export. It is nevertheless sufficient for the relevant commit diff, validation ledger, route state, and hold boundary; the pinned GitHub source was used to check the omitted source dependencies. 

Eingefügter Text

 

Eingefügter Text

 [ABSTRACT][PAPER]

I reconstructed CCMFiniteWeilCell13N2SevenClassLayout.lean byte-for-byte from the pack’s added-file diff. Its SHA-256 is exactly the reported:

734d65982687768421730bb0277fa9add357d5c520672dbd2224e36dc2592b0f

The associated ledger records direct Lean PASS, target build 7746, full build 7817, q3_check PASS, no taint, exactly one public theorem, no public definitions, all three plants firing, and the standard Lean axiom triple. 

Eingefügter Text

 [FINITE_CELL][LEAN]

The bootstrap protocol, arsenal deck, and pending mandate were fetched from rh_clean. The five standing attack-duals are accepted. The [C10 · functional] dual is load-bearing here: the next theorem must prove the exact weighted scalar functional consumed by the prime sum, not stop at a pointwise table and leave the functional assembly open. [ABSTRACT][PAPER]

Status of the finite von-Mangoldt wall

The literal production object is source-locked as

lean
noncomputable def ccmPrimeEntryN1 (mProject : ℕ) (n m : ℤ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 mProject,
    ArithmeticFunction.vonMangoldt k *
      (Real.sqrt (k : ℝ))⁻¹ *
      ccmQKernel (ccmL mProject) n m (Real.log (k : ℝ))

and the full entry orientation is literally

lean
ccmW02Entry - ccmWREntry - ccmPrimeEntryN1

in the same source file. [ABSTRACT][LEAN]

At pinned Mathlib v4.26.0, the necessary exact APIs are present:

lean
ArithmeticFunction.vonMangoldt_apply
ArithmeticFunction.vonMangoldt_apply_pow
ArithmeticFunction.vonMangoldt_apply_prime

with vonMangoldt_apply_pow preserving the base value for a nonzero exponent and vonMangoldt_apply_prime returning Real.log p. [FINITE_CELL][LEAN]

The zero cases are decidable through the exact bounded characterization

lean
isPrimePow_nat_iff_bounded_log_minFac

used by the reported scratch preflight for 6, 10, and 12. [FINITE_CELL][LEAN]

Therefore the distinction is:

Proof availability: closed. The six primes, three proper prime powers, and three zero-support composites are handled by current Mathlib, and the owner reports a direct compiled scratch proof for all twelve points. I did not independently rerun that scratch file because its bytes were not supplied. [FINITE_CELL][LEAN]

Reusable production theorem: open. No public theorem at the pin packages those twelve facts into the complete weighted sum consumed by ccmPrimeEntryN1; the route state correctly remains at theorem-shape selection. [FINITE_CELL][CONDITIONAL]

Thus:

the finite support/value mathematics is closed, but its production normal form is missing.
	​

Candidate comparison
Candidate	Cancellation preservation	Downstream utility	Public surface	Proof risk	Kernel numerics	Verdict
A. Pointwise table	Each value can be exact, but the complete weighted sum and its grouping remain a later case split. A future consumer can still omit a support point or misgroup a coefficient.	Weak. The receiver must enumerate Icc 2 13 again.	Either twelve lemmas or one awkward finite-domain table theorem.	Low.	None.	Reject as too weak. It supplies data, not the scalar functional the consumer requires. [C10 · functional]
B. Generic weighted-sum normal form	Exact. It retains all nine evaluations f 2, f 4, …, f 13; only the equal von-Mangoldt coefficients are factored. No evaluation point is merged or replaced.	High. One specialization gives the literal prime-entry normal form, and the theorem remains reusable for plants and later exact summands.	One theorem; no public definitions.	Low to moderate, already preflighted pointwise.	None. It mentions neither ccmQKernel nor any numerical enclosure.	Select.
C. Direct ccmPrimeEntryN1 13 n m normal form	Exact if written correctly and fully preserves the distinct kernel evaluations.	Highest immediate proximity to the receiver, but only for this one source summand.	One long theorem.	Similar arithmetic risk plus a fragile kernel-heavy right-hand side.	No numerical kernel work, but symbolic kernel syntax is mixed into the discrete arithmetic layer.	Runner-up. After B it is a one-line specialization instead of a second enumeration.

[FINITE_CELL][CONDITIONAL]

Candidate C is not rejected as false and does not violate the kernel-numerics prohibition. It is deferred because it combines two layers that can be separated at no extra public cost:

finite von-Mangoldt arithmetic
→ literal ccmPrimeEntryN1 specialization

Candidate A is rejected more strongly: even if true, it leaves the exact scalar functional open and would force another production transaction or hidden case split.

No fourth shape is smaller in the required sense. Weakening B produces an A-like table that does not close the scalar sum; specializing B produces C and loses reuse. B is the minimal one-theorem hinge between the exact Mathlib values and the literal prime-entry chain. [FINITE_CELL][PAPER]

Selected production surface

Owned file

q3.lean.aristotle/Q3/Proofs/RouteB/
CCMFiniteWeilCell13N2VonMangoldtNormalForm.lean

Sole production import

lean
import Q3.Proofs.RouteB.CCMFiniteWeilCell13N2SevenClassLayout

This keeps the route dependency linear, transitively exposes the literal source object, and avoids importing CCMFiniteWeilLogBounds. The log supplier is unnecessary here because this theorem uses exact symbolic logarithms and proves no rational enclosure. [FINITE_CELL][CONDITIONAL]

Namespace

lean
namespace Q3.RouteB

Exact public theorem

lean
/-- Exact support and value normalization of the complete von-Mangoldt
sum on `Finset.Icc 2 13`. -/
theorem ccmVonMangoldt_sum_Icc_2_13 (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 2 13,
        ArithmeticFunction.vonMangoldt k * f k =
      Real.log 2 * (f 2 + f 4 + f 8) +
      Real.log 3 * (f 3 + f 9) +
      Real.log 5 * f 5 +
      Real.log 7 * f 7 +
      Real.log 11 * f 11 +
      Real.log 13 * f 13 := by
  ...

[FINITE_CELL][CONDITIONAL]

The production surface is exactly:

public theorems:    1
public definitions: 0

Private helper lemmas are permitted. The preferred implementation uses local have facts for the twelve point values, exactly three named private plants, and optionally one private compile-only specialization check against the literal ccmPrimeEntryN1 summand. No pointwise value theorem becomes public.

Why this preserves the source object and orientation

Specialize B with

lean
fun k =>
  (Real.sqrt (k : ℝ))⁻¹ *
    ccmQKernel (ccmL 13) n m (Real.log (k : ℝ))

Then the source definition is obtained by reassociation only:

lean
have hPrime :=
  ccmVonMangoldt_sum_Icc_2_13
    (fun k =>
      (Real.sqrt (k : ℝ))⁻¹ *
        ccmQKernel (ccmL 13) n m (Real.log (k : ℝ)))

-- In a target with the explicit grouped right-hand side:
simpa [ccmPrimeEntryN1, mul_assoc] using hPrime

The resulting log-2 class still contains three different terms:

sqrt(2)⁻¹  · qKernel(..., log 2)
sqrt(4)⁻¹  · qKernel(..., log 4)
sqrt(8)⁻¹  · qKernel(..., log 8)

and similarly the log-3 class retains separate k = 3 and k = 9 evaluations. No qKernel argument is collapsed to a class representative. [FINITE_CELL][LEAN]

The later receiver keeps its literal orientation

ccmW02Entry - ccmPrimeEntryN1 - tauUpper ≤ ccmWREntry
ccmWREntry ≤ ccmW02Entry - ccmPrimeEntryN1 - tauLower

exactly as written in ccmCell13N2_wr_enclosures; B rewrites the positive object ccmPrimeEntryN1 without moving it across an inequality or changing its minus sign. [FINITE_CELL][LEAN]

Local implementation sketch

Open BigOperators, enter Q3.RouteB, and use a noncomputable section.

Prove six local prime facts using:

lean
ArithmeticFunction.vonMangoldt_apply_prime

for 2, 3, 5, 7, 11, and 13, with primality discharged by norm_num.

Prove the three proper prime-power facts by exact rewrites:

4 = 2^2
8 = 2^3
9 = 3^2

followed by:

lean
ArithmeticFunction.vonMangoldt_apply_pow
ArithmeticFunction.vonMangoldt_apply_prime

Prove the zero facts for 6, 10, and 12 using:

lean
ArithmeticFunction.vonMangoldt_apply
isPrimePow_nat_iff_bounded_log_minFac
interval_cases

exactly as in the compiled scratch preflight. Do not prove zero by an unverified primality tactic or a numerical oracle.

Expand the fixed Finset.Icc 2 13 with ordinary norm_num/simp, rewrite the twelve local values, and close the remaining commutative-ring identity with ring.

Instantiate the theorem privately with the literal prime-entry weight and confirm that simpa [ccmPrimeEntryN1, mul_assoc] produces the intended source specialization. Do not unfold ccmQKernel.

No Aristotle call is useful or authorized. This is fixed finite arithmetic already supported by current Mathlib. [FINITE_CELL][CONDITIONAL]

Load-bearing plants
P-VM-1 — prime-power multiplicity

Instantiate the public theorem with

lean
fun k => if k = 8 then (1 : ℝ) else 0

and prove that the complete source sum is Real.log 2, together with Real.log 2 ≠ 0.

Registered mutant: remove f 8 from the log-2 class.

Required fate: the plant fails because the mutant forces 0 = Real.log 2, while Real.log 2 > 0. This detects omission of the third 2-power rather than merely checking that 2 itself is prime. [FINITE_CELL][LEAN]

P-VM-2 — zero support

Instantiate with

lean
fun k => if k = 6 then (1 : ℝ) else 0

and prove that the complete source sum is 0.

Registered mutant: add Real.log 2 * f 6 to the right-hand side.

Required fate: the plant fails because 6 is not a prime power and its literal von-Mangoldt coefficient is zero. This detects accidental replacement of prime-power support by “has a prime divisor” support. [FINITE_CELL][LEAN]

P-VM-3 — equal coefficient grouping

Instantiate with

lean
fun k =>
  if k = 3 then (1 : ℝ)
  else if k = 9 then -1
  else 0

and prove that the complete source sum is 0, together with Real.log 3 ≠ 0.

Registered mutant: replace

lean
Real.log 3 * (f 3 + f 9)

by

lean
Real.log 3 * (f 3 + 2 * f 9)

or any exponent-weighted coefficient.

Required fate: the plant fails because vonMangoldt (3^2) = vonMangoldt 3 = Real.log 3; the exponent is not a multiplicity factor. [FINITE_CELL][LEAN]

These plants mutate three distinct facts: inclusion of a higher prime power, exclusion of a non-prime-power composite, and equality of the coefficients inside a prime-power class.

Validation contract

Run from the repository root:

Bash
cd q3.lean.aristotle

lake env lean \
  Q3/Proofs/RouteB/CCMFiniteWeilCell13N2VonMangoldtNormalForm.lean

lake build \
  Q3.Proofs.RouteB.CCMFiniteWeilCell13N2VonMangoldtNormalForm

lake build

cd ..

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2VonMangoldtNormalForm.lean

Taint and surface gates:

Bash
rg -n \
  '\bsorry\b|\badmit\b|exact\?|\bnative_decide\b|\bopaque\b|\bFloat\b|of_decide_eq_true|^[[:space:]]*axiom\b' \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2VonMangoldtNormalForm.lean

rg -n \
  '^(theorem|lemma|def|noncomputable def|abbrev|structure|class)[[:space:]]' \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2VonMangoldtNormalForm.lean

git diff --check
git status --short

Axiom gate, using a temporary checker rather than adding validation output to the production file:

Bash
cat >/tmp/CCMFiniteWeilCell13N2VonMangoldtNormalFormAxioms.lean <<'EOF'
import Q3.Proofs.RouteB.CCMFiniteWeilCell13N2VonMangoldtNormalForm
#print axioms Q3.RouteB.ccmVonMangoldt_sum_Icc_2_13
EOF

cd q3.lean.aristotle
lake env lean \
  /tmp/CCMFiniteWeilCell13N2VonMangoldtNormalFormAxioms.lean

Required output:

[propext, Classical.choice, Quot.sound]

The report must include the exact direct/target/full command results and observed job counts; no job count should be inferred or silently copied from the previous node. [FINITE_CELL][CONDITIONAL]

Direct consumer and runner-up

The direct downstream consumer remains:

lean
Q3.RouteB.ccmCell13N2_wr_enclosures

B removes the complete finite support/value enumeration from that proof while leaving all kernel, W02, WR, integral, and final cancellation work open. It therefore closes only the discrete von-Mangoldt wall. [FINITE_CELL][CONDITIONAL]

The sole named runner-up leaf is:

G2_CCM_054_1_PRIME_ENTRY_13_EXACT_NORMAL_FORM

Its intended public theorem would be candidate C, obtained from B by the literal specialization above. It is not authorized in this adjudication. If the final receiver can consume B directly, the runner-up may later be killed as unnecessary rather than materialized.

Strongest attack

The strongest objection is:

Candidate C is logically weaker, has the same one-theorem public surface, and is closer to ccmCell13N2_wr_enclosures. Why is B called smaller?

C is weaker as a proposition, but not smaller as a reusable production boundary. It repeats the twelve-value arithmetic inside a long kernel-specific right-hand side and entangles two independent review surfaces:

support/value correctness
kernel summand transcription

B proves exactly the linear functional that determines C. Its arbitrary f quantifier is not speculative generalization; it is the minimal abstraction that keeps the nine distinct summand evaluations while factoring only the six exact coefficients. The proof cost is the same fixed twelve-case computation, and C follows by one source-locked specialization.

The mandatory private literal-specialization check prevents B from drifting into an unused generic library lemma. Thus B is both reusable and demonstrably wired to ccmPrimeEntryN1. [FINITE_CELL][PAPER]

Hold and route boundary

The selected theorem proves no inequality and no enclosure. It does not touch:

ccmQKernel numerics
pi or trigonometric values
sqrt/log rational bounds
reciprocal log 13
ccmW02Entry
ccmWREntry
the integral
the seven endpoint pairs
the final cell

The repaired log supplier remains only a later coefficient supplier. The seven-class theorem plus the selected weighted-sum theorem still do not integrate ccmCell13N2_wr_enclosures or discharge its analytic hole.

Therefore:

GOAL_055                  HOLD_055_RATIFIED
ARISTOTLE_SUBMISSION      NONE
ROUTE                     CHALLENGER / NOT_RH
BUS_010                   VOID
H2A_CLOSED                false
G2_CLOSED                 false
ROUTE_PROMOTION           false
RH_CLAIM                  false

The context pack’s hold condition remains unchanged. 

Eingefügter Text

 [ABSTRACT][PAPER]

Meta closeout

What became smaller?

twelve point values plus a future sum case split

has been compressed to one exact scalar identity:

lean
ccmVonMangoldt_sum_Icc_2_13

What was killed?

A as the selected transaction: exact but too weak.

C as the first transaction: exact but prematurely source-specific.

twelve public value lemmas.

another interval_cases enumeration hidden inside the broad receiver.

What must not be tried again?

Do not replace prime-power support by prime-only support.

Do not weight p^r by r * log p.

Do not combine f 2, f 4, and f 8 into one representative evaluation.

Do not import or overclaim the log supplier.

Do not unfold or numerically enclose ccmQKernel.

Do not move the prime term across the frozen subtraction orientation.

Current smallest named gap

G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM_MISSING

Next cheapest decisive test

Compile the one theorem, instantiate its three precommitted test functions, and run the three semantic mutants.

Fate of prior predictions

finite von-Mangoldt normalization is the runner-up after seven-class layout:
  CONFIRMED.

current Mathlib can discharge all twelve exact values:
  SUPPORTED BY PINNED API AUDIT AND OWNER-REPORTED SCRATCH PREFLIGHT.

a pointwise table is the minimal reusable consumer:
  REFUTED; the exact weighted functional is the minimal reusable consumer.
YAML
iteration:
  target: finite_von_Mangoldt_normalization_for_CCM_cell_13_2
  status: OPEN
  failed_strategy: expose_pointwise_table_before_scalar_functional
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM_MISSING
  invariant_learned: retain_every_supported_evaluation_and_factor_only_equal_von_Mangoldt_coefficients
  forbidden_future_move: inline_the_twelve_cases_into_ccmCell13N2_wr_enclosures
  next_decisive_test: compile_weighted_sum_theorem_and_fire_three_semantic_mutants
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
MODE: STAGED_OWNER_GATED
EXECUTION_AUTHORIZED_NOW: false
REPO_WRITE_AUTHORIZED: false
COMMIT_AUTHORIZED: false
PUSH_AUTHORIZED: false
ARISTOTLE_SUBMISSION: NONE

TARGET:
  G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM

STOP:
  G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM_MISSING

SUCCESS:
  G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM_PROVED

ON_OWNER_RELEASE_ONLY:

  OWNED_FILE:
    q3.lean.aristotle/Q3/Proofs/RouteB/
    CCMFiniteWeilCell13N2VonMangoldtNormalForm.lean

  SOLE_IMPORT:
    Q3.Proofs.RouteB.CCMFiniteWeilCell13N2SevenClassLayout

  NAMESPACE:
    Q3.RouteB

  PUBLIC_SURFACE:
    exactly one public theorem
    zero public definitions
    no public pointwise value table

  PRIMARY_THEOREM: |
    theorem ccmVonMangoldt_sum_Icc_2_13 (f : ℕ → ℝ) :
        ∑ k ∈ Finset.Icc 2 13,
            ArithmeticFunction.vonMangoldt k * f k =
          Real.log 2 * (f 2 + f 4 + f 8) +
          Real.log 3 * (f 3 + f 9) +
          Real.log 5 * f 5 +
          Real.log 7 * f 7 +
          Real.log 11 * f 11 +
          Real.log 13 * f 13 := by
      ...

  PROOF_ROUTE:
    - use local exact values for 2 through 13
    - primes via ArithmeticFunction.vonMangoldt_apply_prime
    - 4, 8, 9 via exact power rewrites and vonMangoldt_apply_pow
    - 6, 10, 12 via vonMangoldt_apply and
      isPrimePow_nat_iff_bounded_log_minFac
    - expand only Finset.Icc 2 13
    - finish coefficient rearrangement by ring
    - include a private literal ccmPrimeEntryN1 specialization compile check
    - do not import CCMFiniteWeilLogBounds

  REQUIRED_PRIVATE_PLANTS:

    P-VM-1:
      test_function: delta_at_8
      expected_sum: Real.log 2
      mutant: remove f_8 from the log_2 class
      required_mutant_fate: COMPILE_FAIL

    P-VM-2:
      test_function: delta_at_6
      expected_sum: 0
      mutant: add a nonzero f_6 coefficient
      required_mutant_fate: COMPILE_FAIL

    P-VM-3:
      test_function: delta_at_3_minus_delta_at_9
      expected_sum: 0
      mutant: replace equal log_3 coefficients by exponent-weighted coefficients
      required_mutant_fate: COMPILE_FAIL

  FORBIDDEN:
    - sorry
    - admit
    - exact?
    - native_decide
    - declared axiom
    - opaque
    - Float
    - of_decide_eq_true
    - surrogate von-Mangoldt definition
    - public twelve-value table
    - prime-only support
    - exponent-weighted prime-power coefficients
    - qKernel unfolding
    - qKernel numerical enclosure
    - pi or trigonometric evaluation
    - reciprocal-log-13 work
    - W02 or WR unfolding
    - integral work
    - endpoint rational pairs
    - modification of existing Lean files
    - route-state mutation
    - Goal 055 materialization
    - Bus 010 creation
    - Aristotle submission
    - route promotion
    - RH claim

  VALIDATION:
    - direct lake env lean on the owned file
    - target lake build of the owned module
    - full lake build
    - scripts/q3_check.sh on the owned file
    - taint scan
    - public-surface scan
    - git diff --check
    - exact git status report
    - "#print axioms Q3.RouteB.ccmVonMangoldt_sum_Icc_2_13"

  EXPECTED_AXIOMS:
    - propext
    - Classical.choice
    - Quot.sound

  REPORT_REQUIRED:
    - exact file SHA-256
    - exact final theorem statement
    - direct Lean result
    - target and full build job counts
    - q3_check result
    - taint result
    - public-surface count
    - axiom output
    - fate of P-VM-1, P-VM-2, P-VM-3
    - confirmation that no existing file changed
    - GOAL_055 HOLD_055_RATIFIED
    - ARISTOTLE_SUBMISSION NONE
    - ROUTE CHALLENGER_NOT_RH
    - BUS_010 VOID

  FAILURE_CODES:
    - G2_CCM_054_1_FINITE_VON_MANGOLDT_SUPPORT_VALUE_MISMATCH
    - G2_CCM_054_1_FINITE_VON_MANGOLDT_GROUPING_MISMATCH
    - G2_CCM_054_1_FINITE_VON_MANGOLDT_LITERAL_WIRING_MISMATCH
    - G2_CCM_054_1_FINITE_VON_MANGOLDT_PLANT_INERT
    - LEAN_BUILD_FAIL
