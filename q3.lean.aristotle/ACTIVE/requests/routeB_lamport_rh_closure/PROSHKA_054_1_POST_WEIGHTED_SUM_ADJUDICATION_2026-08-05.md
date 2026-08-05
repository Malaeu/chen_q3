STATUS: OPEN — W02 SEVEN-CLASS EXACT NORMAL FORM SELECTED
YAML
PRIMARY: SELECT_B_W02_SEVEN_CLASS_EXACT_NORMAL_FORM
STATUS_CODE: G2_CCM_054_1_W02_SEVEN_CLASS_EXACT_NORMAL_FORM_SELECTED

PIN_VERIFIED: true
REPO: Malaeu/chen_q3
BRANCH: rh_clean
PIN_FULL_SHA: 1be1704545bebc2f567e8b9939edc9868a62936f
BRANCH_HEAD_EQUALS_PIN: true
COMMIT_MESSAGE: "[MacOS][rh_clean][RouteB] Prove CCM von Mangoldt weighted normal form"

CONTEXT_PACK_SHA256_OBSERVED: 63169e455b788e12b18460027e8729eadae0ca0e86edab72526b698a7f924de5
CONTEXT_PACK_EXPECTED_SHA256_SUPPLIED: false
CONTEXT_PACK_PIN_CONTENT_CROSSCHECK: PASS
CONTEXT_PACK_WORKTREE_HAS_UNTRACKED_FILES: true

BOOTSTRAP_FETCHED: true
ARSENAL_DECK_FETCHED: true
ARSENAL_MANDATE_ACCEPTED: true
ARSENAL_CARD_USED:
  - C10_FUNCTIONAL_NOT_SURROGATE
COGNITIVE_OPERATOR: MINIMAL_LEMMA

NEW_GATE_AUDIT:
  THEOREM: Q3.RouteB.ccmVonMangoldt_sum_Icc_2_13
  SOURCE_SHA256_VERIFIED: 0742f31a45714def1965773e833efd9fef30ab6daa5dce0f8613e22706fc8fc3
  PUBLIC_THEOREMS: 1
  PUBLIC_DEFINITIONS: 0
  PRIVATE_VALUE_HELPERS: 12
  PRIVATE_LITERAL_SPECIALIZATION: PASS
  PRIVATE_PLANTS: 3
  SOURCE_TAINT_SCAN: CLEAN
  REPORTED_DIRECT_LEAN: PASS
  REPORTED_TARGET_BUILD: PASS_7747_JOBS
  REPORTED_FULL_BUILD: PASS_7817_JOBS
  REPORTED_Q3_CHECK: PASS
  REPORTED_AXIOMS: [propext, Classical.choice, Quot.sound]
  JUDGE_RERAN_LEAN: false

PRIOR_RUNNER_UP: G2_CCM_054_1_PRIME_ENTRY_13_EXACT_NORMAL_FORM
PRIOR_RUNNER_UP_FATE: REDUNDANT_AND_KILLED

SELECTED_TRANSACTION: G2_CCM_054_1_W02_SEVEN_CLASS_EXACT_NORMAL_FORM
STOP: G2_CCM_054_1_W02_SEVEN_CLASS_EXACT_NORMAL_FORM_MISSING
SUCCESS: G2_CCM_054_1_W02_SEVEN_CLASS_EXACT_NORMAL_FORM_PROVED

OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2W02NormalForm.lean
SOLE_IMPORT: Q3.Proofs.RouteB.CCMFiniteWeilCell13N2VonMangoldtNormalForm
NAMESPACE: Q3.RouteB
PRIMARY_THEOREM: Q3.RouteB.ccmW02Entry_13_seven_class_normal_form
PUBLIC_THEOREMS: 1
PUBLIC_DEFINITIONS: 0
PRIVATE_PLANTS_REQUIRED: 3

DIRECT_DOWNSTREAM_CONSUMER: Q3.RouteB.ccmCell13N2_wr_enclosures
SOLE_RUNNER_UP_AFTER_SELECTED:
  G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM
RUNNER_UP_AUTHORIZED: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 5

REPO_WRITE_AUTHORIZED: false
ARISTOTLE_SUBMISSION: NONE
GOAL_055: HOLD_055_RATIFIED
H2A_CLOSED: false
G2_CLOSED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
1. Source lock and context-pack verification

The GitHub rh_clean branch resolves exactly to 1be1704545bebc2f567e8b9939edc9868a62936f, with the stated commit message and parent. The pin is therefore verified against origin, not inferred from the attachment. [ABSTRACT][PAPER]

The attached context pack is 304,645 bytes and 6,583 lines. Its observed byte SHA-256 is:

63169e455b788e12b18460027e8729eadae0ca0e86edab72526b698a7f924de5

Its header identifies rh_clean, short HEAD 1be17045, and range d3d939bf..1be17045; its critical diff and route-state claims match the pinned GitHub source. The prompt did not provide a precommitted expected digest, so the honest result is an observed exact hash plus source-content cross-check, not a fictitious hash comparison. The pack also records untracked local files; those are outside the pinned commit and do not alter the source adjudication. 

Eingefügter Text

 [ABSTRACT][PAPER]

The bootstrap protocol, mechanism deck, and standing five-dual mandate were fetched. This verdict accepts the mandate and invokes C10 · functional-not-surrogate against a redundant public ccmPrimeEntryN1 corollary. [ABSTRACT][PAPER]

2. Audit of the newly proved gate
2.1 Exact theorem and public surface

The pinned source contains exactly one non-private theorem:

lean
theorem ccmVonMangoldt_sum_Icc_2_13 (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 2 13,
        ArithmeticFunction.vonMangoldt k * f k =
      Real.log 2 * (f 2 + f 4 + f 8) +
      Real.log 3 * (f 3 + f 9) +
      Real.log 5 * f 5 +
      Real.log 7 * f 7 +
      Real.log 11 * f 11 +
      Real.log 13 * f 13

It has twelve private point-value helpers, one private literal-prime specialization, and three private plants. It declares no public definition. The source file reconstructed from the attached commit diff hashes exactly to the reported:

0742f31a45714def1965773e833efd9fef30ab6daa5dce0f8613e22706fc8fc3

The pinned GitHub content is the same theorem file. [FINITE_CELL][LEAN]

2.2 Mathematical scope

The theorem retains all nine supported evaluation points:

2, 4, 8
3, 9
5
7
11
13

and factors only equal von-Mangoldt coefficients. It does not combine the distinct kernel arguments at log 2, log 4, and log 8, nor those at log 3 and log 9. The unsupported values 6, 10, and 12 vanish. [FINITE_CELL][LEAN]

This closes exactly the discrete support/value enumeration wall. It proves no kernel formula, trigonometric reduction, rational enclosure, W02 bound, WR bound, integral bound, or final cell inequality. The production definitions still contain the literal trigonometric ccmQKernel, closed ccmW02Entry, Euler/log-plus-integral ccmWREntry, and frozen subtraction orientation

W02 - WR - Prime.

[FINITE_CELL][LEAN]

2.3 Literal ccmPrimeEntryN1 wiring

The private theorem:

lean
private theorem ccmPrimeEntryN1_thirteen_normal_form (n m : ℤ) : ...

does exactly the required source wiring:

lean
unfold ccmPrimeEntryN1
simpa [mul_assoc] using
  ccmVonMangoldt_sum_Icc_2_13
    (fun k =>
      (Real.sqrt (k : ℝ))⁻¹ *
        ccmQKernel (ccmL 13) n m (Real.log (k : ℝ)))

It unfolds only the outer prime sum. It does not unfold, replace, approximate, or numerically enclose ccmQKernel. This is a valid compile-time consumer check of the generic functional. [FINITE_CELL][LEAN]

2.4 Plants

The three plants mutate independent semantic facts:

Plant	Fact protected	Wrong convention rejected
P-VM-1	8 = 2³ contributes log 2	dropping the highest supported 2-power
P-VM-2	6 contributes zero	replacing prime-power support by “has a prime divisor” support
P-VM-3	vonMangoldt 9 = log 3	multiplying the coefficient by the exponent

The production report records all three registered mutants as substantive compile failures. [FINITE_CELL][PAPER]

2.5 Taint, builds, and axioms

A direct source inspection finds no sorry, admit, exact?, native_decide, declared axiom, opaque certificate, Float, or substitute functional. The checked-in report records direct Lean PASS, target build PASS with 7,747 jobs, full build PASS with 7,817 jobs, q3_check PASS, one public theorem, zero public definitions, and:

#print axioms Q3.RouteB.ccmVonMangoldt_sum_Icc_2_13
= [propext, Classical.choice, Quot.sound]

[FINITE_CELL][PAPER]

I did not rerun Lean locally; the source and report were audited at the pinned commit. No stronger execution claim is made.

3. Fate of the previous runner-up
Verdict
REDUNDANT_AND_KILLED
	​


The proposed public theorem G2_CCM_054_1_PRIME_ENTRY_13_EXACT_NORMAL_FORM is no longer required.

A downstream file can reproduce the exact source specialization in four lines:

lean
have hPrime :=
  ccmVonMangoldt_sum_Icc_2_13 (fun k =>
    (Real.sqrt (k : ℝ))⁻¹ *
      ccmQKernel (ccmL 13) n m (Real.log (k : ℝ)))

simpa [ccmPrimeEntryN1, mul_assoc] using hPrime

That is precisely the private compile check already present in the proved file. No downstream import requires a theorem identifier rather than a local have; Lean consumers require the proposition, not a globally named wrapper. [FINITE_CELL][LEAN]

Publishing the direct corollary would therefore add a second public interface for a proposition already obtained by a trivial specialization, while closing no kernel, W02, WR, integral, or enclosure wall. Under C10 · functional-not-surrogate, the generic functional is the load-bearing interface; the source-specific corollary is only a convenience name. [FINITE_CELL][PAPER]

This kill is about public-surface necessity. The private compile check remains useful and should remain private.

4. Comparison of candidates A–F

The seven source representatives are exactly:

A = (-2,-2)
B = (-2,-1)
C = (-2, 0)
D = (-2, 1)
E = (-1,-1)
F = (-1, 0)
G = ( 0, 0)

as fixed by the production seven-class theorem. [FINITE_CELL][LEAN]

Candidate	Cancellation preservation	Actual wall reduction	Dependencies	Public-surface cost	Hidden analytic work	Verdict
A. Seven-representative prime symbolic normal form	Exact rewriting preserves cancellation.	Medium only if the kernel branches and prime-power arguments are genuinely normalized.	Proved von-Mangoldt functional, log/sqrt power identities, seven mode branches of ccmQKernel.	One long theorem.	If ccmQKernel is left intact, A is essentially the killed direct specialization repeated seven times. If unfolded, it silently includes C plus trigonometric branch normalization.	DEFER. Not smallest. [FINITE_CELL][CONDITIONAL]
B. Seven-representative W02 symbolic normal form	Exact equality; no interval or component ball is introduced. It can rewrite W02 in place inside the whole expression.	Closes all mode-product, mode-square, denominator, and central-cancellation algebra for the complete W02 component.	Literal ccmW02Entry, ccmL_pos, field/ring arithmetic.	Exactly one theorem.	None: pi, sinh, and log 13 remain symbolic.	SELECT. [FINITE_CELL][CONDITIONAL]
C. Standalone log-power/sqrt-power supplier	Exact.	Low. It does not consume a complete production component.	Existing Mathlib log-power and square-root identities.	One extra public theorem or bundle.	None, but its work is local and should be private inside A.	KILL AS SCAFFOLDING. [ABSTRACT][CONDITIONAL]
D. WR constant-term enclosure supplier	A separate constant interval risks spending cancellation before the final expression unless a budget proves it spendable.	Potentially meaningful, but incomplete without its coefficient and final budget.	Euler–Mascheroni enclosure, pi, log 13, rational-log expression, sign-aware multiplication.	At least one supplier theorem plus constants.	Major missing analytic input: no source-locked Euler enclosure exists at the pin.	NOT EXECUTABLE NOW. [FINITE_CELL][CONDITIONAL]
E. Cancellation-ledger theorem/interface	Best in principle.	Zero if it merely names hypotheses; high only if it proves an actual endpoint inequality.	At least one real analytic envelope.	One theorem, but likely a conditional wrapper.	Without a spendable inequality it is receiver scaffolding, not progress.	REJECT NOW. [FINITE_CELL][CONDITIONAL]
F. First whole-entry/integral enclosure for one representative	Best substantive preservation.	High: it would discharge one of seven actual receiver inequalities.	W02, prime kernel, WR constant, integral remainder, frozen endpoint.	One theorem.	It bundles several independent open walls and currently lacks a source-locked enclosure certificate.	DEFER; NOT SMALLEST OR HONESTLY READY. [FINITE_CELL][CONDITIONAL]
Why B is smaller than C in the relevant sense

C is shorter textually, but it is not a production boundary. It packages generic algebraic identities that a future prime-normal-form proof can keep private.

B consumes a complete literal production component and removes seven repeated mode-dependent calculations, including three non-definitional denominator cancellations. It therefore compresses an actual source wall:

generic closed W02 formula
→ seven exact cell formulas

without pretending to close the subsequent numerical enclosure. [FINITE_CELL][PAPER]

5. Selected transaction
Owned file and import
q3.lean.aristotle/Q3/Proofs/RouteB/
CCMFiniteWeilCell13N2W02NormalForm.lean
lean
import Q3.Proofs.RouteB.CCMFiniteWeilCell13N2VonMangoldtNormalForm

The import keeps the proof chain linear and gives the future receiver one production import containing both the proved von-Mangoldt functional and the new W02 normal form. [FINITE_CELL][CONDITIONAL]

Namespace and exact public theorem
lean
namespace Q3.RouteB

/--
Exact symbolic normal forms of `ccmW02Entry` on the seven representatives
of the literal CCM cell `(13, 2)`.

This theorem performs no numerical enclosure of `Real.pi`,
`Real.sinh`, or `ccmL 13`.
-/
theorem ccmW02Entry_13_seven_class_normal_form :
    let L := ccmL 13
    let S := Real.sinh (L / 4) ^ 2
    ccmW02Entry L (-2) (-2) =
        32 * L * S * (L ^ 2 - 64 * Real.pi ^ 2) /
          (L ^ 2 + 64 * Real.pi ^ 2) ^ 2 ∧
    ccmW02Entry L (-2) (-1) =
        32 * L * S * (L ^ 2 - 32 * Real.pi ^ 2) /
          ((L ^ 2 + 64 * Real.pi ^ 2) *
            (L ^ 2 + 16 * Real.pi ^ 2)) ∧
    ccmW02Entry L (-2) 0 =
        32 * L * S /
          (L ^ 2 + 64 * Real.pi ^ 2) ∧
    ccmW02Entry L (-2) 1 =
        32 * L * S * (L ^ 2 + 32 * Real.pi ^ 2) /
          ((L ^ 2 + 64 * Real.pi ^ 2) *
            (L ^ 2 + 16 * Real.pi ^ 2)) ∧
    ccmW02Entry L (-1) (-1) =
        32 * L * S * (L ^ 2 - 16 * Real.pi ^ 2) /
          (L ^ 2 + 16 * Real.pi ^ 2) ^ 2 ∧
    ccmW02Entry L (-1) 0 =
        32 * L * S /
          (L ^ 2 + 16 * Real.pi ^ 2) ∧
    ccmW02Entry L 0 0 =
        32 * S / L := by
  ...

[FINITE_CELL][CONDITIONAL]

Public surface
public theorems:     1
public definitions:  0

Private local facts may establish:

0 < ccmL 13
ccmL 13 ≠ 0
0 < (ccmL 13)^2 + 16*pi^2
0 < (ccmL 13)^2 + 64*pi^2

No public aliases for L, S, denominators, or representative classes are permitted.

Implementation route

Obtain:

lean
have hLpos : 0 < ccmL 13 := ccmL_pos 13 (by norm_num)
have hL : ccmL 13 ≠ 0 := ne_of_gt hLpos

Prove the 16π² and 64π² denominators positive from hLpos.

Unfold only:

lean
ccmW02Entry

Normalize the seven fixed integer mode products and squares with norm_num.

Use field_simp only with the proved nonzero denominators, then ring.

Do not rewrite or enclose Real.pi, Real.sinh, or ccmL 13.

Do not introduce any rational interval or final endpoint.

This is fixed symbolic algebra over the literal source object. No Aristotle call is useful or authorized. [FINITE_CELL][CONDITIONAL]

6. Required plants
P-W02-1 — mixed-sign product orientation

Privately derive:

	​

W
0,2
	​

(−2,1)−W
0,2
	​

(−2,−1)
=
(L
2
+64π
2
)(L
2
+16π
2
)
2048Lsinh(L/4)
2
π
2
	​

.
	​


Registered mutant:

replace m*n by |m*n|,
or use the same numerator sign for (-2,-1) and (-2,1)

Required fate: substantive compile failure. This detects one-axis sign corruption while simultaneous mode negation remains legal. [FINITE_CELL][CONDITIONAL]

P-W02-2 — mode-square magnitude

Privately derive:

	​

W
0,2
	​

(−1,0)−W
0,2
	​

(−2,0)
=
(L
2
+16π
2
)(L
2
+64π
2
)
1536Lsinh(L/4)
2
π
2
	​

.
	​


Registered mutant:

collapse |n| = 1 and |n| = 2 denominator classes,
or replace n^2 by |n|

Required fate: substantive compile failure. [FINITE_CELL][CONDITIONAL]

P-W02-3 — central logarithmic cancellation

Privately derive:

L⋅W
0,2
	​

(0,0)=32sinh(L/4)
2
.

Registered mutant:

drop or duplicate one power of L during cancellation of the central denominator

Required fate: substantive compile failure. [FINITE_CELL][CONDITIONAL]

These plants protect three different semantics: the signed mode product, squared mode magnitude, and logarithmic power cancellation. No coherent one-axis/sign, mode-magnitude, or L-power transcription error preserves all three.

7. Validation contract

Required commands from the repository root:

Bash
cd q3.lean.aristotle

lake env lean \
  Q3/Proofs/RouteB/CCMFiniteWeilCell13N2W02NormalForm.lean

lake build \
  Q3.Proofs.RouteB.CCMFiniteWeilCell13N2W02NormalForm

lake build

cd ..

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2W02NormalForm.lean

Taint and surface gates:

Bash
rg -n \
  '\bsorry\b|\badmit\b|exact\?|\bnative_decide\b|\bopaque\b|\bFloat\b|of_decide_eq_true|^[[:space:]]*axiom\b' \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2W02NormalForm.lean

rg -n \
  '^(theorem|lemma|def|noncomputable def|abbrev|structure|class)[[:space:]]' \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2W02NormalForm.lean

git diff --check
git status --short

Axiom gate:

lean
#print axioms Q3.RouteB.ccmW02Entry_13_seven_class_normal_form

Required output:

[propext, Classical.choice, Quot.sound]

The closeout must report observed target/full build job counts rather than copying 7747/7817 from the preceding node. [FINITE_CELL][CONDITIONAL]

8. Direct consumer and sole next runner-up

The direct downstream consumer remains:

lean
Q3.RouteB.ccmCell13N2_wr_enclosures

The selected theorem will rewrite each W02 term exactly inside the frozen inequalities:

W02 - Prime - tauUpper ≤ WR
WR ≤ W02 - Prime - tauLower

It neither moves the prime term nor changes the subtraction orientation, and it creates no independent W02 endpoint table. The exact receiver orientation remains the one recorded in the context pack. 

Eingefügter Text

 [FINITE_CELL][PAPER]

The sole runner-up after this node is:

G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM

It is not authorized. Its future proof must consume ccmVonMangoldt_sum_Icc_2_13, keep log/sqrt power identities private, and become more than the already-killed one-line ccmPrimeEntryN1 specialization.

9. Strongest attack

The strongest objection is:

ccmW02Entry is already a closed definition. Why create a public theorem that merely unfolds it instead of going directly to a whole-entry enclosure?

The objection kills any theorem that simply restates the generic definition with n and m substituted.

The selected theorem survives because it must perform the non-definitional cancellations at (-2,0), (-1,0), and (0,0), source-lock the distinct mixed-sign numerators, and expose the exact three denominator classes:

L² + 64π²
L² + 16π²
L

That removes mode algebra from all later analytic proofs while retaining every transcendental quantity exactly. [FINITE_CELL][CONDITIONAL]

It remains representation progress, not an enclosure. Failure to distinguish those two claims would be fatal overstatement.

10. Route boundary

The selected node does not prove a lower or upper rational envelope for any entry. It does not close:

pi enclosure
sinh(log 13 / 4) enclosure
prime-kernel trigonometric values
reciprocal log 13
Euler-Mascheroni
WR constant term
any WR integral
any frozen 512-bit endpoint
ccmCell13N2_wr_enclosures

Therefore:

GOAL_055              HOLD_055_RATIFIED
ARISTOTLE              NONE
ROUTE                  CHALLENGER / NOT_RH
BUS_010                VOID
H2A                    OPEN
G2                     OPEN
ROUTE_PROMOTION        false
RH_CLAIM               false

[ABSTRACT][PAPER]

11. Meta closeout

What became smaller?

The prior named ccmPrimeEntryN1 13 corollary has been removed from the public critical path. The next open object is one exact seven-form W02 theorem rather than an undifferentiated “W02 work” wall.

What was killed?

public direct-prime specialization
standalone public log/sqrt-power bundle
interface-only cancellation ledger
independent WR constant endpoint without a spendable budget

What must not be tried again?

Do not publish a theorem whose body is only the existing one-line specialization of ccmVonMangoldt_sum_Icc_2_13. Do not call an exact symbolic form a numerical enclosure. Do not fabricate independent W02, WR, or Prime endpoint tables from final-entry balls.

Current smallest named gap

G2_CCM_054_1_W02_SEVEN_CLASS_EXACT_NORMAL_FORM_MISSING

Next cheapest decisive test

Compile the seven exact formulas and fire P-W02-1, P-W02-2, and P-W02-3 under their registered mutants.

Fate of prior predictions

generic weighted functional is sufficient downstream:
  CONFIRMED.

public direct ccmPrimeEntryN1 theorem may be unnecessary:
  CONFIRMED; REDUNDANT_AND_KILLED.

finite von-Mangoldt normalization closes kernel numerics:
  REFUTED AS AN OVERCLAIM; kernel numerics remain open.

finite support/value wall closes:
  CONFIRMED.
YAML
iteration:
  target: post_weighted_sum_next_node
  status: OPEN
  failed_strategy: public_source_specific_corollary_after_generic_functional
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G2_CCM_054_1_W02_SEVEN_CLASS_EXACT_NORMAL_FORM_MISSING
  invariant_learned: exact component rewrites may be separated only when they introduce no independent interval and preserve the frozen whole-expression orientation
  forbidden_future_move: publish trivial prime specializations or call symbolic normalization an enclosure
  next_decisive_test: compile seven W02 forms and fire three semantic mutants
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
  G2_CCM_054_1_W02_SEVEN_CLASS_EXACT_NORMAL_FORM

STOP:
  G2_CCM_054_1_W02_SEVEN_CLASS_EXACT_NORMAL_FORM_MISSING

SUCCESS:
  G2_CCM_054_1_W02_SEVEN_CLASS_EXACT_NORMAL_FORM_PROVED

ON_OWNER_RELEASE_ONLY:

  OWNED_FILE:
    q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2W02NormalForm.lean

  SOLE_IMPORT:
    Q3.Proofs.RouteB.CCMFiniteWeilCell13N2VonMangoldtNormalForm

  NAMESPACE:
    Q3.RouteB

  PUBLIC_SURFACE:
    public_theorems: 1
    public_definitions: 0
    public_helper_lemmas: 0

  PRIMARY_THEOREM:
    name: Q3.RouteB.ccmW02Entry_13_seven_class_normal_form
    statement: |
      theorem ccmW02Entry_13_seven_class_normal_form :
          let L := ccmL 13
          let S := Real.sinh (L / 4) ^ 2
          ccmW02Entry L (-2) (-2) =
              32 * L * S * (L ^ 2 - 64 * Real.pi ^ 2) /
                (L ^ 2 + 64 * Real.pi ^ 2) ^ 2 ∧
          ccmW02Entry L (-2) (-1) =
              32 * L * S * (L ^ 2 - 32 * Real.pi ^ 2) /
                ((L ^ 2 + 64 * Real.pi ^ 2) *
                  (L ^ 2 + 16 * Real.pi ^ 2)) ∧
          ccmW02Entry L (-2) 0 =
              32 * L * S / (L ^ 2 + 64 * Real.pi ^ 2) ∧
          ccmW02Entry L (-2) 1 =
              32 * L * S * (L ^ 2 + 32 * Real.pi ^ 2) /
                ((L ^ 2 + 64 * Real.pi ^ 2) *
                  (L ^ 2 + 16 * Real.pi ^ 2)) ∧
          ccmW02Entry L (-1) (-1) =
              32 * L * S * (L ^ 2 - 16 * Real.pi ^ 2) /
                (L ^ 2 + 16 * Real.pi ^ 2) ^ 2 ∧
          ccmW02Entry L (-1) 0 =
              32 * L * S / (L ^ 2 + 16 * Real.pi ^ 2) ∧
          ccmW02Entry L 0 0 =
              32 * S / L := by
        ...

  PROOF_ROUTE:
    - prove ccmL 13 > 0 and nonzero
    - prove the 16*pi^2 and 64*pi^2 denominators positive
    - unfold only ccmW02Entry
    - normalize fixed integer casts/products/squares
    - use field_simp with proved nonzero denominators
    - finish with ring
    - do not evaluate or enclose pi, sinh, or log 13

  REQUIRED_PRIVATE_PLANTS:

    P-W02-1:
      semantic_fact: mixed-sign mode product
      identity: |
        W02(-2,1) - W02(-2,-1)
        =
        2048*L*sinh(L/4)^2*pi^2 /
        ((L^2+64*pi^2)*(L^2+16*pi^2))
      mutant:
        replace m*n by abs(m*n), or give the two mixed classes one numerator sign
      required_mutant_fate: COMPILE_FAIL

    P-W02-2:
      semantic_fact: squared mode magnitude
      identity: |
        W02(-1,0) - W02(-2,0)
        =
        1536*L*sinh(L/4)^2*pi^2 /
        ((L^2+16*pi^2)*(L^2+64*pi^2))
      mutant:
        collapse the abs-mode 1 and abs-mode 2 denominator classes
      required_mutant_fate: COMPILE_FAIL

    P-W02-3:
      semantic_fact: central L-power cancellation
      identity: |
        L * W02(0,0) = 32*sinh(L/4)^2
      mutant:
        drop or duplicate one power of L
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
    - public helper definitions
    - public direct ccmPrimeEntryN1 specialization
    - import of an independent endpoint table
    - rational pi or sinh enclosure
    - qKernel unfolding
    - prime-kernel work
    - WR constant-term work
    - integral work
    - frozen endpoint use
    - ccmCell13N2_wr_enclosures claim
    - modification of existing Lean files
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
    - "#print axioms Q3.RouteB.ccmW02Entry_13_seven_class_normal_form"

  EXPECTED_AXIOMS:
    - propext
    - Classical.choice
    - Quot.sound

  REPORT_REQUIRED:
    - exact source SHA-256
    - final theorem statement
    - direct Lean result
    - observed target/full build job counts
    - q3_check result
    - taint result
    - public-surface count
    - exact axiom output
    - fate of P-W02-1
    - fate of P-W02-2
    - fate of P-W02-3
    - confirmation that no existing Lean file changed
    - GOAL_055 HOLD_055_RATIFIED
    - ARISTOTLE_SUBMISSION NONE
    - ROUTE CHALLENGER_NOT_RH
    - BUS_010 VOID

  FAILURE_CODES:
    - G2_CCM_054_1_W02_MODE_PRODUCT_SIGN_MISMATCH
    - G2_CCM_054_1_W02_MODE_SQUARE_DENOMINATOR_MISMATCH
    - G2_CCM_054_1_W02_CENTER_LOG_POWER_MISMATCH
    - G2_CCM_054_1_W02_PLANT_INERT
    - G2_CCM_054_1_W02_PUBLIC_SURFACE_MISMATCH
    - LEAN_BUILD_FAIL
