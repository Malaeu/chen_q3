# Proshka adjudication — Goal 054.1b / 054.1-v2

```yaml
date: 2026-08-05
proof_address: RouteB.G2.CCM.054_1
conversation_id: 6a72c9d4-ea88-83eb-a06f-99bc5364f647
request_message_id: cf0ec589-2b55-4940-8339-13889804ec4a
response_message_id: 80197a13-a587-4171-951c-9cae3078a0e5
sent_at: 2026-08-05T07:27:48.554+02:00
observed_complete_at: 2026-08-05T07:51:54.909+02:00
observed_wall_seconds: 1446
observed_wall_human: 24m06s
ui_reasoning_time: 23m10s
answer_now_shown: true
answer_now_clicked: false
context_pack_sha256: e14b5e13aeb1c9f72516b2767b877dd6d309e8cce85905990f604950d37c903b
prompt_sha256: 6f52adb5abefa579f5370f0f5180cc4f3088540d491799a3667278ba10732f1d
response_visible_text_sha256: 81226e3d85bcd432a17687f7873d05e4103e31e5b7aa47694ef7ca7ea02894e3
response_visible_text_chars: 25023
response_visible_text_lines: 714
codex_directive_count: 1
A_CLASSIFICATION: ACCEPT_054_1B_ONLY_AFTER_REPAIR
B_DECISION: DO_NOT_SUBMIT_054_1_V2_SPLIT_REQUIRED
GOAL_055: HOLD_055_RATIFIED
NEXT_NODE: G2_CCM_CELL13N2_ANTIPODAL_CLASS_CROSSWALK
ARISTOTLE_SUBMISSION_AUTHORIZED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
```

The block below is the exact visible text extracted from the completed assistant
message in the project chat. No early-answer action was used.

## Verbatim visible response

```text
STATUS: OPEN
YAML
A_CLASSIFICATION: ACCEPT_054_1B_ONLY_AFTER_REPAIR
B_DECISION: DO_NOT_SUBMIT_054_1_V2_SPLIT_REQUIRED
GOAL_055: HOLD_055_RATIFIED

SURROGATE_INTEGRATED: false
H2A_CLOSED: false
G2_CLOSED: false
ROUTE_PROMOTION: false
RH_CLAIMED: false
BUS_010: VOID

PIN_VERIFIED: true
CONTEXT_PACK_SHA256_VERIFIED: true
ARSENAL_MANDATE_ACCEPTED: true
ARISTOTLE_SUBMISSION_AUTHORIZED: false
OWNER_APPROVAL_REQUIRED: true
JUDGE_RERAN_LEAN: false

NEXT_NODE: G2_CCM_CELL13N2_ANTIPODAL_CLASS_CROSSWALK
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 5
Pin and protocol lock

The rh_clean branch points exactly to 2ff3031a850ad7748d358a90123fef18717d8a42, whose commit message is [MacOS][rh_clean][RouteB] Prepare real CCM cell receiver v2. The attached context pack independently hashes to the requested e14b5e13aeb1c9f72516b2767b877dd6d309e8cce85905990f604950d37c903b. 

PROSHKA_054_1B_V2_ADJUDICATION_…

The Arsenal mandate is accepted. Its pinned materialization ledger records the required deck hash 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d. This verdict invokes [C10 · FUNCTIONAL-NOT-SURROGATE] against 054.1.a and recognizes [C09 · PRECOMMIT] for the frozen 512-bit endpoint table.

1. Definition-level comparison: production versus rejected surrogate

The production chain is source-shaped and literal: the finite carrier is Fin (2*N+1), the labels are -N,…,N, and the finite matrix is obtained by applying the unchanged scalar constructor ccmWeilTauN1. The scalar constructor contains the trigonometric CCM kernel, the closed W
0,2
	​

 expression, the finite von-Mangoldt sum, and the removable-singularity archimedean integral.

The prior Aristotle archive states that these definitions were absent from its submitted project and were reconstructed. Its own journal classifies Defs.lean, ClosedForm.lean, and Cell13N2.lean as archive-only because their hyperbolic-cosine/truncated-exponential construction is not the production functional.

Object	Production object	Rejected 054.1.a object	Adjudication
Mode carrier and labels	CCMModeFinite N := Fin (2*N+1) and ccmModeFinite N i = i-N, with the literal N=2 order [−2,−1,0,1,2].	Reconstructed locally because the upstream module was absent; no definitional crosswalk to production was supplied.	Production [ABSTRACT][LEAN]; surrogate [ABSTRACT][PAPER]
ccmQKernel	Diagonal cosine branch and off-diagonal sine-difference quotient with exact π, L, and integer-mode conventions.	Reported hyperbolic-cosine/truncated-exponential replacement.	[C10] surrogate rejected [ABSTRACT][PAPER]
Prime entry	∑
k∈[2,m]
	​

Λ(k)(
k
	​

)
−1
Q
L
	​

(n,m,logk), using ArithmeticFunction.vonMangoldt.	Reconstructed prime expression evaluated against the reconstructed kernel.	Not the same functional [ABSTRACT][LEAN] / [ABSTRACT][PAPER]
W
0,2
	​

	Literal formula with Real.sinh, Real.pi, L, and mode products.	Reconstructed closed form without a source equality theorem.	No production reuse [ABSTRACT][PAPER]
W
R
	​

	Euler–Mascheroni/log constant term plus the literal set integral of ccmWRIntegrand over Ioc 0 L; the endpoint singularity is treated as removable.	Surrogate closed-form/truncated analytic object; no equality to the production integral.	No production reuse [ABSTRACT][LEAN] / [ABSTRACT][PAPER]
Full entry	ccmWeilTauN1 = ccmW02Entry - ccmWREntry - ccmPrimeEntryN1.	Assembly of reconstructed components and reconstructed endpoint tables.	054.1.a remains SURROGATE_OBJECT [FINITE_CELL][PAPER]
Cell theorem	ccmWeilMatFinite 13 2 on the actual imported source definitions.	A theorem about the archive’s local substitutes.	Integration forbidden [FINITE_CELL][PAPER]

No part of Defs.lean, ClosedForm.lean, or Cell13N2.lean may be cited as evidence about the production cell. SURROGATE_INTEGRATED: false is therefore ratified.

2. Exact coverage and gaps of 054.1.b
Classification
ACCEPT_054_1B_ONLY_AFTER_REPAIR
	​


The mathematical bodies are trustworthy as independent Mathlib proofs. The staged file imports only Mathlib, contains no reference to any reconstructed CCM declaration, and the intended audited interface has the standard axiom triple.

The repair is nevertheless mandatory for two reasons:

The module-level relevance claim is false for the production object. It says, in effect, that every cell entry is an exact rational combination of the listed log/square-root constants. The production entry also contains π, trigonometric evaluations, the Euler constant, logarithmic denominators, and a literal integral.

The file currently exposes 31 namespace-level lemmas, while only 19 declarations are listed in the axiom audit. The twelve Mercator-input and linear-relation helpers are public rather than private. This is an interface/ledger mismatch, even though their trust is transitively covered by the final bounds that consume them.

This is a zero-mathematics repair: no rational endpoint changes and no new numerical assertion.

Coverage table
Required ingredient	054.1.b status	Exact scope
Real.log p, p∈{2,3,5,7,11,13}	DIRECTLY COVERED	Public lower/upper rational bounds. [ABSTRACT][LEAN]
Real.sqrt p, same primes	DIRECTLY COVERED	Public lower/upper rational bounds. [ABSTRACT][LEAN]
Real.log p * Real.sqrt p	DIRECTLY COVERED	Public product bounds. [ABSTRACT][LEAN]
Prime coefficients for k=p	DERIVABLE, NOT PACKAGED	logp/
p
	​

=(logp
p
	​

)/p; requires separate exact rational transport. [FINITE_CELL][CONDITIONAL]
Prime powers 4,8,9	DERIVABLE, NOT PACKAGED	Λ(4)/
4
	​

=log2/2, Λ(8)/
8
	​

=(log2
2
	​

)/4, Λ(9)/
9
	​

=log3/3. The file does not prove the finite von-Mangoldt case split. [FINITE_CELL][CONDITIONAL]
Non-prime-powers in Icc 2 13	NOT COVERED	Requires exact lemmas proving the corresponding von-Mangoldt values are zero. [FINITE_CELL][CONDITIONAL]
Independent inverse-square-root bounds	NOT EXPORTED	There is no theorem directly enclosing (
k
	​

)
−1
. The actual von-Mangoldt-weighted products can be derived as above, but a general reciprocal-sqrt supplier is absent. [ABSTRACT][CONDITIONAL]
π	NOT COVERED	No rational bounds or algebraic receiver for Real.pi. [ABSTRACT][CONDITIONAL]
Trigonometric arguments and values	NOT COVERED	No enclosure for 2πnlogk/log13, sin, or cos. [FINITE_CELL][CONDITIONAL]
Reciprocal powers of log 13	NOT EXPORTED	A positive interval for log 13 is available; reciprocal/division bounds are not packaged. [FINITE_CELL][CONDITIONAL]
W
0,2
	​

	NOT CLOSED	The file supplies some of its scalar inputs, but not π, denominator control, sinh reduction, or the final entry bound. [FINITE_CELL][CONDITIONAL]
Full prime entry	NOT CLOSED	Kernel evaluations and exact von-Mangoldt normalization remain. [FINITE_CELL][CONDITIONAL]
Euler–Mascheroni constant	NOT COVERED	No enclosure theorem. [ABSTRACT][CONDITIONAL]
W
R
	​

 constant term	NOT CLOSED	Requires Euler, π, the logarithmic expression, and sign-aware arithmetic. [FINITE_CELL][CONDITIONAL]
W
R
	​

 integral	NOT TOUCHED	No derivative majorant, partition, quadrature remainder, or rational integral enclosure. [FINITE_CELL][CONDITIONAL]
Final cell / receiver	NONE	No theorem mentions ccmQKernel, ccmPrimeEntryN1, ccmW02Entry, ccmWREntry, or ccmWeilMatFinite. [FINITE_CELL][LEAN]

The brick is therefore a production scalar coefficient supplier, not a production cell receiver.

Exact 054.1.b repair

Owned file:

q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilLogBounds.lean

Required patch:

Replace the overbroad module description by:

lean
/-!
# Rational scalar bounds used in the CCM cell `(13, 2)`

This file proves rational enclosures for `Real.log p`, `Real.sqrt p`, and
`Real.log p * Real.sqrt p` for `p ∈ {2,3,5,7,11,13}`.

These are coefficient suppliers only. This file does not enclose
`ccmQKernel`, `ccmW02Entry`, `ccmPrimeEntryN1`, `ccmWREntry`,
`ccmWeilTauN1`, or `ccmWeilMatFinite`, and it makes no cell-enclosure claim.
-/

Make these twelve implementation lemmas private:

ccm_log_frac_9
ccm_log_frac_16
ccm_log_frac_25
ccm_log_frac_49
ccm_log_frac_121
ccm_log_frac_169

ccm_log_frac_eq_9
ccm_log_frac_eq_16
ccm_log_frac_eq_25
ccm_log_frac_eq_49
ccm_log_frac_eq_121
ccm_log_frac_eq_169

Retain exactly this 19-theorem public surface:

ccm_log_series_bound

ccm_log_bounds_2
ccm_log_bounds_3
ccm_log_bounds_5
ccm_log_bounds_7
ccm_log_bounds_11
ccm_log_bounds_13

ccm_sqrt_bounds_2
ccm_sqrt_bounds_3
ccm_sqrt_bounds_5
ccm_sqrt_bounds_7
ccm_sqrt_bounds_11
ccm_sqrt_bounds_13

ccm_log_sqrt_bounds_2
ccm_log_sqrt_bounds_3
ccm_log_sqrt_bounds_5
ccm_log_sqrt_bounds_7
ccm_log_sqrt_bounds_11
ccm_log_sqrt_bounds_13

No theorem statement, denominator, numerator, or rational endpoint may change.

3. Theorem-shape and endpoint-orientation audit of 054.1-v2
Actual imported object

The skeleton imports the genuine production module and uses the exact production names without shadowing. Its two matrices contain the fourteen audited rational endpoints in the source mode order [−2,−1,0,1,2]. The pinned journal records a 14-of-14 endpoint match and exactly one sorry.

This passes [C09 · PRECOMMIT]: the target endpoints were frozen before the proposed proof, rather than tuned after a Lean result.

Orientation

Let

T=W
0,2
	​

−W
R
	​

−P.

For a desired final interval

L≤T≤U,

solving for W
R
	​

 gives

W
0,2
	​

−P−U≤W
R
	​

≤W
0,2
	​

−P−L.

That is exactly the orientation of ccmCell13N2_wr_enclosures: the upper final endpoint appears in the lower relative W
R
	​

 inequality, and the lower final endpoint appears in the upper relative inequality. The Phase-0 inventory independently records this orientation and explains that the JSON contains final-entry intervals rather than component intervals. 

PROSHKA_054_1B_V2_ADJUDICATION_…

Thus:

ENDPOINT_ORIENTATION: CORRECT
SIGN_W02: POSITIVE
SIGN_WR: NEGATIVE
SIGN_PRIME: NEGATIVE

[FINITE_CELL][PAPER]

The theorem name is slightly misleading: it is not an independently sourced interval for W
R
	​

. It is the final cell enclosure rewritten relative to W
R
	​

, specifically to preserve the available final-entry cancellation.

Fin 5 matrix layout and the seven classes

The displayed A–G matrices are symmetric and centrosymmetric. Their intended representatives are:

Class	Representative
A	(−2,−2)
B	(−2,−1)
C	(−2,0), with (−2,2) assigned to the same class
D	(−2,1)
E	(−1,−1)
F	(−1,0), with (−1,1) assigned to the same class
G	(0,0)

However, the advertised reduction in Step 1 is incomplete.

Transpose symmetry together with simultaneous negation produces nine, not seven, orbits on the 5×5 mode pairs. The imported source contains the special exact identity

T(−1,1)=T(−1,0),

which merges the two F-orbits and reduces nine to eight. 

PROSHKA_054_1B_V2_ADJUDICATION_…

To obtain the stated seven classes, one more exact identity is required:

T(−2,2)=T(−2,0).
	​


More generally, the source formulas satisfy

T(−r,r)=T(−r,0),

but that general theorem is not present in the imported public surface, and it does not follow from only the four lemmas listed in the PROVIDED SOLUTION.

Therefore:

ENDPOINT_MATRIX_LAYOUT: SOURCE-CONSISTENT_AFTER_MISSING_IDENTITY
SEVEN_CLASS_REDUCTION_AS_INSTRUCTED: INCOMPLETE

[FINITE_CELL][CONDITIONAL]

This is not endpoint corruption. It is a missing exact source crosswalk.

Honesty and usefulness of PROVIDED SOLUTION

The block is honest on the decisive trust boundaries:

it imports the real source object;

it forbids reconstruction and shadowing;

it forbids treating the Arb result as a Lean proof;

it preserves the correct subtraction orientation;

it requires the standard axiom triple.

Those are substantive improvements over 054.1.a. [ABSTRACT][PAPER]

It is not operationally sufficient for an Aristotle resubmission:

The claimed seven-class reduction lacks the antipodal r=2 identity.

The log/sqrt brick is mentioned but not imported. This is logically correct—no hidden assumption is introduced—but the lemmas are unavailable to the Lean proof unless the import is changed. A fill-only task cannot use them merely because a comment names the file.

The prime term needs more than coefficient bounds: it needs exact von-Mangoldt normalization, reciprocal transport, log 13 denominator control, π, and rigorous sine/cosine bounds.

W
0,2
	​

 needs its own exact normal form and transcendental enclosure.

The W
R
	​

 constant term requires Euler and π bounds.

The integral requires a concrete extension, partition, derivative or monotonicity bounds, and a complete rational error budget.

The target intervals are roughly 10
−70
-scale final balls. The instructions provide no allocation showing that independently bounded subexpressions can retain that final width.

The Phase-0 inventory already found that the existing source proves only integrability, not these concrete inequalities, and that no zero-assumption Arb-to-Lean receiver exists. 

PROSHKA_054_1B_V2_ADJUDICATION_…

Single-hole decision
DO_NOT_SUBMIT_054_1_V2_SPLIT_REQUIRED
	​


The theorem statement itself is mathematically valid and source-faithful. This is not a SOURCE_OR_THEOREM_SHAPE_INVALID verdict.

It is nevertheless not an admissible single Aristotle hole at the current granularity. One syntactic sorry hides several independent proof-producing walls:

Hidden wall	Why it is independent
Seven-class exact source reduction	Pure symbolic mode/kernel identity; no numerics required.
Finite von-Mangoldt and prime-power normalization	Discrete arithmetic and exact support classification.
W
0,2
	​

/prime-kernel normal forms	π, reciprocal log 13, and trigonometric reduction.
W
R
	​

 constant term	Euler–Mascheroni and logarithmic/transcendental enclosure.
Seven representative integral bounds	Real-analysis enclosure of distinct diagonal/off-diagonal integrands.
Final cancellation ledger	Must combine all errors against the frozen 512-bit final intervals without inventing component balls.

All are [FINITE_CELL][CONDITIONAL].

The required split must not create independent numerical W02, WR, and Prime endpoint tables. The JSON does not contain them. Subsequent analytic nodes must continue to bound the exact whole final expression or carry a proven error ledger preserving its cancellation.

Pure algebra corollary

ccmCell13N2_entry_enclosures is a genuine algebraic consequence of ccmCell13N2_wr_enclosures. It unfolds ccmWeilMatFinite and ccmWeilTauN1, then closes the sign rearrangement with linarith. No additional analysis is hidden in that proof body.

The implication is Lean-checked [FINITE_CELL][LEAN]; the resulting production enclosure remains conditional until the upstream sorry is removed [FINITE_CELL][CONDITIONAL].

Forbidden-route audit
Route	Verdict
Reconstruct or shadow production definitions	FORBIDDEN; repeats [C10] surrogate failure.
Import the external Arb acceptance verdict as a theorem	FORBIDDEN; no kernel-checked receiver exists.
Declare endpoint inequalities as an axiom	FORBIDDEN.
Use native_decide or of_decide_eq_true for transcendental truth	FORBIDDEN.
Use opaque to conceal a certificate	FORBIDDEN.
Use Float in a proof-producing path	FORBIDDEN.
Replace the trigonometric kernel or integral by the archive closed form	FORBIDDEN SURROGATE.
Weaken to approximate numerics about a different matrix	FORBIDDEN TARGET SWITCH.
Prove independent component balls not present in the source JSON and cite them as imported data	FORBIDDEN INVENTED CERTIFICATE.
4. Goal 055 hold
HOLD_055_RATIFIED
	​


The pinned file is a draft outside the physical bus. Its release condition requires ccmCell13N2_wr_enclosures to be integrated, hole-free, free of sorry/admit/native_decide/declared project axiom/opaque, validated by direct and full builds, and to print exactly the standard axiom triple. 

PROSHKA_054_1B_V2_ADJUDICATION_…

The hold is not released by:

repairing 054.1.b;

proving one representative class;

proving the seven-class crosswalk;

obtaining another external Arb run;

receiving an Aristotle answer that still contains a hole or surrogate object.

Before any 055_*.goal.md canon/mirror materialization, the authoritative verbatim P-LEAN-1..5 payload must also be recovered and byte-copied. It must not be reconstructed from the draft summary. [ABSTRACT][PAPER]

5. Strongest attack against this decision

The relative theorem is exactly the final desired finite-cell statement. A single Lean proof may contain arbitrarily many local helper lemmas. Splitting it risks destroying the cancellation that the relative orientation was designed to preserve.

That objection is correct about theorem semantics but does not justify the present Aristotle transaction.

I am not ordering a split into independently bounded W02, WR, and Prime components. Such a split would be unsound relative to the available certificate.

The selected first split is an exact symbolic source identity. It introduces no interval, no error estimate, and no component decomposition. It only proves the missing equality needed to justify the seven-class endpoint layout. The final cancellation-preserving theorem remains unchanged as the eventual assembly target.

A secondary attack applies to A:

The 054.1.b problem is only an inaccurate comment; the theorem proofs themselves are valid.

The proofs are valid. Production acceptance, however, includes a truthful public contract. A file advertising cell-entry coverage while exporting 31 declarations under a ledger that audits 19 is not ready to serve as a source-locked production interface. The required repair changes no mathematics and is therefore proportionate.

6. Exact next action and validation gates
Selected node
TRANSACTION:
  G2_CCM_CELL13N2_ANTIPODAL_CLASS_CROSSWALK

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMFiniteWeilCell13N2ClassCrosswalk.lean

IMPORT:
  Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
Exact public theorem
lean
theorem ccmWeilTauN1_neg_self_eq_neg_zero
    (mProject : ℕ) (r : ℤ) :
    ccmWeilTauN1 mProject (-r) r =
      ccmWeilTauN1 mProject (-r) 0

Scope and verifier on success: [ABSTRACT][LEAN].

Proof representation

Use only the literal source definitions.

Split r = 0.

For r ≠ 0, prove locally:

lean
ccmQKernel L (-r) r x = ccmQKernel L (-r) 0 x

by unfolding the two off-diagonal branches, using Real.sin_neg, exact cast nonvanishing, and field/ring normalization.

Push that exact identity through the complete Finset.Icc 2 mProject von-Mangoldt sum.

Prove the matching ccmW02Entry identity, treating L = 0 separately so Lean’s division-by-zero convention is not hidden.

Push the kernel identity through the WR constant term and set integral with setIntegral_congr_fun.

Unfold ccmWeilTauN1 and combine the three exact component equalities.

No numeric approximation, interval endpoint, CCMFiniteWeilLogBounds, or Arb artifact is used.

Direct consumer

With r=2, this theorem identifies the two C-orbits:

T(−2,2)=T(−2,0).

With the already imported r=1 identity, transpose symmetry, simultaneous-negation symmetry, ccmModeFinite_two_values, and fin_cases, the seven-class matrix layout becomes source-justified.

Registered prediction
P-054-ANTI:
  The general antipodal identity compiles from the literal source definitions
  with the standard axiom triple and makes the A–G class reduction exact.

P-054-ANTI-MUTANT-1:
  Replacing the first mode `-r` by `r` must fail for a nonzero control mode.

P-054-ANTI-MUTANT-2:
  Replacing the second mode `r` by `2*r` must fail.

P-054-ANTI-MUTANT-3:
  Flipping only the sine-quotient denominator orientation must fail before
  the prime and WR transports.
Gates
DIRECT:
  cd q3.lean.aristotle
  lake env lean \
    Q3/Proofs/RouteB/CCMFiniteWeilCell13N2ClassCrosswalk.lean

TARGET:
  lake build \
    Q3.Proofs.RouteB.CCMFiniteWeilCell13N2ClassCrosswalk

FULL:
  lake build

Q3_CHECK:
  cd ..
  scripts/q3_check.sh \
    q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2ClassCrosswalk.lean

TAINT:
  rg -n \
    '\bsorry\b|\badmit\b|exact\?|\bnative_decide\b|\bopaque\b|\bFloat\b|of_decide_eq_true|^[[:space:]]*axiom\b' \
    q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2ClassCrosswalk.lean

AXIOMS:
  #print axioms Q3.RouteB.ccmWeilTauN1_neg_self_eq_neg_zero

EXPECTED:
  [propext, Classical.choice, Quot.sound]

The repository’s q3_check.sh performs direct Lean execution, proof-hole scanning, and a new-axiom diff check; the additional scan above is required because the SectorCell prohibition list is broader.

SUCCESS:
  G2_CCM_CELL13N2_ANTIPODAL_CLASS_CROSSWALK_PROVED

STOP:
  G2_CCM_CELL13N2_ANTIPODAL_SOURCE_IDENTITY_GAP

The 054.1.b interface repair remains mandatory before the first node that imports that supplier, but it is not to be combined with this one-theorem source crosswalk.

AUTOPSY: 054.1-v2 is source-correct but submission-invalid at this granularity: one syntactic sorry hides multiple independent analytic suppliers, and its advertised seven-class reduction is missing the exact antipodal (−2,2)=(−2,0) source identity.

META CLOSEOUT

What became smaller?

The vague “prove 25 final cell inequalities” target now has an exact first obstruction:

ccmWeilTauN1_neg_self_eq_neg_zero
	​

.

It also has a separated, accurately scoped coefficient library whose production repair is purely interface-level.

What was killed?

all production use of the 054.1.a reconstructed functional;

the claim that 054.1.b closes a cell receiver;

the claim that the listed symmetries alone yield seven endpoint classes;

immediate Aristotle resubmission of the broad one-hole skeleton;

any attempt to promote an external Arb verdict into a Lean theorem.

What must not be tried again?

Do not resubmit a task that asks Aristotle simultaneously to invent the source class crosswalk, von-Mangoldt reduction, π/trigonometric enclosure, Euler bound, integral quadrature, and final 512-bit error ledger. Do not split the final certificate into fabricated component intervals.

Fate of registered evidence

054.1.a surrogate classification:
  CONFIRMED; no retroactive repair.

14 endpoint pairs:
  CONFIRMED byte-for-byte against the Phase-0 ledger.

Relative WR orientation:
  CONFIRMED.

"Seven classes from the listed symmetries":
  REFUTED; one exact antipodal identity is missing.

054.1.b as log/sqrt-only supplier:
  CONFIRMED, but public-surface repair required.
YAML
iteration:
  target: CCM_cell_13_2_real_receiver_v2
  status: OPEN
  failed_strategy: one_broad_fill_sorry_after_surrogate_rejection
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G2_CCM_CELL13N2_ANTIPODAL_SOURCE_IDENTITY_GAP
  invariant_learned: preserve the final-entry cancellation and prove class compression from literal source identities
  forbidden_future_move: invent independent W02_WR_Prime endpoint tables
  next_decisive_test: ccmWeilTauN1_neg_self_eq_neg_zero
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
CODEX DIRECTIVE
TARGET:
  G2_CCM_CELL13N2_ANTIPODAL_CLASS_CROSSWALK

AUTHORIZATION:
  Implement exactly one new Lean file.
  Do not submit Aristotle.
  Do not materialize Goal 055.
  Do not modify route state, Bus files, the endpoint matrices, or any existing
  production definition.

OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMFiniteWeilCell13N2ClassCrosswalk.lean

IMPORT:
  Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

PRIMARY THEOREM:

  theorem ccmWeilTauN1_neg_self_eq_neg_zero
      (mProject : ℕ) (r : ℤ) :
      ccmWeilTauN1 mProject (-r) r =
        ccmWeilTauN1 mProject (-r) 0

PROOF ROUTE:
  1. Split r = 0.
  2. Prove the exact q-kernel antipodal identity by unfolding the literal
     diagonal/off-diagonal branches.
  3. Push it through the complete finite von-Mangoldt sum.
  4. Prove the matching W02 identity, with an explicit L = 0 branch.
  5. Push the kernel identity through the WR constant term and set integral.
  6. Unfold ccmWeilTauN1 and combine exact equalities.

FORBIDDEN:
  reconstructed definitions
  surrogate closed forms
  external Arb verdict
  numeric endpoint use
  CCMFiniteWeilLogBounds import
  sorry
  admit
  exact?
  axiom
  native_decide
  opaque
  Float
  of_decide_eq_true
  theorem weakening

PLANTS:
  P-054-ANTI-1: replace first mode -r by r; control r=2 must reject.
  P-054-ANTI-2: replace second mode r by 2*r; control r=2 must reject.
  P-054-ANTI-3: reverse only the q-kernel denominator orientation; downstream
                  prime/WR equalities must fail.

VALIDATION:
  cd q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/CCMFiniteWeilCell13N2ClassCrosswalk.lean
  lake build Q3.Proofs.RouteB.CCMFiniteWeilCell13N2ClassCrosswalk
  lake build
  cd ..
  scripts/q3_check.sh \
    q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2ClassCrosswalk.lean
  run the full SectorCell taint scan
  #print axioms Q3.RouteB.ccmWeilTauN1_neg_self_eq_neg_zero

EXPECTED_AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  G2_CCM_CELL13N2_ANTIPODAL_CLASS_CROSSWALK_PROVED

FAILURE:
  G2_CCM_CELL13N2_ANTIPODAL_SOURCE_IDENTITY_GAP

REPORT:
  exact file hash
  exact commands and stdout summary
  theorem statement
  axiom output
  taint result
  plant fate
  no Aristotle submission
  CHALLENGER_NOT_RH
  BUS_010 VOID
```

