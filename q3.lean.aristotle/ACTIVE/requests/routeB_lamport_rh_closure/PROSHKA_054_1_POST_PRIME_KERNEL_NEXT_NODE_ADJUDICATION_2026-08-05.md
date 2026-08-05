STATUS: OPEN — SELECT_A_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM
YAML
PRIMARY: SELECT_A_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM
PRIMARY_COUNT: 1
STATUS_CODE: G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM_SELECTED

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  ADJUDICATION_REF: b41b4735cd6a2c6b597dcf081dd698882a8203eb
  PIN_EXISTS: true
  PIN_COMMIT_MESSAGE: "[MacOS][rh_clean][RouteB] Prove CCM prime kernel normal form"
  ORIGIN_HEAD_AT_AUDIT: 87e4c72169d1616643fcf7b17c13cdbf79ec7241
  ORIGIN_HEAD_EQUALS_PIN: false
  PIN_IS_DIRECT_PARENT_OF_ORIGIN_HEAD: true
  POST_PIN_CHANGE_CLASS: CONTROL_STATE_ONLY
  PINNED_PRODUCTION_SOURCE_CHANGED_POST_PIN: false

CONTEXT_PACK:
  EXPECTED_SHA256: 0d769f95c31595ce4dbd0396294c36cdf4548c4763c7de770c1c9e1c9d4a395a
  OBSERVED_SHA256: 0d769f95c31595ce4dbd0396294c36cdf4548c4763c7de770c1c9e1c9d4a395a
  SHA256_MATCH: true

PRIME_GATE_AUDIT:
  VERDICT: RATIFIED
  PUBLIC_CONCLUSION_SHAPE: PASS
  FORBIDDEN_RESIDUES_ABSENT: PASS
  LOG13_REMOVED_BY_SEVEN_BOUNDARY_ZEROS: PASS
  NUMERICAL_COMPONENT_INTERVALS_USED: false
  FROZEN_ORIENTATION_CHANGED: false
  SUBSTANTIVE_COMPLETE_COMPONENT_REWRITE: true
  PUBLIC_THEOREMS: 1
  PUBLIC_DEFINITIONS: 0
  AXIOMS: [propext, Classical.choice, Quot.sound]

CANDIDATES:
  A: ACCEPT
  B: REJECT_PUBLIC_SCAFFOLDING
  C: REJECT_PUBLIC_SUBCOMPONENT_WRAPPER
  D: REJECT_AT_THIS_GATE
  E: DEFER_AS_SOLE_RUNNER_UP

SELECTED_NODE:
  NODE: G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM
  STOP_CODE: G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM_MISSING
  SUCCESS_CODE: G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM_PROVED
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean
  NAMESPACE: Q3.RouteB
  SOLE_IMPORT: Q3.Proofs.RouteB.CCMFiniteWeilCell13N2PrimeKernelNormalForm
  PUBLIC_THEOREMS: 1
  PUBLIC_DEFINITIONS: 0
  DIRECT_CONSUMER: Q3.RouteB.ccmCell13N2_wr_enclosures
  SCOPE: FINITE_CELL
  VERIFIER: CONDITIONAL_UNTIL_LEAN_EXECUTION

SOLE_RUNNER_UP:
  NODE: OWNER_FORK_G2_CCM_054_1_SEVEN_REPRESENTATIVE_RELATIVE_WR_INTEGRAL_ENCLOSURES
  AUTHORIZATION: false

ARSENAL_MANDATE_2026_08_04:
  ACCEPTED: true
  ACTIVE_ATTACK_DUALS:
    - C10_GRAM
    - C03_MULTIPLICITY
    - C12_BOUNDEDNESS
    - C10_FUNCTIONAL
    - C09_PRECOMMIT
  USED_IN_THIS_VERDICT:
    - C10_FUNCTIONAL
    - C09_PRECOMMIT

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

GOAL_055: HOLD_055_RATIFIED_OUTSIDE_BUS
ARISTOTLE_SUBMISSION_AUTHORIZED: false
H2A_CLOSED: false
G2_CLOSED: false
ROUTE_PROMOTION: false
RH_CLAIMED: false
ROUTE_B: CHALLENGER_NOT_RH
BUS_010: VOID
Source-lock qualification

The requested mathematical pin is valid. The current remote rh_clean head is no longer exactly b41b4735; it is the direct child 87e4c721…, whose diff only records that this adjudication started in the route-control JSON files. It does not alter the pinned production theorem or its source dependencies. The mathematical adjudication is therefore locked to b41b4735, not silently moved to the later control-plane commit. [FINITE_CELL][PAPER]

The attached pack hash matches the requested SHA-256 and contains the pinned theorem, source definitions, W02 theorem, receiver skeleton, and validation report. 

proshka_ccm_post_prime_context

 [FINITE_CELL][PAPER]

The pending arsenal mandate is accepted. This verdict uses C10 · FUNCTIONAL-NOT-SURROGATE to distinguish a public theorem for the exact final scalar functional from public helper wrappers, and C09 · PRECOMMIT to preserve the already frozen endpoint orientation and class ordering. [ABSTRACT][PAPER]

Exact theorem/proof audit of the completed Prime node
1. Public conclusion shape — confirmed

Apart from the seven literal ccmPrimeEntryN1 13 … left-hand sides and the local bandwidth binding L := ccmL 13, the public right-hand sides contain only:

the normalized local functional primeFunctional;

the seven explicit functions K22, K2m1, K20, K21, K11, K10, K00;

the intended primitive values log 2, log 3, log 5, log 7, log 11 and their corresponding square-root weights;

symbolic sine, cosine, Real.pi, and L.

There is no public helper definition and no public helper theorem. [FINITE_CELL][LEAN]

2. Forbidden residue scan — confirmed

None of the following survives in the public conclusion:

ccmQKernel
Real.log 4
Real.log 8
Real.log 9
Real.sqrt 4
Real.sqrt 8
Real.sqrt 9
an explicit Real.log 13 summand
a k = 13 prime-functional term

L = ccmL 13 remains as the cell bandwidth. That is not a residual k = 13 summand. The theorem correctly retains sqrt 2, sqrt 3, sqrt 5, sqrt 7, and sqrt 11, because those are the normalized prime and prime-power weights, not composite-value debris. [FINITE_CELL][LEAN]

3. The missing log 13 summand is deleted by proof — confirmed

The private consumer first expands the exact finite von-Mangoldt sum. Its last summand is then rewritten at

log13=ccmL(13).

The helper requires a proof

K(ccmL(13))=0.

The public proof supplies seven separate boundary facts:

K
22
	​

(L)=K
2,−1
	​

(L)=K
20
	​

(L)=K
21
	​

(L)=K
11
	​

(L)=K
10
	​

(L)=K
00
	​

(L)=0.

Only after that rewrite does norm_num remove the summand. There is no edited coefficient list with the last term omitted in advance. [FINITE_CELL][LEAN]

This matters: retaining the log 13 term, evaluating at x = 0, or replacing the full period by a half-period would break the proof rather than merely change presentation.

4. No numerical component interval was smuggled in — confirmed

The proof uses exact identities for:

the finite von-Mangoldt support;

prime-power logarithms;

square roots;

the seven literal kernel branches;

integer-multiple trigonometric zeros.

It uses no rational sine, cosine, logarithm, square-root, W02, Prime, WR, integral, or final-entry enclosure. The production report records direct Lean, target build, full build, q3_check, taint, public-surface, semantic-plant, and axiom passes. [FINITE_CELL][LEAN]

The theorem is an equality about the Prime component. It never rewrites the source definition

τ=W02−WR−Prime

into a different sign convention. The frozen relative receiver still has the exact orientation

W02−Prime−τ
upper
	​

≤WR≤W02−Prime−τ
lower
	​

.

[FINITE_CELL][PAPER]

5. Substantive node, not a cosmetic wrapper — confirmed

The theorem closes all of the following in one production boundary:

exact support through Finset.Icc 2 13;

prime-power coefficient normalization at 4, 8, and 9;

the asymmetric off-diagonal denominator;

the diagonal mode frequencies;

seven separate literal kernel branches;

all seven x = L boundary deletions.

The four fired plants protect independent mathematical facts: the k = 8 weight, the asymmetric class orientation, the diagonal frequency, and the endpoint deletion. That is materially more than re-exporting the imported weighted-sum theorem. [FINITE_CELL][LEAN]

Prime gate closeout:

G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM_PROVED

is ratified without qualification. It proves no interval and closes neither G2 nor H2a.

Source claims governing the next split

The literal source entry is

ccmWREntry(L,n,m)=
2
q
L
	​

(n,m;0)
	​

(γ+log(4π
e
L
+1
e
L
−1
	​

))+∫
(0,L]
	​

ccmWRIntegrand(L,n,m;x)dx.

At L = ccmL 13, the pinned source supplies exp L = 13. Exact arithmetic therefore gives

4π
e
L
+1
e
L
−1
	​

=4π
14
12
	​

=
7
24π
	​

.

At x = 0:

the three diagonal representatives have ccmQKernel L n n 0 = 2;

the four off-diagonal representatives have ccmQKernel L n m 0 = 0.

Consequently the WR constant occurs with coefficient exactly one in classes 22, 11, and 00, and vanishes exactly in classes 2m1, 20, 21, and 10. These are source identities, not numerical estimates. [FINITE_CELL][PAPER]

Define only locally in the theorem:

C
13
	​

:=γ+log(
7
24π
	​

).

No independent numerical enclosure of C
13
	​

 is authorized.

Candidate adjudication A–E
Candidate	Verdict	Source-only	Lean-executable now	Directly consumed by ccmCell13N2_wr_enclosures	Frozen orientation preserved	Exact reason
A. Seven-representative nonintegral constant exact normal form	ACCEPT	Yes	Yes	Yes	Yes	It rewrites the exact scalar functional ccmWeilTauN1 13 n m, combining the proved W02 and Prime forms with the exact WR constant while retaining each literal integral inside the subtracted WR term. It is the first theorem whose public conclusion is already the certificate-facing whole expression. [FINITE_CELL][CONDITIONAL]
B. Seven-class theorem only for q_L(n,m;0)	REJECT	Yes	Yes	No; only through another theorem	Yes	It proves a two-valued diagonal/off-diagonal helper. It does not consume W02, Prime, WR, or the final functional. Under C10, this is public scaffolding. Keep it private inside A. [FINITE_CELL][PAPER] [C10]
C. Seven-class decomposition of ccmWREntry	REJECT as a public node	Yes	Yes	Technically yes, but only as one of three rewrites	Yes if used exactly	It is a complete WR-component unfolding, but the final receiver needs the combined scalar W02 - WR - Prime. Publishing C would create a permanent component interface immediately followed by another algebraic composition. Its useful content belongs privately inside A. [FINITE_CELL][PAPER] [C10]
D. No-new-public-theorem route	REJECT at this gate	Yes	Only the exact rewrites are executable; the enclosure is not	Eventually	Potentially	This would mix source normalization, class bookkeeping, external certificate interpretation, and inequality verification in one future analytic file. It saves one public theorem but reopens all source algebra inside the certificate consumer. That is a worse audit boundary. [FINITE_CELL][CONDITIONAL]
E. Immediate analytic owner fork	DEFER	No	No, not without owner data	Yes	Only if whole-expression orientation is retained	The genuine remaining analytic theorem is real, but one exact source-only boundary remains worth materializing first: A. After A, E becomes the sole runner-up and no additional symbolic node is justified. [FINITE_CELL][CONDITIONAL]
Why A survives the hard attack
It is the smallest complete cancellation-preserving consumer

B and C are syntactically smaller. They are not smaller complete consumers.

B stops before a production component. C stops at one component. A reaches the exact scalar object that the final endpoint receiver bounds:

ccmWeilTauN1(13,n,m).

The final analytic checker can consume A without reopening:

ccmW02Entry
ccmPrimeEntryN1
ccmWREntry
ccmQKernel at x = 0
Real.exp (ccmL 13)
the prime-power normalization

It sees exactly seven literal integrals and seven exact symbolic nonintegral thresholds.

It preserves the useful cancellation

A does not prove separate intervals for W02, C
13
	​

, or Prime. It performs exact rewriting only.

The external or future Lean certificate must evaluate

W02
exact
	​

−C
13
	​

−Prime
exact
	​


as one combined expression before any outward rounding. No independent component budget is created. Thus exact normalization of the WR constant does not spend the final-entry cancellation.

The dangerous move would be:

bound W02 independently
bound C13 independently
bound Prime independently
add interval widths

That move remains forbidden.

It is public representation mathematics, not new analysis

A is not an analytic estimate. Its progress class is representation progress.

It is nevertheless a valid public theorem because it establishes the exact source-to-certificate normal form of the literal finite Weil entry and has a named direct consumer. The kill rule forbids an interface-only ledger without a direct proof consumer. A has one.

Selected production contract
Node, stop, and success codes
NODE:
  G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM

STOP:
  G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM_MISSING

SUCCESS:
  G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM_PROVED
Owned path, namespace, and sole import
OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean

NAMESPACE:
  Q3.RouteB

SOLE_PRODUCTION_IMPORT:
  Q3.Proofs.RouteB.CCMFiniteWeilCell13N2PrimeKernelNormalForm
Exact public theorem statement
lean
theorem ccmWeilTauN1_13_seven_class_nonintegral_constant_normal_form :
    let L := ccmL 13
    let S := Real.sinh (L / 4) ^ 2
    let C13 : ℝ :=
      Real.eulerMascheroniConstant +
        Real.log (((24 : ℝ) * Real.pi) / 7)
    let primeFunctional : (ℝ → ℝ) → ℝ := fun K =>
      Real.log 2 *
          ((Real.sqrt 2)⁻¹ * K (Real.log 2) +
            (2 : ℝ)⁻¹ * K (2 * Real.log 2) +
            (2 * Real.sqrt 2)⁻¹ * K (3 * Real.log 2)) +
        Real.log 3 *
          ((Real.sqrt 3)⁻¹ * K (Real.log 3) +
            (3 : ℝ)⁻¹ * K (2 * Real.log 3)) +
        Real.log 5 * (Real.sqrt 5)⁻¹ * K (Real.log 5) +
        Real.log 7 * (Real.sqrt 7)⁻¹ * K (Real.log 7) +
        Real.log 11 * (Real.sqrt 11)⁻¹ * K (Real.log 11)
    let K22 : ℝ → ℝ := fun x =>
      2 * (L - x) / L * Real.cos (4 * Real.pi * x / L)
    let K2m1 : ℝ → ℝ := fun x =>
      (Real.sin (2 * Real.pi * x / L) -
          Real.sin (4 * Real.pi * x / L)) / Real.pi
    let K20 : ℝ → ℝ := fun x =>
      -Real.sin (4 * Real.pi * x / L) / (2 * Real.pi)
    let K21 : ℝ → ℝ := fun x =>
      -(Real.sin (2 * Real.pi * x / L) +
          Real.sin (4 * Real.pi * x / L)) / (3 * Real.pi)
    let K11 : ℝ → ℝ := fun x =>
      2 * (L - x) / L * Real.cos (2 * Real.pi * x / L)
    let K10 : ℝ → ℝ := fun x =>
      -Real.sin (2 * Real.pi * x / L) / Real.pi
    let K00 : ℝ → ℝ := fun x =>
      2 * (L - x) / L

    ccmWeilTauN1 13 (-2) (-2) =
        32 * L * S * (L ^ 2 - 64 * Real.pi ^ 2) /
            (L ^ 2 + 64 * Real.pi ^ 2) ^ 2 -
          (C13 +
            (∫ x in Set.Ioc 0 L,
              ccmWRIntegrand L (-2) (-2) x)) -
          primeFunctional K22 ∧

    ccmWeilTauN1 13 (-2) (-1) =
        32 * L * S * (L ^ 2 - 32 * Real.pi ^ 2) /
            ((L ^ 2 + 64 * Real.pi ^ 2) *
              (L ^ 2 + 16 * Real.pi ^ 2)) -
          (∫ x in Set.Ioc 0 L,
            ccmWRIntegrand L (-2) (-1) x) -
          primeFunctional K2m1 ∧

    ccmWeilTauN1 13 (-2) 0 =
        32 * L * S / (L ^ 2 + 64 * Real.pi ^ 2) -
          (∫ x in Set.Ioc 0 L,
            ccmWRIntegrand L (-2) 0 x) -
          primeFunctional K20 ∧

    ccmWeilTauN1 13 (-2) 1 =
        32 * L * S * (L ^ 2 + 32 * Real.pi ^ 2) /
            ((L ^ 2 + 64 * Real.pi ^ 2) *
              (L ^ 2 + 16 * Real.pi ^ 2)) -
          (∫ x in Set.Ioc 0 L,
            ccmWRIntegrand L (-2) 1 x) -
          primeFunctional K21 ∧

    ccmWeilTauN1 13 (-1) (-1) =
        32 * L * S * (L ^ 2 - 16 * Real.pi ^ 2) /
            (L ^ 2 + 16 * Real.pi ^ 2) ^ 2 -
          (C13 +
            (∫ x in Set.Ioc 0 L,
              ccmWRIntegrand L (-1) (-1) x)) -
          primeFunctional K11 ∧

    ccmWeilTauN1 13 (-1) 0 =
        32 * L * S / (L ^ 2 + 16 * Real.pi ^ 2) -
          (∫ x in Set.Ioc 0 L,
            ccmWRIntegrand L (-1) 0 x) -
          primeFunctional K10 ∧

    ccmWeilTauN1 13 0 0 =
        32 * S / L -
          (C13 +
            (∫ x in Set.Ioc 0 L,
              ccmWRIntegrand L 0 0 x)) -
          primeFunctional K00

This is the complete required public statement. It introduces no public definition: L, S, C13, primeFunctional, and the seven kernels are theorem-local let bindings.

Public surface
PUBLIC_THEOREMS: 1
PUBLIC_DEFINITIONS: 0
PUBLIC_HELPER_LEMMAS: 0
PRIVATE_HELPERS: allowed
PRIVATE_PLANTS: required
Proof route

Set L := ccmL 13 and prove:

lean
have hLpos : 0 < ccmL 13 := ccmL_pos 13 (by norm_num)
have hL : ccmL 13 ≠ 0 := ne_of_gt hLpos

Consume the two existing complete component theorems:

lean
ccmW02Entry_13_seven_class_normal_form
ccmPrimeEntryN1_13_seven_class_exact_normal_form

Use dsimp only at ... and destruct their seven conjunctions. Do not restate or reprove their branch algebra.

Prove privately:

lean
Real.exp (ccmL 13) = 13

using:

lean
ccm_exp_L 13 (by norm_num)

Prove the exact source argument identity:

lean
4 * Real.pi *
    ((Real.exp (ccmL 13) - 1) /
     (Real.exp (ccmL 13) + 1))
  = ((24 : ℝ) * Real.pi) / 7

by rewriting ccm_exp_L, then exact rational algebra.

Prove privately the seven x = 0 q-kernel values:

q22(0)  = 2
q2m1(0) = 0
q20(0)  = 0
q21(0)  = 0
q11(0)  = 2
q10(0)  = 0
q00(0)  = 2

Unfold only the literal ccmQKernel branches. Use hL, Real.sin_zero, Real.cos_zero, norm_num, and ring.

Unfold only:

lean
ccmWeilTauN1
ccmWREntry

Do not unfold ccmWRIntegrand or any set integral.

Rewrite the W02 equations, Prime equations, q-kernel-at-zero equations, and the exact logarithm-argument identity.

Close each equality by exact ring normalization. No transcendental value is numerically enclosed.

Mandatory plants
P-NIC-1 — diagonal/off-diagonal constant selector

Control:

ccmQKernel L (-2) (-2) 0 = 2
ccmQKernel L (-2) (-1) 0 = 0

Mutant: assign coefficient 2 to the off-diagonal class or coefficient 0 to the diagonal class.

Required fate: the mutant reduces to a false real equality.

P-NIC-2 — exact exp L constant

Control:

4π
13+1
13−1
	​

=
7
24π
	​

.

Mutants:

use (exp L + 1)/(exp L - 1)
replace 24*pi/7 by 48*pi/7
replace denominator 7 by 14

At least one must be formalized and must fail by exact arithmetic, not numerical approximation.

P-NIC-3 — load-bearing factor q(0)/2

Control for a diagonal class:

q(0)=2,q(0)/2=1.

Mutant: omit /2, giving coefficient 2 * C13.

Use a generic symbolic constant in the plant so failure does not depend on proving C13 ≠ 0.

P-NIC-4 — subtraction orientation

Control:

W−(C+I)−P.

Mutants:

W - C + I - P
W + (C + I) - P
W - (C + I) + P

Use a generic algebraic plant and instantiate the changed term by 1; parser failure or missing imports do not count.

P-NIC-5 — representative-label integrity

Control the distinction between the (-2,-1) and (-2,1) kernels at an exact test point such as L = 1, x = 1/4.

Mutant: retain the W02 class (-2,-1) but substitute K21 for K2m1, or vice versa.

This detects a conjunction-order or class-label swap during assembly.

Direct downstream consumer

The direct consumer remains:

lean
Q3.RouteB.ccmCell13N2_wr_enclosures

After rewriting by the selected theorem, each representative final-entry inequality has the form

τ
r
−
	​

≤N
r
	​

−∫
(0,L]
	​

f
r
	​

(x)dx≤τ
r
+
	​

,

where N
r
	​

 is one exact combined symbolic expression containing the W02, WR-constant, and Prime terms.

The future analytic work is therefore isolated to seven literal set integrals. It no longer contains finite prime enumeration, q-kernel branch selection at zero, exp (log 13), or component sign assembly.

That is what materially becomes smaller. The interval width does not become larger or smaller merely because the symbolic expression is longer. No analytic inequality has yet been proved.

Validation gates
Direct and build gates
Bash
cd q3.lean.aristotle

lake env lean \
  Q3/Proofs/RouteB/CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean

lake build \
  Q3.Proofs.RouteB.CCMFiniteWeilCell13N2NonintegralConstantNormalForm

lake build

cd ..

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean

The closeout must report the actually observed target and full-build job counts. It must not copy 7749 or 7817 from the Prime report without rerunning.

Taint gate
Bash
rg -n \
  '\bsorry\b|\badmit\b|exact\?|\bnative_decide\b|\bopaque\b|\bFloat\b|of_decide_eq_true|^[[:space:]]*axiom\b' \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean

Required result: no hit.

Public-surface gate
Bash
rg -n \
  '^(theorem|lemma|def|noncomputable def|abbrev|structure|class)[[:space:]]' \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean

Required surface:

1 public theorem
0 public definitions
0 public helper lemmas
Axiom gate

Use a temporary checker:

Bash
cat >/tmp/CCMFiniteWeilCell13N2NonintegralConstantNormalFormAxioms.lean <<'EOF'
import Q3.Proofs.RouteB.CCMFiniteWeilCell13N2NonintegralConstantNormalForm
#print axioms Q3.RouteB.ccmWeilTauN1_13_seven_class_nonintegral_constant_normal_form
EOF

cd q3.lean.aristotle
lake env lean \
  /tmp/CCMFiniteWeilCell13N2NonintegralConstantNormalFormAxioms.lean

Required output, exactly:

[propext, Classical.choice, Quot.sound]
Semantic-mutation gate

All five plants must fire for their intended mathematical mismatch. An unrelated compile failure, timeout, unavailable import, or malformed mutant does not count.

Git gate
Bash
git diff --check
git status --short
git diff -- \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean

The closeout must enumerate every changed path.

External-certificate facts

The existing JSON and Arb work certify final-entry balls externally. They do not serialize independent W02, WR-constant, Prime, or integral intervals. The receiver must therefore remain cancellation-preserving. [FINITE_CELL][PAPER]

The pinned Lean project has integrability and generic quadrature infrastructure, but the pack does not supply the concrete rational derivative bounds, removable-endpoint bounds, quadrature partition, and error ledger needed to prove the seven integral inequalities. Integrability alone is not an enclosure. 

proshka_ccm_post_prime_context

 [FINITE_CELL][PAPER]

No external certificate is imported or trusted by the selected node.

Open analytic obligation and sole runner-up

After A succeeds, no additional exact-normal-form theorem should be inserted.

The sole runner-up is:

OWNER_FORK_G2_CCM_054_1_SEVEN_REPRESENTATIVE_RELATIVE_WR_INTEGRAL_ENCLOSURES

Its minimal owner-supplied data requirement is one of the following, source-locked to the seven literal integrals and the frozen final-entry orientation:

rational derivative and Taylor bounds for the removable extension, together with a rational quadrature partition and checked remainder bounds; or

a direct kernel-checkable whole-expression interval certificate whose verifier proves the seven relative inequalities without inventing component balls.

It must include:

exact mode representative
exact change of variables
endpoint-limit certificate
all interval boundaries and junctions
coverage-completeness proof
directed rounding convention
lower and upper rational result
source hashes and certificate hashes

It may not derive an “integral interval” by subtracting independently rounded component intervals from the final-entry JSON.

Authorization for this owner fork is false.

STRONGEST ATTACK

The proposed theorem is only seven applications of previously proved normal forms plus one unfolding of ccmWREntry. Why should it be public?

That objection is valid unless the theorem satisfies the exact public contract above.

The node is killed under C10 if any of the following occurs:

the public RHS retains ccmW02Entry;
the public RHS retains ccmPrimeEntryN1;
the public RHS retains ccmWREntry;
the public RHS retains ccmQKernel at x = 0;
the public RHS retains Real.exp (ccmL 13);
the integral is moved across the equality or changes sign;
W02, C13, Prime, or the integral receives an independent numerical interval;
a new public C13/q0/helper definition is introduced;
the final receiver must still unfold a source component to expose the integral;
the theorem is not actually imported by the integral-enclosure consumer.

If any one holds, A has collapsed into a decorative ledger and must be replaced by route D or the analytic owner fork.

The repaired statement survives because it gives the exact source-normal form of the scalar functional the receiver bounds, with every analytic unknown visible as one of seven literal integrals. That is the C10 functional, not a Jensen-like or component surrogate.

The strongest mathematical limitation remains unchanged:

A proves no lower or upper envelope for any integral or final entry.

Correct. It is representation progress only. Failure of the later analytic sufficient condition will not certify the negation of the desired enclosure.

FINAL PROPOSAL

Select A as the last source-only symbolic node.

Registered prediction:

P-NIC-MAIN:
  the theorem compiles from the sole import with the standard axiom triple;
  all five plants fire;
  the public conclusion contains exactly seven complete tau normal forms;
  no analytic certificate is needed.

Likeliest failure point:

the proposed public statement accidentally reorders one mixed representative
or fails to normalize the WR constant with the exact q(0)/2 coefficient.

Required response to that failure: repair the exact representative or coefficient. Do not weaken the theorem to a WR-only or q0-only public wrapper.

Meta closeout

What became smaller?

seven source entries with three nested components

becomes:

seven exact symbolic thresholds minus seven literal integrals.

What was killed?

B as a public q-kernel-at-zero bundle;

C as a permanent public WR subcomponent wrapper;

D as a reason to mix source algebra with certificate verification;

immediate owner-fork execution before the exact certificate-facing normal form.

What must not be tried again?

independent component endpoint tables;

separate rounded enclosures for W02, C
13
	​

, and Prime;

movement of WR or Prime across the frozen subtraction orientation;

another symbolic normal-form theorem after A;

calling A a rational or interval enclosure.

Current smallest named gap after success:

G2_CCM_054_1_SEVEN_REPRESENTATIVE_RELATIVE_WR_INTEGRAL_ENCLOSURES

Prior registered prediction fate:

complete Prime normalization is substantive:
  CONFIRMED.

nonintegral constant normal form is the sole source-only runner-up:
  CONFIRMED AFTER ADVERSARIAL COMPARISON.

public q0 or WR-only decomposition is sufficient:
  REFUTED AS A PUBLIC NODE; retained only as private proof structure.

Strategy memory:

YAML
iteration:
  target: post_prime_smallest_cancellation_preserving_node
  status: OPEN
  failed_strategy: publish_subcomponent_helpers_before_the_exact_final_functional
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM_MISSING
  invariant_learned: exact component normalization may be private, but the public boundary must expose the full scalar functional consumed by the certificate
  forbidden_future_move: independently intervalize W02_WRconstant_Prime
  next_decisive_test: compile the exact seven-equation tau normal form and fire P-NIC-1..5
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
CODEX DIRECTIVE
YAML
EXECUTION_AUTHORIZED_NOW: false
REPO_WRITE_AUTHORIZED_NOW: false
ARISTOTLE_AUTHORIZED: false

SELECTED_NODE:
  ID: G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM
  STOP_CODE: G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM_MISSING
  SUCCESS_CODE: G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM_PROVED

ONLY_AFTER_OWNER_STANDING_RELEASE:
  CREATE_ONLY:
    - q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean

  NAMESPACE: Q3.RouteB
  SOLE_IMPORT: Q3.Proofs.RouteB.CCMFiniteWeilCell13N2PrimeKernelNormalForm
  PUBLIC_THEOREM: Q3.RouteB.ccmWeilTauN1_13_seven_class_nonintegral_constant_normal_form
  PUBLIC_THEOREMS: 1
  PUBLIC_DEFINITIONS: 0

  REQUIRED_STATEMENT:
    use_the_exact_statement_in_this_verdict_without_weakening: true
    seven_literal_integrals_retained: true
    ccmWeilTauN1_on_left_hand_sides: true
    W02_WR_Prime_subtraction_orientation_preserved: true
    no_independent_component_intervals: true

  PRIVATE_HELPER_POLICY:
    allowed:
      - exact_exp_ccmL13
      - exact_log_argument_24pi_over_7
      - seven_qkernel_at_zero_values
      - local_conjunction_assembly
      - P_NIC_1_through_P_NIC_5
    forbidden_public:
      - C13_definition
      - qkernel_zero_table
      - WR_component_wrapper
      - imported_theorem_reexports

  MANDATORY_PLANTS:
    - P-NIC-1_DIAGONAL_OFFDIAGONAL_CONSTANT_SELECTOR
    - P-NIC-2_EXP_L_CONSTANT_ARGUMENT
    - P-NIC-3_QZERO_HALF_FACTOR
    - P-NIC-4_SUBTRACTION_ORIENTATION
    - P-NIC-5_REPRESENTATIVE_LABEL_INTEGRITY

  VALIDATION:
    DIRECT:
      - cd q3.lean.aristotle
      - lake env lean Q3/Proofs/RouteB/CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean
    TARGET_BUILD:
      - lake build Q3.Proofs.RouteB.CCMFiniteWeilCell13N2NonintegralConstantNormalForm
    FULL_BUILD:
      - lake build
    Q3_CHECK:
      - bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2NonintegralConstantNormalForm.lean
    TAINT_SCAN:
      forbidden:
        - sorry
        - admit
        - exact?
        - native_decide
        - opaque
        - Float
        - of_decide_eq_true
        - declared_axiom
    PUBLIC_SURFACE:
      expected_theorems: 1
      expected_definitions: 0
      expected_public_helpers: 0
    AXIOMS:
      expected_exactly:
        - propext
        - Classical.choice
        - Quot.sound
    GIT:
      - git diff --check
      - git status --short
      - report_every_changed_path
    JOB_COUNTS:
      copy_from_prior_report: forbidden
      report_observed_counts: required
    MUTANTS:
      parser_or_import_failure_counts_as_fired: false
      all_five_must_fail_for_intended_mathematical_reason: true

FORBIDDEN_FILES_AND_ACTIONS:
  - q3.lean.aristotle/aristotle_input/054_1_v2_CCMFiniteWeilSectorCell13N2.lean
  - q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean
  - q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2W02NormalForm.lean
  - q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2PrimeKernelNormalForm.lean
  - any_tau_endpoint_matrix
  - any_route_state_file
  - any_bus_file
  - any_main_export
  - any_Goal_055_materialization
  - independent_W02_WR_Prime_or_integral_tables
  - theorem_weakening
  - surrogate_CCM_object
  - Aristotle_submission
  - Bus_010_creation
  - route_promotion
  - RH_claim

SOLE_RUNNER_UP:
  ID: OWNER_FORK_G2_CCM_054_1_SEVEN_REPRESENTATIVE_RELATIVE_WR_INTEGRAL_ENCLOSURES
  AUTHORIZED: false
  REQUIRED_OWNER_DATA:
    - source_locked_rational_integral_certificate
    - removable_endpoint_certificate
    - complete_partition_or_direct_whole_expression_verifier
    - directed_rounding_and_error_ledger
    - source_and_certificate_hashes

GOAL_055: HOLD_055_RATIFIED_OUTSIDE_BUS
ROUTE_B: CHALLENGER_NOT_RH
H2A_CLOSED: false
G2_CLOSED: false
ROUTE_PROMOTION: false
RH_CLAIMED: false
BUS_010: VOID
