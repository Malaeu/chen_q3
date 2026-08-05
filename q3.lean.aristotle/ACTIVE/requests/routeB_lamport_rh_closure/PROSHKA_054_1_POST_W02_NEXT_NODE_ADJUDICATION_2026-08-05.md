# STATUS: OPEN — PRIME-KERNEL SEVEN-CLASS EXACT NORMAL FORM SELECTED
```yaml
PRIMARY: SELECT_A_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM
PRIMARY_COUNT: 1
STATUS_CODE: G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM_SELECTED

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: c237cbe44d3e86e5b968d62a1ccc34dba4ec0dbe
  PIN_EXISTS_ON_ORIGIN: true
  PIN_IS_ANCESTOR_OF_CURRENT_RH_CLEAN: true
  CURRENT_RH_CLEAN_HEAD_AT_AUDIT: 9deeb433fe4b098a6f65c80bf1ddd3d5b3aef663
  BRANCH_HEAD_EQUALS_PIN_AT_AUDIT: false
  ADJUDICATION_REF: c237cbe44d3e86e5b968d62a1ccc34dba4ec0dbe
  COMMIT_MESSAGE: "[MacOS][rh_clean][RouteB] Prove CCM W02 seven-class normal form"

CONTEXT_PACK:
  FILE: markdown.md eingefügt
  EXPECTED_SHA256: ee5177ecfdf7c0421c496ab29741dcbf25acd26be78950e6187727827ea0d950
  OBSERVED_SHA256: ee5177ecfdf7c0421c496ab29741dcbf25acd26be78950e6187727827ea0d950
  SHA256_MATCH: true
  PIN_CONTENT_CROSSCHECK: PASS
  WORKTREE_UNTRACKED_FILES_RECORDED: true

BOOTSTRAP:
  PROSHKA_PROTOCOL_FETCHED: true
  ARSENAL_DECK_FETCHED: true
  ARSENAL_DECK_SHA256_LEDGER_MATCH: true
  ARSENAL_MANDATE_2026_08_04_ACCEPTED: true
  ATTACK_DUALS_ACCEPTED:
    - C10_GRAM
    - C03_MULTIPLICITY
    - C12_BOUNDEDNESS
    - C10_FUNCTIONAL
    - C09_PRECOMMIT
  ARSENAL_CARD_USED:
    - C10_FUNCTIONAL_NOT_SURROGATE

NEW_GATE_AUDIT:
  THEOREM: Q3.RouteB.ccmW02Entry_13_seven_class_normal_form
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2W02NormalForm.lean
  FILE_SHA256: 79cfceeb52d7996bbb7a92256b580c4fb7302911166e65613e7eff9fbad49768
  SOURCE_SHA256_MATCH: true
  EXACT_SEVEN_STATEMENTS: PASS
  PROOF_BOUNDARY: EXACT_SYMBOLIC_W02_ONLY
  PUBLIC_THEOREMS: 1
  PUBLIC_DEFINITIONS: 0
  PRIVATE_PLANTS: 3
  PLANTS_SUBSTANTIVE: true
  SOURCE_TAINT_RECHECK: CLEAN
  ARCHIVED_DIRECT_LEAN: PASS
  ARCHIVED_TARGET_BUILD: PASS_7748_JOBS
  ARCHIVED_FULL_BUILD: PASS_7817_JOBS
  ARCHIVED_Q3_CHECK: PASS
  ARCHIVED_AXIOMS: [propext, Classical.choice, Quot.sound]
  JUDGE_RERAN_LEAN: false

NAMED_RUNNER_UP:
  CODE: G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM
  FATE: REQUIRED_AND_EXECUTABLE
  REDUNDANT_DIRECT_WRAPPER_REMAINS_KILLED: true

SELECTED_TRANSACTION:
  CODE: G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM
  STOP: G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM_MISSING
  SUCCESS: G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM_PROVED
  NAMESPACE: Q3.RouteB
  THEOREM: Q3.RouteB.ccmPrimeEntryN1_13_seven_class_exact_normal_form
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2PrimeKernelNormalForm.lean
  SOLE_PRODUCTION_IMPORT: Q3.Proofs.RouteB.CCMFiniteWeilCell13N2W02NormalForm
  PUBLIC_THEOREMS: 1
  PUBLIC_DEFINITIONS: 0
  PRIVATE_HELPERS_ONLY: true
  NUMERICAL_ENCLOSURE: false

DIRECT_DOWNSTREAM_CONSUMER: Q3.RouteB.ccmCell13N2_wr_enclosures
SOLE_RUNNER_UP_AFTER_SELECTED:
  G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM
RUNNER_UP_AUTHORIZED: false

REPO_WRITE_AUTHORIZED_NOW: false
ARISTOTLE_SUBMISSION: NONE
GOAL_055: HOLD_055_RATIFIED
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
H2A_CLOSED: false
G2_CLOSED: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## 1. Source lock, context pack, and standing mandate

The commit `c237cbe44d3e86e5b968d62a1ccc34dba4ec0dbe` exists on GitHub and has the stated W02 commit message. The current `rh_clean` tip has moved one documentation-only commit beyond it, but GitHub's comparison identifies `c237cbe...` as the merge base and ancestor. This review is therefore pinned to the requested immutable commit, not to the moving branch tip. [ABSTRACT][PAPER] fileciteturn6file0 fileciteturn7file0 fileciteturn8file0

The attached context pack hashes byte-for-byte to the supplied digest:

```text
ee5177ecfdf7c0421c496ab29741dcbf25acd26be78950e6187727827ea0d950
```

Its header, commit range, W02 diff, source snapshots, and route-state records cross-check against the pinned repository. The pack also records untracked local files; they are outside the commit and are not admitted as proof inputs. [ABSTRACT][PAPER] fileciteturn0file0

The Proshka protocol, the twelve-card arsenal, and the pending 2026-08-04 mandate were fetched. The repository's byte-exact materialization ledger records the mandated deck SHA-256 `018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d`. I accept the five standing attack-duals. This verdict uses **C10 · functional-not-surrogate** to distinguish a complete prime-component rewrite from a public helper that merely renames an intermediate expression. [ABSTRACT][PAPER] fileciteturn1file0 fileciteturn3file0 fileciteturn4file0 fileciteturn15file0

## 2. Audit of `ccmW02Entry_13_seven_class_normal_form`

### 2.1 Exact theorem surface

The pinned file imports only:

```lean
Q3.Proofs.RouteB.CCMFiniteWeilCell13N2VonMangoldtNormalForm
```

It declares exactly one public theorem, no public definition, and three private plant theorems. The source SHA-256 agrees with the report:

```text
79cfceeb52d7996bbb7a92256b580c4fb7302911166e65613e7eff9fbad49768
```

[FINITE_CELL][LEAN] fileciteturn9file0 fileciteturn18file0

### 2.2 The seven exact statements

Let

\[
L=\operatorname{ccmL}(13),\qquad S=\sinh(L/4)^2.
\]

The theorem proves, in the source representative order:

\[
\begin{aligned}
W_{02}(-2,-2)&=\frac{32LS(L^2-64\pi^2)}{(L^2+64\pi^2)^2},\\
W_{02}(-2,-1)&=\frac{32LS(L^2-32\pi^2)}{(L^2+64\pi^2)(L^2+16\pi^2)},\\
W_{02}(-2,0)&=\frac{32LS}{L^2+64\pi^2},\\
W_{02}(-2,1)&=\frac{32LS(L^2+32\pi^2)}{(L^2+64\pi^2)(L^2+16\pi^2)},\\
W_{02}(-1,-1)&=\frac{32LS(L^2-16\pi^2)}{(L^2+16\pi^2)^2},\\
W_{02}(-1,0)&=\frac{32LS}{L^2+16\pi^2},\\
W_{02}(0,0)&=\frac{32S}{L}.
\end{aligned}
\]

These are exactly the seven representatives consumed by the source-locked `Fin 5 × Fin 5` layout. [FINITE_CELL][LEAN] fileciteturn9file0 fileciteturn10file0

### 2.3 Proof boundary

The proof:

- keeps `ccmL 13`, `Real.pi`, and `Real.sinh (ccmL 13 / 4)` symbolic;
- establishes only the nonvanishing needed for `L`, `L²+16π²`, and `L²+64π²`;
- unfolds only `ccmW02Entry`;
- uses fixed-integer normalization, exact field clearing, and ring identities;
- introduces no interval, decimal, rational endpoint, component ball, or numerical trigonometric claim.

Thus it is a complete exact rewrite of one literal component, not a numerical enclosure and not a sign theorem. [FINITE_CELL][LEAN]

### 2.4 Plant audit

| Plant | Protected semantic fact | Wrong convention rejected |
|---|---|---|
| `P-W02-1` | sign of the mixed product for `(-2,±1)` | replacing the signed product by an absolute product or using one numerator sign for both classes |
| `P-W02-2` | distinction between mode magnitudes `1` and `2` | collapsing `L²+16π²` and `L²+64π²`, or replacing a square by an absolute value |
| `P-W02-3` | exact central cancellation of one power of `L` | dropping or duplicating the central logarithmic power |

The plants mutate different semantic facts and their archived mutant runs all fired. [FINITE_CELL][PAPER] fileciteturn18file0

### 2.5 Taint, execution, and axioms

Independent source inspection finds no `sorry`, `admit`, `exact?`, `native_decide`, declared axiom, opaque certificate, `Float`, or surrogate decision proof. The pinned report records direct Lean PASS, target build PASS with 7,748 jobs, full build PASS with 7,817 jobs, `q3_check` PASS, and exactly:

```text
[propext, Classical.choice, Quot.sound]
```

for `#print axioms Q3.RouteB.ccmW02Entry_13_seven_class_normal_form`. I did not rerun Lean in this review environment; execution claims are ratified from the pinned report, while source hash, theorem shape, public/private surface, taint, and algebraic content were independently re-audited. [FINITE_CELL][PAPER] fileciteturn18file0

## 3. Fate of the named prime-kernel runner-up

### Verdict: `REQUIRED_AND_EXECUTABLE`

The killed theorem was the public direct wrapper

```text
ccmPrimeEntryN1 13 n m = the same nine-point sum still containing ccmQKernel
```

obtained by a one-line specialization of `ccmVonMangoldt_sum_Icc_2_13`. It remains correctly killed: it added a name but removed no source algebra. [FINITE_CELL][LEAN]

The named runner-up is different. A **complete** seven-representative prime-kernel normal form must do all of the following:

1. consume the exact von-Mangoldt support theorem;
2. rewrite `log 4`, `log 8`, and `log 9` to prime-log multiples;
3. rewrite reciprocal square-root weights for `4`, `8`, and `9`;
4. select and normalize the seven literal diagonal/off-diagonal `ccmQKernel` branches;
5. preserve the one-axis orientation in the asymmetric classes;
6. prove that the `k=13` boundary contribution vanishes exactly for every representative;
7. leave all remaining trigonometric values symbolic.

Those steps are not supplied by the generic weighted-sum theorem or its private literal specialization. Without a public complete component theorem, the final cancellation proof would have to repeat this seven-class branch, power, and boundary algebra locally. That is a real downstream wall, not convenience scaffolding. [FINITE_CELL][LEAN]

The theorem is therefore required as the smallest **complete source-only prime component rewrite**. It is executable from pinned Lean and Mathlib facts; it needs no new analytic certificate, no interval data, and no owner-supplied constants. [FINITE_CELL][CONDITIONAL]

Under **C10**, the distinction is exact: the killed wrapper was a surrogate interface; the surviving theorem is the literal scalar component needed by the whole-expression consumer. [FINITE_CELL][PAPER]

## 4. Comparison of A–G

| Candidate | Cancellation preservation | Actual wall reduction | Lean/source dependencies | Public-surface cost | Hidden analytic work | Verdict |
|---|---|---|---|---|---|---|
| **A. Seven prime representatives** | Exact rewrite in place; the `Prime` term remains subtracted in `W02 - WR - Prime`. | Closes the full finite prime support, log-power, square-root-weight, branch-sign, mode-frequency, and `x=L` boundary algebra. | Existing von-Mangoldt theorem, literal `ccmQKernel`, elementary log/sqrt identities, exact trigonometric periodicity. | One theorem, zero definitions. | None; no trig enclosure. | **SELECT.** [FINITE_CELL][CONDITIONAL] |
| **B. Public branch/log/sqrt supplier** | Exact. | Low: it does not consume a production component. | A proper subset of A. | At least one extra interface. | None. | **KILL AS PUBLIC SCAFFOLDING; keep private inside A.** [FINITE_CELL][CONDITIONAL] **[C10]** |
| **C. Full non-integral constant part** | Excellent: rewrites `W02 - WR_constant - Prime` and leaves each integral literal. | High, but it strictly contains A plus WR constant algebra. | W02 theorem, A, `ccmQKernel ... 0`, Euler/log expression. | One large theorem. | No enclosure if kept exact, but it bundles two component walls before A exists. | **TOO LARGE NOW; sole runner-up after A.** [FINITE_CELL][CONDITIONAL] |
| **D. WR constant supplier** | Exact rewrite can preserve orientation; an independent interval can spend cancellation prematurely. | Exact-only version mostly reduces `qKernel(...,0)` and belongs privately inside C. Enclosure version would be meaningful. | Exact branch algebra; enclosure additionally needs Euler–Mascheroni/log/transcendental bounds. | One or more public constants/theorems. | The needed source-locked Euler/log enclosure is absent. | **REJECT NOW: exact part is scaffolding; enclosure part is blocked.** [FINITE_CELL][CONDITIONAL] |
| **E. Spendable cancellation ledger** | Best possible if it proves a real endpoint inequality. | High only with actual audited lower/upper inputs. | Whole-expression envelopes. | One theorem. | Those envelopes do not yet exist; a budget name is not evidence. | **NOT EXECUTABLE.** [FINITE_CELL][CONDITIONAL] |
| **F. First one-representative final/integral enclosure** | Potentially excellent if derived from the whole expression. | Would close one genuine receiver inequality. | Final JSON provenance, exact components, WR integral certificate, Lean import path. | One theorem plus certificate machinery. | The JSON contains final-entry balls, not independent W02, Prime, WR-constant, or integral balls, and there is no Arb-to-Lean importer. | **NOT EXECUTABLE; provenance is insufficient for the requested component/integral claim.** [FINITE_CELL][PAPER] fileciteturn28file0 |
| **G. Owner fork** | N/A. | Appropriate only if every theorem-shaped candidate requires absent data. | Owner-supplied source. | N/A. | N/A. | **NOT TRIGGERED because A is executable.** [ABSTRACT][CONDITIONAL] |

The decisive ordering is therefore:

```text
A now
→ C later
→ numerical whole-expression/integral work only after audited certificates exist.
```

A is representation progress. It does not close a numerical enclosure. [FINITE_CELL][PAPER]

## 5. Selected transaction

### 5.1 File, import, namespace, and public surface

```text
Namespace: Q3.RouteB
Owned file:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMFiniteWeilCell13N2PrimeKernelNormalForm.lean
Sole production import:
  Q3.Proofs.RouteB.CCMFiniteWeilCell13N2W02NormalForm
Public theorems: 1
Public definitions: 0
Private policy: every log/sqrt/kernel/boundary helper and every plant is private
```

The linear import preserves one source chain for the future receiver: weighted von-Mangoldt support → W02 exact normal form → Prime exact normal form. [FINITE_CELL][CONDITIONAL]

### 5.2 Exact Lean theorem statement

```lean
namespace Q3.RouteB

/--
Exact seven-representative symbolic normal form of the literal CCM prime
component for the cell `(13,2)`.  Prime-power logarithms and reciprocal
square-root weights are normalized; the seven fixed `ccmQKernel` branches are
unfolded; the `k = 13` boundary term is proved zero.  No trigonometric value is
numerically enclosed.
-/
theorem ccmPrimeEntryN1_13_seven_class_exact_normal_form :
    let L := ccmL 13
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
    ccmPrimeEntryN1 13 (-2) (-2) = primeFunctional K22 ∧
    ccmPrimeEntryN1 13 (-2) (-1) = primeFunctional K2m1 ∧
    ccmPrimeEntryN1 13 (-2) 0 = primeFunctional K20 ∧
    ccmPrimeEntryN1 13 (-2) 1 = primeFunctional K21 ∧
    ccmPrimeEntryN1 13 (-1) (-1) = primeFunctional K11 ∧
    ccmPrimeEntryN1 13 (-1) 0 = primeFunctional K10 ∧
    ccmPrimeEntryN1 13 0 0 = primeFunctional K00 := by
  ...

end Q3.RouteB
```

[FINITE_CELL][CONDITIONAL]

The omission of a `Real.log 13` summand is not a table edit. It is a theorem consequence: every displayed kernel vanishes at `x = L = Real.log 13`. [FINITE_CELL][CONDITIONAL]

### 5.3 Proof route

1. Set `L := ccmL 13`; prove `0 < L` and `L ≠ 0` from `ccmL_pos`.
2. For each representative, specialize `ccmVonMangoldt_sum_Icc_2_13` to the literal weighted kernel function. Keep that specialization local.
3. Prove private exact power identities:
   - `Real.log 4 = 2 * Real.log 2`;
   - `Real.log 8 = 3 * Real.log 2`;
   - `Real.log 9 = 2 * Real.log 3`;
   - `Real.sqrt 4 = 2`;
   - `Real.sqrt 8 = 2 * Real.sqrt 2`;
   - `Real.sqrt 9 = 3`;
   and derive the corresponding inverse-weight equalities.
4. Unfold only the seven required fixed branches of `ccmQKernel`. Normalize integer casts, `Real.sin_neg`, `Real.cos_neg`, signs, and the denominators `π`, `2π`, and `3π` exactly.
5. Prove all seven `x=L` kernel values zero using the diagonal factor and exact integer-multiple-of-π lemmas; the pinned Mathlib provides `Real.sin_two_pi`, `Real.sin_nat_mul_pi`, and `Real.sin_int_mul_pi`. [ABSTRACT][LEAN] fileciteturn24file0 fileciteturn26file0
6. Reassemble the seven conjunctions by `rw`/`simp`, controlled `field_simp`, and `ring`; do not evaluate any remaining sine, cosine, π, or logarithm numerically.

No helper may become a second public interface. No numerical interval or component endpoint may enter the file. [FINITE_CELL][CONDITIONAL]

## 6. Load-bearing plants

At least the following four plants are required. Each must have a pre-registered mutant and an observed substantive failure.

### `P-PRIME-1` — prime-power weight normalization

Privately prove the exact `k=8` coefficient identity:

\[
\Lambda(8)\,\sqrt 8^{-1}
=
\log 2\,(2\sqrt2)^{-1}.
\]

**Mutants:** use `3 log 2`, use `4 sqrt 2`, or drop the `k=8` contribution. This protects both the von-Mangoldt prime-power convention and the reciprocal-square-root normalization. [FINITE_CELL][CONDITIONAL]

### `P-PRIME-2` — off-diagonal one-axis orientation

Privately prove:

\[
q_L(-2,1;x)
=-\frac{\sin(2\pi x/L)+\sin(4\pi x/L)}{3\pi}.
\]

**Mutants:** reverse `n-m`, use the simultaneous-negation symmetry as a one-axis symmetry, or replace `3π` by `π`. [FINITE_CELL][CONDITIONAL]

### `P-PRIME-3` — diagonal mode frequency

Privately prove:

\[
q_L(-2,-2;x)
=
2\frac{L-x}{L}\cos(4\pi x/L).
\]

**Mutants:** use the mode-one frequency `2π`, route through the off-diagonal branch, or drop the triangular factor. [FINITE_CELL][CONDITIONAL]

### `P-PRIME-4` — exact `p=13` boundary deletion

Privately prove a conjunction containing at least one diagonal and one asymmetric class, for example:

\[
q_L(0,0;L)=0,
\qquad
q_L(-2,1;L)=0.
\]

The production proof must establish all seven boundary zeros. **Mutants:** retain a `log 13` term, use `x=0`, or use a half-period instead of `x=L`. [FINITE_CELL][CONDITIONAL]

These plants protect four different facts: arithmetic support/weight, off-diagonal orientation, diagonal frequency, and endpoint deletion. No coherent wrong convention preserves all four.

## 7. Validation gates

The transaction cannot close without all of the following.

### Lean and build gates

```bash
cd q3.lean.aristotle
lake env lean Q3/Proofs/RouteB/CCMFiniteWeilCell13N2PrimeKernelNormalForm.lean
lake build Q3.Proofs.RouteB.CCMFiniteWeilCell13N2PrimeKernelNormalForm
lake build
cd ..
bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2PrimeKernelNormalForm.lean
```

Report the observed target and full-build job counts; do not copy the preceding node's counts.

### Taint and public-surface gates

```bash
rg -n '\bsorry\b|\badmit\b|exact\?|\bnative_decide\b|\bopaque\b|\bFloat\b|of_decide_eq_true|^[[:space:]]*axiom\b' \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2PrimeKernelNormalForm.lean

rg -n '^(theorem|lemma|def|noncomputable def|abbrev|structure|class)[[:space:]]' \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2PrimeKernelNormalForm.lean
```

Required public surface:

```text
1 public theorem
0 public definitions
0 public helper lemmas
private helpers and private plants only
```

### Git gates

```bash
git diff --check
git status --short
git diff -- \
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2PrimeKernelNormalForm.lean
```

The closeout must identify every changed path. No unrelated state, receiver, Goal 055, or export file may change.

### Axiom gate

```lean
#print axioms Q3.RouteB.ccmPrimeEntryN1_13_seven_class_exact_normal_form
```

Required result, exactly:

```text
[propext, Classical.choice, Quot.sound]
```

### Semantic mutation gate

Each registered mutant for `P-PRIME-1` through `P-PRIME-4` must fail for the intended mathematical mismatch. A parser error, missing import, or unrelated timeout does not count as a fired plant.

## 8. Direct downstream consumer and sole runner-up

The direct consumer is:

```lean
Q3.RouteB.ccmCell13N2_wr_enclosures
```

A later proof can rewrite each `Prime` term exactly inside the frozen inequalities while preserving the source orientation:

\[
W02-WR-Prime.
\]

It may not infer independent Prime intervals from the final 512-bit entry balls. [FINITE_CELL][PAPER] fileciteturn28file0

Exactly one runner-up is named after the selected node:

```text
G2_CCM_054_1_SEVEN_REPRESENTATIVE_NONINTEGRAL_CONSTANT_EXACT_NORMAL_FORM
```

Its intended content is the seven exact forms of

\[
W02-WR_{\mathrm{constant}}-Prime,
\]

with every WR integral kept literal and the subtraction orientation unchanged. It is not authorized by this verdict.

## 9. Strongest attack

The strongest reviewer objection is:

> This is the killed direct prime wrapper expanded seven times. Why should it be public?

That objection is fatal if any right-hand side still contains `ccmQKernel`, `Real.log 4`, `Real.log 8`, `Real.log 9`, `Real.sqrt 4`, `Real.sqrt 8`, `Real.sqrt 9`, or a surviving `k=13` term. In that event the theorem is a cosmetic repetition and must be killed under **C10**. [FINITE_CELL][PAPER]

The selected theorem survives only under the stricter success condition above: all seven kernel branches are literal trigonometric formulas, every composite prime-power log/weight is normalized, and the boundary term is eliminated by proof. That is the discriminator between a complete component rewrite and public scaffolding.

A second objection is that a symbolic theorem could be mistaken for numerical progress. It is not. The theorem proves no rational lower or upper envelope for any sine, cosine, π, logarithm, W02 value, Prime value, WR value, integral, or final entry. [FINITE_CELL][PAPER]

## 10. Route boundary and meta closeout

### What became smaller?

The open prime wall is no longer “normalize the prime component somehow.” It is one exact theorem with seven equations and four semantic plants:

```text
G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM_MISSING
```

### What was killed?

- the already-killed one-line public direct `ccmPrimeEntryN1` wrapper remains killed;
- a public qKernel-branch bundle remains killed as scaffolding;
- a public log/sqrt-power bundle remains killed as scaffolding;
- an interface-only cancellation ledger remains killed;
- inference of component or integral balls from final-entry JSON remains killed.

### What must not be tried again?

Do not publish a prime theorem that retains the generic kernel or composite prime-power arguments. Do not call exact symbolic normalization an enclosure. Do not split final-entry balls into fabricated W02, WR, Prime, or integral tables. Do not move `Prime` across the frozen subtraction orientation.

### Current smallest named gap

```text
G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM_MISSING
```

### Next cheapest decisive test

Before any long proof, prove the four private identities behind `P-PRIME-1` through `P-PRIME-4` in a scratch file importing only the proposed sole production import. If any one cannot be proved without a new analytic assumption, stop with the exact missing lemma rather than weakening the public theorem.

### Fate of registered predictions

```text
P-W02-1, P-W02-2, P-W02-3:
  CONFIRMED by the pinned production report.

Public direct prime wrapper is redundant:
  CONFIRMED; remains REDUNDANT_AND_KILLED.

Complete seven-class prime normalization is substantive:
  CONFIRMED by source-shape audit; Lean execution remains untested.

Finite von-Mangoldt normalization closes prime-kernel algebra:
  REFUTED as an overclaim; the selected theorem is the missing algebra.

Final JSON supplies independent component/integral enclosures:
  REFUTED; provenance supports final-entry balls only.
```

### Strategy memory

```yaml
iteration:
  target: post_W02_smallest_next_node
  status: OPEN
  failed_strategy: publish_direct_prime_specialization_without_kernel_normalization
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM_MISSING
  invariant_learned: complete component rewrites may be public; algebraic suppliers remain private
  forbidden_future_move: infer independent component balls from final-entry intervals
  next_decisive_test: prove four private prime normalization plants from the sole import
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

Goal 055 remains `HOLD_055_RATIFIED`; Aristotle remains `NONE`; Route B remains `CHALLENGER / NOT_RH`; Bus 010 remains `VOID`; no route promotion or RH claim is made. [ABSTRACT][PAPER]

## CODEX DIRECTIVE
```yaml
EXECUTION_AUTHORIZED_NOW: false
REPO_WRITE_AUTHORIZED_NOW: false
ARISTOTLE_AUTHORIZED: false

OWNER_RELEASE_TARGET:
  G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM

WHEN_OWNER_RELEASES:
  CREATE_ONLY:
    - q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2PrimeKernelNormalForm.lean
    - one matching canon/mirror report if the owner separately authorizes report materialization
  NAMESPACE: Q3.RouteB
  SOLE_IMPORT: Q3.Proofs.RouteB.CCMFiniteWeilCell13N2W02NormalForm
  PUBLIC_THEOREM: Q3.RouteB.ccmPrimeEntryN1_13_seven_class_exact_normal_form
  PUBLIC_THEOREMS: 1
  PUBLIC_DEFINITIONS: 0

EXACT_REQUIRED_STATEMENT:
  Use the theorem statement in Section 5.2 without weakening.
  Every right-hand side must contain only the normalized primeFunctional and
  the seven explicit K22/K2m1/K20/K21/K11/K10/K00 trigonometric functions.
  No ccmQKernel, log 4/log 8/log 9, sqrt 4/sqrt 8/sqrt 9, or k=13 term may
  survive in the public conclusion.

PROOF_ROUTE:
  - specialize ccmVonMangoldt_sum_Icc_2_13 locally for each representative
  - normalize prime-power logs and reciprocal square-root weights privately
  - unfold only the seven fixed ccmQKernel branches
  - prove all seven x=L boundary values zero exactly
  - assemble by exact Lean algebra; do not numerically enclose trigonometric values

MANDATORY_PLANTS:
  - P-PRIME-1 prime-power weight at k=8
  - P-PRIME-2 off-diagonal orientation for (-2,1)
  - P-PRIME-3 diagonal frequency for (-2,-2)
  - P-PRIME-4 exact p=13 boundary deletion

FORBIDDEN:
  - public helper theorem or definition
  - retained generic ccmQKernel in the public conclusion
  - numerical sine/cosine/pi/log enclosure
  - independent component endpoint table
  - theorem weakening
  - sorry, admit, exact?, native_decide, opaque certificate, Float, new axiom
  - edits to Goal 055, route state, Bus 010, main exports, or existing Lean files
  - Aristotle submission

VALIDATE:
  - direct lake env lean on the owned file
  - target build and full build with observed job counts
  - scripts/q3_check.sh
  - taint and public-surface scans
  - git diff --check and exact git status
  - substantive mutant failures for all four plants
  - "#print axioms Q3.RouteB.ccmPrimeEntryN1_13_seven_class_exact_normal_form"

EXPECTED_AXIOMS:
  - propext
  - Classical.choice
  - Quot.sound

STOP:
  G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM_MISSING
SUCCESS:
  G2_CCM_054_1_SEVEN_REPRESENTATIVE_PRIME_KERNEL_EXACT_NORMAL_FORM_PROVED
FAILURE_CODES:
  - PRIME_POWER_LOG_WEIGHT_NORMALIZATION_GAP
  - QKERNEL_BRANCH_ORIENTATION_GAP
  - QKERNEL_DIAGONAL_FREQUENCY_GAP
  - PRIME_13_BOUNDARY_ZERO_GAP
  - PUBLIC_SURFACE_BLOAT
  - PLANT_NOT_DETECTED
  - TAINT_OR_AXIOM_PROFILE_FAIL
  - LEAN_BUILD_FAIL
```
