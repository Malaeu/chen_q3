# CLAUDE AGENT REPORT — GOAL058 / Weil "Gram minus shift" finite algebra

```yaml
REPORT_DATE: 2026-09-05
SUCCESS_CODE: WEIL_GRAM_MINUS_SHIFT_KERNEL_GREEN
BOUNDARY_ID: GOAL058_DIRECT_WEIL_SOURCE_PROOF_CONSTRUCTION
SOURCE_VERDICT: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DIRECT_WEIL_SOURCE_PROOF_2026-09-04.md
SOURCE_SECTIONS_USED: ["2", "4", "9"]
LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/WeilGramMinusShift.lean
LEAN_FILE_SHA256: 65ca4b3429b516146818c0f73950fe2ff1137d58cd1c1f42f52b150b21f8e7a1
LEAN_FILE_GIT_BLOB: 5343f3001580c22c19a9e5bb1d0a7ba9518f06a9
LEAN_FILE_LINES: 395
BASE_COMMIT_AT_WORK_TIME: ae0c260af30705de0b26a859bc2a90043aebd34b
TOOLCHAIN: leanprover/lean4:v4.26.0 (mathlib rev v4.26.0)
LEAN_KERNEL_RERUN: true
AXIOM_PROFILE: [propext, Classical.choice, Quot.sound]   # all 25 theorems
DECLARATIONS: 25 theorems + 2 definitions
NUMERICAL_EXPERIMENT_PERFORMED: true
COMMIT_PERFORMED: false
PUSH_PERFORMED: false
EXISTING_FILES_MODIFIED: none
ROUTE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
K_PSD_CLAIM: NOT_MADE          # explicitly refuted as an inference from Γ ⪰ 0
ANALYTIC_INTEGRAL_FORMALIZED: false
SOURCE_CROSSWALK_TO_CCM_ENTRIES: false
```

## 1. What was asked and what was produced

The judge's §9 proposes two LEAN-READY finite-algebra heads. Both are now Lean
declarations, kernel-checked, with the standard three-axiom profile:

1. `weil_pole_difference_of_squares` — the scalar pole identity behind (3).
2. `weil_translation_gram_minus_shift` — the finite quadratic assembly of (8),
   packaged from the separately named parts (a), (b), (c), together with the
   plant (d), the equivalence (e), and the positivity ingredients (f).

Nothing analytic entered. No integral is modelled. No RH-conditional statement
appears. No new axiom was introduced.

## 2. Declaration map (file: `q3.lean.aristotle/Q3/Proofs/RouteB/WeilGramMinusShift.lean`)

Namespace `Q3.RouteB`.

| Judge's item | Lean declaration | Statement |
|---|---|---|
| (1) §9.1 | `weil_pole_difference_of_squares` | `∀ A B : ℂ, 2 * (A * conj B).re = 2‖(A+B)/2‖² − 2‖(A−B)/2‖²` |
| (1) applied | `weil_pole_difference_of_squares_cosh_sinh` | `2‖C‖² − 2‖S‖² = 2 * ((C+S) * conj (C−S)).re` — the `C_L`/`S_L` reading of (3) |
| object | `rankOneStar` (def) | `rankOneStar v = vecMulVec v (star v)`, i.e. `v v*` |
| object | `weilShiftMatrix` (def) | `K = Γ − (c_L : ℂ) • 1 − 2 • rankOneStar β`, `c_L : ℝ` |
| helper | `rankOneStar_posSemidef` | `(rankOneStar v).PosSemidef` — reuses `Matrix.posSemidef_vecMulVec_self_star` |
| helper | `quadForm_rankOneStar` | `c*(v v*)c = conj(v*c) · (v*c)` |
| helper | `dotProduct_star_self`, `conj_mul_self_ofReal` | the two "this scalar is real" casts |
| **(a)** | `weilShiftMatrix_quadForm` | `c*Kc = c*Γc − c_L (c*c) − 2 conj(β*c)(β*c)` for all `c`; no positivity used |
| (a) real | `weilShiftMatrix_re_quadForm` | `Re(c*Kc) = Re(c*Γc) − c_L ∑‖cᵢ‖² − 2‖β*c‖²` |
| **(b)** | `weilShiftMatrix_add_shift` | `K + c_L•1 + 2•ββ* = Γ` (matrix identity) |
| **(b)** | `weilShiftMatrix_add_shift_posSemidef` | `Γ ⪰ 0 → (K + c_L•1 + 2•ββ*) ⪰ 0` |
| helper | `norm_dotProduct_star_sq_le` | discrete Cauchy–Schwarz: `‖β*c‖² ≤ (∑‖βᵢ‖²)(∑‖cᵢ‖²)` |
| **(c)** | `weilShiftMatrix_re_lower_bound` | `Γ ⪰ 0 → −(c_L + 2∑‖βᵢ‖²)·∑‖cᵢ‖² ≤ Re(c*Kc)`, i.e. `λ_min(K) ≥ −(c_L + 2‖β‖²)` |
| helper | `smul_one_isHermitian`, `weilShiftMatrix_isHermitian` | `Γ` Hermitian ⇒ `K` Hermitian |
| **(e)** | `weilShiftMatrix_posSemidef_iff` | `Γ` Hermitian ⇒ (`K ⪰ 0` ↔ `∀c: c_L(c*c) + 2 conj(β*c)(β*c) ≤ c*Γc`) |
| **(d)** | `weilShiftMatrix_plant_gamma_posSemidef` | `(diagonal ![0,2]).PosSemidef` |
| **(d)** | `weilShiftMatrix_plant_eq` | `weilShiftMatrix (diagonal ![0,2]) 1 0 = diagonal ![-1,1]` |
| **(d)** | `weilShiftMatrix_plant_negative` | `∃ c, Re(c*Kc) < 0` — witness `c = ![1,0]`, value `−1` |
| **(d)** | `weilShiftMatrix_plant_not_posSemidef` | `¬ (weilShiftMatrix (diagonal ![0,2]) 1 0).PosSemidef` |
| **(d)** | `weilShiftMatrix_plant` | the pair: `Γ ⪰ 0` **and** `¬ K ⪰ 0` |
| **(f)** | `posSemidef_gramMatrix` | for `v : n → E`, `E` a complex inner-product space, `(of fun j k => ⟪v j, v k⟫_ℂ).PosSemidef` |
| **(f)** | `posSemidef_conjTranspose_mul_self'` | `(Gᴴ * G).PosSemidef` — the `D(t) = G(t)ᴴ G(t)` form, reuse of Mathlib |
| **(f)** | `posSemidef_weighted_sum` | `wᵢ ≥ 0`, `Mᵢ ⪰ 0` ⇒ `(∑ᵢ∈s, (wᵢ:ℂ) • Mᵢ) ⪰ 0` (**finite** sum only) |
| **(f)** | `weilGamma_posSemidef` | `(∑ᵢ∈s, (wᵢ:ℂ) • Dᵢ) + 2 • αα* ⪰ 0` |
| **head (2)** | `weil_translation_gram_minus_shift` | conjunction of (a), (b), (c) under `Γ ⪰ 0` |

Shelf reuse (existing declarations, not re-proved): `Matrix.PosSemidef`,
`Matrix.posSemidef_vecMulVec_self_star`, `Matrix.posSemidef_conjTranspose_mul_self`,
`Matrix.posSemidef_sum`, `Matrix.PosSemidef.add`, `Matrix.PosSemidef.smul`,
`Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`,
`Matrix.PosSemidef.dotProduct_mulVec_nonneg`, `Matrix.posSemidef_diagonal_iff`,
`Complex.zero_le_real`, `Complex.nonneg_iff`, `EuclideanSpace.inner_toLp_toLp`,
`EuclideanSpace.norm_sq_eq`, `norm_inner_le_norm`.

Shelf survey run first (`rg -n "PosSemidef|posSemidef|Gram" q3.lean.aristotle/Q3` and
`./ask.sh "Gram"`): the repository has nine RouteB files touching `Matrix.PosSemidef`
(`CofinalFixedShiftLiteralComplementFloor`, `H2aPenaltyCoercivity`,
`G6N1SelectedFerrersFiniteAssetBank`, `D0HermitianNegativeIndexDrop`, …), all of
them *consumers* of a PSD certificate on an already-assembled matrix. None of them
states the `Γ − c_L I − 2ββ*` decomposition or the plant. `./ask.sh "Gram"` returns
four standing kills around Gram-based floors, including
`full_matrix_gram_existence_as_supplier` and
`moving_shift_gram_certificates_or_silent_fixed_shift_substitution` — this file does
not resurrect either: it supplies no floor and no moving-shift certificate, it only
records that the shift is subtracted and that the subtraction can turn the sign.

## 3. Validation — pasted outputs

### 3.1 `lake env lean` (in `q3.lean.aristotle`)

```
$ cd /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle
$ lake env lean Q3/Proofs/RouteB/WeilGramMinusShift.lean; echo "EXIT=${PIPESTATUS[0]}"
EXIT=0
```

No output: no errors, no warnings.

### 3.2 `lake build`

```
$ lake build Q3.Proofs.RouteB.WeilGramMinusShift; echo "EXIT=${PIPESTATUS[0]}"
✔ [2375/2375] Built Q3.Proofs.RouteB.WeilGramMinusShift (7.2s)
Build completed successfully (2375 jobs).
EXIT=0
```

### 3.3 `scripts/q3_check.sh` (repo root)

```
$ scripts/q3_check.sh Q3/Proofs/RouteB/WeilGramMinusShift.lean; echo "EXIT=${PIPESTATUS[0]}"
lean Q3/Proofs/RouteB/WeilGramMinusShift.lean
scan Q3/Proofs/RouteB/WeilGramMinusShift.lean
q3_check ok
EXIT=0
```

### 3.4 Axiom profile

Scratch file
`/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/AxiomProfile.lean`
imports the module and prints the axioms of every theorem:

```
'Q3.RouteB.weil_pole_difference_of_squares' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weil_pole_difference_of_squares_cosh_sinh' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.rankOneStar_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.quadForm_rankOneStar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.dotProduct_star_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.conj_mul_self_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_quadForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_re_quadForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_add_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_add_shift_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.norm_dotProduct_star_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_re_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.smul_one_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_posSemidef_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_plant_gamma_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_plant_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_plant_negative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_plant_not_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilShiftMatrix_plant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.posSemidef_gramMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.posSemidef_conjTranspose_mul_self'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.posSemidef_weighted_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weilGamma_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.weil_translation_gram_minus_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Expected profile `[propext, Classical.choice, Quot.sound]` on all 25 printed
declarations. No `sorryAx`, no project axiom.

### 3.5 Second channel — numpy

Script:
`/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/check_weil_gram_minus_shift.py`
(seed 20260905). It re-derives (1) and (a)–(f) from the mathematical statements
on random complex data; it does not read the Lean proofs.

```
[PASS] (1) weil_pole_difference_of_squares max err 3.553e-15
[PASS] (a) quadratic-form identity max err 1.139e-13
[PASS] (b) K + c_L I + 2 bb^H = Gamma and is PSD max entry err 3.997e-15, min eig 5.225e-04
[PASS] (c) Cauchy-Schwarz lower bound min slack 7.774e-04
[PASS] (c') lambda_min(K) >= -(c_L + 2||beta||^2) min slack 1.218e-02
[PASS] (d) plant: Gamma PSD, K = diag(-1,1), c*Kc = -1.0 < 0
[PASS] (e) PSD(K) <=> frame bound (GAP-GRAM) violations 0
[PASS] (f) Gram matrix PSD min eig -4.912e-15
[PASS] (f) weighted sum + 2 alpha alpha^H PSD min eig 8.191e-02

RESULT: ALL CHECKS PASS
```

Cell counts: 2000 scalar draws for (1); 500 random `Γ = GᴴG` instances of size
1–6 for (a) and (b); 2000 for (c) and (c'); 400 instances × 3 values of `c_L`
(random, below the threshold, above it) for (e); 300 instances each for the two
(f) checks.

This is a table on random cells, not a certificate. It is here to kill a
mis-transcription of the identity, not to prove anything.

## 4. Internal non-vacuity check

`Matrix.PosSemidef` over `ℂ` uses the scoped `ComplexOrder` instance, so a
degenerate reading of the predicate would make the whole file empty. Two theorems
in the file rule that out from both sides:

* `weilShiftMatrix_plant_gamma_posSemidef` proves the predicate holds for a
  concrete matrix (it is not always false);
* `weilShiftMatrix_plant_not_posSemidef` proves it fails for a concrete matrix
  (it is not always true).

Both are needed for `weilShiftMatrix_posSemidef_iff` and
`weilShiftMatrix_add_shift_posSemidef` to carry content.

## 5. What this file does **not** do

Explicit, because the failure mode the judge names is exactly the inference this
file must not license.

* **It does not claim `K ⪰ 0`.** `weilShiftMatrix_plant` is the counterexample:
  `Γ = diag(0,2) ⪰ 0`, `c_L = 1`, `β = 0`, `K = diag(−1,1)`, and `c = (1,0)` gives
  `c*Kc = −1`. A checker that verifies only `Γ ⪰ 0` must reject `K ⪰ 0`.
* **It contains no integral.** The verdict's `Γ` is
  `∫₀^L a(t) D(t) dt + Σ_{n≤m} (Λ(n)/√n) D(log n) + 2αα*`. Only the finite
  weighted-sum shape is formalised (`posSemidef_weighted_sum`,
  `weilGamma_posSemidef`); the archimedean integral term is out of scope and is
  stated as such in the file's own docstrings. Nothing in the file asserts that
  the finite sum equals the verdict's `Γ`.
* **It contains no source crosswalk.** The literal CCM entries `ccmQKernel`,
  `ccmW02Entry`, `ccmPrimeEntryN1`, `ccmWREntry` of
  `Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean` are not referenced. The claim
  of §4 of the verdict that (8) reproduces those entries is **not** verified here.
* **No RH-conditional statement, no route promotion, no `PX_RH_CLAIM`.**
* **The frame bound (GAP-GRAM) is not proved.** `weilShiftMatrix_posSemidef_iff`
  only says that proving `K ⪰ 0` and proving the frame bound are the same task.
  It restates the open problem in Lean; it does not shrink it.

## 6. Remaining obligations, in the judge's own terms

1. `(GAP-GRAM)`: `∀c: c*Γ_{m,N(m)}c ≥ (c_L − e_m)‖c‖² + 2|β*c|²` with `e_m ≥ 0`,
   `e_m → 0`, proved directly from the entries. Nothing in this file bears on it.
2. The source crosswalk of §4 (that (8) with the stated phases and constants is
   the literal CCM matrix). Registered by the judge as
   `P_WEILPROOF_LITERAL_GRAM_IDENTITY_SURVIVES_SOURCE_CHECK: 0.85`, still `PENDING`.
3. The integral form of the archimedean term, if the assembly is ever to be
   formalised end-to-end rather than as a finite surrogate.
4. Head (3) `weil_smooth_test_diagonal_recovery` (§7 fixed-test recovery) — not
   attempted here; the judge names it as the single proposed Codex task.

## 7. Files

* Lean source (new, untracked, not committed):
  `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/WeilGramMinusShift.lean`
* This report (new, untracked, not committed):
  `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/CLAUDE_AGENT_REPORT_2026-09-05_GOAL058_WEIL_GRAM_MINUS_SHIFT.md`
* Axiom scratch:
  `/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/AxiomProfile.lean`
* Numeric scratch:
  `/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/check_weil_gram_minus_shift.py`
* Source verdict:
  `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DIRECT_WEIL_SOURCE_PROOF_2026-09-04.md`

No existing file was modified. No commit, no push, no registry entry
(`docs/cartographer/TOOLS.yaml` is untouched — this is a proof file, not a tool,
but if the project wants it visible to `brief.py`/`cheap.py` that registration is
an owner decision, not mine).
