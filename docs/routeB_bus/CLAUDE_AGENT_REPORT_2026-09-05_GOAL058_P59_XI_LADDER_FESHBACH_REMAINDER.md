# CLAUDE AGENT REPORT — GOAL058 · P59_XI_LADDER_FESHBACH_EXACT_REMAINDER

RESULT: **SUCCESS — `P59_XI_LADDER_FESHBACH_EXACT_REMAINDER_LEAN`**

- Date: 2026-09-05
- Directive: `CODEX_DIRECTIVE / TASK_ID: P59_XI_LADDER_FESHBACH_EXACT_REMAINDER`
  in `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SECOND_MODE_OVERLAP_SUPPLIER_AFTER_TRIAL_CROSSWALK_2026-09-04.md`
  (blocks `Q2_A_LADDER_COMPRESSION`, lines 107-172; `CODEX_DIRECTIVE`, lines 437-464)
- Target file created: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean` (407 lines)
- Executed by: Claude (Opus) agent, owner policy, Linux body. Nothing committed, nothing pushed, no existing file edited.
- Toolchain: Lean `leanprover/lean4:v4.26.0`, Mathlib `v4.26.0` (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

---

## 1. What is formalized

Abstract finite real linear algebra. `K : Matrix (Fin n) (Fin n) ℝ`, ladder synthesis
`B : Matrix (Fin n) (Fin 3) ℝ` with `Bᵀ * B = 1`. Namespace `Q3.RouteB`. Only import is `Mathlib`.

| # | Directive item | Lean declaration | Statement (as compiled) |
|---|---|---|---|
| 1 | orthonormal ladder synthesis, `P`, `Q` | `ladderProj`, `ladderComplement` | `P = B * Bᵀ`, `Q = 1 - P` |
| 1 | `P`, `Q` symmetric idempotents, `P Q = 0` | `ladderProj_isSymm`, `ladderProj_mul_self`, `ladderComplement_isSymm`, `ladderComplement_mul_self`, `ladderProj_mul_ladderComplement`, `ladderComplement_mul_ladderProj`, `ladderProj_add_ladderComplement` | `Pᵀ = P`, `P*P = P`, `Qᵀ = Q`, `Q*Q = Q`, `P*Q = 0`, `Q*P = 0`, `P + Q = 1` |
| 2 | blocks | `ladderBlockA`, `ladderBlockC`, `ladderBlockD` | `A = Bᵀ K B` (3×3), `C = Bᵀ K Q` (3×n), `D = Q K Q` (n×n); plus `ladderBlockA_isSymm`, `ladderBlockD_isSymm`, `ladderBlockC_transpose : Cᵀ = Q K B` |
| 3 | head projected eigen-equation | `ladder_projected_eigen_equation_head` | `(A - lam • 1) *ᵥ (Bᵀ *ᵥ u) + C *ᵥ (Q *ᵥ u) = 0` from `hu : K *ᵥ u = lam • u`, `hB : Bᵀ * B = 1` |
| 3 | tail projected eigen-equation | `ladder_projected_eigen_equation_tail` | `Cᵀ *ᵥ (Bᵀ *ᵥ u) + (D - lam • 1) *ᵥ (Q *ᵥ u) = 0` — an **n-vector identity**, `r = Q *ᵥ u` already in the range of `Q`; needs `hK : K.IsSymm` |
| 4 | `d2` is the first-ladder-row overlap | `ladder_d2_eq_ladderRow_overlap` | `⟪e0, Bᵀ *ᵥ u⟫ = ⟪B *ᵥ e0, u⟫`, `e0 = Pi.single 0 1` |
| 4 | exact remainder | `ladder_d2_exact_remainder` | `⟪e0,p⟫ - ⟪e0,z⟫ = ⟪e0, p - z⟫` for **arbitrary** `z` |
| 4 | normalized remainder | `ladder_d2_exact_remainder_normalized` | with `s = ‖p‖ ≠ 0`, `p' = s⁻¹ • p` : `⟪e0,p⟫ - ⟪e0,z⟫ = (s-1)*⟪e0,z⟫ + s*⟪e0, p' - z⟫` |
| 4 | Cauchy–Schwarz bound | `ladder_d2_remainder_bound` | `|⟪e0,p⟫ - ⟪e0,z⟫| ≤ |1-s|*|⟪e0,z⟫| + s*‖p' - z‖` |
| 4 | supporting | `ladderE0`, `ladderNorm`, `ladderNorm_nonneg`, `ladderE0_dotProduct`, `abs_ladderE0_dotProduct_le` | `‖v‖ := √(v ⬝ᵥ v)`; `|⟪e0,v⟫| ≤ ‖v‖` (Cauchy–Schwarz against the unit `e0`) |
| 5 | Feshbach tail | `ladder_feshbach_tail_eq` | `Q *ᵥ u = -((G * Cᵀ) *ᵥ (Bᵀ *ᵥ u))` |
| 5 | Feshbach effective equation | `ladder_feshbach_effective_equation` | `(A - C*G*Cᵀ - lam • 1) *ᵥ (Bᵀ *ᵥ u) = 0` |
| 5 | block-inverse bridge | `ladder_feshbach_hypothesis_of_blockInverse` | `G * (D - lam • 1) * Q = Q  ⟹  G *ᵥ ((D - lam • 1) *ᵥ (Q *ᵥ u)) = Q *ᵥ u` for every `u` |
| 6 | `u(θ)` plant | `directionalPlantVector`, `directionalPlantVector_self`, `directionalPlantVector_dotProduct_left`, `directionalPlantVector_dotProduct_right`, `directionalPlantVector_tendsto` | `u θ = √(1-θ²) • b + θ • y`; `⟪uθ,uθ⟫ = 1` (for `θ² ≤ 1`), `⟪uθ,b⟫ = √(1-θ²)`, `⟪y,uθ⟫ = θ`, and `Tendsto (fun θ => ⟪uθ,b⟫) (nhds 0) (nhds 1)` |

### Hypothesis choice for item 5 (explicitly stated, as required)

The **weakest clean hypothesis** is used in both Feshbach theorems:

```
hG : G *ᵥ ((ladderBlockD K B - lam • 1) *ᵥ (ladderComplement B *ᵥ u)) = ladderComplement B *ᵥ u
```

that is, `G` inverts `D - lam·1` **on the single vector `r = Q u`**, from the left. No
invertibility of `D - lam·1` on all of `range Q` is assumed, no `Q G = G`, no nonsingularity of
any matrix. The recognizable stronger form is supplied separately and *implies* the weak one:
`ladder_feshbach_hypothesis_of_blockInverse` takes the Q-block inverse
`G * (D - lam·1) * Q = Q` and produces `hG` for every `u`. So a consumer may enter through
either door.

### Forbidden premises — audit

- No smallness of the remainder: `z` is a free `Fin 3 → ℝ` in `ladder_d2_exact_remainder`,
  `ladder_d2_exact_remainder_normalized` and `ladder_d2_remainder_bound`; the identities are
  equalities, not estimates, and the one inequality is a Cauchy–Schwarz bound with no constant.
- The raw compressed vector `z` is **never** identified with `Bᵀ *ᵥ u`. No hypothesis relates them.
- No complement floor, no `O(T_m)` premise, no spectral gap, no simplicity, no Rayleigh excess,
  no cofinal schedule anywhere in the file.
- No `sorry`, no `admit`, no `exact?`, no `axiom` declaration (verified by `q3_check.sh`'s scan
  and by the axiom audit below).
- No post-request numerical result is used as proof. The numeric run in §3 is a *verification
  channel only*; nothing in the Lean file depends on it.

---

## 2. Validation outputs (pasted verbatim)

### 2.1 `lake env lean` (in `q3.lean.aristotle`), exit code via `${PIPESTATUS[0]}`

```
$ cd /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle
$ (lake env lean Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean 2>&1; exit ${PIPESTATUS[0]})
'Q3.RouteB.ladderProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderComplement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderProj_isSymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderProj_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderComplement_isSymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderComplement_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderProj_mul_ladderComplement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderComplement_mul_ladderProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderProj_add_ladderComplement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderBlockA' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderBlockC' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderBlockD' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderBlockA_isSymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderBlockD_isSymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderBlockC_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladder_projected_eigen_equation_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladder_projected_eigen_equation_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderE0' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderNorm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladderE0_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.abs_ladderE0_dotProduct_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladder_d2_eq_ladderRow_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladder_d2_exact_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladder_d2_exact_remainder_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladder_d2_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladder_feshbach_hypothesis_of_blockInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladder_feshbach_tail_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.ladder_feshbach_effective_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.directionalPlantVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.directionalPlantVector_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.directionalPlantVector_dotProduct_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.directionalPlantVector_dotProduct_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.directionalPlantVector_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
LEAN_EXIT=0
```

No errors, no warnings.

### 2.2 `lake build Q3.Proofs.RouteB.P59XiLadderFeshbachRemainder`

```
$ (lake build Q3.Proofs.RouteB.P59XiLadderFeshbachRemainder 2>&1 | tail -20; exit ${PIPESTATUS[0]})
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:387:0: 'Q3.RouteB.ladder_projected_eigen_equation_head' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:388:0: 'Q3.RouteB.ladder_projected_eigen_equation_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:389:0: 'Q3.RouteB.ladderE0' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:390:0: 'Q3.RouteB.ladderNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:391:0: 'Q3.RouteB.ladderNorm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:392:0: 'Q3.RouteB.ladderE0_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:393:0: 'Q3.RouteB.abs_ladderE0_dotProduct_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:394:0: 'Q3.RouteB.ladder_d2_eq_ladderRow_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:395:0: 'Q3.RouteB.ladder_d2_exact_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:396:0: 'Q3.RouteB.ladder_d2_exact_remainder_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:397:0: 'Q3.RouteB.ladder_d2_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:398:0: 'Q3.RouteB.ladder_feshbach_hypothesis_of_blockInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:399:0: 'Q3.RouteB.ladder_feshbach_tail_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:400:0: 'Q3.RouteB.ladder_feshbach_effective_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:401:0: 'Q3.RouteB.directionalPlantVector' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:402:0: 'Q3.RouteB.directionalPlantVector_self' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:403:0: 'Q3.RouteB.directionalPlantVector_dotProduct_left' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:404:0: 'Q3.RouteB.directionalPlantVector_dotProduct_right' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean:405:0: 'Q3.RouteB.directionalPlantVector_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (7743 jobs).
BUILD_EXIT=0
```

### 2.3 `scripts/q3_check.sh` (from repo root)

```
$ cd /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean
$ (scripts/q3_check.sh Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean 2>&1 | grep -v "depends on axioms"; exit ${PIPESTATUS[0]})
lean Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean
scan Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean
q3_check ok
Q3CHECK_EXIT=0
```

### 2.4 `#print axioms` from a **separate scratch file importing the compiled module**

Scratch file: `/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/P59AxiomAudit.lean`,
containing `import Q3.Proofs.RouteB.P59XiLadderFeshbachRemainder` and 34 `#print axioms` lines
(every `def` and every `theorem` of the module, fully qualified).

```
$ (lake env lean "$SP/P59AxiomAudit.lean" 2>&1; exit ${PIPESTATUS[0]})
... 34 lines, all identical in shape ...
AXIOM_EXIT=0

$ sed 's/^.*depends on axioms: //' /tmp/p59_axioms.txt | sort -u
[propext, Classical.choice, Quot.sound]

$ wc -l < /tmp/p59_axioms.txt
34
```

**Every one of the 34 declarations depends on exactly `[propext, Classical.choice, Quot.sound]`**
— the `EXPECTED_AXIOMS` of the directive. No `sorryAx`, no project axiom, nothing else.

---

## 3. Independent verification channel (owner axiom: an agent's claim is unverified until a
different channel confirms it)

The Lean kernel is the first channel. A second, structurally independent channel: a numeric run
with `numpy` on a random 9×9 symmetric `K`, `B` from a QR factorization, `(lam, u)` the **second**
exact eigenpair from `numpy.linalg.eigh` (not from anything the Lean file computes), a
pseudo-inverse Q-block `G`, and a random `z`. The two sides share no code and no dictionary.

```
P sym 0.00e+00  P^2-P 2.22e-16  PQ 1.21e-16
block eq1 8.23e-16   block eq2 1.01e-15
Feshbach hyp G(D-lam)r=r 8.61e-15   r=-GC^T p 3.27e-14   effective 1.05e-14
d2=<Be0,u> 4.16e-17   raw remainder 0.00e+00   normalized 5.55e-17
|d2-<e0,z>|=0.381889 <= bound 0.451169 : True
plant: <ut,ut>=1.000000000000  <ut,b1>=0.999549898704 sqrt(1-th^2)=0.999549898704  <y,ut>=0.030000000000 theta=0.03
```

All residuals at machine precision; the Cauchy–Schwarz bound holds and is not tight (0.3819 vs
0.4512), i.e. it is a real inequality, not a disguised equality. The plant line reproduces the
judge's observation directly: at `θ = 0.03` the directional accuracy toward `b1` is `0.99955`
while the `y`-overlap is exactly `0.03` — 99.955 % directional accuracy gives no relative control
of `d2`.

This is a DIAGNOSTIC, never a proof. It is recorded only because the directive forbids using
numerics as proof and the owner's rule requires a second channel for any agent claim.

---

## 4. Shelf check performed before writing (rule «спроси полку первой»)

```
$ rg -n "Feshbach|Schur complement|schurComplement" q3.lean.aristotle/Q3 | head -30
```

Existing project material found and inspected:

- `q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean` — **rank-one**
  complex trial-*line* Feshbach/Schur decomposition of the literal CCM source cell
  (`complexTrialLineProjection q`, one row `q`, `ℂ`, literal source objects). It is a different
  object: one-dimensional projector, complex, tied to `D0Pstar.sourceCCM*`. It gives the shifted
  matrix identity `K - a·1 = q r* + r q* + Q(K-a·1)Q`, not the block eigen-equations of a
  three-dimensional ladder, and it carries no eigenpair, no `d2`, no `G`.
- `D0Mode4BackwardTailFiniteSchurCrosswalk.lean`, `D0PstarSourceWeilShiftedOddHeadSchur.lean`,
  `D0PstarSourceWeilOddTargetFloorSchurReduction.lean`, `CofinalFixedShiftLiteralComplementFloor.lean`
  — Schur complements of *literal source truncations*, all specialized to the `D0Pstar` data and to
  positivity/floor questions. None states a projected eigen-equation pair or a `d2` remainder.
- Mathlib's `Matrix.fromBlocks` / `Matrix.schur_complement` family was checked and **not** used:
  those lemmas are about `fromBlocks`-shaped matrices and `IsHermitian`/PosSemidef inertia, whereas
  the judge's object is an oblique-free `B / Q` resolution of the *same* index type `Fin n`. Forcing
  a `fromBlocks` reindexing would have added an equivalence layer and lengthened, not shortened, the
  proofs. The file is self-contained over `Matrix.mulVec` / `dotProduct`, as the directive suggested.

CLOSES (per the directive): `P59_XI_LADDER_COMPRESSION_BLOCK_EQUATIONS`,
`P59_XI_LADDER_D2_EXACT_REMAINDER`.
OPENS: nothing. No new input, no new supplier, no new tool is created by this file.

---

## 5. What this does NOT give (kept explicit, so the file is not over-read)

The Feshbach effective equation is the *statement of the problem*, not its solution. Nothing here
bounds the `e0`-coordinate change caused by the self-energy `C G Cᵀ`, and nothing here selects the
compressed second mode coherently. That remains the judge's `FIRST_FAILURE` and the open analytic
items `P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M`, `P59_SECOND_MODE_SELECTION_COHERENCE`,
`P59_COMPRESSED_SECOND_RITZ_VECTOR_ASYMPTOTIC`. The `u(θ)` plant is formalized precisely to make
the trap unrepeatable: it is now a kernel-checked object that directional accuracy toward the
quadratic ladder direction does not control `d2`.

The `EXECUTION_AUTHORIZED_BY_THIS_VERDICT: false` flag of the directive is noted: this run produced
the artifact and validated it, and stopped there. Nothing was committed or pushed; no existing file
was modified; `TOOLS.yaml`, `PROSHKA_QUEUE.md`, precommit files and verdict files were not touched.

---

SUCCESS CODE: `P59_XI_LADDER_FESHBACH_EXACT_REMAINDER_LEAN`
