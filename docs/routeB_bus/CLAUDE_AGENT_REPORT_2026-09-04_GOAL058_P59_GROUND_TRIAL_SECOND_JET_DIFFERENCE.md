# GOAL058_P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY — agent report

**Date:** 2026-09-04
**Agent:** Claude (Opus, RouteB Lean agent), autonomous run on owner policy
**Directive:** judge's CODEX_DIRECTIVE `GOAL058_P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY`
**Result: `P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY_KERNEL_GREEN`**

New file (only file created in the Lean tree):
`/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean`

No existing file was edited. Nothing was committed or pushed.

---

## 1. What is proved

With `F_v = proposition59RawTransform L (Finset.Icc (-N) N) v`, i.e. the project's own
`F_v(z) = L^{-1/2} ∑_{k ∈ [-N,N]} v_k · 2 sin(zL/2)/(z − x_k)`, `x_k = proposition59Pole L k = 2πk/L`,
and `κ(F) := −F''(0)/(2 F(0))` written out as the second-jet quotient
`-(iteratedDeriv 2 F 0) / (2 * F 0)`:

| # | Theorem | Statement |
|---|---|---|
| 1 | `proposition59SecondJetCurvature_closed_form` | `hL : 0 < L`, `v : ℤ → ℂ`, `v 0 ≠ 0` ⊢ `κ(F_v) = (L²/2)·(1/12 + (1/(2π²·v₀))·∑_{k ∈ Icc(-N,N)\{0}} v_k/k²)` |
| 2 | `proposition59SecondJetCurvature_positive_modes` | + evenness `∀ k, v (-k) = v k` ⊢ `κ(F_v) = L²/24 + (L²/(2π²·v₀))·∑_{n=1}^{N} v_n/n²` |
| 3 | `proposition59_ground_trial_second_jet_difference` | **main**, complex rows: `κ(F_v) − κ(F_q) = (L²/(2π²))·∑_{k=1}^{N} (v_k/v₀ − q_k/q₀)/k²` |
| 4 | `proposition59_ground_trial_second_jet_difference_real` | real rows `v q : ℤ → ℝ`, same identity with the right-hand side a **coerced real** number |

Hypotheses used, in full: `0 < L`, evenness of both rows (`∀ k, v (-k) = v k`), `v 0 ≠ 0`, `q 0 ≠ 0`.
Nothing else.

## 2. Deviation from the directive's proof route, and why (important)

The directive said to subtract two copies of `proposition59_curvature_closed_form`
(`Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean:1010`). That theorem's
statement is

```lean
theorem proposition59_curvature_closed_form
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) (hv : ∀ k : ℤ, v (-k) = v k)
    (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun k => (v k : ℂ)))) :
    ((proposition59Curvature L N v : ℝ) : ℂ) = (L : ℂ)^2/2 * (1/12 + …)
```

It carries a **real-zero hypothesis** `hzeros`, which the same directive lists as FORBIDDEN.
The hypothesis is there for a reason that does not concern us: `proposition59Curvature` is
*defined* (bridge file line 922) as a **root sum plus tail**, and identifying that root sum with
the second-jet quotient is exactly what needs the zeros to be real.

The quantity the directive asks about, `κ(F) := −F''(0)/(2F(0))`, needs no such hypothesis. So,
per the directive's own fallback clause ("if a step of the closed form is not available in the
form needed, prove the small bridging lemma inside your file"), theorem 1 above **reproves the
same closed form directly from the two exact jets** — one `rw` with
`proposition59RawTransform_secondDerivative_zero` and
`proposition59RawTransform_at_zero_eq_sqrt`, then `field_simp`. Three lines. The result is the
identical right-hand side as `proposition59_curvature_closed_form`, minus `hzeros`.

Consequence for the consumer: the identity holds for **arbitrary** even rows with nonzero centre —
ground row, trial row, Ξ-row, any row — with no spectral or zero-location precondition. That is
strictly stronger than what the directed route would have produced, and it is why the file imports
only `Proposition59EntireTransform` and not the bridge module.

Everything else follows the directive literally: the `1/12` head cancels in the difference, and
`∑_{k≠0} v_k/k² = 2∑_{k≥1} v_k/k²` by evenness.

## 3. What was added, what was closed (`CLOSES` / `OPENS`)

* **CLOSES:** the P59 ground/trial second-jet difference as a kernel-checked finite identity;
  additionally the hypothesis-free closed form of `κ = −F''(0)/(2F(0))` (theorem 1), which was
  previously available only through the `hzeros`-gated bridge.
* **OPENS:** nothing. No new definition, no new axiom, no new input. The file introduces **zero**
  `def`s — the curvature is written out as the second-jet quotient so that no new name competes
  with `proposition59Curvature`. The single private helper
  `sum_erase_zero_Icc_symm_complex` is the ℂ-valued twin of the private
  `sum_erase_zero_Icc_symm` in `Proposition59AlternatingLatticeCurvature.lean:189` — that one is
  `private` and typed `ℤ → ℝ`, hence not reusable from outside; the proof is the same induction.

## 4. Validation — all three runs, verbatim

### 4.1 `lake env lean` (in `q3.lean.aristotle`)

```
$ lake env lean Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean
'Q3.RouteB.proposition59SecondJetCurvature_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59SecondJetCurvature_positive_modes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_ground_trial_second_jet_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_ground_trial_second_jet_difference_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXIT=0            # ${PIPESTATUS[0]} of lake, not of the tee
```

No warnings, no errors, no linter output on the new file.

### 4.2 `lake build` (in `q3.lean.aristotle`)

```
$ lake build Q3.Proofs.RouteB.Proposition59GroundTrialSecondJetDifference
⚠ [7743/7744] Replayed Q3.Proofs.RouteB.Proposition59EntireTransform
  (pre-existing warnings of that dependency: unnecessarySeqFocus ×2, unnecessarySimpa ×2,
   two `aesop: failed to prove the goal after exhaustive search`, one `Nat.Icc_succ_left`
   deprecation — all in Proposition59EntireTransform.lean, untouched by this task)
ℹ [7744/7744] Built Q3.Proofs.RouteB.Proposition59GroundTrialSecondJetDifference (17s)
info: …GroundTrialSecondJetDifference.lean:190:0: 'Q3.RouteB.proposition59SecondJetCurvature_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
info: …:191:0: 'Q3.RouteB.proposition59SecondJetCurvature_positive_modes' depends on axioms: [propext, Classical.choice, Quot.sound]
info: …:192:0: 'Q3.RouteB.proposition59_ground_trial_second_jet_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
info: …:193:0: 'Q3.RouteB.proposition59_ground_trial_second_jet_difference_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Build completed successfully (7744 jobs).
EXIT=0            # ${PIPESTATUS[0]} of lake
```

### 4.3 `scripts/q3_check.sh` (at repo root)

```
$ scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean
lean Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean
'Q3.RouteB.proposition59SecondJetCurvature_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59SecondJetCurvature_positive_modes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_ground_trial_second_jet_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_ground_trial_second_jet_difference_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
scan Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean
q3_check ok
EXIT=0
```

The `scan` step is the hole-marker grep and it is silent: no `sorry`, no `admit`, no `exact?`
anywhere in the file, including the docstrings (the docstring-word trap from
`q3-check-admitted-trap` was avoided deliberately).

### 4.4 Axiom print from a scratch file **outside** the repo

`/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/P59AxiomProbe.lean`
(imports the module and prints axioms — nothing written into the repository):

```
$ lake env lean $SCRATCH/P59AxiomProbe.lean
'Q3.RouteB.proposition59_ground_trial_second_jet_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_ground_trial_second_jet_difference_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.proposition59SecondJetCurvature_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59SecondJetCurvature_positive_modes' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

Expected `[propext, Classical.choice, Quot.sound]` on every theorem — **matched**.
No `sorryAx`, no new axiom.

## 5. Second channel: numeric check against the source formula

Per the owner axiom "agent output is unverified until checked in a *different* channel", the
identity was checked once more without touching the Lean algebra: the left-hand side was computed
by **Cauchy contour integrals** of `F` built straight from the paper formula
`F(z) = L^{-1/2} ∑ v_n · 2 sin(zL/2)/(z − 2πn/L)` (removable node at `z = x_n` given its limit
`L(−1)^n`), the right-hand side from the coefficient rows alone. `mpmath`, 40 digits, `L = 3`,
`N = 4`, random even rows, `v₀ = 1.3`, `q₀ = −0.7`, contour `|z| = 0.3`:

```
kappa_v = 0.1476280696864517817200757263861824635021
kappa_q = 1.600842814466517364963920743357428128014
LHS  = -1.453214744780065583243845016971245664512
RHS  = -1.453214744780065583243845016971245664512
|LHS - RHS| = 2.30e-41
```

The two sides share no code path: the left side sees only `sin`, the poles and a contour integral;
the right side sees only `v_k`, `q_k` and `1/k²`. Agreement to 40 digits.
This is DIAGNOSTIC, never a proof — the proof is §4.

## 6. Progress notes (ETA-style)

| Stage | Wall time | Note |
|---|---|---|
| Locate `proposition59RawTransform`, both jets, `proposition59Curvature`, closed form, evenness pairing | ~4 min | 4 `rg`/`sed` passes; `hzeros` in the closed form spotted here — the one real design decision of the task |
| Write the file (197 lines) | ~6 min | one private pairing lemma + 4 theorems |
| First `lake env lean` | 1 run | two `error: No goals to be solved` — `field_simp` had already closed the goal at two spots; the redundant trailing `ring`s removed |
| Second `lake env lean` | 1 run | clean, all four axiom lines green |
| `lake build` | 17 s (module), 7744 jobs replayed | green |
| `scripts/q3_check.sh` | 1 run | `q3_check ok` |
| Scratch axiom probe | 1 run | expected triple on all four theorems |
| Numeric second channel | ~1 min | agreement to 1e-41 |

No long computations, no overnight jobs, no paid calls, no judge batch consumed.

## 7. Boundaries respected

* Exactly one new Lean file plus this report. No existing file touched.
* `TOOLS.yaml`, `PROSHKA_QUEUE.md`, precommit files and verdicts untouched.
* No commit, no push.
* Forbidden list honoured: no real-zero hypothesis (see §2 — this is the point of the file),
  no eigenvector or gap hypothesis, no cofinal rate claim, no hole marker, no new axiom.
* `PX_RH_CLAIM` not approached: this is a finite-cell identity about two coefficient rows and
  says nothing about `Ξ`, about zeros of anything, or about any limit in `N` or `L`.

## 8. What this closes for the front, in the owner's language

One more rope on the pillar, tightened and bolted: the *difference* of the ground and trial
curvature is now, in kernel, exactly a weighted difference of the two normalized rows — the head
term `L²/24` cancels and cannot hide anything. The numerical probes of 2026-09-04 (Probes 4-6:
`q − y` as the `x²`-modulation of the Ξ-row, `d2 = 0.43‖rem‖`) were all statements about the
row difference `v_k/v₀ − q_k/q₀`; from now on those statements convert into curvature statements
with no further approximation and, notably, with no precondition on where the zeros of `F` sit.
