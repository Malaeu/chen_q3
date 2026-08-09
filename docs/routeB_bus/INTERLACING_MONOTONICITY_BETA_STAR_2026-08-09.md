# Interlacing and monotonicity of the finite `beta*_N` profile — 2026-08-09

Status: finite diagnostic note, not a Lean theorem and not a continuum-gap claim.

Source lock:

- Phase-1 generator: `phase1_scripts/ccm_control_cell_penalty.py`, lines 150–201, `sha256:1be57db69683652ed4f6d56dba6fc3b70c186f429fbb7f5bef978cd84f08ed0d`.
- Phase-2 driver: `phase2_scripts/ccm_beta_n_profile.py`, line 27 and lines 90–125, `sha256:851db5963b4ad012cc3746b2827931b1beedad0b931676d2b40f4cb9ca774f72`.
- Retained result: `PHASE2_RESULTS_2026-08-07.md`, `sha256:40b645862ccc4173377f3718296458ce3aa594d0698a945ce2cc9167d33f347e`.

## F1 — literal entries are cutoff-independent

The pinned Phase-1 builder defines

```text
tau(n,m) = W02(n,m) - WR(n,m) - Prime(n,m)
```

directly from `n`, `m`, and the fixed cell data. No cutoff parameter occurs in the entry formula at lines 150–201. Therefore two cutoffs evaluate the same overlapping matrix entries, subject to the same interval implementation and source pin.

## F2 — the odd blocks form principal corners

Phase 2 builds the odd entry as

```text
K_odd[i-1,j-1] = tau(i,j) - tau(i,-j)
```

at lines 90–101. Combined with F1, the `N1` odd block is the leading principal submatrix of the `N2` odd block whenever `N1 < N2`.

By finite Hermitian Cauchy interlacing, the smallest odd-sector eigenvalue is non-increasing under this nesting. This sentence is a mathematical inference from the pinned construction; it has not been formalized in Lean here.

The even restriction is different: the ambient even blocks nest, but the restricted space `q_N^perp` changes with dimension after zero-padding and Householder construction at lines 111–125. No monotonicity claim for the restricted even floor is made in this note.

## F3 — the retained ladder has four points, all odd-controlled

Inventory correction: the retained ladder is `N = 120, 160, 200, 240`, not a two-point ladder.

| `N` | controlling sector | `a` | `beta*_N` |
|---:|---|---:|---:|
| 120 | odd | `4.7199799795094300e-59` | `3.0559133975151657e-55` |
| 160 | odd | `4.7199799795094300e-59` | `2.7228638920503397e-55` |
| 200 | odd | `4.7199799795094300e-59` | `2.6230059967905176e-55` |
| 240 | odd | `4.7199799795094300e-59` | `2.4778868595077980e-55` |

The observed sequence is strictly decreasing, as predicted for the nested odd competitor. The invariant value of `a` is the zero-padding control: the fixed vector remains in `E_120`, and the low-mode quadratic entry is unchanged.

## F4 — what interlacing settles, and what it does not

Interlacing explains why the binding odd competitor can drift downward with larger finite sections. It does not decide whether

```text
lim_N beta*_N = 0,
```

or whether the sequence approaches a positive floor. It supplies neither the decay rate nor a cofinal lower envelope. A power-law witness decay and positive-floor models can both fit four finite points.

Consequently, the measured ratio `beta*_240 / beta*_120 = 0.8108498302087439...` is finite-section evidence, not an `inf_N > 0` theorem.

## F5 — registered N=480 scope

The frozen N=480 decision rule distinguishes preregistered models of this fixed-`q` witness. A low positive plateau `L <= 1e-56` lies below the current ladder's resolving power and outside that classifier. The N=480 result may therefore re-rank diagnostics without becoming:

- a true-gap decision;
- a uniform operator lower bound;
- a continuum transfer;
- Route B closure;
- an RH claim.

## Decision record

- **Развилка:** interpret the 19% fall as numerical noise, a killed gap, or nested finite-section drift.
- **Выбрали:** nested odd-sector interlacing as the structural explanation; preserve zero-floor and positive-floor possibilities.
- **Почему:** pinned entries are cutoff-independent, odd blocks are principal corners, and all four retained minima are odd-controlled.
- **Что отвергли и почему:** precision-noise explanation is rejected by dual interval algorithms and precision doubling; true-gap conclusions are rejected because finite interlacing has no cofinal lower bound.
- **Техника:** source-addressed construction audit plus Cauchy interlacing.
- **Следующий ход:** N=480 only under its frozen fixed-witness registration; currently on hold.
- **Адреса:** source locks and line addresses at the top of this note.
- **Чей вердикт и аргумент:** local synthesis of Phase-2 evidence; Proshka independently ranks N=480 first only as a fixed-witness classifier.

Boundaries: `CHALLENGER_NOT_RH`; `BUS_010 VOID`; `GOAL_055 HOLD`; no promotion; `PX_RH_CLAIM NOT_MADE`.
