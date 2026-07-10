# MYTHOS_PROSHKA_HANDOFF: TailReturnProbe_v1

STATUS: STOP.
SCOPE: NOT_RH; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.

## Verdict

Code: `AMBIGUOUS + LEDGER_CONSISTENT + MASS_P_OUT_OF_RANGE`.

This is not `TROUGH_EXTENDED`: the last marathon window exits the trough by the registered C-band judge.

This is not full `TAIL_RETURN_CONFIRMED`: the marathon `p_mass(W7/W8)` judge is still below the registered band.

## Registered scoreboard

| Registered item | Measured | Verdict |
| --- | ---: | --- |
| R1 `C_eff(W8)` in `[6e-29, 1.1e-28]` | `8.88720589993e-29` | PASS |
| R1 fork: all `W5..W8 C_eff < 4e-29` | false | `TROUGH_EXTENDED` REFUTED |
| R2 `S5000/a1 in [0.90,0.96]`, rising | `0.911323348114`, rising true | PASS |
| R3 ledger C refit within `+-15%` of `7.9e-29` | checkpoint mean `8.77110786822e-29`, rel miss `0.110266818762` | PASS |
| R4 `p_mass(W7/W8) in [0.7,1.5]` | `0.468369826058` | MISS |
| ceiling `S_J/a1 <= 1.05` | max `0.911323348114` at J=5000 | PASS |
| zoned realness | all windows finite; `Im(K*conj(K))=0` | PASS |

## Tail profile

Checkpoints:

| J | gamma | `S_J/a1` | `C_from_residual` |
| ---: | ---: | ---: | ---: |
| 2500 | `3031.28921746806` | `0.877049677733` | `9.36121197761e-29` |
| 3000 | `3533.32824339582` | `0.884719611093` | `9.68359145645e-29` |
| 4000 | `4506.31149672882` | `0.899358441396` | `1.00526187216e-28` |
| 5000 | `5447.86199830130` | `0.911323348114` | `1.02476813437e-28` |

Windows:

| Window | `DeltaS/a1` | `C_eff` |
| --- | ---: | ---: |
| W5 `[2000,2500]` | `0.00645199347220` | `5.14354910794e-29` |
| W6 `[2500,3000]` | `0.00766993336060` | `6.64586320936e-29` |
| W7 `[3000,4000]` | `0.0146388303023` | `7.91853283880e-29` |
| W8 `[4000,5000]` | `0.0119649067183` | `8.88720589993e-29` |

Adjacent mass exponents:

| Pair | `DeltaS` ratio | `p_mass` |
| --- | ---: | ---: |
| W6/W7 | `0.523944413741` | `0.116654058340` |
| W7/W8 | `1.22348052074` | `0.468369826058` |

Interpretation: the profile has returned to the ledger C-level and the mass is rising into the registered S-band, but the strict adjacent-window law judge still rejects the marathon `p~1` claim. Treat this as a mixed tail-return result, not as a clean law confirmation.

## READ-ONLY IMPORTS quote from STATE

Verbatim section from `ROUTE_B_STATE.md`:

```md
## READ-ONLY IMPORTS (do not edit)

Canonical Mythos docs dir: `/Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs`.

Paths are relative to `q3.lean.aristotle/`.

- `docs/MYTHOS_KERNEL_PROTOCOL.md`
  sha256 `0bb4d6613e74c65f5fa0f436904319b8da9208ced26c7eb66e32de0d3d47ec49`
- `docs/RESEARCH_DIGEST_LITERATURE_2026-07.md`
  sha256 `8dbcef9f253d10737eedaf231c732d7053a5d6e5b2937e92373c77ba2dce8335`

Mythos-maintained living docs, read-only for Codex, no sha pin:

- `docs/PROJECT_TREE.md`
- `docs/project_tree.json`
- `docs/PROJECT_MAP_LEVEL0.svg`

Rule: Codex reads/cites; any edit = protocol violation; corrections via Mythos
review only; verify sha before every import.

Header check:

- `docs/MYTHOS_KERNEL_PROTOCOL.md` first line:
  `# MYTHOS KERNEL — RH Campaign Discipline Protocol (K1–K9)`
- `docs/RESEARCH_DIGEST_LITERATURE_2026-07.md` first line:
  `# RESEARCH DIGEST — Literature for the Weil-Positivity / Prolate RH Paper`
- `EPISTEMIC FIREWALL` section visible in
  `docs/RESEARCH_DIGEST_LITERATURE_2026-07.md`; this is the anti-circularity
  guard for future gates: RH-conditional imports never enter the concluding
  chain.
```

## ACTIONS LOG

H0 hygiene:

- Staged goal-bus 001 files, `bus/BUS_PROTOCOL.md`, `bus/002_tail_return_probe.goal.md`, `comb_meanvalue_falsifier_v1.py`, and `out/comb_meanvalue_falsifier_v1.json`.
- Created `archive_duplicates/`.
- Moved Finder duplicates, not deleted:
  - `archive_duplicates/handoff_to_proshka 2.md`
  - `archive_duplicates/handoff_to_proshka 3.md`

Execution:

- Command: `/Users/emalam/GitHub/rh_lean_01_2026/venv_djo/bin/python tail_return_probe_v1.py`
- First run generated `out/anchor_locked_zeros_first_5000.json` from pinned J<=2000 cache plus `mpmath.zetazero` for J=2001..5000.
- Second run reused the 5000-zero cache after making the C-refit rule AnchorLocked-compatible (`checkpoint_mean` primary; all-J median retained as diagnostic).
- No j<=2000 recomputation: parent zero cache sha verified before extension.

Artifacts:

- `tail_return_probe_v1.py`
  sha256 `208e4ace36d766f6aefa74ee9114cdb1fd57b544e0bd50ced0e4481a2f5cfaee`
- `out/anchor_locked_zeros_first_5000.json`
  sha256 `79cf9c8f678321ca75a35aa84bf7e7dbe6b277463bf0fbb89fb62b27382caf33`
- `out/tail_return_probe_v1.json`
  sha256 `7c9286e41d0f1ac27c7bca5a25925e4f25fad194f9bbd174cd9fc5ecb2bbeeca`
- `ROUTE_B_STATE.md`
  sha256 after history update `763197d666385932d9bd3442b381408ae88f4553d279e6c0d9208bf6a625c670`
- `archive_duplicates/handoff_to_proshka 2.md`
  sha256 `9843df655915eb1fd1d84c0717de1bc670bbf87d20abad9f77cb643b27a6d29c`
- `archive_duplicates/handoff_to_proshka 3.md`
  sha256 `db8fb33fc413c7dea92f2797bfb8cc31b562b80dc9c043c742e3983b4f2fad4c`

Pinned inputs:

- `out/anchor_locked_zeros_first_2000.json`
  sha256 `60dba843b9dca732b232d1bf4f3a133b174ca403fd9929d99d49122a38303356`
- `out/portable_k_coeffs_lambda_sq_13_N_120.json`
  sha256 `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88`

Git/state notes:

- Final `ROUTE_B_STATE.md` history line added for TailReturnProbe_v1.
- At answer time, external unexecuted `bus/003_leakage_falsifier.goal.md` and `bus/004_split_identity_check.goal.md` are present in the working tree but were not created, staged, or executed by this gate.
- No next gate selected by TailReturnProbe_v1. STOP.
