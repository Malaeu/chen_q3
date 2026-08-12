# M1C parity-sector ground-to-trial bound — one control cell

Date: 2026-08-12

Scope: `[FINITE_CELL][CONDITIONAL]` · Goal 058 / G3 M1C · cell `(13,120)`

Outcome: `M1C_PARITY_SECTOR_CONTROL_CELL_CLASSIFIED`

## Decision

The frozen M1C classification is **STRONG**. The selected theorem-facing judge is `RAYLEIGH` with `sqrt(U_sector) = [9.891988957989617418204345910556896812837349607442717469918262181272077201196126092785942628978441937e-5 +/- 2.65e-105]`.

This is the honest parity repair of M1B: the literal saved trial was not replaced or normalized after inspection. Its nonzero odd mass is paid as `omega` in every bound.

## Proshka verdict preservation

The complete UTF-8 verdict is embedded verbatim in the JSON output: SHA-256 `a4e80622fa061cbde6c71d44d95443e1c569b83adfb9034f5989ea88e9fce014`, 12551 bytes, 582 LF-delimited lines, final LF `True`.

## Parity semantics

- `||Jq-q|| = [3.438401150870251704626573989908596575412203663213839003758121852029973282275841678055536984807326706e-30 +/- 2.87e-130]`
- `||q_-|| = [1.719200575435125852313286994954298287706101831606919501879060926014986641137920839027768492403663353e-30 +/- 1.44e-130]`
- `omega = ||q_-||² = [2.955650618576467856178070671082267875189857628022350254152101822113928863793632346196548053090707468e-60 +/- 1.63e-160]`
- `q_+ + q_- = q`: `True`
- `<q_+,q_-> = 0`: `True`
- `||q||² = ||q_+||² + ||q_-||²`: `True`
- `J²=I`: `True`; `KJ=JK`: `True`.

The earlier M1B field `norm_q_minus_Jq` means `||q-Jq|| = 2||q_-||`; it is neither `||q_-||` nor `omega`. No exact source theorem asserting that the intended projected `kTrial_m_N` is even was found. The available ground-vector theorem is conditional and is not a trial-parity theorem.

## Certified sector order

- `epsilon0_even = [3.5e-59 +/- 5.09e-61]`
- `epsilon0_odd = [3.1e-55 +/- 7.47e-57]`
- `epsilon1_even = [1.3e-51 +/- 2.50e-53]`
- `epsilon0_even_upper < epsilon0_odd_lower`: `True`
- `epsilon0_even_upper < epsilon1_even_lower`: `True`
- `Delta_even_lower = [1.298735706535507701533436912873415913046953268840518215619317669673884660915138568812059159999700000e-51 +/- 3.70e-153]`

Each persisted M1B bracket endpoint was independently replayed against a rebuilt outward-rounded source matrix with validated Arb inverse and LDL inertia counts.

## Bounds

- `alpha_plus = [1.2e-59 +/- 7.09e-61]`
- `U_sector_rayleigh = [9.785144554498851699504382366768730125436122389112967406226723950570669410217858084313905774576180143e-9 +/- 4.47e-109]`; square root `[9.891988957989617418204345910556896812837349607442717469918262181272077201196126092785942628978441937e-5 +/- 2.65e-105]`.
- `a_plus = [4.719979979509430007212307320368543162357030244266592639202693594039682351490894514153870576e-59 +/- 1.45e-150]`; `nu_plus = [2.249633892998169487027941203689678423636316991898181936144078828371910842002941803852595160834042995e-30 +/- 4.04e-130]`; `separation_plus_lower = [1.298735694523988719685477464958930663301880726043470679929995295604175298424386014091054858460994239e-51 +/- 1.73e-151]`.
- `U_sector_residual = [3000420604598026788716831297964379535213156.528060640140717557177476737928069699751606068020621423904 +/- 2.21e-58]`; square root `[1732172221402371637951.272849484401625774268180472673608865786726248210152737529739397698349595807156 +/- 3.75e-79]`.
- selected `U_sector = [9.785144554498851699504382366768730125436122389112967406226723950570669410217858084313905774576180143e-9 +/- 4.47e-109]`; square root `[9.891988957989617418204345910556896812837349607442717469918262181272077201196126092785942628978441937e-5 +/- 2.65e-105]`.
- M1B square-root bound: `[0.007974761644204909274982095966648536343773916247223670450103585043098804933680522163505080131940000007 +/- 2.22e-103]`; observed projective distance: `[6.84973178301832e-5 +/- 4.34e-20]`.

The ground overlap remains validator-only and was never used to alter `q_+`, the sector split, the Rayleigh quotient, or either bound.

## Validation and plants

Precision ladder `[80, 105, 130]` passed; dense/source matvec agreement `True`; independent sector validator `True`.

- `drop_odd_mass` → `M1C_ODD_MASS_DROPPED` (`PASS`)
- `posthoc_symmetrize` → `M1C_SOURCE_TRIAL_REPLACED` (`PASS`)
- `uncertified_ground_parity` → `M1C_GLOBAL_GROUND_SECTOR_UNJUSTIFIED` (`PASS`)
- `parity_unit_confusion` → `M1C_PARITY_DEFECT_UNIT_MISMATCH` (`PASS`)
- `midpoint_as_envelope` → `M1C_ODD_MASS_UPPER_ENVELOPE_MISSING` (`PASS`)
- `ground_oracle` → `M1C_GROUND_ORACLE_SURROGATE` (`PASS`)

## Registered prediction fate

- `P058_M1C_1`: `CONFIRMED`
- `P058_M1C_2`: `CONFIRMED: certified omega is negligible relative to 1e-6`
- `P058_M1C_3`: `CONFIRMED`
- `P058_M1C_4`: `NOT_TRIGGERED: M1C is not WEAK`

## Evidence boundary

This is one finite-cell conditional certificate. It does not close G1 or G3, does not establish a cofinal family, does not promote Route B, and makes no RH claim. A later ladder or Feshbach run requires a separate precommit.

`ARSENAL_USED: C04 · C07 · C09 · C10`

`M1C_PARITY_SECTOR_CONTROL_CELL_CLASSIFIED`
