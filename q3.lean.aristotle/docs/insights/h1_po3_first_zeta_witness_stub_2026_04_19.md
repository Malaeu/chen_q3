# H1 / PO3 — first-zeta witness stub at `a = 1`

## Status

Локальный witness-пакет закрыт.

- singleton-ветка для `γ₀, γ₁, γ₂` закрыта честно;
- `prefix2` закрыт честной theorem-level леммой без внешнего сертификата;
- `prefix3` теперь тоже закрыт честной theorem-level леммой без внешнего
  сертификата.

## Purpose

Freeze one concrete `prefix2/prefix3` witness target so that the remaining gap
is only:

1. an external certificate that a named complex number is nonzero;
2. plugging that certificate into an already compiled Lean bridge lemma.

## Lean objects

In
[`Q3/Proofs/HBridge_PO3_Shell.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/HBridge_PO3_Shell.lean)
we now have:

- `po3_first_zeta_gamma0_decimal28`
- `po3_first_zeta_gamma1_decimal28`
- `po3_first_zeta_gamma2_decimal28`
- `po3_first_zeta_gap_sum2_a1_decimal28`
- `po3_first_zeta_gap_sum3_a1_decimal28`

and the two conditional witness lemmas:

- `po3_no_suzuki_raw_gamma_pm_prefix2_of_first_zeta_decimal28_witness`
- `po3_no_suzuki_raw_gamma_pm_prefix3_of_first_zeta_decimal28_witness`

## External certificate targets

The direct targets are now simply:

```lean
hgap2 : po3_first_zeta_gap_sum2_a1_decimal28 ≠ 0
hgap3 : po3_first_zeta_gap_sum3_a1_decimal28 ≠ 0
```

Once one of these is available, the corresponding formal conclusion is already
compiled.

## Numerical source

The decimal-28 witness values come from the local script
[`scripts/po3_gamma_gap_witness.py`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/scripts/po3_gamma_gap_witness.py),
using `mpmath.zetazero(n)`.

For the current frozen run:

- `γ₀ ≈ 14.1347251417346937904572519836`
- `γ₁ ≈ 21.0220396387715549926284795939`
- `γ₂ ≈ 25.0108575801456887632137909926`

and the witness JSON snapshot is
[`ACTIVE/pipeline/po3_gamma_gap_witness_2026_04_19.json`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/pipeline/po3_gamma_gap_witness_2026_04_19.json).

## Current numerical signal

For `a = 1` the frozen run gives:

- `po3_first_zeta_gap_sum2_a1_decimal28 ≈ 8.012376722781014e-4`
- `po3_first_zeta_gap_sum3_a1_decimal28 ≈ 8.013257563312617e-4`

So the local numerical signal is comfortably away from zero.

## Current honest `prefix2` landing

В
[`Q3/Proofs/PO3Cert/FirstZetaPrefix2_2026_04_19.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PO3Cert/FirstZetaPrefix2_2026_04_19.lean)
теперь есть theorem-level closure для конкретного двухчленного witness-пакета
при `a = 1`.

Файл доказывает:

- вещественную формулу для six-pole gap term `po3_gap_term20_11_real_a1`;
- его положительность на окне `x > 3 * π`;
- вещественную факторизацию manuscript gap-weight на реальной оси;
- положительность двух весов при `γ₀`, `γ₁`;
- теорему
  `Q3.Proofs.PO3Cert.po3_first_zeta_gap_sum2_a1_decimal28_ne_zero_honest`;
- и итоговое shell-замыкание
  `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_prefix2_from_first_zeta_gap_sum2_honest`.

Это уже не сертификатная заглушка: `prefix2` закрыт честной леммой внутри Lean.

## Current certificate landing

That certificate layer now exists as the separate off-chain file
[`Q3/Proofs/PO3Cert/FirstZetaGapWitness_2026_04_19_Data.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PO3Cert/FirstZetaGapWitness_2026_04_19_Data.lean).

It exports:

- `Q3.Proofs.PO3Cert.po3_first_zeta_gap_sum2_a1_decimal28_ne_zero` as the
  named external certificate axiom for the concrete `prefix2` gap;
- `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_prefix2_from_first_zeta_gap_cert`
  as the closure point for the compiled `prefix2` shell;
- `Q3.Proofs.PO3Cert.po3_first_zeta_gap_sum3_a1_decimal28_ne_zero` as the
  named external certificate axiom;
- `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_prefix3_from_first_zeta_gap_cert`
  as the closure point back into the compiled `PO3` shell.

Для `prefix2` этот off-chain слой теперь не обязателен: его заменяет честный
theorem-level файл `FirstZetaPrefix2_2026_04_19.lean`. Для `prefix3` он всё ещё
остаётся только provenance-слоем, а не обязательным мостом.

## Current honest `prefix3` landing

В
[`Q3/Proofs/PO3Cert/FirstZetaPrefix3_2026_04_19.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PO3Cert/FirstZetaPrefix3_2026_04_19.lean)
теперь есть theorem-level closure и для трёхчленного witness-пакета при
`a = 1`.

Файл добавляет только недостающий третий witness:

- вещественную форму `γ₂`;
- оценку `γ₂ > 3 * π`;
- ненулевость `sin γ₂`;
- положительность третьего manuscript gap-weight;
- теорему
  `Q3.Proofs.PO3Cert.po3_first_zeta_gap_sum3_a1_decimal28_ne_zero_honest`;
- и итоговое shell-замыкание
  `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_prefix3_from_first_zeta_gap_sum3_honest`.

Итог: и `prefix2`, и `prefix3` уже выведены в Lean без внешней аксиомы.

## Current reusable witness-stack landing

Поверх отдельных honest-closures теперь есть ещё и один собранный reusable
пакет:

[`Q3/Proofs/PO3Cert/FirstZetaWitnessStack_2026_04_19.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PO3Cert/FirstZetaWitnessStack_2026_04_19.lean)

Он не добавляет новой математики. Его роль другая:

- собрать в один named object три singleton-обструкции;
- добавить к ним honest `prefix2` и honest `prefix3`;
- дать shell-facing proposition
  `Q3.Proofs.PO3Cert.po3_first_zeta_initial_packet_kill_layer`;
- и дать bundled theorem
  `Q3.Proofs.PO3Cert.po3_first_zeta_initial_packet_kill_layer_honest`,
  а также disjunctive shell-form
  `Q3.Proofs.PO3Cert.po3_first_zeta_some_initial_packet_profile_false_honest`.

Это уже не просто набор локальных лемм, а готовый reusable witness-stack для
дальнейшей `PO3-shell` упаковки.

## Current honest singleton landing

There is now also a theorem-level singleton obstruction with no external axiom
in
[`Q3/Proofs/PO3Cert/FirstZetaSingleton_2026_04_19.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PO3Cert/FirstZetaSingleton_2026_04_19.lean).

It exports:

- the shared structural helpers
  `Q3.Proofs.PO3Cert.po3_rational_complex_ne_int_mul_pi`
  and
  `Q3.Proofs.PO3Cert.po3_rational_complex_sin_ne_zero`,
  together with the bridge helper
  `Q3.Proofs.PO3Cert.po3_complex_sin_ne_zero_of_ne_int_mul_pi`;
- `Q3.Proofs.PO3Cert.po3_first_zeta_gamma0_decimal28_ne_int_mul_pi`;
- `Q3.Proofs.PO3Cert.po3_first_zeta_gamma0_decimal28_sin_ne_zero`;
- `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma0_decimal28`;
- `Q3.Proofs.PO3Cert.po3_first_zeta_gamma1_decimal28_ne_int_mul_pi`;
- `Q3.Proofs.PO3Cert.po3_first_zeta_gamma1_decimal28_sin_ne_zero`;
- `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma1_decimal28`;
- `Q3.Proofs.PO3Cert.po3_first_zeta_gamma2_decimal28_ne_int_mul_pi`;
- `Q3.Proofs.PO3Cert.po3_first_zeta_gamma2_decimal28_sin_ne_zero`;
- `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma2_decimal28`.

The key point is structural:
each decimal-28 witness `γ₀,γ₁,γ₂` is rational, so it cannot equal an integer
multiple of `π`; the file currently packages this into three honest singleton
kill theorems at `a = 1`, one for each of the first three witness ordinates.

## Intended next formal move

Первый-zeta witness route при `a = 1` теперь закрыт целиком на уровне
`singleton/prefix2/prefix3`.

Следующий честный ход уже не внутри этого локального пакета, а выше по цепочке:

1. либо использовать закрытые `prefix2/prefix3` obstruction-леммы как готовые
   локальные kill-пакеты в `PO3-shell`;
2. либо перейти к следующему живому family/witness узлу, если нужен ещё один
   независимый packet beyond the first zeta stack.
