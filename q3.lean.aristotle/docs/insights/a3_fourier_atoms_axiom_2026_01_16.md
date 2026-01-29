# A3 Fourier → Atoms Positivity (2026-01-16)

## Проблема
Цепочка `Atoms_Positive` использовала старую аксиому
`Q_nonneg_on_atoms_of_A3_RKHS_axiom`, завязанную на sampling Toeplitz и `a_star`.
Это уводит от контрактного A3 (Fourier Toeplitz + `P_A`).

## Как быстро детектить
- Проверить, что в `Q3/Atoms_Positive.lean` **нет** старой аксиомы:
  - `rg -n "Q_nonneg_on_atoms_of_A3_RKHS_axiom" Q3/Atoms_Positive.lean`
- Проверить, что используется Fourier-вариант:
  - `rg -n "A3_bridge_data_rayleigh_Fourier|Q_nonneg_on_atoms_of_A3_Fourier" Q3/Atoms_Positive.lean`

## Фикс
1) Добавлена новая аксиома (Fourier-вариант):
   - `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`
   - `Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`
2) `Q3/Atoms_Positive.lean` переведен на:
   - `A3_bridge_data_rayleigh_Fourier` из `Q3/Proofs/P_A_Toeplitz_bridge.lean`
   - `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`
3) `Q3/CheckAxioms.lean` и `Q3/AxiomsTheorems.lean` обновлены под новый интерфейс.

## Связанные файлы
- `Q3/Atoms_Positive.lean`
- `Q3/Proofs/P_A_Toeplitz_bridge.lean`
- `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`
- `Q3/AxiomsTheorems.lean`
- `Q3/CheckAxioms.lean`
- `Q3/Main.lean`
