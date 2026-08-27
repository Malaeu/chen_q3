```yaml
SUPPLIER_CONTRACT: v7
DATE: 2026-08-27
BODY: Linux (Claude)
TASK: BETA_CONSUMER_PAIRING_CANCELLATION — exact identity, kernel-checked
ORIGIN: параллельный разбор Прошки (share 6a9075a2); тождество ПЕРЕПРОВЕРЕНО
  мной независимо на бумаге (вещественный и комплексный случай), затем
  формализовано; комплексный случай в исходном разборе не выписан.
FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersHilbertPairing.lean
GIT_BLOB: cb21b1124463ed3ff0931ab8ad6e4758db85c754
SHA256: 43cf371ce7baf2697fe7570c8a93ba7a77d1f5acb5b20ecadcde542b44d2cfda
LINES: 228
GATE:
  lake_env_lean: EXIT 0
  lake_build_module: EXIT 0 (7743 jobs)
  lake_build_full: EXIT 0 (7814 jobs)
  q3_check: ok
  hole_scan: 0
  axioms_all_public: [propext, Classical.choice, Quot.sound]
PUBLIC_SURFACE:
  - dividedDifferenceHilbert / dividedDifferenceHilbertC (defs)
  - loewnerOffDiag / loewnerOffDiagC (defs)
  - dividedDifferenceHilbert_antisymm : H j i = -H i j
  - loewnerOffDiag_eq : Loewner entry factors through H
  - hilbert_weight_total_mass_zero : sum_i v i * (H *ᵥ v) i = 0
  - loewner_quadratic_eq_two_mul_hilbert_pairing (real carrier)
  - hilbert_weight_total_mass_zero_complex : sum_i re(conj(v i) * (H *ᵥ v) i) = 0
  - loewner_form_eq_two_mul_hilbert_pairing_complex (star-first carrier)
RESTRICTIONS_HONORED:
  Tendsto: 0
  Eventually: 0
  rate_hypotheses: 0
  cofinal_conclusions: 0
  arithmetic_input_about_beta: 0
  frozen_asset_bank_file_touched: false
CLOSES:
  - BETA_CONSUMER_PAIRING_IDENTITY (exact, both carriers)
  - BUILT_IN_ZERO_TOTAL_MASS_OF_THE_PAIRING_WEIGHT
OPENS: []
CARRIES_OPEN:
  - BETA_CONSUMER_PAIRING_CANCELLATION (количественная оценка спаривания)
NEXT_LOAD_BEARING_GAP: >-
  порядок-зависимое сокращение sum_i beta_i * w_i(v) при известной нулевой
  сумме весов w; дискриминатор — сравнение с фазово-перемешанным beta
```

## Что именно доказано и почему это не переписывание

Для литеральной структуры «разделённых разностей» (Loewner)
`K_ij = (β_i − β_j)/(n_i − n_j)`, `i ≠ j`, доказано:

1. Оператор `H_ij = 1/(n_i − n_j)` (нуль на диагонали) **антисимметричен**.
2. Квадратичная форма внедиагональной части равна **удвоенному спариванию**
   `β` с весом, порождённым самим тестовым вектором:
   `Σ_ij K_ij v_i v_j = 2·Σ_i β_i · w_i`, `w_i = v_i (H v)_i`.
3. **Суммарная масса веса тождественно ноль**: `Σ_i w_i = 0`, потому что
   `H` антисимметричен. Сокращение встроено в конструкцию, а не
   предполагается.
4. Всё то же в star-first комплексном носителе, с `w_i = re(conj(v_i)(Hv)_i)`
   — эта версия выведена и формализована мной, в исходном разборе её нет.

Значение: матрица потребляет `β` НЕ поэлементно. Оценка вида
`sup_n |β_n|` не является требуемой; требуется оценка спаривания с весом
нулевой суммы. Это меняет постановку, а не переименовывает её.
