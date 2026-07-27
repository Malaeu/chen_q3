# ОТВЕТ 015 — MUNTZ_CLOUD_HARVEST

`CLONE_FAIL`

Архивный fallback полностью собран и проаудирован, но требуемый Git-клон с
историей получить нельзя: официальный Aristotle-архив не содержит `.git`, а
исходный Montel-клон `aristotle_output/1803227e-9c5a-4a8e-b20b-6eb7d33871fb/`,
из которого директива требовала взять remote URL, на диске отсутствует.

`LOCAL_GIT_ARCHIVE_INITIALIZED`

После owner-уточнения скачанный snapshot оформлен как отдельный локальный Git
repository прямо в существующем каталоге. Это не поддельная реконструкция
закрытой cloud-истории: remote не назначен, происхождение и SHA архива
зафиксированы в `PROVENANCE.md`.

## 1. Получение проекта

- Project UUID: `c746a674-5849-4dfa-9e4c-b7dd5af231b2`.
- CLI-проверка:

  ```text
  API request failed with status 403: Forbidden
  ```

- Через авторизованную страницу Aristotle скачан официальный project-result
  archive и распакован в:

  ```text
  q3.lean.aristotle/aristotle_output/c746a674-5849-4dfa-9e4c-b7dd5af231b2/
  ```

- Архив:

  ```text
  q3.lean.aristotle/aristotle_output/c746a674-5849-4dfa-9e4c-b7dd5af231b2.tar.gz
  SHA-256 f2618a8fa6c9f3cbc254aa1b3acc08dc2d457b989048910d1ba18f74c7ba1618
  ```

- Архив содержит `lean-toolchain`, `lake-manifest.json`, `lakefile.toml`,
  `RequestProject/Main.lean`, `ARISTOTLE_SUMMARY.md`, `RESULT.md`, `README.md`
  и `RequestProject/.gitkeep`; `.git` отсутствует.
- Строгая ошибка локального `git log` при запрете поиска родительского
  репозитория:

  ```text
  fatal: not a git repository (or any of the parent directories): .git
  ```

## 2. Нотариат

### Build

```text
lake build
exit code: 0
Build completed successfully (8027 jobs).
warning: RequestProject/Main.lean:89:8: declaration uses `sorry`
warning: RequestProject/Main.lean:99:8: declaration uses `sorry`
```

Точный SHA-256 проверенного текущего файла:

```text
9c657af1d47464bb40c81aa332ae65dcec07785e992dd85338c7f1f28343b7f2  RequestProject/Main.lean
```

Текущий официальный архив уже содержит follow-up-редакцию: после трёх
доказанных теорем в неё добавлены две новые декларации с `sorry`. Поэтому
утверждение вложенного `RESULT.md` о чистом файле относится к завершённому
коммиту 12:15, а не к более позднему follow-up working tree.

### Grep текущего `RequestProject/Main.lean`

```text
sorry=2
admit=0
axiom=0
native_decide=0
```

Два `sorry`:

```text
RequestProject/Main.lean:96:  sorry
RequestProject/Main.lean:106:  sorry
```

### `#print axioms`

```text
'EStarMuntzZeroMassContinuation.Estar_eq_zero_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'EStarMuntzZeroMassContinuation.zeta_product_not_continuousAt_of_simple_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'EStarMuntzZeroMassContinuation.shifted_zeta_product_not_continuousAt_of_simple_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'EStarMuntzZeroMassContinuation.dilation_tsum_uniform_bound' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'EStarMuntzZeroMassContinuation.norm_Estar_le_sqrt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Итог нотариата:

- доказанный пакет исходного рана: стандартная тройка;
- follow-up `dilation_tsum_uniform_bound` и `norm_Estar_le_sqrt`: черновики,
  зависят от `sorryAx`;
- весь текущий архив: не sorry-free.

### `RESULT.md` целиком, verbatim

````md
# Result

`RIEMANN_SUM_LIPSCHITZ_GAP`

The corrected formulation was used: `ZetaMellinReg` assigns the derivative of the Mellin transform at the pole, and the support interval in the proved tail lemma is `[0,b]`.

The full requested T1–T5/PL2 package was not completed. The exact blocking library-level step is a quantitative right-endpoint Riemann-sum estimate for a **complex-valued measurable function of bounded variation**:

```lean
‖u * ∑' n : ℕ+, h (n * u) - ∫ x in Set.Ioi 0, h x‖
  ≤ u * (eVariationOn h Set.univ).toReal
```

(up to a harmless endpoint constant), for `u > 0` and compact support. Mathlib supplies the primitive variation bounds `eVariationOn.sum_le`, `eVariationOn.sum_le_of_monotoneOn_Icc`, `eVariationOn.sum'`, and `BoundedVariationOn.dist_le`, but no theorem connecting those bounds to Lebesgue integrals/right-endpoint Riemann sums in the required form. Assembling that bridge from the primitive definitions remains the gap.

`RequestProject/Main.lean` contains no `sorry`, `admit`, new `axiom`, or `native_decide`. It proves:

* the pointwise T1 tail statement `Estar_eq_zero_of_gt` for support in `[0,b]`;
* a general theorem showing that the raw product `riemannZeta w * M w` is discontinuous at `w = 1` whenever `M 1 = 0` and `M` has nonzero derivative there;
* the shifted version at `s = 1/2`;
* the corrected definition `ZetaMellinReg`.

All three proved theorems use exactly `[propext, Classical.choice, Quot.sound]`.

Relevant Mathlib APIs located during the work:

1. Zeta pole: `riemannZeta_residue_one`; also `tendsto_riemannZeta_sub_one_div`, `differentiableAt_riemannZeta`, and `HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div`.
2. Identity theorem: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
3. Differentiation under the integral: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` and `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`.
````

## 3. Инвентарь и совместимость

### Определения

```text
EStarMuntzZeroMassContinuation.Estar (h : ℝ → ℂ) (u : ℝ) : ℂ
EStarMuntzZeroMassContinuation.Mellin (k : ℝ → ℂ) (s : ℂ) : ℂ
EStarMuntzZeroMassContinuation.Gwin (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ
EStarMuntzZeroMassContinuation.Rminus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ
EStarMuntzZeroMassContinuation.Rplus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ
EStarMuntzZeroMassContinuation.ZetaMellinReg (h : ℝ → ℂ) (w : ℂ) : ℂ
```

Точная формула регуляризации:

```lean
noncomputable def ZetaMellinReg (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  if w = 1 then deriv (Mellin h) 1 else riemannZeta w * Mellin h w
```

### Доказанные декларации

```text
EStarMuntzZeroMassContinuation.Estar_eq_zero_of_gt
  (h : ℝ → ℂ) (b u : ℝ) (hb : 0 ≤ b)
  (hsupp : ∀ v ∉ Set.Icc 0 b, h v = 0) (hu : b < u) :
  EStarMuntzZeroMassContinuation.Estar h u = 0

EStarMuntzZeroMassContinuation.zeta_product_not_continuousAt_of_simple_zero
  (M : ℂ → ℂ) (d : ℂ) (hM0 : M 1 = 0)
  (hMderiv : HasDerivAt M d 1) (hd : d ≠ 0) :
  ¬ ContinuousAt (fun w => riemannZeta w * M w) 1

EStarMuntzZeroMassContinuation.shifted_zeta_product_not_continuousAt_of_simple_zero
  (M : ℂ → ℂ) (d : ℂ) (hM0 : M 1 = 0)
  (hMderiv : HasDerivAt M d 1) (hd : d ≠ 0) :
  ¬ ContinuousAt
      (fun s => riemannZeta (s + 1 / 2) * M (s + 1 / 2))
      (1 / 2)
```

### Follow-up-декларации, не доказаны

```text
EStarMuntzZeroMassContinuation.dilation_tsum_uniform_bound
  (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
  (hsupp : ∀ v ∉ Set.Icc a b, h v = 0)
  (hlip : LipschitzOnWith K h (Set.Ico 0 b))
  (hmass : ∫ (v : ℝ) in Set.Ioi 0, h v = 0) :
  ∃ C, ∀ u ∈ Set.Ioo 0 1, ‖∑' (n : ℕ+), h (↑↑n * u)‖ ≤ C

EStarMuntzZeroMassContinuation.norm_Estar_le_sqrt
  (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
  (hsupp : ∀ v ∉ Set.Icc a b, h v = 0)
  (hlip : LipschitzOnWith K h (Set.Ico 0 b))
  (hmass : ∫ (v : ℝ) in Set.Ioi 0, h v = 0) :
  ∃ C, ∀ u ∈ Set.Ioo 0 1,
    ‖EStarMuntzZeroMassContinuation.Estar h u‖ ≤ C * √u
```

### Совместимость с локальной линией

`NEEDS_RENAME(Estar→Q3.RouteB.D0Pstar.E_star; Mellin→Mathlib.mellin;
Gwin/Rminus/Rplus→windowedMellin/lowerMellinTail/upperMellinTail;
Ioo-window→Icc-window requires an a.e./measure-zero endpoint bridge)`

- Формула `Estar` математически совпадает с D0 `E_star`:
  `√u · ∑' n : ℕ+, h(nu)`.
- Облачный `Mellin` использует
  `∫_{(0,∞)} k(u)u^(s-1)du`; локальный файл использует Mathlib `mellin`.
  Для комплексных значений порядок скалярного множителя эквивалентен, но это
  не definitional equality.
- Облачный `Gwin` интегрирует по `Ioo Λ⁻¹ Λ`; локальный
  `windowedMellin` использует indicator `Icc Λ⁻¹ Λ`. Требуется отдельная
  a.e.-лемма об удалении двух концов.
- В дерево ничего не переносилось.

## 4. Недостающая лемма-мост, verbatim

```lean
‖u * ∑' n : ℕ+, h (n * u) - ∫ x in Set.Ioi 0, h x‖
  ≤ u * (eVariationOn h Set.univ).toReal
```

Условия из `RESULT.md`: `u > 0`, компактный носитель, допустима безвредная
endpoint-константа; функция комплекснозначная, измеримая, ограниченной
вариации.

Ближайшие API, названные в `RESULT.md`:

```text
eVariationOn.sum_le
eVariationOn.sum_le_of_monotoneOn_Icc
eVariationOn.sum'
BoundedVariationOn.dist_le
riemannZeta_residue_one
tendsto_riemannZeta_sub_one_div
differentiableAt_riemannZeta
HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div
AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
hasDerivAt_integral_of_dominated_loc_of_deriv_le
intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
```

## 5. Хронология

Локальный `git log --oneline -10` невозможен: официальный архив не содержит
`.git`. Не подменять его логом родительского `rh_lean_01_2026`.

Доступная нотариальная хронология облачного журнала:

```text
2026-07-27 12:15  git add RequestProject/Main.lean RESULT.md &&
                  git commit -m "Formalize zeta product discontinuity and tail lemma" &&
                  git push origin HEAD
2026-07-27 12:20  Aristotle finished successfully
2026-07-27 12:23  follow-up instruction received; status RUNNING
2026-07-27 12:28–12:53  follow-up reads/searches/build work and subagent polling
```

`FOLLOWUP_ALIVE`

Дополнительное материальное свидетельство: официальный архив, скачанный после
старта follow-up, содержит две новые декларации
`dilation_tsum_uniform_bound` и `norm_Estar_le_sqrt`, которых нет в
завершённом `RESULT.md`; обе пока с `sorry`.

`STATE` не изменялся. `BUS_010_VOID` соблюдён.

## 6. Локальный Git-архив после owner-уточнения

Каталог:

```text
q3.lean.aristotle/aristotle_output/c746a674-5849-4dfa-9e4c-b7dd5af231b2/
```

Ветка и коммиты:

```text
main
ec48f99 [Local audit] Add axiom inventory
4dbb115 [Aristotle c746a674] Import downloaded project snapshot
```

Устройство:

- `4dbb115` хранит скачанный project snapshot, `.gitignore` и
  `PROVENANCE.md`;
- `ec48f99` отдельно добавляет локальный `AxiomAudit.lean`;
- `.lake/` игнорируется;
- remote отсутствует намеренно: Aristotle API экспортирует result-архив, но
  не cloud-worker Git URL;
- `git status --porcelain=v1`: пусто;
- `lake build`: exit `0`;
- worktree ровно один — сам каталог repository; дополнительных worktree не
  создавалось.

Корневой `rh_lean_01_2026` и `chen_q3` также имеют по одному обычному
worktree. Ничего удалять или размножать не потребовалось.
