# Проба типизированного моста: матрица → евклидов оператор → нижнее собственное значение

Прогон 2026-08-11, тело Linux. Основание — вердикт
`docs/routeB_bus/PROSHKA_H2A_LEAN_NATIVE_PROBE_ADJUDICATION_2026-08-11.md`,
проба `H2A_RAYLEIGH_TYPED_BRIDGE_PROBE`.

**Чем этот прогон отличается от директивы.** Директива адресована Codex на Mac, с пином
`HEAD = 087e3bb` и путём `/Users/emalam/…`. Здесь прогнана её позитивная часть и
отрицательный контроль в том же пакете (`q3.lean.aristotle`, Lean/Mathlib `v4.26.0`), но
на **обобщённой** `A : Matrix n n ℝ` с гипотезой `Aᵀ = A`, а не на самой
`ccmWeilMatFinite`: её модуль на этой машине не собран, сборка шла параллельно прогону.
**Дополнено в тот же день, после того как модуль собрался:** инстанцирование на настоящую
`ccmWeilMatFinite` **сделано и скомпилировано**, все три теоремы с аксиомами
`[propext, Classical.choice, Quot.sound]`:

```lean
ccmWeilMatFinite_toEuclideanLin_isSymmetric      (mProject N) (hm) (hN)
ccmWeilMatFinite_hasEigenvalue_iInf_rayleigh     (mProject N) (hm) (hN)
ccmWeilMatFinite_map_complex_isHermitian         (mProject N) (hm) (hN)
```

Мост и подъём ℝ→ℂ идут прямо из `ccmWeilMatFinite_transpose_eq`. Тексты — в
`scratchpad/CCMInst.lean`, в репозиторий **не** внесены.
Обобщение законно ровно в одну сторону: `ccmWeilMatFinite_transpose_eq` даёт в точности
`Aᵀ = A`, то есть посылку пробы, и ничего сверх неё.

Файлы прогона: `/tmp/claude-1000/…/scratchpad/Probe{0,1,2,3,4,5,6,7,8,9}.lean` —
временные, вне репозитория, как требует режим `TEMPORARY_READ_ONLY_REPO`.

---

## Фаза 0 — точные типы, взятые из `#check`, а не из головы

```
Matrix.isHermitian_iff_isSymmetric :
  ∀ {𝕜} {n} {A : Matrix n n 𝕜} [RCLike 𝕜] [Fintype n] [DecidableEq n],
    A.IsHermitian ↔ (Matrix.toEuclideanLin A).IsSymmetric

LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional :
  ∀ {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} [Nontrivial E],
    T.IsSymmetric →
      Module.End.HasEigenvalue T ↑(⨅ x, RCLike.re (inner 𝕜 (T ↑x) ↑x) / ‖↑x‖ ^ 2)

Matrix.toEuclideanLin :
  Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m
```

Носитель Mathlib — **`EuclideanSpace ℝ n`**. Наш `ccmWeilOpFinite` объявлен как
`Module.End ℝ (CCMModeFinite N → ℝ)` (`CCMFiniteWeilSourceMatrix.lean:63`), то есть на
Pi-типе. Это разные типы с разными инстансами нормы и произведения, хотя функция под ними
одна. Расхождение носителей — не придирка: именно оно роняло вчерашнюю пробу.

## Фаза 1 — поиск

| шаг | цель | результат `exact?` |
|---|---|---|
| 1 | `Aᵀ = A ⊢ A.IsHermitian` | `exact h` — над ℝ совпадают определительно |
| 2 | `A.IsHermitian ⊢ (toEuclideanLin A).IsSymmetric` | `exact isHermitian_iff_isSymmetric.mp h` |
| 3 | `Aᵀ = A ⊢ (toEuclideanLin A).IsSymmetric` | `exact isHermitian_iff_isSymmetric.mp h` |
| 4 | заключение Rayleigh дословно | **не закрыл** |

Весь путь 9 секунд на файл.

**Шаг 3 — иллюстрация пункта 2 вердикта на нашем материале.** Подсказка выглядит как одна
готовая лемма, а на деле молча использует определительное равенство шага 1. Считать её
«найден один поставщик» без разбора зависимостей нельзя — ровно то, о чём предупреждает
вердикт.

## Фаза 2 — явный терм и аксиомы

```lean
theorem transpose_eq_toEuclideanLin_isSymmetric (A : Matrix n n ℝ) (h : Aᵀ = A) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  isHermitian_iff_isSymmetric.mp h

theorem transpose_eq_hasEigenvalue_iInf_rayleigh [Nonempty n] (A : Matrix n n ℝ) (h : Aᵀ = A) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin A)
      ↑(⨅ x : { x : EuclideanSpace ℝ n // x ≠ 0 },
          RCLike.re (inner ℝ (Matrix.toEuclideanLin A ↑x) ↑x)
            / ‖(x : EuclideanSpace ℝ n)‖ ^ 2) :=
  (transpose_eq_toEuclideanLin_isSymmetric A h).hasEigenvalue_iInf_of_finiteDimensional
```

Оба компилируются. Заключение второго скопировано из вывода Фазы 0 и не ослаблено.

```
'transpose_eq_toEuclideanLin_isSymmetric'   : [propext, Classical.choice, Quot.sound]
'transpose_eq_hasEigenvalue_iInf_rayleigh'  : [propext, Classical.choice, Quot.sound]
```

## Фаза 4 — отрицательный контроль

`plantM = !![0, 1; 0, 0]`, та же цель моста. Отдельным файлом, по коду возврата:

```
H2A_PLANT_REJECTED
error: Tactic `rfl` failed … ⊢ plantM.IsHermitian
```

Саженец отвергнут типовой ошибкой, а не таймаутом.

---

## Побочно найденный и закрытый разрыв: подъём ℝ → ℂ

Оба наших «станка», принимающих эрмитову матрицу, объявлены **над ℂ**:

```
zerosRealOn_of_hermitian_charpoly_mul   HermitianDeterminantRealZeros.lean:31   (M : Matrix n n ℂ)
H2a_SimpleEvenGround_FromPenaltyCoercivity  H2aPenaltyCoercivity.lean:395       (G K J : Matrix n n ℂ)
```

А `ccmWeilMatFinite` — над ℝ, и доказано у нас `Aᵀ = A`. Между ними нужен подъём.
`exact?` его не находит; явно доказывается в шесть строк, аксиомы чистые:

```lean
theorem real_symm_map_complex_isHermitian (A : Matrix n n ℝ) (h : Aᵀ = A) :
    (A.map (algebraMap ℝ ℂ)).IsHermitian
```

Вердикт этого разрыва не называет — он найден здесь, диском и прогоном.

---

## Наблюдение, записанное до объяснения

**`exact?` промахивается по цели, которая является дословным экземпляром заключения
леммы, при гипотезе, лежащей в контексте.**

Различающие опыты, поставленные сразу:

| опыт | что менялось | исход |
|---|---|---|
| Probe6 | `IsSymmetric` подана прямо гипотезой (склейка не нужна) | промах |
| Probe7 | добавлен инстанс `[Nontrivial (EuclideanSpace ℝ n)]` | промах |
| Probe8 | `toEuclideanLin` заменён абстрактным `T : E →ₗ[ℝ] E` | промах |
| Probe9 | тот же контекст, терм подан явно | **компилируется**, аксиомы чистые |

Прочтения и их судьба:

- *провал склейки* — **отпало** (Probe6);
- *неразрешённый инстанс* — **отпало** (Probe7);
- *`toEuclideanLin` мешает унификации* — **отпало** (Probe8);
- *цель отличается от заключения леммы по типу* — **отпало** (Probe9: тот же терм её
  закрывает);
- остаётся: **форма заключения** — громоздкое `⨅`-выражение под коэрцией `↑` не берётся
  деревом различения библиотечного поиска.

Последнее прочтение не проверено положительно, только осталось единственным выжившим.
Различит его опыт на другой лемме Mathlib с крупным термом в заключении и без всякой
связи с нашей предметной областью: если промах воспроизведётся — прочтение верно.

**Следствие для конструктора.** Библиотечный поиск нельзя ставить слоем отбора для целей
такой формы: он даёт ложное «поставщика нет» при существующем поставщике. Это повышает
типизированный дамп окружения (`M3` вердикта, там `ALIVE_DEFERRED`) из отложенного в
необходимое.

---

## Скоринг предсказаний вердикта

Зарегистрированы до прогона, не переписаны после.

| | предсказание | p | исход |
|---|---|---|---|
| `P1` | явный мост матрица→Rayleigh компилируется под Lean 4.26 | 0.85 | **подтверждено** (в обобщённой форме) |
| `P2` | `exact?` может закрыть; иначе `apply?` назовёт теорему Rayleigh и оставит остаток по симметрии | 0.55 / 0.80 | **расщепилось**: `exact?` закрыл мост, но не Rayleigh; `apply?` теорему **не назвал** — вернул только развёртки (`hasEigenvalue_iff`, `of_mem_spectrum`). Вторая половина **опровергнута** |
| `P3` | несимметричный саженец не закроется | 0.99 | **подтверждено** |
| `P4` | чужой `hsimple` невидим в окружении Q3 | 0.99 | **подтверждено** тривиально: ноль импортов `Zeta23` в дереве |
| `P5` | `doc-gen4` не нужен для этого решения | 0.95 | не потребовался ни разу; как опыт **не ставился** |

## Исход по карте вердикта

Две цели — два разных исхода, и смешивать их нельзя:

```
CCM_MATRIX_TO_EUCLIDEAN_SYMMETRIC_BRIDGE   → Outcome A   (exact? закрыл, терм компилируется, саженец отвергнут)
BOTTOM_RAYLEIGH_IINF_IS_EIGENVALUE         → Outcome C   (поиск не нашёл, терм компилируется)
                                             LIBRARY_SEARCH_RECALL_INSUFFICIENT
```

## Чего эта проба НЕ даёт

Не закрывает `H2a` — вердикт запрещает такое утверждение прямо, и оснований для него нет.
Не инстанцирована на `ccmWeilMatFinite`. Не трогает `hbottom` при заданном `epsilon`:
Rayleigh даёт **существование** нижней собственной пары, а не сертификат при заранее
выбранном `epsilon` (см. исправление словаря от того же числа). Ни одной записи в
репозиторий во время прогона сделано не было.
