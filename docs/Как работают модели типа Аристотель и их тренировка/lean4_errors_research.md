# Исследование ошибок Lean 4

## Источник 1: Lean.Exception (официальная документация)

URL: https://leanprover-community.github.io/mathlib4_docs/Lean/Exception.html

### Структура Exception в Lean 4

```lean
inductive Lean.Exception : Type
| error (ref : Syntax) (msg : MessageData) : Exception
  -- Error messages that are displayed to users. ref is used to provide position information.
| internal (id : InternalExceptionId) (extra : KVMap := { }) : Exception
  -- Internal exceptions that are not meant to be seen by users. 
  -- Examples: "postpone elaboration", "stuck at universe constraint", etc.
```

### Ключевые функции для работы с ошибками

1. **Lean.throwError** — базовая функция для выброса ошибки
2. **Lean.throwErrorAt** — ошибка с указанием позиции в синтаксисе
3. **Lean.throwNamedError** — ошибка с именем (для категоризации)
4. **Lean.throwUnknownIdentifierAt** — ошибка "неизвестный идентификатор"
5. **Lean.throwUnknownConstantAt** — ошибка "неизвестная константа"
6. **Lean.throwKernelException** — ошибка ядра Lean
7. **Lean.throwMaxRecDepthAt** — превышение глубины рекурсии

### Важные теги ошибок

- **unknownIdentifierMessageTag** — тег для неизвестных идентификаторов (используется для code actions)

### Внутренние исключения (не показываются пользователю)

- "postpone elaboration" — отложить элаборацию
- "stuck at universe constraint" — застрял на ограничении универсума
- interrupt — прерывание

---

## TODO: Исследовать далее

- [ ] Kernel.Exception — ошибки ядра
- [ ] Tactic errors — ошибки тактик
- [ ] Elaboration errors — ошибки элаборации
- [ ] Type inference errors — ошибки вывода типов


---

## Источник 2: Lean.Kernel.Exception (официальная документация)

URL: https://leanprover-community.github.io/mathlib4_docs/Lean/Environment.html#Lean.Kernel.Exception

### Полный список Kernel.Exception (ошибки ядра)

```lean
inductive Lean.Kernel.Exception : Type

-- Exceptions that can be raised by the kernel when type checking new declarations.

| unknownConstant (env : Environment) (name : Name) : Exception
  -- Неизвестная константа

| alreadyDeclared (env : Environment) (name : Name) : Exception
  -- Константа уже объявлена

| declTypeMismatch (env : Environment) (decl : Declaration) (givenType : Expr) : Exception
  -- Несоответствие типа декларации

| declHasMVars (env : Environment) (name : Name) (expr : Expr) : Exception
  -- Декларация содержит мета-переменные

| declHasFVars (env : Environment) (name : Name) (expr : Expr) : Exception
  -- Декларация содержит свободные переменные

| funExpected (env : Environment) (lctx : LocalContext) (expr : Expr) : Exception
  -- Ожидалась функция

| typeExpected (env : Environment) (lctx : LocalContext) (expr : Expr) : Exception
  -- Ожидался тип

| letTypeMismatch (env : Environment) (lctx : LocalContext) (x : Expr) (name : Name) (givenType : Expr) (expectedType : Expr) : Exception
  -- Несоответствие типа в let-выражении

| exprTypeMismatch (env : Environment) (lctx : LocalContext) (expr : Expr) (expectedType : Expr) : Exception
  -- Несоответствие типа выражения

| appTypeMismatch (env : Environment) (lctx : LocalContext) (app : Expr) (Type : Expr) (argType : Expr) : Exception
  -- Несоответствие типа в применении функции (APPLICATION TYPE MISMATCH)

| invalidProj (env : Environment) (lctx : LocalContext) (proj : Expr) : Exception
  -- Некорректная проекция

| thmTypeIsNotProp (env : Environment) (name : Name) (type : Expr) : Exception
  -- Тип теоремы не является Prop

| other (msg : String) : Exception
  -- Другая ошибка

| deterministicTimeout : Exception
  -- Детерминистический таймаут

| excessiveMemory : Exception
  -- Превышение памяти

| deepRecursion : Exception
  -- Глубокая рекурсия

| interrupted : Exception
  -- Прервано
```

### Ключевые ошибки для семантического именования

| Ошибка | Описание | Семантический префикс |
|--------|----------|----------------------|
| `unknownConstant` | Неизвестная константа | `unknown_const_` |
| `alreadyDeclared` | Уже объявлено | `redecl_` |
| `declTypeMismatch` | Несоответствие типа декларации | `decl_type_mismatch_` |
| `declHasMVars` | Мета-переменные в декларации | `has_mvars_` |
| `declHasFVars` | Свободные переменные | `has_fvars_` |
| `funExpected` | Ожидалась функция | `fun_expected_` |
| `typeExpected` | Ожидался тип | `type_expected_` |
| `letTypeMismatch` | Несоответствие типа в let | `let_type_mismatch_` |
| `exprTypeMismatch` | Несоответствие типа выражения | `expr_type_mismatch_` |
| `appTypeMismatch` | Несоответствие типа применения | `app_type_mismatch_` |
| `invalidProj` | Некорректная проекция | `invalid_proj_` |
| `thmTypeIsNotProp` | Тип теоремы не Prop | `thm_not_prop_` |



---

## Источник 3: Common Lean Pitfalls (leanprover-community)

URL: https://leanprover-community.github.io/extras/pitfalls.html

### Полный список типичных ошибок и подводных камней

| Категория | Ошибка/Pitfall | Описание | Семантический префикс |
|-----------|----------------|----------|----------------------|
| Implicit params | `autoImplicit` | Неявные параметры из опечаток | `auto_implicit_` |
| Cache | `Mathlib cache` | Забыли скачать кэш | `cache_missing_` |
| Data vs Proof | `have for data` | Использование have вместо let для данных | `have_vs_let_` |
| Rewriting | `rewrite under binders` | rw не работает под биндерами | `rw_under_binder_` |
| Definitions | `unfold definitions` | Тактики не разворачивают определения | `unfold_def_` |
| Ordering | `b > a vs a < b` | Неправильный порядок в неравенствах | `order_swap_` |
| Types | `Prop vs Bool` | Путаница между Prop и Bool | `prop_vs_bool_` |
| Distinctness | `not checking distinctness` | Не проверили различность | `distinctness_` |
| Zero | `not accounting for 0` | Не учли случай 0 | `zero_case_` |
| Division | `division by 0` | Деление на 0 | `div_zero_` |
| Division | `integer division` | Целочисленное деление | `int_div_` |
| Subtraction | `natural subtraction` | Вычитание натуральных | `nat_sub_` |
| Partial | `partial functions` | Частичные функции | `partial_fn_` |
| Fin | `wrapping arithmetic` | Арифметика в Fin | `fin_wrap_` |
| Power | `real power` | Степень вещественных | `real_pow_` |
| Distance | `distance in Fin n → ℝ` | Расстояние в Fin | `fin_dist_` |
| Inf/Sup | `double iInf/iSup` | Двойной iInf/iSup | `double_inf_sup_` |
| Extraction | `extract data from proofs` | Извлечение данных из доказательств | `extract_data_` |
| Equality | `equality of types` | Равенство типов | `type_eq_` |
| Instances | `parameters for existing instances` | Параметры для существующих инстансов | `inst_params_` |
| Sets | `sets as types` | Использование множеств как типов | `set_as_type_` |
| Sort | `Sort _` | Проблемы с Sort | `sort_` |
| Float | `properties about Float` | Свойства Float | `float_prop_` |
| native_decide | `native_decide` | Проблемы с native_decide | `native_decide_` |
| Panic | `panic does not abort` | Panic не прерывает | `panic_` |
| Lean 3 | `Lean 3 code` | Код Lean 3 в Lean 4 | `lean3_compat_` |
| simp | `non-terminal simp` | Нетерминальный simp | `non_term_simp_` |
| Warnings | `ignoring warnings` | Игнорирование предупреждений | `ignored_warning_` |
| Unicode | `ambiguous unicode` | Неоднозначные unicode символы | `unicode_ambig_` |
| Structures | `default values in fields` | Значения по умолчанию в полях структур | `struct_default_` |

### Ключевые сообщения об ошибках тактик

1. **`tactic 'rewrite' failed, did not find instance of the pattern`**
   - Причина: rw не нашёл паттерн (часто под биндером)
   - Решение: использовать `simp_rw` или `conv` mode

2. **`simp made no progress`**
   - Причина: simp не смог упростить
   - Решение: развернуть определения, добавить леммы

3. **`failed to synthesize instance`**
   - Причина: не найден инстанс тайпкласса
   - Решение: добавить инстанс или проверить импорты

4. **`motive is not type correct`**
   - Причина: проблема с зависимым типом при rewrite
   - Решение: использовать `subst` или `conv`



---

## Источник 4: Полный список тактик mathlib4 и их ошибки

URL: https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md

### Ключевые тактики и их типичные ошибки

| Тактика | Описание | Типичная ошибка | Семантический префикс |
|---------|----------|-----------------|----------------------|
| `rfl` | Рефлексивность | `expected type is not definitionally equal` | `rfl_not_defeq_` |
| `simp` | Упрощение | `simp made no progress` | `simp_no_progress_` |
| `ring` | Кольцевая арифметика | `ring failed to close the goal` | `ring_failed_` |
| `linarith` | Линейная арифметика | `linarith failed to find a contradiction` | `linarith_failed_` |
| `nlinarith` | Нелинейная арифметика | `nlinarith failed` | `nlinarith_failed_` |
| `omega` | Целочисленная арифметика | `omega failed` | `omega_failed_` |
| `exact` | Точное совпадение | `type mismatch` | `exact_type_mismatch_` |
| `exact?` | Поиск леммы | `exact? could not find a matching lemma` | `exact_search_failed_` |
| `apply` | Применение леммы | `failed to unify` | `apply_unify_failed_` |
| `rw` | Перезапись | `did not find instance of the pattern` | `rw_pattern_not_found_` |
| `cases` | Разбор случаев | `cases tactic failed` | `cases_failed_` |
| `induction` | Индукция | `induction tactic failed` | `induction_failed_` |
| `intro` | Введение | `intro tactic failed` | `intro_failed_` |
| `have` | Утверждение | `type mismatch` | `have_type_mismatch_` |
| `constructor` | Конструктор | `constructor tactic failed` | `constructor_failed_` |
| `use` | Использование | `use tactic failed` | `use_failed_` |
| `exists` | Существование | `exists tactic failed` | `exists_failed_` |
| `ext` | Экстенсиональность | `ext tactic failed` | `ext_failed_` |
| `funext` | Функц. экстенс. | `funext tactic failed` | `funext_failed_` |
| `congr` | Конгруэнтность | `congr tactic failed` | `congr_failed_` |
| `norm_num` | Числовая нормализация | `norm_num failed` | `norm_num_failed_` |
| `positivity` | Позитивность | `positivity failed` | `positivity_failed_` |
| `polyrith` | Полиномиальная арифм. | `polyrith failed` | `polyrith_failed_` |
| `decide` | Решение | `decide tactic failed` | `decide_failed_` |
| `native_decide` | Нативное решение | `native_decide failed` | `native_decide_failed_` |
| `norm_cast` | Приведение типов | `norm_cast failed` | `norm_cast_failed_` |
| `push_cast` | Проталкивание cast | `push_cast failed` | `push_cast_failed_` |
| `field_simp` | Упрощение полей | `field_simp failed` | `field_simp_failed_` |
| `gcongr` | Обобщ. конгруэнтность | `gcongr failed` | `gcongr_failed_` |
| `aesop` | Автоматический поиск | `aesop failed` | `aesop_failed_` |
| `tauto` | Тавтология | `tauto failed` | `tauto_failed_` |
| `trivial` | Тривиальное | `trivial failed` | `trivial_failed_` |
| `assumption` | Предположение | `assumption tactic failed` | `assumption_failed_` |
| `contradiction` | Противоречие | `contradiction tactic failed` | `contradiction_failed_` |
| `exfalso` | Ex falso | `exfalso failed` | `exfalso_failed_` |
| `by_contra` | От противного | `by_contra failed` | `by_contra_failed_` |
| `push_neg` | Проталкивание отрицания | `push_neg failed` | `push_neg_failed_` |
| `contrapose` | Контрапозиция | `contrapose failed` | `contrapose_failed_` |
| `calc` | Вычисление | `calc step failed` | `calc_step_failed_` |
| `conv` | Конверсия | `conv tactic failed` | `conv_failed_` |
| `ac_rfl` | AC-рефлексивность | `ac_rfl failed` | `ac_rfl_failed_` |
| `abel` | Абелева группа | `abel failed` | `abel_failed_` |
| `group` | Группа | `group failed` | `group_failed_` |
| `module` | Модуль | `module failed` | `module_failed_` |

### Детали по ключевым тактикам

#### linarith
- **Описание:** Находит противоречие между линейными неравенствами
- **Типичные ошибки:**
  - `linarith failed to find a contradiction`
  - Не может идентифицировать атомы (используйте `linarith!`)
  - Не работает с нелинейными выражениями (используйте `nlinarith`)

#### nlinarith
- **Описание:** Расширение linarith для некоторых нелинейных задач
- **Типичные ошибки:**
  - `nlinarith failed`
  - Не может обработать сложные нелинейные выражения

#### omega
- **Описание:** Решает задачи целочисленной арифметики (Nat, Int)
- **Типичные ошибки:**
  - `omega failed`
  - Не работает с вещественными числами
  - Проблемы с контекстом, содержащим нелинейные выражения

#### exact?
- **Описание:** Ищет лемму в библиотеке
- **Типичные ошибки:**
  - `exact? could not find a matching lemma`
  - Требует правильных импортов



---

## Источник 5: Lean.Exception (исходный код Lean 4)

URL: https://leanprover-community.github.io/mathlib4_docs/Lean/Exception.html

### Структура исключений Lean 4

```lean
inductive Lean.Exception : Type
  | error (ref : Syntax) (msg : MessageData) : Exception
    -- Сообщения об ошибках для пользователей. ref используется для позиционной информации.
  
  | internal (id : InternalExceptionId) (extra : KVMap := {}) : Exception
    -- Внутренние исключения, не предназначенные для пользователей.
    -- Примеры: "postpone elaboration", "stuck at universe constraint" и т.д.
```

### Ключевые функции для работы с ошибками

| Функция | Описание | Использование |
|---------|----------|---------------|
| `throwError` | Бросает ошибку с MessageData | Основной способ создания ошибок |
| `throwErrorAt` | Бросает ошибку с указанием позиции | Для точной локализации ошибки |
| `throwNamedError` | Бросает именованную ошибку | Для категоризации ошибок |
| `throwUnknownIdentifierAt` | Неизвестный идентификатор | `unknown_id_` |
| `throwUnknownConstantAt` | Неизвестная константа | `unknown_const_` |
| `throwKernelException` | Ошибка ядра | `kernel_` |
| `throwMaxRecDepthAt` | Превышение глубины рекурсии | `max_rec_depth_` |
| `throwInterruptException` | Прерывание | `interrupt_` |

### Внутренние исключения (InternalExceptionId)

Внутренние исключения используются для управления потоком выполнения и не предназначены для пользователей:

1. **postpone elaboration** — отложить элаборацию
2. **stuck at universe constraint** — застрял на ограничении universe
3. **interrupt** — прерывание

### Именованные ошибки (Named Errors)

Lean 4 поддерживает именованные ошибки через `throwNamedError`:

```lean
def Lean.throwNamedError (name : Name) (msg : MessageData) : m α
```

Это позволяет категоризировать ошибки и обрабатывать их по-разному.



---

## Источник 6: Zulip Chat Archive - типичные ошибки

### Ошибка: `failed to synthesize type class instance`

**Пример:**
```lean
failed to synthesize type class instance for
x m : ℝ
⊢ has_pow ℝ ℝ
```

**Причина:** Lean не может найти инстанс тайпкласса для операции.

**Решение:** Добавить правильный импорт. Например, для `has_pow ℝ ℝ` нужен `import analysis.special_functions.pow`.

**Отладка:** Использовать `#print instances has_pow` для просмотра доступных инстансов.

---

## ПОЛНАЯ КЛАССИФИКАЦИЯ ОШИБОК LEAN 4

### Категория 1: Ошибки типов (Type Errors)

| Код ошибки | Сообщение | Причина | Семантический префикс | Решение |
|------------|-----------|---------|----------------------|---------|
| `type_mismatch` | `type mismatch` | Несовпадение типов | `type_mismatch_of_` | Проверить типы, использовать `@` для явных аргументов |
| `app_type_mismatch` | `application type mismatch` | Неправильное применение функции | `app_mismatch_` | Проверить аргументы функции |
| `expected_type` | `expected type` | Ожидался другой тип | `expected_type_` | Привести к нужному типу |
| `def_type_mismatch` | `definition type mismatch` | Тип определения не совпадает | `def_type_` | Исправить тип определения |

### Категория 2: Ошибки синтеза инстансов (Instance Synthesis)

| Код ошибки | Сообщение | Причина | Семантический префикс | Решение |
|------------|-----------|---------|----------------------|---------|
| `synth_failed` | `failed to synthesize instance` | Инстанс не найден | `inst_synth_` | Добавить импорт или определить инстанс |
| `no_instance` | `no instance of type class` | Тайпкласс не определён | `no_inst_` | Определить инстанс |
| `ambiguous_inst` | `ambiguous instances` | Несколько подходящих инстансов | `ambig_inst_` | Указать явно нужный инстанс |

### Категория 3: Ошибки унификации (Unification Errors)

| Код ошибки | Сообщение | Причина | Семантический префикс | Решение |
|------------|-----------|---------|----------------------|---------|
| `unify_failed` | `failed to unify` | Не удалось унифицировать | `unify_` | Проверить структуру выражений |
| `motive_not_correct` | `motive is not type correct` | Проблема с зависимым типом | `motive_` | Использовать `subst` или `conv` |
| `occurs_check` | `occurs check failed` | Циклическая зависимость | `occurs_` | Переструктурировать выражение |

### Категория 4: Ошибки тактик (Tactic Errors)

| Код ошибки | Сообщение | Причина | Семантический префикс | Решение |
|------------|-----------|---------|----------------------|---------|
| `rfl_failed` | `rfl failed` | Не definitionally equal | `rfl_` | Использовать `simp` или `ring` |
| `simp_no_progress` | `simp made no progress` | simp не смог упростить | `simp_` | Развернуть определения, добавить леммы |
| `ring_failed` | `ring failed to close the goal` | Не кольцевое выражение | `ring_` | Проверить структуру, использовать `ring_nf` |
| `linarith_failed` | `linarith failed to find a contradiction` | Нет линейного противоречия | `linarith_` | Добавить гипотезы, использовать `nlinarith` |
| `nlinarith_failed` | `nlinarith failed` | Слишком сложное нелинейное | `nlinarith_` | Разбить на части, использовать `polyrith` |
| `omega_failed` | `omega failed` | Не целочисленная задача | `omega_` | Проверить типы (Nat/Int) |
| `rw_failed` | `rewrite tactic failed` | Паттерн не найден | `rw_` | Использовать `simp_rw` или `conv` |
| `exact_failed` | `exact tactic failed` | Тип не совпадает | `exact_` | Проверить тип, использовать `exact?` |
| `apply_failed` | `apply tactic failed` | Не удалось применить | `apply_` | Проверить гипотезы |
| `cases_failed` | `cases tactic failed` | Не индуктивный тип | `cases_` | Проверить тип выражения |
| `induction_failed` | `induction tactic failed` | Не индуктивный тип | `induction_` | Проверить тип переменной |
| `assumption_failed` | `assumption tactic failed` | Нет подходящей гипотезы | `assumption_` | Добавить гипотезу |
| `contradiction_failed` | `contradiction tactic failed` | Нет противоречия | `contradiction_` | Добавить противоречащие гипотезы |
| `decide_failed` | `decide tactic failed` | Не decidable | `decide_` | Проверить Decidable инстанс |
| `norm_num_failed` | `norm_num failed` | Не числовое выражение | `norm_num_` | Проверить структуру |
| `positivity_failed` | `positivity failed` | Не удалось доказать позитивность | `positivity_` | Добавить гипотезы о знаках |
| `polyrith_failed` | `polyrith failed` | Слишком сложный полином | `polyrith_` | Упростить выражение |
| `aesop_failed` | `aesop failed` | Автоматический поиск не нашёл | `aesop_` | Добавить подсказки |

### Категория 5: Ошибки идентификаторов (Identifier Errors)

| Код ошибки | Сообщение | Причина | Семантический префикс | Решение |
|------------|-----------|---------|----------------------|---------|
| `unknown_id` | `unknown identifier` | Идентификатор не найден | `unknown_id_` | Проверить импорты и имена |
| `unknown_const` | `unknown constant` | Константа не найдена | `unknown_const_` | Добавить импорт |
| `ambiguous_id` | `ambiguous identifier` | Несколько определений | `ambig_id_` | Указать полное имя |

### Категория 6: Ошибки ядра (Kernel Errors)

| Код ошибки | Сообщение | Причина | Семантический префикс | Решение |
|------------|-----------|---------|----------------------|---------|
| `kernel_type_mismatch` | `(kernel) type mismatch` | Ошибка в ядре | `kernel_type_` | Серьёзная ошибка, проверить всё |
| `kernel_app_mismatch` | `(kernel) application type mismatch` | Ошибка применения в ядре | `kernel_app_` | Проверить типы аргументов |
| `kernel_universe` | `(kernel) universe level mismatch` | Несовпадение уровней universe | `kernel_univ_` | Проверить уровни universe |

### Категория 7: Специфические ошибки Mathlib

| Код ошибки | Сообщение | Причина | Семантический префикс | Решение |
|------------|-----------|---------|----------------------|---------|
| `gcongr_failed` | `gcongr failed` | Не удалось применить gcongr | `gcongr_` | Проверить монотонность |
| `field_simp_failed` | `field_simp failed` | Не удалось упростить поле | `field_simp_` | Проверить ненулевость |
| `norm_cast_failed` | `norm_cast failed` | Не удалось привести типы | `norm_cast_` | Проверить coercion |
| `push_cast_failed` | `push_cast failed` | Не удалось протолкнуть cast | `push_cast_` | Проверить структуру |

