# Полный справочник по ошибкам Lean 4 для семантического именования sorry

Этот документ объединяет информацию из официальной документации Lean 4, исходного кода, комьюнити-ресурсов (Zulip, GitHub) и полного списка тактик mathlib4 для создания исчерпывающей таблицы ошибок. Цель — автоматическая генерация семантически осмысленных имён для `sorry` на основе типа ошибки.

---

## Полная таблица ошибок Lean 4

| Категория | Сообщение об ошибке (Error Message) | Код ошибки | Тактика/Контекст | Вероятная причина | Решение | Семантический префикс |
|---|---|---|---|---|---|---|
| **Ошибки типов** | `type mismatch ... has type ... but is expected to have type ...` | `type_mismatch` | `exact`, `have`, `let` | Несовпадение типов. | Проверить типы, использовать `@` для явных аргументов, `show` для уточнения цели. | `type_mismatch_of_` |
| | `application type mismatch` | `app_type_mismatch` | Применение функции | Аргумент имеет неверный тип. | Проверить типы аргументов. | `app_mismatch_` |
| | `(kernel) type mismatch` | `kernel_type_mismatch` | Ядро Lean | Глубокая ошибка в логике, нарушение правил ядра. | Критическая ошибка. Пересмотреть доказательство с нуля. | `kernel_type_` |
| **Синтез инстансов** | `failed to synthesize instance` | `synth_failed` | Любая операция, требующая тайпкласс | Инстанс не найден в контексте. | Добавить нужный `import`, определить инстанс вручную. | `inst_synth_of_` |
| | `ambiguous instances` | `ambiguous_inst` | Любая операция, требующая тайпкласс | Найдено несколько подходящих инстансов. | Указать инстанс явно: `(@operation _ _ inst ...)` | `ambig_inst_for_` |
| **Унификация** | `failed to unify ... with ...` | `unify_failed` | `apply`, `exact` | Не удалось сопоставить термы. | Проверить структуру выражений, унифицируемость. | `unify_` |
| | `motive is not type correct` | `motive_not_correct` | `rewrite`, `induction` | Проблема с зависимыми типами при замене. | Использовать `subst`, `conv`, `induction ... with ...`. | `motive_` |
| **Ошибки тактик** | `tactic 'rfl' failed` | `rfl_failed` | `rfl` | Выражения не являются definitionally equal. | Использовать `simp`, `ring` или `show`. | `rfl_` |
| | `simp made no progress` | `simp_no_progress` | `simp` | `simp` не смог ничего упростить. | Развернуть определения (`unfold`), добавить леммы в `simp`. | `simp_` |
| | `tactic 'ring' failed` | `ring_failed` | `ring` | Выражение не является полиномом в кольце. | Проверить структуру, использовать `ring_nf`. | `ring_` |
| | `tactic 'linarith' failed` | `linarith_failed` | `linarith` | Нет линейного противоречия в гипотезах. | Добавить гипотезы, проверить линейность, использовать `nlinarith`. | `linarith_` |
| | `tactic 'nlinarith' failed` | `nlinarith_failed` | `nlinarith` | Слишком сложное нелинейное выражение. | Упростить, разбить на подзадачи. | `nlinarith_` |
| | `tactic 'omega' failed` | `omega_failed` | `omega` | Не целочисленная арифметика (Nat/Int). | Проверить типы, убедиться в отсутствии нелинейности. | `omega_` |
| | `rewrite tactic failed...` | `rw_failed` | `rw`, `simp_rw` | Паттерн для перезаписи не найден. | Проверить, что лемма применима; использовать `conv` для перезаписи под биндерами. | `rw_` |
| | `tactic 'exact?' failed` | `exact_search_failed` | `exact?` | Не удалось найти лемму в библиотеке. | Проверить импорты, попробовать другие ключевые слова. | `exact_search_` |
| | `tactic 'assumption' failed` | `assumption_failed` | `assumption` | Нет гипотезы, совпадающей с целью. | Проверить контекст. | `assumption_` |
| | `tactic 'contradiction' failed` | `contradiction_failed` | `contradiction` | В контексте нет противоречия (`p` и `¬p`). | Найти или доказать противоречие. | `contradiction_from_` |
| **Идентификаторы** | `unknown identifier` | `unknown_id` | Любой контекст | Идентификатор не определён или не импортирован. | Проверить имя, добавить `import`. | `unknown_id_` |
| | `ambiguous identifier` | `ambiguous_id` | Любой контекст | Несколько идентификаторов с таким именем. | Указать полное имя (namespace). | `ambig_id_` |
| **Ядро Lean** | `(kernel) declaration has metavariables` | `kernel_meta` | `end` файла | В определении остались метапеременные. | Найти и решить все `sorry` или `_`. | `kernel_meta_in_` |
| | `(kernel) unknown constant` | `kernel_unknown_const` | Ядро Lean | Ядро не знает о константе. | Ошибка сборки или окружения. | `kernel_unknown_const_` |
| **Прочее** | `maximum recursion depth has been reached` | `max_rec_depth` | Любая тактика | Слишком глубокая рекурсия. | Увеличить лимит (`set_option maxRecDepth ...`) или переписать доказательство. | `max_rec_depth_at_` |
| | `don't know how to synthesize placeholder` | `synth_placeholder` | `_` | Lean не может вывести пропущенный терм. | Указать терм явно. | `synth_placeholder_for_` |

