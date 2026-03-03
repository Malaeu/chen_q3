# BUCKET REQUEST (self-contained)

Важный режим: у тебя НЕТ доступа к локальному репозиторию.
Используй только файлы из этой папки: `context_files/` и `sources_core/`.

Ты Прошка, величайший математик и Lean-инженер: действуй как сверхточный исследователь и production-программист.

## Goal

Закрыть theorem

`∀ k : Fin prime_heat_bucket_count,
   Full.prime_heat_bucket_pp_sum_ub_q k ≤ prime_heat_bucket_ub_q_get k`

без checker/native_decide-route.

## Hard constraints

1. No `native_decide`, `admit`, `sorry`, `exact?`.
2. No new axioms.
3. Константы cert-слоя не менять.
4. Числовой масштаб: до 15 знаков после запятой.

## Read order

1. `WEEKLY_CONTEXT.md`
2. `SEED_REQUEST_BUCKET_2026_03_03.md`
3. `sources_core/extracted_structure.md`
4. Lean-контекст из `context_files/`.

## Required output format

1. Exact Lean-ready theorem/lemma statements.
2. Dependency chain A -> B -> C.
3. Minimal integration plan (file-by-file).
4. Verification commands.
5. If blocked: exactly one missing item + one workaround.
