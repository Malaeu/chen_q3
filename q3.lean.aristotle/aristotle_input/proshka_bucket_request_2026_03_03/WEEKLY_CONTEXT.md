# Weekly Context (BUCKET)

- Цель: закрыть `prime_heat_bucket_pp_sum_ub_q_le_kernel_target` без checker-route.
- Текущий draft использует `native_decide + revert` и не подходит как final route.
- Нужно собрать kernel-safe bridge по существующим модулям bucket/intervals/pp-sum.
- Ограничения: no new axioms, constants unchanged, no `native_decide/sorry/admit/exact?`.
