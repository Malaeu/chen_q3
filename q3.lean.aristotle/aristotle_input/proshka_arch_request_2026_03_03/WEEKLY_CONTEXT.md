# Weekly Context (ARCH)

- Основной блокер: `prime_heat_bounds_arch_data` всё ещё привязан к legacy-axiom.
- Уже подготовлены модули для math-route:
  - `ArchHeatMajorant.lean`
  - `PrimeHeatArchPiecewiseKernel.lean`
  - `PrimeHeatDigammaShift.lean`
- Ограничения фиксированы: без `native_decide/sorry/admit/exact?`, без новых аксиом, константы не менять.
- Требуется чистый theorem-route с kernel-safe доказательством.
