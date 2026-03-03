# START HERE (ARCH)

Цель: закрыть `prime_heat_bounds_arch_data` theorem-route без checker-heavy и без новых аксиом.

Порядок чтения:
1. `REQUEST.md`
2. `WEEKLY_CONTEXT.md`
3. `MANIFEST.txt`
4. `sources_core/extracted_structure.md`
5. `context_files/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
6. `context_files/q3.lean.aristotle/Q3/Proofs/PrimeCert/ArchHeatMajorant.lean`
7. `context_files/q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeHeatArchPiecewiseKernel.lean`
8. `context_files/q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeHeatDigammaShift.lean`

Ключевые ограничения:
- No `native_decide`, `sorry`, `admit`, `exact?`
- No new axioms
- Не менять cert-константы
- Числовой масштаб: до 15 знаков после запятой
