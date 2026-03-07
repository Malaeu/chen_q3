# Progress Log — Formal_RH_2026

## 2026-02-28 (Post-sync, no Lean run)

- Задача: сверить документальный слой с рабочей цепью τ=0 и зафиксировать мост:
  `prime_cert_margin_from_rkhs`.
- Исправлены офлайн-описания в статусных файлах: `CHAIN_STATUS.md`,
  `PROJECT_ORCHESTRATOR.md`, `ACTIVE/MAIN_CHAIN_DEPS.md`, `FORMALIZATION_STATS.md`,
  `Q3/CheckAxioms.lean`.
- Критическая техника: не запускать `lake env lean` автоматически из‑за проблемы с
  памятью; проверки продолжать только точечными и короткими командами после контроля.
- Следующий минимальный шаг: внедрить чистый `PrimeTerm_tau0_brange_pure` мост через
  без-цикловый адаптер и повторить `#print axioms Q3.Main.RH_of_Weil_and_Q3`.

## 2026-02-28 (Europe/Berlin)

### Context (last chat excerpt summary)
- Mainline was intentionally de‑entangled from the heavy PrimeCert “checker” chain; RH pipeline currently reduces to a small set of remaining trusted contracts (e.g. Weil criterion equivalence + one prime-term bound at t_critical).  
- Work proceeded on *kernel‑safe* analytic replacements for “data axioms”, including the unified Gaussian tail kernel and removal of at least one redundant grid data axiom.
- The next critical-path blocker identified: a **clean τ=0, B-range bridge** for the prime-term margin that does **not** depend on `Brange_2046` / legacy PathB.

### Current objective
Build a **pure τ=0 B-range module** producing the prime-term vs arch-term margin on `B ∈ [B_min, prime_cert_B_max]` and wire it into `Q_nonneg_t_critical` via `prime_cert_margin_from_rkhs`, removing the legacy PathB proxy.

### Plan (structured)
1. Add `Q3/Proofs/PrimeTerm_tau0_brange_pure.lean`:
   - prove `arch_term_ge_cstar_on_brange` (τ=0).
   - prove `prime_term_le_cstar_quarter_on_brange` via RKHS cap `rho 1` and `rho_one_lt_one_over_twentyfive`.
   - deduce `prime_term_le_arch_term_tau0_brange_pure` and/or package into `PrimeCertMarginOnBrange`.
   - allow temporary assumptions only as *explicit TODO gaps* (no legacy imports).
2. Refactor wiring:
   - avoid import cycles: keep `RKHS_PrimeCap_Analytic` as “rho + cap lemmas” layer; put `prime_cert_margin_from_rkhs` wrapper in a separate adapter module if needed.
3. Patch `Q_nonneg_t_critical.lean` minimally to consume the same `PrimeCertMarginOnBrange` API.
4. Verification:
   - `lake env lean` on new module, then the RKHS adapter, then `Q_nonneg_t_critical`, then `Q3/Main.lean`.
   - `rg -n "sorry|admit|exact\?"` in the active chain.
   - `#print axioms` on the top theorem to confirm no new trust.

### Main risk
Potential **import cycle** if `PrimeTerm_tau0_brange_pure` imports `RKHS_PrimeCap_Analytic` while that same file is modified to import the new module. Mitigation: split definitions vs adapters or move the wrapper out.
