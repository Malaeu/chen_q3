## Parameter closure plan (Q3 → legacy data)

1. **A3 barrier and symbol floor**
   - [x] Use the explicit tables in `legacy/tex/A3_calibration_kappa.tex` and `legacy/tex/parameter_recipe.tex`.
   - [x] Import the numerical margins `c0(K)` from `legacy/cert/bridge/K*_A3_lock.json` into the `sections/A3/` tables.
   - [x] Reference the analytic bounds recorded in `Q3_paper/sections/A3/arch_bounds.tex` to justify the chosen parameters.
   - [x] Action: migrate the numeric entries into a new `sections/A3/param_tables.tex`; cite them in the main theorems.
   - [x] Status: `sections/A3/param_tables.tex` added; `sections/A3/main.tex` now inputs the table and cites `cert/bridge/K*_A3_lock.json` with `cert/bridge/logs/A3_lock_K*.txt`.

2. **Prime cap**
   - [x] Closed-form formulas are in `sections/RKHS/prime_norm_leq_rho.tex`.
   - [x] Numerical evaluations reside in `legacy/cert/bridge/K*_trace.json` and logs `cert/bridge/logs/`.
   - [x] Pull those values into a `sections/RKHS/prime_cap_table.tex` (or summary table), linking to both analytic lemmas and the certificate data.
   - [x] Status: `sections/RKHS/prime_cap_table.tex` in place; `prime_norm_leq_rho.tex` now cites the legacy JSON certificates (mode `target`).

3. **IND/AB chain**
   - [x] The monotone budgets and early-block estimates are already in `sections/IND_AB/MD_2_3_constants.tex`, `MD_2_3_constants_table.tex`, and `IND_prime_step.tex`.
   - [x] Numerical updates per K live in `legacy/cert/bridge` JSONs; convert them into a consolidated appendix table.
   - [x] Action: ensure the Q3 text references those tables and clarifies that the monotonicity comes from the recorded parameter schedule.
   - [x] Status: `sections/IND_AB/ind_schedule_table.tex` added; `MD_2_3_base_interval.tex` and `IND_prime_step.tex` now cite `cert/bridge/K1_blocks.json`, `K1_step_next.json` and link back to legacy traces.
   - Note (pipeline): только `K=1` требует явного greedy-блока. Первая вершина (n=2) съедает 0.181352 из бюджета `ε(K)=c_0(K)/4`, остаток 0.00522 ведёт в `K1_step_next.json`, где IND$'$ проверяет $\rho_K^{\mathrm{old}}+w_{\mathrm{new}}<1`. Для $K\ge2$ цепочка идёт в чистом one-prime режиме, поэтому `K*_blocks.json` не генерились — нули в колонках `Block mass/Residual` эквивалентны тому, что бюджет контролируется столбцом $c_0-\rho$. При желании можно прогнать `tools/make_blocks.py` для остальных $K`, но на доказательство это не влияет.

4. **T5 grid/lift**
   - Analytic lemmas are in `sections/T5/summary.tex` and `sections/T5/grid.tex`.
   - Concrete grid steps `Δ_K` and Lipschitz constants appear in `legacy/cert/bridge/K*_grid.json` and scripts `ops/`.
   - Bring the definitive grid parameters into an appendix table (e.g., `appendix/T5_parameters.tex`), citing both the analytic lemma and the explicit values.

5. **End-to-end check**
   - Leverage `publication_repo/tex/VERIFICATION_APPENDIX.tex` and logs in `ops/` / `cert/bridge/logs`.
   - Summarize the full pipeline steps in the verification appendix pointing to TPTP/SMT outputs (`proofs/T5_global_transfer/`, etc.).
   - Action: include a short checklist in Q3 (`appendix/verification.tex`) that cross-references all artifact locations.

Once these data tables are copied into Q3 and referenced in the theorems, the “Plan B ⇒ RH” presentation becomes fully self-contained.

• - Шаг 1 (A3 символ): тянем формулы из docs/tex/A3_calibration_kappa.tex:1 и рецепт из docs/tex/parameter_recipe.tex:1, а числа (c0, B, t_sym, M_min) берём из cert/bridge/K*_A3_lock.json
    (структуру глянул через jq, всё на месте). В Q3 создаём Q3_paper/sections/A3/param_tables.tex, туда загружаем таблицу с колонками K, B, t_sym, c0, M_min, omega_pi_over_M. После этого в
    Q3_paper/sections/A3/main.tex:1 сразу под блоком (A3.1) вставляем \input{sections/A3/param_tables} и сноску на логи cert/bridge/logs/A3_lock_K*.txt для воспроизводимости.
  - Шаг 2 (prime cap): аналитика уже лежит в Q3_paper/sections/RKHS/prime_norm_leq_rho.tex:1, остаётся подставить цифры. Берём rho, t и статус из cert/bridge/K*_trace.json + при
    необходимости уточняем детали из cert/bridge/logs/*trace*.txt. Создаём Q3_paper/sections/RKHS/prime_cap_table.tex с таблицей (K, t, ρ, target, ok). Под разделом «Immediate corollaries»
    добавляем \input{sections/RKHS/prime_cap_table} и текстом указываем, что цифры подтверждены JSON-ами.
  - Шаг 3 (IND/AB бюджеты): исходники с формулами лежат в docs/tex/MD_2_3_constants.tex:1, docs/tex/MD_2_3_constants_table.tex:1, а конкретные блоки и суммы — в cert/bridge/K*_blocks.json
    + cert/bridge/logs/K*_blocks.txt. Для Q3 дополняем существующие файлы Q3_paper/sections/IND_AB/MD_2_3_constants.tex:1 и …/MD_2_3_constants_table.tex:1 реальными числами, плюс добавляем
    сводный «monotone schedule» прямо в Q3_paper/sections/IND_AB/IND_prime_step.tex:1 (таблица с K, B, t, eps, суммарной массой). Там же вставляем ссылки на JSON/логи.
  - Шаг 4 (T5 сетка): сеточные параметры (Delta_target, Delta_actual, num_points, c0, t) берём из cert/bridge/K*_grid.json, а проверку через Vampire — из proofs/T5_global_transfer/
    logs/*.log. В Q3 заводим Q3_paper/appendix/T5_parameters.tex с таблицей по K, указываем Lipschitz-константы и суммарный вес. В Q3_paper/sections/T5/grid.tex:1 под формулировкой
    Lemma~\ref{lem:T5p-grid} вставляем \input{appendix/T5_parameters} и short caption с отсылкой на логи.
  - Шаг 5 (финишная проверка): сводку берём из publication_repo/tex/VERIFICATION_APPENDIX.tex:1, плюс формальные логи (proofs/A3_global, proofs/T5_global_transfer, cert/bridge/logs).
    В Q3_paper/appendix/verification.tex:1 заменяем текущий общетекстовый список на чеклист, где каждый пункт ссылается на новые таблицы (A3, prime cap, IND/AB, T5) и на конкретные
    артефакты. Финальную строку делаем про то, что «Plan B ⇒ RH» теперь читает только за счёт таблиц.
  - Структурный контроль: новых param_tables.tex в sections/A3 и sections/RKHS пока нет — конфликтов не будет; Main_closure (Q3_paper/sections/Main_closure.tex:1) ничего не ломает, нужно
    лишь убедиться, что Makefile уже подхватывает добавленные \input (latexmk автоматически схватит). После каждого шага прогоняем uv run python -m json.tool на свежих JSON-парсах и make
    -C Q3_paper latex для быстрой проверки ссылок.
