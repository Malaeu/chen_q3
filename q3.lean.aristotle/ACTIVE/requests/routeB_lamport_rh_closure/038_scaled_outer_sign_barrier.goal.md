# ГОЛ 038 — ScaledOuterSignBarrierFourThirds (по ратифицированной директиве)

От: Mythos (диспетчер). Авторизация: директива судьи
`SUPPLIER_A_038_DIRECTIVE_RATIFIED` (route_score 5), цикл «го» продолжается
через кондуктора. Статус: `CHALLENGER / NOT_RH`. `BUS_010_VOID`.
Scope: `COFINAL_FAMILY`; регрессии — finite-cell.

Целевой путь этого файла:
`/Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/038_scaled_outer_sign_barrier.goal.md`

## Нормативный источник

`docs/routeB_bus/PROSHKA_038_SUPPLIER_A_DIRECTIVE_2026-07-30.md`
sha256 `bbd599fbca17e752fa5c2b5b8b4ac667d84cb6bc6799c40a2568b04b07c16aac`

Раздел CODEX DIRECTIVE этого файла (STEP 0–5, планты P038-1..11, коды
вердиктов и стопов, FORBIDDEN SHORTCUTS, VALIDATION GATE, R1/R2) исполняется
ДОСЛОВНО. Настоящий гол — операционная обёртка: порядок, ресурсы, границы
этого рана, прогнозы диспетчера. При любом расхождении приоритет за
директивой; расхождение само по себе — материал для ответа, не для
интерпретации.

## Порядок исполнения (K2: дешёвый решающий тест первым)

0. **Hash gate** (VALIDATION GATE п.1): SHA-256 всех источников из STEP 0
   против MANIFEST. Любое расхождение → `SOURCE_HASH_MISMATCH`, стоп гола.

1. **Generic-m replay** (первая половина STEP 1; судья: «самый дешёвый
   решающий тест»): из exact 031-источника (generator + certificate +
   checker, структура коэффициентов Ψ_m / δ_q-леджер) извлечь точное 𝒟,
   рекуррентность `L_Θ`, полный Green ledger с ЖИВЫМ terminal term; заменить
   каждое зашитое `257` на символьный `m`; выполнить exact-rational /
   символьный реплей тождества
   `S_scaled_m = ((Θ4_m − Θ0_m)/2)·D_m`.
   Исходы:
   - тождество держится символьно → это evidence-класс
     `REPLAY_HOLDS_SYMBOLICALLY` (НЕ флаг
     `PARAMETRIC_SCALED_JACOBI_PROFILE_IDENTITY_PROVED` — флаг только при
     доказанной теореме);
   - слом → артефакт `JACOBI_LIFT_BREAK_LIST.md`: каждое место слома с
     файлом/строкой/термом/причиной. Это вход пен-фазы диспетчера.
   Запрещено в этом ране: любые знаковые оценки (STEP 2 заперт до identity);
   определять 𝒟 по желаемому знаку.

2. **Rehearsal m=257** (STEP 5): `finiteSupplierAGreenEngineRehearsal_m257` —
   диагностика на конечном скелете: exact 031 alias, ориентация forcing,
   нижняя граница строго из `a_{-1}=0` и `δ_0=0`, живой terminal, 179
   positive controls, 62 zero-compatible случая, sign-flip и terminal-drop
   планты. Флаг `SUPPLIER_A_REHEARSAL_036_PASSED` или стоп
   `SUPPLIER_A_REHEARSAL_ENGINE_MISMATCH`. Результат диагностический;
   премисой кофинала не является (P038-10 сторожит).

3. **Планты этого рана**: P038-2, P038-4, P038-5, P038-6,
   P038-7 (включая точную проверку внутриполосного перехода:
   `S_r(1/(r+1)) = −r/(6(r+1))`, `S_r(1/r) = (3r+1)/(6r)`), P038-8 —
   исполнить полностью. P038-1, P038-3, P038-9, P038-10, P038-11 —
   на harness-уровне: попытка вставить finite-объект (257-сертификат, 027,
   036-результат) в параметрический слот обязана отклоняться скоуп-чекером;
   зафиксировать срабатывание. Каждый плант обязан выстрелить, иначе
   `PLANT_NOT_DETECTED`.

4. **Опциональная диагностика, не блокирует** (семантика STEP 3, Γ-дискриминатор):
   интервальный (Arb) брекет `a_intrinsic(257)` внутри полосы r=195 через
   L/U-огибающие `S_scaled_257`; вывод строго в трёх статусах
   PASS-строгое-внутри / ZERO_CONSISTENT (с шириной интервалов) / KILL-край.
   Запрещено любое участие `ε_r`, `r_cert`, `ρ_033`, `q=700`, `τ_response`,
   box widths в определении (P038-8). Артефакты:
   `A_INTRINSIC_257_BRACKET.md` + `.csv`.

5. **036**: транзакцией НЕ исполнять. В шапку
   `036_tooth_sign.goal.md` (канон + зеркало) дописать решение судьи
   дословно: `ABSORB_AS_FINITE_SUPPLIER_A_REHEARSAL`,
   `standalone_critical_path_goal=false`,
   `may_be_used_as_cofinal_premise=false`,
   `execute_existing_goal_as_written=false`, + SHA директивы. Тело не менять.

6. **Bootstrap-алиас судьи**: положить копию
   `docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md` по вложенному пути
   `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` (судья запрашивал —
   статус был MISSING); SHA обеих копий в ответ.

## Границы этого рана и честный выход

Доказательств знака в ране нет по построению, поэтому ожидаемый честный
первичный вердикт — `SCALED_OUTER_SIGN_BARRIER_FOUR_THIRDS_INCONCLUSIVE`
с ОБЯЗАТЕЛЬНЫМИ по директиве приложениями:
- `Γ_257(4/3)` назван дискриминатором; если п.4 исполнен — его L/U-числа и
  точный zero-consistent терм, мешающий вердикту;
- оба кандидата пере-представления R1 (continuant / transfer-matrix,
  kill-power 5 / cost 3) и R2 (generating / Euler–Maclaurin с coupled
  endpoint remainder, 4/3) — с конкретной привязкой к реальному 031-коду:
  какие термы леджера ложатся на какую форму.
`PROVED`/`KILLED` в этом ране допустимы только при полном закрытии по
MODE FULL / MODE SPLIT — не форсировать. Эскалация точности и новые m-клетки
запрещены директивой при INCONCLUSIVE.

Lean в этом ране не трогается: пункт 4 VALIDATION GATE (`lake build`,
`#print axioms`) исполняется при входе в Lean-фазу; в ответе явно заявить
`LEAN_PHASE_NOT_ENTERED`. Пункты 1–3, 5–7 VALIDATION GATE — исполнить.

## Прогнозы диспетчера (K6; скорить в ответе, без ретроактивного ремонта)

```text
P038-M1: слом generic-m реплея локализуется в КОНЕЧНОМ именованном списке
         мест (ожидаю: δ_q-леджер и оконная длина с зашитым 257), а не
         диффузно; пен-лифт становится well-posed.
P038-M2: (если п.4 исполнен) a_intrinsic(257) СТРОГО < 257/195 — переход
         внутри полосы; вилка: ZERO_CONSISTENT у края ⇒ сообщить ширины
         интервалов, это не провал.
P038-M3: rehearsal пройдёт: 179 controls подтверждаются, 62 зубца остаются
         zero-compatible, KILL-события нет.
```

## Замки

Дословно раздел FORBIDDEN SHORTCUTS директивы. Дополнительно: байты
источников не менять; Aristotle-проекты `b14fe0a5-…` и `987ff124-…` не
трогать (`ARISTOTLE_ACTIONS_BY_CODEX=false`); канон и зеркало едут одним
коммитом (правило канала от 2026-07-30, коммит `a6b1533`); одна строка
истории в `ROUTE_B_STATE.md` по закрытии; глоссарий заморожен — коды
директивы суть шинные коды транзакции.

## Ответ

`038_scaled_outer_sign_barrier.answer.md` — handoff + полный ACTIONS LOG
(иначе REJECTED), primary-вердикт первой строкой, scope/verifier-леджер на
каждое утверждение (VALIDATION GATE п.5), подтверждение отсутствия 036 в
dependency tree цели (п.6) и `CHALLENGER / NOT_RH`, `BUS_010_VOID` (п.7).
Артефакты: `JACOBI_LIFT_BREAK_LIST.md` (или символьный реплей-сертификат),
rehearsal-леджер m=257, лог плантов, [опц.] `A_INTRINSIC_257_BRACKET.{md,csv}`,
обновлённый MANIFEST.
