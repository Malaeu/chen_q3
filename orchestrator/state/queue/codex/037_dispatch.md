Ты Codex — репозиторный исполнитель шины Route B. Диспетчер Mythos выдал гол 037,
кондуктор доставил его на шину.

ГОЛ (исполнять дословно):
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/037_muntz_r6_harvest.goal.md

Прочитай его целиком первым действием.

## ПОПРАВКА К ДИАГНОЗУ ГОЛА — прочитай до начала задачи B

Гол утверждает, что канон не тронут и `_INBOX_cowork_034edge_2026-07-29/` стоит
целиком. На диске это НЕ так. Mythos ставил диагноз по GitHub, а не по рабочему
дереву, и увидел только зеркало. Фактическое состояние:

- `_INBOX_cowork_034edge_2026-07-29/` уже УДАЛЁН с диска;
- семь артефактов уже лежат в корне канонной шины под именами схемы 035
  (`034_edge_sliver_REGISTRATION.md`, `034_edge_sliver_INBOX_COVER.md`,
  `034_cofinal_scaled_edge_sliver_moment.answer.md`, `check_034_edge_sliver_reduction.py`,
  `CHECK_034_RUN.log`, оба `ARISTOTLE_TASK_*.md`);
- канонный `proshka/` уже содержит `PROSHKA_033_AND_MUNTZ_POLE_SUBTRACTED_v2.md`
  и `PROSHKA_034_EDGE_SLIVER_CONTRACT.md`;
- `035_edge_sliver_materialization.{goal,answer}.md`, `036_tooth_sign.goal.md`
  и `P1_RADIUS_MUTATION.csv` уже в корне канона.

Причина расхождения: всё это НЕ ЗАКОММИЧЕНО. Ты в прошлом голе следовал
CHANNEL_RULE буквально — «коммитить только docs/routeB_bus/» — поэтому на
GitHub уехало одно зеркало, а канонные изменения остались в рабочем дереве как
untracked и как незастейдженные удаления.

Поэтому задача B — это НЕ перенос заново. Это:
1. верификация, что перечисленное выше на месте и байты не изменились;
2. пересчёт SHA-256 всех этих файлов с полной таблицей в ответ;
3. досбор того, чего действительно не хватает.

Не копируй поверх существующего вслепую и не трогай байты уже проверенных
артефактов — гол это прямо запрещает.

## КОММИТ КАНОНА — граница, которую сам не переходи

Чтобы канон доехал до GitHub, нужен коммит ВНЕ `docs/routeB_bus/`. По
guardrail'у это требует явного разрешения владельца, которого пока НЕТ.

Поэтому: сделай всю работу на диске, но канонные пути НЕ коммить и НЕ пушить.
Зеркало по правилу 014 обновляй и коммить как обычно. В ответе отдельным
пунктом перечисли точный список канонных путей, ожидающих разрешения на коммит,
чтобы кондуктор поднёс это владельцу одним вопросом.

## Задача A — харвест R6

Архив уже скачан кондуктором из правильного аккаунта Aristotle и распакован:
q3.lean.aristotle/aristotle_output/c746a674_R6_RMINUS_HALFPLANE_2026-07-30/

Внутри `output-final.tar.gz` и распакованный `output-final_aristotle/`
(RESULT.md, ARISTOTLE_SUMMARY.md, lakefile.toml, lean-toolchain, lake-manifest.json,
RequestProject/*.lean). Стоп-код R6_ARCHIVE_MISSING не применим.

Предварительные факты, перепроверь их сам:
- taint-scan `rg "sorry|admit|axiom|native_decide|exact\?"` по `RequestProject/*.lean`
  дал НОЛЬ вхождений;
- `TailAnalyticity.lean`: R5 = 94 строки с `sorry` на 92-й, R6 = 148 строк без дырок;
- теорема `Rminus_differentiableOn_halfPlane` доказана через
  `mellin_differentiableAt_of_isBigO_rpow`, опирается на `Estar_bounded_by_sqrt_of_zeroMass`;
- R5-версия для строчного дифа лежит рядом:
  `q3.lean.aristotle/aristotle_output/c746a674-5849-4dfa-9e4c-b7dd5af231b2_R5_BROWSER_RECOVERY_2026-07-29/`.

Ядовитую метку про протухший RESULT.md в `_COVER.md` поставь обязательно —
Mythos сделал это постоянным правилом шины.

## Замки

Aristotle-раны `b14fe0a5-4065-44cb-8c49-237f3cf9b595` и
`987ff124-3032-42e5-aa9f-24ceef69f62a` не трогать, `ARISTOTLE_ACTIONS_BY_CODEX=false`.
036 не исполнять (JUDGE_PENDING). Статус не повышать, глоссарий заморожен,
force-push запрещён. 038 зарезервирован под директиву Supplier A — не занимать.

## Выход

`037_muntz_r6_harvest.answer.md` в грамматике шины: первая строка `# STATUS: <код>`,
следом machine-readable блок, дальше разбор задач, ACTIONS LOG и скоринг прогнозов
диспетчера P037-1 (taint-scan даст ноль) и P037-2 (canon sync без хэш-расхождений).
