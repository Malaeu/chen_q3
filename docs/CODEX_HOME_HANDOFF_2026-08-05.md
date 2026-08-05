# OWNER → CODEX (Mac) HANDOFF — 2026-08-05

Памятка для владельца: что закинуть Codex'у дома, в каком порядке, с какими правилами.
Открой этот файл на Mac, скопируй «СТАРТОВЫЙ ПРОМПТ» ниже в Codex — дальше он работает по этому файлу
и по двум вердиктам Прошки, которые уже лежат в репо.

---

## OWNER

- Владелец: Ылша (Eugen Malamutmann).
- Проект: Q3 Riemann-Hypothese Lean-Formalisierung, Route B (**CHALLENGER / NOT_RH**, Bus 010 VOID).
- Repo: `Malaeu/chen_q3`, branch `rh_clean`.
- Роль Codex дома: **executor body (Mac)** — та же роль, что Claude Code на Linux (одна роль, два тела).

## CONTEXT (что произошло, коротко)

Прошка дала ДВА архитектурных вердикта (оба ратифицированы, оба уже в репо):
1. `docs/routeB_bus/proshka/PROSHKA_VERDICT_UNIFIED_MEMORY_CONTOUR_2026-08-05.md` — единый one-Spine
   memory-контур.
2. `docs/routeB_bus/proshka/PROSHKA_VERDICT_BEHAVIOR_CONTROL_CONTOUR_2026-08-05.md` — **второй, AMENDS
   первый**: batch-per-PHASE, авто-звонок Прошке на goal-close УБИТ, P9 `CODEX_CONTROL.md` = единое ядро
   поведения executor'а, `EXECUTOR_ARSENAL_ADDENDUM` убит как active control, закон
   BEHAVIOR_CONTROL_SYMMETRY. **Второй вердикт имеет приоритет там, где расходится с первым.**

Реализация архитектуры (P9 и далее) была отложена, потому что 5 фактов про **Mac-тело Codex** мы
СОЗНАТЕЛЬНО не держим в GitHub — их знает только Codex дома. Их надо сначала записать из ФАКТА, иначе
`CODEX_CONTROL.md` будет написан из догадки. Эти 5 пробелов зафиксированы как GAPS в
`docs/CODEX_CYCLE_RECONSTRUCTION_2026-08-05.md` §5.

Этот файл-хендофф = **owner relay** (вердикты требуют `OWNER_RELAY_REQUIRED`; закидывание этого промпта
Codex'у и есть relay). Но `REPO_WRITE_AUTHORIZED_BEFORE_RELAY: false` остаётся — каждый commit/push
Codex показывает владельцу payload и ждёт «ок» (per-action OK, ADVISORY v1).

---

## ЗАДАНИЕ 1 (СНАЧАЛА) — заполнить 5 Mac-only GAPS из факта

Codex читает своё РЕАЛЬНОЕ Mac-окружение и дописывает `docs/CODEX_CYCLE_RECONSTRUCTION_2026-08-05.md` §5
фактами (не догадками). Пять пробелов:

1. **Полный Mac `~/.codex/config.toml`**: model / effort / approval / sandbox / projects / plugins /
   **notify** (есть ли на Mac native-notification hook, которого нет на Linux); присутствует ли
   `chrome-devtools` MCP или его заменяет встроенный авторизованный браузер Codex.app.
2. **Desktop-app driving stack**: `osascript` / `cliclick` / Ghostty Accessibility; Codex.app +
   Claude Desktop как GUI, clipboard-paste — как Mac реально «водит» головы (Fable/Proshka).
3. **Auth pathway**: Mac embedded logged-in session vs Linux token — для Aristotle + ChatGPT.
4. **Standing-goal / session-bootstrap contour** как Codex реально его гоняет (тот 22h off-git артефакт) —
   авторитетная версия, а не снятый владельцем снапшот.
5. **Точный chat open/continue trigger**, который Codex использует СЕГОДНЯ (чтобы `CODEX_CONTROL`
   сначала кодифицировал реальность, а потом исправил её до one-living-chat-per-phase).

Выход Задания 1: правка §5 + отдельный маленький безопасный коммит `[MacOS][rh_clean][Docs] Fill Mac-only
GAPS in Codex cycle reconstruction`. Никакой математики, никаких Lean-файлов. Показать владельцу → «ок» → push.

## ЗАДАНИЕ 2 (ПОТОМ) — материализовать P9 по CODEX DIRECTIVE

Только после Задания 1 Codex исполняет CODEX DIRECTIVE из второго вердикта
(`PROSHKA_VERDICT_BEHAVIOR_CONTROL_CONTOUR_2026-08-05.md`, секция `## CODEX DIRECTIVE`). Кратко:
- CREATE: `docs/CODEX_CONTROL.md`, `orchestrator/state/CHANNEL_RUNTIME.json`.
- MODIFY (→ thin pointers / superseded): `AGENTS.md`, `CLAUDE.md`, `q3.lean.aristotle/CLAUDE.md`,
  `docs/EXECUTOR_ARSENAL_ADDENDUM_2026-08-04.md`, `orchestrator/KNOWLEDGE_SPINE.md`,
  `orchestrator/spine.py`, `orchestrator/packet.py`.
- Обязательные секции CODEX_CONTROL, phase_key (6 полей), owner-boundaries, chat-rules, plants,
  validation, failure-codes — всё перечислено в директиве. Прогнать MANDATORY_PLANTS и VALIDATION.
- **Порядок всего контура:** P1a → P1b → **P9+P6+P8** → P2a → P2 → P4 → P5 → P3 → P7.
  (P9 идёт сразу после P1b.)

Каждый шаг — показать владельцу payload → «ок» → commit/push.

---

## RULES (жёсткие — из CODEX DIRECTIVE, не менять)

- **Порядок дома: Задание 1 (GAPS) → Задание 2 (P9).** Не писать `CODEX_CONTROL.md` из догадки.
- **Per-action OK на каждый commit/push/upload** — показать точный payload владельцу перед действием.
- **НЕ трогать Lean theorem/proof source** в этой транзакции (только docs/orchestrator/state).
- **НЕ создавать второй executor control-файл**; ровно один active control на роль
  (BEHAVIOR_CONTROL_SYMMETRY). Addendum → `SUPERSEDED_BY_CODEX_CONTROL`, а не второй активный.
- **НЕ оставлять активную политику** в `AGENTS.md` / обоих `CLAUDE.md` — только тонкие указатели.
- **Прошке звонить только на owner boundary** (`MINT` / `PROMOTION` / `FRONT_CHANGE` / `FATAL`); на
  обычный goal-close — ноль звонков. Одна живая Прошка-чат-сессия на фазу; фаза = 6-полевой phase_key.
- **НЕ хранить в репо секреты/токены**, абсолютные машинные пути, browser session tokens, текущую
  теорему/route-state внутри `CODEX_CONTROL.md`.
- **Route остаётся CHALLENGER / NOT_RH.** Bus 010 VOID. Никакого promotion. Никакой Aristotle-submission.
  RH НЕ заявляется.
- Commit format на Mac: `[MacOS][rh_clean][...] ...`. После коммита — `git pull --rebase` → `git push`.
- Disk-wins: работу выбирает физическое состояние на диске, не вставленный текст.

## ЧЕК ПОСЛЕ ЗАВЕРШЕНИЯ (что Codex должен доложить)

- §5 GAPS заполнены фактом; отдельный коммит запушен.
- (P9) точный source pin + список тронутых файлов; инвентарь секций `CODEX_CONTROL.md`; before/after
  где лежит нормативная политика; доказательство, что AGENTS/CLAUDE — тонкие; реестр каналов; phase-key
  comparator; судьбы всех plants; sample runtime-ledger; `ordinary_goal_close_proshka_call_count == 0`;
  подтверждение «ноль изменений Lean source»; `ROUTE CHALLENGER_NOT_RH`; `BUS_010 VOID`;
  `ARISTOTLE_SUBMISSION NONE`.

---

## СТАРТОВЫЙ ПРОМПТ (скопировать в Codex дома)

Ты executor-тело (Mac) проекта Q3 Route B. Открой и прочитай полностью:
docs/CODEX_HOME_HANDOFF_2026-08-05.md,
docs/routeB_bus/proshka/PROSHKA_VERDICT_UNIFIED_MEMORY_CONTOUR_2026-08-05.md,
docs/routeB_bus/proshka/PROSHKA_VERDICT_BEHAVIOR_CONTROL_CONTOUR_2026-08-05.md,
docs/CODEX_CYCLE_RECONSTRUCTION_2026-08-05.md.
Второй вердикт имеет приоритет над первым при расхождении. Route остаётся CHALLENGER / NOT_RH, Bus 010
VOID, никакого promotion и Aristotle-submission, RH не заявляется. Lean source не трогать.
Сначала выполни ЗАДАНИЕ 1: заполни пять Mac-only GAPS в CODEX_CYCLE_RECONSTRUCTION §5 из своего реального
Mac-окружения (config.toml, desktop-driving stack, auth pathway, standing-goal contour, точный
chat-trigger). Покажи мне правку и дождись «ок» перед коммитом. Не начинай ЗАДАНИЕ 2 (P9 / CODEX_CONTROL),
пока Задание 1 не запушено и я не сказал «переходи к P9». Каждый commit/push — сперва покажи payload и жди
моего «ок».

---

*Файлы-ссылки (repo-relative, работают на Mac и Linux):*
- `docs/CODEX_CYCLE_RECONSTRUCTION_2026-08-05.md` (§5 = 5 GAPS)
- `docs/routeB_bus/proshka/PROSHKA_VERDICT_BEHAVIOR_CONTROL_CONTOUR_2026-08-05.md` (CODEX DIRECTIVE)
- `docs/routeB_bus/proshka/PROSHKA_VERDICT_UNIFIED_MEMORY_CONTOUR_2026-08-05.md`
- `docs/SYSTEM_SPEC_2026-08-05.md`, `docs/MEMORY_ARCHITECTURE_AUDIT_2026-08-05.md`
- `SESSION_PROTOKOLL_2026-08-05.md`
