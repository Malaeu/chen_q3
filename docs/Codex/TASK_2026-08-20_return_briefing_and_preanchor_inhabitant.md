# TASK 2026-08-20 — брифинг после лимита + обитатель SelectedProlatePreAnchorData

От: Linux-тело. Codex вернулся с недельного лимита — сначала догнать
изменения (раздел 1), затем два задания (разделы 2-3), по порядку.

## 1. Что изменилось за 18-20 августа (обязательное чтение, по порядку)

```
docs/routeB_bus/SUPPLIER_CONTRACT.md      контракт ВСЕХ пишущих Lean-тел:
                                          W9-леджер CLOSES/OPENS, каталог
                                          стыковок ./ask.sh, запрет имён
                                          внешних лемм по памяти, §4b
                                          append-only, §7 YAML-handoff
docs/cartographer/CHAIN_GAP_DESIGN.md     микроскоп разрывов, измерения опор
docs/NIGHT_LOOP_DESIGN.md                 ночная петля Claude↔Прошка
                                          (работает: за ночь 4 оборота)
specs_docs/session_start.sh               счётчик ОПОРЫ И КАНАТЫ: обе дороги
                                          к RH по 14; порядок несущих дыр
docs/routeB_bus/PROSHKA_QUEUE.md          REQ-дисциплина: id + STATUS
```

Первое действие: исполнить лежащий с 19.08
`docs/Codex/TASK_2026-08-19_supplier_contract_link.md` (две однострочные
правки твоей цепи: ссылка на контракт в CODEX_CONTROL.md + зеркальный
абзац мигратора в .agents-копию кондуктора).

## 2. Главное задание: обитатель SelectedProlatePreAnchorData

Ночью ядро приняло условный композер (G6N1PreAnchorLimitZeroModeAndSelectedShell.lean,
все 9 теорем стандартная тройка). Его вход №1 — пакет, обитателя нет:

```lean
-- G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:262
structure SelectedProlatePreAnchorData where
  index : ℕ → PairIndex
  pair : ℕ → ProlatePair
  mCofinal : Tendsto (fun k => (index k).m) atTop atTop
  nCofinal : Tendsto (fun k => (index k).N) atTop atTop
  lambda_eq : ∀ k, (pair k).pw.lambda = lambda_m (index k)
  eStar_memLp : ∀ k, MemLp (E_star (prolateCombination (pair k))) 2
      (dStar.restrict (I_m (index k)))
```

ЦЕЛЬ: `def/theorem`, дающие обитателя из УЖЕ доказанного. Кандидат-сырьё:
`exists_modeZero_modeFour_selectedFerrersProductionProlatePair`
(D0ModeZeroFourFerrersProductionProlatePair.lean, 18.08: даёт ProlatePair с
λ = √mProject, MemLp-полями при mProject ≥ 2, K ≥ 3 + условие hsep) и вся
Ferrers-серия 15.08. Расписание index k выбрать ЗАРАНЕЕ и записать
(precommit, C09) — например k ↦ (m_k, N_k) с явной монотонностью; НЕ
подгонять после. Кофинальности mCofinal/nCofinal при явном расписании —
арифметика.

ЛЕДЖЕР (обязателен в SOURCE RECORD):
  CLOSES: [SELECTED_PROLATE_PREANCHOR_DATA_INHABITANT]
  OPENS:  [] — если появляется новый вход, источник НЕ писать, доложить

ГЕЙТ: lake env lean + scripts/q3_check.sh (из корня; исполняемый);
профиль на КАЖДУЮ печатаемую декларацию [propext, Classical.choice,
Quot.sound]; sorryAx = не доказано. Квитанции blob+sha256.

ЗАПРЕЩЕНО: трогать G6N1-файл (зелёный, append-only-логика на источники);
Classical.choose без теоремы существования; произвольный удобный
ProlatePair вместо selected Ferrers-свидетелей (прецедент-запрет в
PROSHKA_KILL_N0...md); правки глобальных правил.

## 3. После зелёного №2 — стоп и доклад

Обитателя №2 (CCMLemma73PreAnchorPort — бумажная аналитика Lemma 7.3)
НЕ начинать: его этажи сейчас раскладывает судья. Порядок жёсткий,
записан в счётчике.

## Валидация задания

- оба файла из TASK_2026-08-19 исправлены, diff абзацев кондуктора пуст;
- новый Lean-файл зелёный полным гейтом;
- SOURCE RECORD с леджером и квитанциями лежит рядом одним коммитом;
- per-action OK владельца перед коммитом/пушем — как всегда для твоей цепи.
