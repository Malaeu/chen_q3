# Q3 — где мы и что дальше

Единственная точка продолжения на любой машине: `git pull` → прочитать этот файл → работать.
Обновлять в каждом рабочем коммите (заменой, не дописыванием). Максимум ~40 строк.
Режим: простой (owner instruction 2026-09-25, control §1 precedence).

Updated: 2026-09-25 · by: Claude Code (owner order) · HEAD at update: c626f00d

## Цель
Проверяемое доказательство RH в этом репо (Route B, Goal058). `CHALLENGER_NOT_RH`, `PX_RH_CLAIM: NOT_MADE`.

## Последний доказанный результат
- 2026-09-22: Lean-кандидаты Ferrers/prolate, `q3_check ok`, аксиомы только propext/Classical.choice/Quot.sound:
  `docs/session_protocols/{ferrers_endpoint_flux,ferrers_form_approx,fourier_overlap,quasimode_correction}_candidate_20260922.lean`
  (последний: `10c20237`, `selected_zero_four_form_approximation`). В `q3.lean.aristotle` ещё НЕ интегрированы.
- Paired-window Mellin identity, Rminus crosswalk, Euler identity: PAPER-level
  (`docs/Codex/BRIEF_2026-09-22_FOKAS_PAIRED_WINDOW.md`, `docs/Codex/REPORT_2026-09-22_FOKAS_RMINUS_CROSSWALK.md`).

## Следующий шаг
1. Интегрировать 4 кандидата 22.09 в `q3.lean.aristotle/Q3/Proofs/RouteB/`, `scripts/q3_check.sh <file>`, `lake build`, commit, push.
   (В рабочем дереве уже лежат неотслеженные `Q3*Candidate20260922.lean` от Codex — проверить, достроить, закоммитить.)
2. Fokas rank-2 joint green (TRY_GOAL058_FOKAS_JOINT_GREEN_RANK2): тождество даёт точную формулу остатка;
   НЕ доказаны равномерная оценка убывания дефекта и sector floors. Граничный контроль t−V = 3√2/4 воспроизведён.

## Прошка
- Активная фаза: `PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923`, чат `6aafb38a-a7a4-83eb-9940-84a574eae168`.
- Последний запрос: `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_FOKAS_MATRIX_DEFECT_20260923.txt` — ответ получен
  («убывание остатка не доказано / floors не доказаны»). Новый запрос — только по реальному глобальному блокеру.

## Не повторять
- Owner recovery, старые launch/ingest/publication (RESUME `Do not repeat`) — не переигрывать.
- Не подменять оценки selected Ferrers packet явными гауссовыми пределами; не дифференцировать C0-сходимость.
- Не отправлять повторно уже отправленные запросы Прошке.

## Жёсткие линии (не обсуждаются)
Без `sorry`; аксиомы только три; `PX_RH_CLAIM` не делать; перед PROVED — независимый review;
одновременно работает одна машина (какая — решает владелец).
