# ГОЛ 014 — PROSHKA_GITHUB_CHANNEL (канал Прошки через chen_q3)

От: Mythos, по указанию Ылши. Статус: CHALLENGER / NOT_RH. BUS_010_VOID соблюдать.
Цель: Прошка читает материалы САМ через свой GitHub-коннектор; ручные zip'ы для
исходящих уходят в прошлое.

Репо-обменник: /Users/emalam/GitHub/chen_q3, папка docs/.
⚠️ В docs/ лежат личные архивы Ылши — НИЧЕГО за пределами docs/routeB_bus/
не трогать, не переименовывать, не чистить.

## Задача

1. Создать docs/routeB_bus/ и наполнить зеркалом Прошка-релевантных файлов шины
   (плоско, один уровень):
   — все NNN_*.goal.md и NNN_*.answer.md из routeB_lamport_rh_closure;
   — все пробы (*_PROBE.md, *_PROBE.csv, *_REPORT_*.md);
   — proshka/*.md (его же вердикты — для самоссылок);
   — действующие контракты Aristotle (v2_REPAIRED и последующие);
   — ключевые Lean: EStarWindowedMellinCrosswalk.lean, D0KTrialStage1.lean,
     D0KTrialStage2.lean, D0KTrialStage3.lean, D0AnchorFloor.lean,
     MontelNormalFamilies.lean, D0CanonicalApproximation.lean,
     CanonicalRHRouteSkeleton.lean.

2. Сгенерировать docs/routeB_bus/MANIFEST.md: одна строка описания + SHA-256
   на каждый файл. MANIFEST пересобирается при каждой синхронизации.

3. git: add → commit (осмысленное сообщение) → ОБЯЗАТЕЛЬНО push origin
   <текущий branch>. Один branch, БЕЗ новых worktrees, без веток,
   без force-push. Если в репо уже есть мусорные worktrees/ветки от прошлых
   работ — перечислить в отчёте (НЕ удалять без отдельной команды).

4. Постоянное правило (в handoff-дисциплину): последним шагом каждого
   закрытого гола — обновить зеркало + MANIFEST + push.

## Отчёт (014_proshka_github_channel.answer.md)

URL репо (git remote -v), branch, видимость (public/private и как проверил),
хэш коммита, число файлов в зеркале, полный путь к MANIFEST.
Коды: PROSHKA_CHANNEL_LIVE / GIT_PUSH_AUTH_FAIL / REPO_REMOTE_MISSING.
STATE не трогать.
