# SESSION_PROTOKOLL 2026-09-21 — Linux Claude (наблюдатель)

## Kontext
Понедельник после выходных владельца с Прошкой (коммиты `[Proshka]` 18–20.09, MAC `d9fb105c` M13 transfer).
Grok работал параллельно в этом же дереве (`systemd-inhibit --who=grok`), пять коммитов утром.
Ветка `rh_clean`, старт с `a5298835`, конец на `2c0f3cc5` (мой) — origin синхронен.

## Ausgangslage
- Прошка `70da2617` (20.09): точный генератор Ferrers→Mellin; равенство кэша точному источнику опровергнуто
  структурно (фаза, мнимые части 1e−35…1e−110); положительность аналитической семьи — открыто.
- MAC audit `CCM_DIRECTIONAL_RATE_AUDIT_2026-09-20.md`: кэшевый пролатный источник коэрцитивен при m=13, N≥90.
- Grok `3305959a`: «forcing N-extension убит при m=2, η растёт с N».

## Aufgabe
Подтянуть репо, разобрать, что делает Grok, проверить его число. Потом: правило для Grok «коммит только после проверки» и два рычага (permission, обрезка CLAUDE.md).

## Erledigt
1. Продлил зонд Grok с N=3 до N=24 при его параметрах — η плато 2.34; поймал два дефекта скрипта: `even_chi` схлопывает моды при c²=13 (оба корня 48.6737), `DPS=40` зашит. Патч с регрессией бит в бит на m=2 — Grok положил в дерево `9cfa268d`.
2. Ошибочно объявил прогон m=13 шумом → перезапуск dps 240 дал те же числа → отозвал.
3. Ошибочно решил, что опровержение Прошки означает численную близость → проверил, отозвал.
4. Сверил строку Grok с публичной сборкой Прошки `zero_mass_packet_row` — совпадение 2.5e−17 (сборка верна).
5. Нашёл корень всего дня: зонд строит пакет при `c² = m` (`probe_n_extension.py:363`), конвейер кэша при `c = 2π·LAMBDA_SQ` (`true_precision_packet_gate_v1.py:171`), Прошка в тексте `c = 2πm` (VERDICT 70da2617 строка 203). Поймано косинусом 0.30 между строкой и кэшем.
6. При правильной полосе: m=13 N=13 — |cos| = 1−5.3e−63, a = 4.22609145762e−16 у точного источника и у кэша; m=2 c=4π — η строго падает, β(q)>0, Δ−2e>0 при N=1..12 → FALLS.
7. Коммит `2c0f3cc5`: полоса в зонде исправлена, `result.json` перегенерирован, `bandwidth_test.py` и `m2_forcing_rerun.py` в папке зонда, CORRECTION в VERDICT.md, записи в Progress_Log и CHAT_DIGESTS. Отозваны выводы `3305959a` и `f1bce92b` (Grok коммитил мои непроверенные числа из чата).
8. Владелец остановил Grok. По его слову: `~/.grok/AGENTS.md` (7 пунктов «коммит после проверки» + выжимка правил 1–20, 6 439 знаков), `always-approve` выключен в `~/.grok/config.toml` (бэкап `.bak-2026-09-21`), обёртка `grok()` в `~/.bash_functions` (`acceptEdits`, allow-список, `git commit/push` спрашивают, force-push/reset --hard/rm -rf запрещены).

## Geprüft
- Матрица `build_K` Grok = матрица MAC: λ₀ = 7.92103597375e−31 против 7.921e−31 (dps 40/60/240 одинаково).
- Кэшевая строка в `build_K`: a = 4.22609145762e−16 = MAC 4.226e−16; при N=90 ‖r‖ = 1.8368725e−30 = MAC 1.837e−30.
- Обёртка `grok()` подхватывается в интерактивной оболочке (`~/.bash_functions:3` — guard на `$-`), бинарь 1.0.40 стартует через неё и голым.
- НЕ проверено: поведение Grok с новыми правилами вживую (остановлен владельцем).

## Versendet
Ничего наружу. Push в origin: `2c0f3cc5`.

## Offen — nächste Schritte
- Узел G4 (Grok): вторая половина «строка = c_n от prolateCombination» снова путь к знаку, не только тождество. `c_n` в `docs/routeB_bus/D0KTrialStage3.lean:81` абстрактен, кэш не импортирует.
- FALLS-ветка при m=2 живая → `FiniteGroundTransformToCCMTrialLocallyUniform` есть смысл трогать.
- Расхождения `session_start.sh` (exit 1) не чинены: `SEMANTIC_INDEX_CORPUS_STALE` → `python3 orchestrator/spine.py --refresh --reason semantic-index-refresh`; мигратор 4 строки M3 → `workflow_runtime.py close-phase --repair`.
- Четыре запроса Прошке не отправлены с 05–13.09: BROWNIANJOINT, DISTANCE, HODGE, PROVE.
- Jev-пилот: ключ и «да» владельца на одну карточку (`jev_lemma_ranker_one_card_2026-09-21/PILOT.md`).
- Сектора: MAC меряет чётный блок dim N+1, `build_K` полный 2N+1 — e/Δ между конвейерами не сравнивать без проекции.

## Wichtige Fakten
- Полоса пролатного пакета лестницы: **c = 2πm**. Никогда c² = m.
- Плантаж источника перед любым вердиктом: |⟨кэш, строка⟩| при m=13 N=13 → 1, a → 4.22609145762e−16.
- Прошка не проглядел ничего; его структурное опровержение точного равенства стоит.
- Grok читает `AGENTS.md`/`CLAUDE.md` с обрезкой 10 000 знаков; `CLAUDE.md` = 31 268 → правила 1–20 не доходят.
- Пересчёт с чекпойнта: PROVED +0, KILL +16, ANSWERED +59.

## Dateien (absolute Pfade)
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/ccm_n_extension_probe_2026-09-21/VERDICT.md
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/ccm_n_extension_probe_2026-09-21/probe_n_extension.py
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/ccm_n_extension_probe_2026-09-21/bandwidth_test.py
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/ccm_n_extension_probe_2026-09-21/m2_forcing_rerun.py
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/Progress_Log.md (запись CORRECTION 2026-09-21)
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/CHAT_DIGESTS.md (запись КОРРЕКЦИЯ 2026-09-21)
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/true_precision_packet_gate_v1.py:171
- /home/chirurgie/.grok/AGENTS.md · /home/chirurgie/.grok/config.toml (+ .bak-2026-09-21) · /home/chirurgie/.bash_functions (функция grok)
- /home/chirurgie/.claude/projects/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/memory/ladder-bandwidth-c-2pi-m.md

---

# Nachtrag (вторая половина дня) — правила Grok, чистка диска

## Erledigt (продолжение)
9. **Правила для Grok** (по слову владельца «делаем оба»): `/home/chirurgie/.grok/AGENTS.md` — 7 пунктов «коммит только после проверки» (плантаж источника |⟨кэш,строка⟩|≈1 при m=13 N=13, параметры с локаторами, один токен вердикта, журнал = развилки, не коммитить за другое тело) + выжимка правил 1–20 из проектного CLAUDE.md (Grok видит только первые 10 000 знаков файла из 31 268). 6 439 знаков.
10. `always-approve` выключен в `/home/chirurgie/.grok/config.toml` (бэкап `config.toml.bak-2026-09-21`); обёртка `grok()` в `/home/chirurgie/.bash_functions`: `--permission-mode acceptEdits`, allow-список рутины, `git commit`/`git push` спрашивают, `push --force`/`reset --hard`/`rm -rf` запрещены. Проверено в интерактивной оболочке; вживую с Grok не запускалось.
11. **Чистка NVMe `/` 82 % → 51 %** (+137 ГБ). Отчёт Grok по диску: цифры верны, вывод «клоны — копии» ложный. Перед сносом спасено: 63 коммита Codex (TEAM/recovery/publication/alias-hunt, 11–16.09) из 8 клонов + 6 WIP-деревьев → `refs/heads/rescue/<клон>/<ветка>` (23 ветки, только HDD, на origin не пушены) + 2 патча в `.git/rescue/`. Проверка: 0 пропавших sha, 0 грязных, fsck чист. Снесены: `~/.cache/q3-*` (683 каталога, 90 ГБ), `~/.codex/worktrees` (18 ГБ), два лога (владелец, sudo), Lean v4.27.0-rc1/4.24/4.22 (default → v4.26.0), `uv cache prune` 3,5 ГБ, CUDA 12.6 (56 dpkg-пакетов, владелец; 12.9 работает, nvcc 12.9.86), flatpak SpeechNote-nvidia-аддон без приложения, две TrOCR-модели.
12. Grok ошибся ещё дважды в отчёте по диску: «Lean только v4.28 актуальна» (в деле 4.26 chen_q3, 4.27 comparator, 4.28 comparator-4.28) и счёт клонов (17 больших + 667 фикстур).

## Geprüft (продолжение)
- Chrome 8 ГБ = две копии `OptGuideOnDeviceModel` (Gemini Nano); используется только фичей 15 = `MODEL_EXECUTION_FEATURE_SCAM_DETECTION` (Chromium `model_execution.proto`), сегодня 06:01 и 07:44. Владелец: оставить.
- huggingface 5,5 ГБ — всё рабочее: whisper large-v3 + small = **voice-shim** (`~/.claude/bin/voice-shim/server.py`, 17.06), surya = marker-pdf, GOT-OCR. Мою ошибочную атрибуцию whisper → markitdown владелец поправил; записано в память.
- ollama: моделей ноль, 2,1 ГБ — его библиотеки.

## Offen (дополнение)
- Rescue-ветки только на HDD; решение владельца — не пушить; через месяц без спроса можно удалить.
- Логи `/var/log` растут до ГБ — источник спама (syslog 2,6 ГБ за неделю августа) не искали.
- flatpak GL 24.08 (0,9 ГБ) держится чем-то — не трогали.

## Dateien (дополнение)
- /home/chirurgie/.grok/AGENTS.md · /home/chirurgie/.grok/config.toml(.bak-2026-09-21) · /home/chirurgie/.bash_functions (grok)
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/.git/rescue/ (2 патча) · `git for-each-ref refs/heads/rescue`
- /home/chirurgie/.claude/projects/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/memory/rescue-branches-from-cache-clones.md
