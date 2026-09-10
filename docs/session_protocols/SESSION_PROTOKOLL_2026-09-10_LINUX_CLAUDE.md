# SESSION_PROTOKOLL 2026-09-10 — Linux-Claude (наблюдатель, второе тело)

## Kontext
Утро после перезагрузки рабочей станции. Сессия инфраструктурная: связь, голос, подсказки, Remote Control. Математика не трогалась.

## Ausgangslage
- Remote Control показывал «disconnected»: локальная сессия умерла при перезагрузке.
- `/voice` не распознавал русский: три попытки 08:21–08:22 дали галлюцинации Whisper на немецком и английском.
- `claude remote-control` отказывался стартовать: `ANTHROPIC_BASE_URL` указывает на локальный прокси подсказок `127.0.0.1:8787` (sugg-proxy, 09.09), а бинарник требует хост ровно `api.anthropic.com`.

## Aufgabe
1. Восстановить Remote Control. 2. Починить голос. 3. Сделать так, чтобы прокси подсказок и Remote Control работали одновременно, при обычном запуске с `--dangerously-skip-permissions`.

## Erledigt
- **Голос.** Сервис `voice-shim.service` (faster-whisper large-v3, cuda, `ws://127.0.0.1:8765`) был здоров с 08:02. Причина: встроенный микрофон ALC1220 отдавал тишину (rms 7e-5). Переключение `amixer -c 0 sset 'Input Source'` Front Mic → Rear Mic вернуло сигнал. Проверка: 08:27:38 распознана длинная русская фраза `[ru]` без ошибок.
- **Патч P4** в `/home/chirurgie/.claude/bin/patch-claude-binary.sh`: проверка хоста `return["api.anthropic.com"].includes(t)` → `return/api.anthropic.com|8787$/.test(t)` (39 → 39 байт); байткод модуля `chunk-5jacf3nm.js` (#82, 27 КБ) отключён по схеме P3. Применён к 2.1.266, бинарник запускается, размер не изменился. Резервная копия патчера: `patch-claude-binary.sh.bak-2026-09-10`.
- **Функция `claude()`** в `/home/chirurgie/.bash_aliases`: CLI запускается с `env -u ANTHROPIC_API_KEY` (второй гейт Remote Control: отказ при API-ключе; `.bashrc` подгружает `~/.api_keys`). Резервная копия `~/.bash_aliases.bak-2026-09-10`.
- **Док** `/home/chirurgie/.claude/docs/claude_code_install.md`: строка про P4 (по слову владельца, review skipped on owner's word).
- **Память:** `voice-mic-dead-after-reboot.md` (новая), `claude-2-1-259-off-stable.md` (переписана: явная версия + защита от даунгрейда).

## Geprüft
- `claude remote-control --help` через функцию в интерактивной оболочке печатает справку (оба гейта пройдены). Ловушка: `timeout claude …` обходит функцию и даёт ложный отказ.
- Обычная сессия через прокси: `claude -p` ответил, журнал прокси показывает `tmpl=cyr-v5`, подсказки кириллицей.
- `claude auth status` без ключа: `subscriptionType=max`; с ключом: `apiKeySource=ANTHROPIC_API_KEY`, `subscriptionType=null`. Консоль Anthropic: расход 0,67 $ за месяц, 143K токенов за 7 дней → сессии CLI по ключу не ходили.
- Владелец перезапустил сессию `claude --resume <id> --remote-control --dangerously-skip-permissions`: Remote Control поднят, подсказки работают (подтверждено владельцем и скриншотом TUI 2.1.266).

## Versendet
Ничего наружу.

## Offen — nächste Schritte
- `claude_code_install.md`: устаревшие строки («running 2.1.169», fallback `2.1.112`) — предложены замены, правка только со слова владельца.
- `~/.claude/CLAUDE.md` § Claude Code Install: фраза, что явная версия выше `stable` допустима и `update` вниз не ходит — со слова владельца.
- Проект: BRIDGE у Прошки (REQ-2026-09-09-BRIDGE, новый чат доставлен по коммиту fd72b51b), вахта. Следующий ход: `./specs_docs/session_start.sh` и проверка ответа.

## Wichtige Fakten
- Версии: установлено 2.1.266 (явно), latest 2.1.267, stable 2.1.236. Баннер «Updated to latest» в TUI — просто текст после установки.
- Диагностика голоса по порядку: `journalctl --user -u voice-shim.service` → `arecord … 2 с` + rms → `amixer` Input Source.
- Причина «мёртвого» микрофона после перезагрузки не доказана, только лечение.

## Dateien
- /home/chirurgie/.claude/bin/patch-claude-binary.sh
- /home/chirurgie/.claude/bin/sugg-proxy.py
- /home/chirurgie/.claude/bin/voice-shim/server.py
- /home/chirurgie/.bash_aliases
- /home/chirurgie/.claude/docs/claude_code_install.md
- /home/chirurgie/.claude/projects/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/memory/voice-mic-dead-after-reboot.md
- /home/chirurgie/.claude/projects/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/memory/claude-2-1-259-off-stable.md
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/session_protocols/SESSION_PROTOKOLL_2026-09-10_LINUX_CLAUDE.md
