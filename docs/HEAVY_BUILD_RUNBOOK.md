# Heavy Build Runbook

Prerequisite: set `Q3_REPO` to the checkout to operate on when the current directory is
outside that checkout. If it is unset, every command below resolves the repository from
the current directory with `git rev-parse --show-toplevel` and fails closed outside a Q3
worktree.

## 1) Безопасный мониторинг в другом терминале

```bash
cd "$(git -C "${Q3_REPO:-$PWD}" rev-parse --show-toplevel)"
./scripts/primepow_status.sh
LOG=$(ls -1t tmp/primepow_gt10000_logs/build_*.log | head -1)
tail -f "$LOG"
```

Это только чтение состояния. Одновременно второй build не запускать.

## 2) Ночной перезапуск после timeout/fail (больший таймаут на шард)

```bash
cd "$(git -C "${Q3_REPO:-$PWD}" rev-parse --show-toplevel)"
systemctl --user daemon-reload
systemctl --user set-property --runtime codex-heavy.slice MemoryHigh=24G MemoryMax=32G CPUWeight=80 ManagedOOMPreference=avoid
./scripts/run_heavy.sh ./scripts/build_primepow_gt10000_sequential.sh --timeout 18000
```

## 3) Быстрый чек, что запущен только один build

```bash
pgrep -af 'build_primepow_gt10000_sequential.sh|lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000'
```

Если строк больше одной группы одного запуска, останови дубли и оставь один процесс.

## 4) Правильный запуск в tmux (рекомендуется)

Запуск:

```bash
tmux new -s primepow
cd "$(git -C "${Q3_REPO:-$PWD}" rev-parse --show-toplevel)"
systemctl --user daemon-reload
./scripts/run_heavy.sh ./scripts/build_primepow_gt10000_sequential.sh --timeout 18000
```

Отцепиться от tmux (процесс продолжит работать):

```bash
Ctrl-b d
```

Вернуться в сессию:

```bash
tmux attach -t primepow
```

Если сессия уже есть:

```bash
tmux ls
tmux attach -t primepow
```

## 5) Мониторинг из любого терминала

```bash
cd "$(git -C "${Q3_REPO:-$PWD}" rev-parse --show-toplevel)"
./scripts/primepow_status.sh
LOG=$(ls -1t tmp/primepow_gt10000_logs/build_*.log | head -1)
tail -f "$LOG"
```

Оценка прогресса/ETA/среднего времени на batch (шард):

```bash
cd "$(git -C "${Q3_REPO:-$PWD}" rev-parse --show-toplevel)"
watch -n 30 './scripts/primepow_status.sh'
```

## 6) Важно для уже запущенного процесса

- Если текущий build стартовал в обычном терминале (не в tmux), не закрывай это окно до завершения.
- Перенос такого процесса в tmux "на лету" без риска не поддерживается в этом окружении.
