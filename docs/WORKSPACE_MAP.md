# Workspace Map (Q3 + Paper)

## Что где лежит
- Формализация Q3 (Lean): `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean`
- Paper A (LaTeX): `/mnt/hdd01/Soft/GitHub/rh_paper_a`

## Какие это репозитории
- Q3 repo:
  - `origin`: `https://github.com/Malaeu/chen_q3.git`
  - рабочая ветка сейчас: `rh_clean`
- Paper repo:
  - `origin`: `https://github.com/Malaeu/Paper_RH.git`
  - рабочая ветка сейчас: `main`

## Текущее правило (без submodule)
- Держим **две отдельные репы рядом**.
- История формализации и история paper разделены.
- Это проще и безопаснее, пока workflow не стабилизирован.

## Быстрая проверка “где я”
```bash
pwd
git rev-parse --show-toplevel
git rev-parse --abbrev-ref HEAD
git remote -v | head -n 2
```

## Базовый цикл: Q3 (Lean)
```bash
cd /mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean
git status --short --branch
# проверки/сборка
git add <нужные_файлы>
git commit -m "[Linux][rh_clean] <msg>"
git pull --rebase origin rh_clean
git push origin rh_clean
```

## Базовый цикл: Paper A (LaTeX)
```bash
cd /mnt/hdd01/Soft/GitHub/rh_paper_a
git status --short --branch
# сборка: pdflatex/bibtex
git add <только_исходники>
git commit -m "[Linux][main] <msg>"
git pull --rebase origin main
git push origin main
```

## Важно, чтобы не запутаться
- Перед `git add` всегда смотри `pwd` и `git rev-parse --show-toplevel`.
- Не делай `git add -A`, если не проверил, в какой ты репе.
- Для paper обычно не коммитим служебные артефакты (`*.aux`, `*.log`, `*.out`, `*.blg`), если это не требуется специально.

## Мини-чеклист перед push
```bash
git status --short --branch
git log --oneline -n 3
```

## Страховка (sync 2026-02-12)
- Ключевая фраза для поиска в будущих сессиях: **`у нас была страховка`**
- Что было создано перед синхронизацией:
  - backup-ветка: `backup/pre_sync_20260212_140841`
  - stash: `stash@{0}` с сообщением `pre-sync-20260212_140841`
- Что произошло:
  - локальная ветка `rh_clean` синхронизирована с `origin/rh_clean` (ahead/behind = `0/0`);
  - stash был применён обратно после rebase.

### Как восстановить из backup-ветки
```bash
cd /mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean
git switch backup/pre_sync_20260212_140841
```

### Как поднять содержимое stash (если не удалён)
```bash
cd /mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean
git stash list
git stash apply stash@{0}
```
