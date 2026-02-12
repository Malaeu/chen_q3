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
