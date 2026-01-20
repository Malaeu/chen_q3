# Sandbox Tasks

Готовые задания для `/x-sandbox`. Каждый файл — полное описание задачи для агента.

## Использование

```bash
# Из chen_q3:
/x-sandbox arch_prime      # создаёт sandboxes/arch_prime/ с TASK.md

# В НОВОМ терминале:
cd sandboxes/arch_prime
claude "/x-sandbox-work"   # агент читает TASK.md и работает
```

## Доступные задачи

| Task | File | Description | Difficulty |
|------|------|-------------|------------|
| `arch_prime` | arch_prime.md | Prove arch ≥ prime via localization | 7/10 |
| `carleson` | carleson.md | Prime sampling is Carleson measure | 8/10 |
| `measure_dom` | measure_dom.md | Measure domination bound | 5/10 |

## Приоритет

1. **arch_prime** — ключевой инсайт, хорошо проработан
2. **carleson** — перспективный, но сложный
3. **measure_dom** — альтернатива, средняя сложность

## Создание новой задачи

```bash
# Скопировать шаблон
cp sandbox_tasks/arch_prime.md sandbox_tasks/new_task.md

# Отредактировать
# Запустить
/x-sandbox new_task
```

## Структура файла задачи

```markdown
# Task: name

## Goal
Что доказать (одно предложение)

## Mathematical Statement
Формальная формулировка

## Key Insight
Главная идея

## Aristotle Reference
UUID и путь к файлу

## Proof Strategy
Шаги доказательства

## Key Files
Релевантные файлы

## Success Criteria
Чеклист завершения

## Notes
Место для заметок агента
```
