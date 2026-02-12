# Шаблон задачи для агента (`x-insider`)

## Короткий промпт

Сделай выжимку по последним 5-10 сообщениям нашего чата и запиши ее в `docs/insides_knowledge_base_personal.md`.
Включи: решения, риски, блокеры, важные команды, следующие шаги.
Формат: 4-10 коротких пунктов.

## Строгий промпт

Сделай инсайд-выжимку по последним 5-10 сообщениям чата.

Ограничения:
- Писать только факты из недавнего диалога.
- Не добавлять длинные цитаты логов.
- Отдельно пометить гипотезы как "Гипотеза:".

Структура выжимки:
- Решения
- Риски
- Блокеры
- Команды/пути
- Следующие шаги

После формирования выжимки запиши ее в `docs/insides_knowledge_base_personal.md` через скрипт `skills/x-insider/scripts/append_chat_insights.py`.

## Режим с экспортом чата

Если у тебя есть файл экспорта, используй:

```bash
python3 skills/x-insider/scripts/append_chat_insights.py \
  --from-chat-file session_exports/chat_latest.md \
  --messages-window 10 \
  --max-insights 8 \
  --title "Выжимка из экспорта"
```

## Slash-стиль (`/x-export`) как команда

Интерпретация:
- `/x-export` -> выполнить `./scripts/x-export` (вся последняя сессия)
- `/x-export 10` -> выполнить `./scripts/x-export 10` (последние 10 сообщений)
- `/x-export 5` -> выполнить `./scripts/x-export 5`

## Slash-стиль (`/x-insider`) как one-shot

Интерпретация:
- `/x-insider` -> выполнить `./scripts/x-insider` (вся последняя сессия)
- `/x-insider 10` -> выполнить `./scripts/x-insider 10`
- `/x-insider 5` -> выполнить `./scripts/x-insider 5`
