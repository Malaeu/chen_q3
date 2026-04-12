# Шаблон карточки вопроса к оракулу

Карточка должна иметь frontmatter и адресное тело. Поля ниже обязательны.

```text
---
status: "active"
date: "2026-04-12"
main_address: "PO3a.3"
related_addresses: ["PO3a.2", "PO3a.4"]
ancestor_addresses: ["PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a.4"]
raw_address_notation: "PO3a.2, 3, 4; D2Q3B5, 7"
normalized_addresses: ["PO3a.2", "PO3a.3", "PO3a.4", "D2Q3B5", "D2Q3B7"]
address_status: "active"
blocker: "Короткое имя точного блокера"
collections: ["q3_docs", "math_papers"]
tags: ["po3", "boundary"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md"]
strong_terms: ["граничное слово (boundary word)", "алгебра знаковой чистоты (sign-pure algebra)"]
empty_terms: ["общая классификация"]
false_friend_terms: ["стилтьесова монотонность (Stieltjes monotonicity)"]
opens_new_branch_terms: ["вольтеррово слово (Volterra word)"]
neighbor_addresses: ["PO3a.2", "PO3a.4"]
---
```

Обязательные разделы тела:

1. `Точный блокер`
2. `Почему этот поиск нужен сейчас`
3. `Что уже известно по этому адресу`
4. `Что именно мы хотим узнать поиском`
5. `Серия запросов`
6. `Пустые / шумовые слова`
7. `Новые возможные комбинации слов`
8. `Переход в INSIGHTS`
9. `Следующий адресный шаг`

Правило адресов:

- `raw_address_notation` хранит буквальную рабочую запись;
- `normalized_addresses` хранит явный список адресов без сокращений;
- killed address трактуется как killed subtree, если не записано обратное.

Правило терминов:

- при первом упоминании писать термин по-русски;
- если нужен английский эквивалент, добавлять его в скобках:
  `граничное слово (boundary word)`,
  `алгебра знаковой чистоты (sign-pure algebra)`,
  `нулевой режим (zero mode)`.
