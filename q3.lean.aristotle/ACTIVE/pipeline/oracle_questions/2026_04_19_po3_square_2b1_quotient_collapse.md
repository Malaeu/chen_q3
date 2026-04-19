---
status: "active"
date: "2026-04-19"
main_address: "PO3-square.2b1"
related_addresses: ["PO3-square.2b", "PO3-square.2d1", "SQ2c"]
ancestor_addresses: ["PO3-square.2b", "PO3-square.2"]
child_or_next_addresses: ["PO3-square.2c"]
raw_address_notation: "PO3-square.2b1; PO3-square.2b, PO3-square.2d1; SQ2c"
normalized_addresses: ["PO3-square.2b1", "PO3-square.2b", "PO3-square.2d1", "SQ2c", "PO3-square.2", "PO3-square.2c"]
address_status: "active"
blocker: "Формализовать алгебраическое схлопывание внутренней квадратной цепочки после деления на общий square-tail divisor: нормализованные quotients остаются только скалярными кратными."
collections: ["q3_docs"]
tags: ["po3-square", "quotient-collapse", "square-tail"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: ["PO3-square.2b1"]
strong_terms: ["нормализованный quotient (normalized quotient)", "общий square-tail divisor", "внутренняя квадратная цепочка"]
empty_terms: ["global uniqueness theorem"]
false_friend_terms: ["готовая ordering theorem import"]
opens_new_branch_terms: ["one-line quotient collapse"]
neighbor_addresses: ["PO3-square.2d1"]
---

# PO3-square.2b1 — Формализовать алгебраическое схлопывание внутренней квадратной цепочки после деления на общий square-tail divisor: нормализованные quotients остаются только скалярными кратными.

## Статус

- карточка создана;
- первая серия локальных запросов уже отработана;
- следующий ход зафиксирован как узкая Lean-лемма.

## Точный блокер

Формализовать алгебраическое схлопывание внутренней квадратной цепочки после деления на общий square-tail divisor: нормализованные quotients остаются только скалярными кратными.

## Почему этот поиск нужен сейчас

После закрытия `PO3-square.2b0` у Newton-ветки исчез definitional туман, и
остался уже не общий uniqueness-вопрос, а более узкий стратегический риск:
не даёт ли внутренняя квадратная цепочка после деления на общий square-tail
делитель хоть какое-то второе нетривиальное направление. Если цепочка
схлопывается в одну линию, то наивный ordering-route надо честно убить прямо
сейчас, а не тащить его выше.

## Что уже известно по этому адресу

- в `PO3-square.2b0` уже формализована квадратная Newton/divided-difference
  башня, так что следующий шаг теперь должен быть не про encoding, а про
  содержательное схлопывание;
- мартовская заметка и апрельский synthesis уже содержат точную формулу:
  если `E_k^{sq}` — общий square-tail делитель для `J_{a,k}`, то
  `G_k := J_{a,k} / E_k^{sq}` удовлетворяет
  `G_k = - s_{k+1} G_{k+1}`;
- локальный поиск по `q3_docs` трижды вернул именно этот фрагмент как главный
  сигнал, а не какой-то внешний theorem import;
- внешний поиск по de Branges / Cauchy-de Branges ordering дал только общий
  фон про nearly invariant subspaces и ordered structure, но не дал готовой
  теоремы, которая бы автоматически закрывала именно нашу внутреннюю цепочку.

## Что именно мы хотим узнать поиском

- есть ли в наших notes уже точная алгебраическая запись схлопывания, которую
  можно без аналитики посадить в Lean;
- есть ли внешний theorem import, который закрывает именно quotient-collapse,
  а не только общий ordering background;
- какой минимальный формальный statement надо заморозить сейчас, чтобы
  следующий стратегический вывод уже стал механикой.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3-square.2b1 quotient collapse internal square division chain G_k = - s_{k+1} G_{k+1}` | `PO3-square.2b1` | Найти самый прямой in-repo statement для схлопывания | точная формула | strong | прямо вернул апрельский synthesis с формулой `G_k = - s_{k+1} G_{k+1}` |
| `SQ2c internal divided receivers common-zero factor collapse normalized quotients scalar multiples` | `PO3-square.2b1` | Проверить, не маскируется ли это под другой адрес `SQ2c` | адрес ветки / язык подпространств | strong | подтвердил, что вопрос про ordering становится вакуумным после quotient-normalization |
| `J_{a,k+1}=J_{a,k}/(z-s_{k+1}) E_k^{sq} quotient collapse one line` | `PO3-square.2b1` | Вытащить именно формулу “вся цепочка = одна линия” | язык деления / общего делителя | strong | вернул мартовскую note с буквальной формулировкой “chain collapses to one line” |

## Пустые / шумовые слова

- `global uniqueness theorem`;
- `готовый ordering import`.

## Новые возможные комбинации слов

- `one-line quotient collapse`;
- `normalized quotient scalar multiple`;
- `internal square-division chain`.

## Переход в INSIGHTS

- синтез зафиксирован в `q3.lean.aristotle/docs/INSIGHTS.md` как адрес
  `PO3-square.2b1`.

## Следующий адресный шаг

- сначала закрыть `PO3-square.2b1` как абстрактную алгебраическую shell-лемму;
- после этого либо переходить к `PO3-square.2c`, либо возвращаться к живой
  uniqueness-стене уже без ложной внутренней ordering-двери.
