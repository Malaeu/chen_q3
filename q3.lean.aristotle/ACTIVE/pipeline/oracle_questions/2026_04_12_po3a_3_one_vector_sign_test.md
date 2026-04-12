---
status: "active"
date: "2026-04-12"
main_address: "PO3a.3"
related_addresses: ["PO3a.2", "PO3a.4"]
ancestor_addresses: ["PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a.4", "PO3a.5"]
raw_address_notation: "PO3a.3; PO3a.2, 4, 5; H-bridge.11"
normalized_addresses: ["PO3a.3", "PO3a.2", "PO3a.4", "PO3a.5", "H-bridge.11", "PO3a"]
address_status: "active"
blocker: "Знаковая структура одного вектора граничной поправки"
collections: ["q3_docs", "math_papers"]
tags: ["po3", "boundary", "zero_mode", "one_vector"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md"]
strong_terms: ["граничная оболочка (boundary-cap space)", "двойственный функциональный критерий (dual functional criterion)", "одновекторный знаковый тест (one-vector sign test)"]
empty_terms: ["общая классификация оператора"]
false_friend_terms: ["стилтьесова монотонность (Stieltjes monotonicity)"]
opens_new_branch_terms: ["ортогональное дополнение граничной оболочки (orthogonal complement of the boundary-cap space)"]
neighbor_addresses: ["PO3a.2", "PO3a.4", "PO3a.5"]
---

# PO3a.3 — Знаковая структура одного вектора граничной поправки

## Статус

- карточка активна;
- это рабочая память для серии запросов вокруг `PO3a.3`.

## Точный блокер

После редукции `PO3a` до первого порядка живой вопрос больше не про всю
граничную алгебру сразу. Он локализован в одном векторе:
нужно понять, может ли реальный вектор граничной поправки после действия
оператора `G_g[a]` породить запрещённую межзнаковую составляющую.

После нового локального сжатия точный плюс-сторонний тест уже такой:

```tex
P_+ v_{a,N} \notin E_{+,\partial},
```

где `E_{+,\partial}` — конечномерная граничная оболочка
`PO3a-finite reduction` на плюс-стороне.

## Почему этот поиск нужен сейчас

На этом адресе мы уже знаем общую конечномерную схему и конечную матрицу
смешивания. Но это ещё не закрывает шаг: остаётся один локальный вопрос о
знаке одного вектора. Если здесь снова спросить “вообще про граничную
алгебру (boundary algebra)”, оракул уводит нас назад в слишком широкий
контекст. Поэтому здесь особенно
важно держать точную формулировку и словарь именно для `PO3a.3`.

## Что уже известно по этому адресу

- `PO3a.1 -> PO3a.5` уже заморожен как жёсткий proof-packet.
- `PO3a.2` теперь сводит граничную поправку к конечному набору кирпичей.
- `PO3a.3` сужен ещё на один шаг: живой объект — знаковая структура одного
  вектора, а не полная классификация всех граничных членов.
- Первый порядок уже связан с нулевым режимом (zero mode)
  `v_{a,N} = T_{a,\infty,N}^* G_g[a] 1`, и старый shortcut через “общую
  монотонность” уже убит.
- В основной `PO3a`-заметке уже определены конечные граничные оболочки
  `E_+`, `E_-`; это даёт точную синергию с новым ходом:
  плюс-стороннюю независимость можно проверять до применения `U^*`.
- Если `U` сохраняет знак и `U^*|_{\mathcal H_+}` инъективен, то
  коллинеарность
  `U^* h_{+,N} \parallel P_+ U^* v_{a,N}`
  эквивалентна коллинеарности
  `h_{+,N} \parallel P_+ v_{a,N}`.
- Так как `h_{+,N} \in E_{+,\partial}`, достаточно показать
  `P_+ v_{a,N} \notin E_{+,\partial}`.
- Ещё дешевле: достаточно найти функционал
  `\Lambda_+`, который зануляет `E_{+,\partial}`, но не зануляет
  `P_+ v_{a,N}`.
- Ещё более практичная форма уже видна:
  как только `PO3a.2` даёт boundary-word form
  `B_{a,N}=\sum X_\ell P_J Y_\ell`,
  можно собрать raw генераторы
  `g_{\ell,j}^+ := P_+ Y_\ell^* e_j`,
  их Gram matrix и ортопроектор `\Pi_{+,\partial}` на
  `E_{+,\partial} = \operatorname{span}\{g_{\ell,j}^+\}`.
- Тогда живой witness становится буквальным:
  `f_+ := (I-\Pi_{+,\partial}) P_+ v_{a,N}`.
  Если `f_+ \neq 0`, plus-side collapse уже невозможен.
- Главный источник: `q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`.
- Формальная оболочка по-прежнему сидит в
  `q3.lean.aristotle/q3/Proofs/HBridge_PO3_Shell.lean`.

## Что именно мы хотим узнать поиском

- Какие формулировки лучше всего вытаскивают из нашей базы уже найденные
  локальные редукции про `PO3a.3`, а не возвращают весь `PO3` целиком.
- Есть ли в reviewed notes или старых request nodes точный словарь для
  “одновекторного” знакового теста и отделения от конечномерной граничной
  оболочки.
- Какие слова лучше переключают поиск с общей граничной алгебры на
  язык граничных оболочек, нулевого режима и двойственного функционального
  критерия.
- Какие слова лучше поднимают именно projector / Gram / annihilator version
  этого шага, а не только абстрактную формулировку “найти функционал”.
- Какие соседние адреса (`PO3a.2`, `PO3a.4`, `PO3a.5`) уже дают полезные
  зацепки, которые стоит переносить сюда.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a.3 boundary-cap space dual functional criterion zero-mode` | `PO3a.3` | Поднять новую узкую формулировку через отделение от конечномерной оболочки | one-vector test → boundary-cap separation | strong hit | вернул `PO3a-finite reduction` и те же late `PO3a` notes |
| `PO3a.3 plus-side independence zero-mode boundary-cap space` | `PO3a.3` | Проверить, держится ли плюс-сторонняя независимость на нашей терминологии | zero-mode column → plus-side independence | strong hit | вернул exact `PO3a.3` packet про zero-mode column и reflection-evenness |
| `PO3a.3 finite boundary-cap spaces U sign preserving injective functional criterion` | `PO3a.3` | Проверить синергию с конечными граничными оболочками и оболочкой `U^*` | finite receiver → functional criterion | hit | вернул boundary-cap packet и подтвердил, что route остаётся внутренним |
| `PO3a.3 U star injective sign preserving zero-mode column boundary-cap` | `PO3a.3` | Проверить, есть ли уже готовый словарь для снятия `U^*` с плюсовой стороны | operator shell → before/after `U^*` | hit | вернул late `PO3a.3` notes и `HBridge_PO3_Shell.lean` как shell consumer |
| `PO3a.3 Gram projector boundary-cap witness` | `PO3a.3` | Поднять вычислимую форму через ортопроектор и Gram matrix | functional criterion → projector witness | internal synthesis | это уже не найденная внешняя теорема, а наш следующий theorem-packet |

## Пустые / шумовые слова

- `generic operator classification`
- слишком широкая `граничная алгебра (boundary algebra)` без адреса
- глобальное `Cauchy injectivity` без привязки к `PO3a.3`
- короткий внешний поиск по общим словам про Hahn-Banach и separation не дал
  готовой внешней теоремы именно под наш маршрут

## Новые возможные комбинации слов

- `boundary-cap space + zero-mode`
- `dual functional criterion + PO3a.3`
- `plus-side independence + boundary-cap`
- `annihilator functional + zero-mode column`
- `Gram projector + boundary-cap witness`
- `orthogonal residual + zero-mode column`

## Переход в INSIGHTS

- После завершения серии надо оставить короткий синтез в `docs/INSIGHTS.md`
  с явной пометкой адреса `PO3a.3`.
- В итоговом insight должно быть отдельно записано:
  какие слова реально усилили `PO3a.3`,
  а какие только возвращали нас в широкое `PO3`.
- Первый боевой синтез по этой новой формулировке добавляется сейчас:
  живой brick — это уже не просто знаковый тест одного вектора, а отделение
  `P_+ v_{a,N}` от конечномерной граничной оболочки `E_{+,\partial}`.
- Следующая более жёсткая версия тоже уже зафиксирована:
  искать надо не произвольный `\Lambda_+`, а сначала raw generators,
  потом `\Pi_{+,\partial}`, и уже затем witness
  `f_+ = (I-\Pi_{+,\partial}) P_+ v_{a,N}`.

## Следующий адресный шаг

- Если удаётся построить функционал `\Lambda_+`, который зануляет
  `E_{+,\partial}` и не зануляет `P_+ v_{a,N}`, это сразу усиливает `PO3a.3`
  и даёт прямой ход в `PO3a.4`.
- Ещё лучше: если удаётся вычислить `\Pi_{+,\partial}` и показать
  `f_+ \neq 0`, то этот functional идёт автоматически как
  `\Lambda_+(x)=\langle x, f_+ \rangle`.
- Если для `\Lambda_+` не хватает явной формы оболочки, откатиться на
  `PO3a.2`, но только для извлечения `E_{+,\partial}`, а не для переоткрытия
  всей граничной поправки.
- Если снова всплывает только physical-word route, считать это побочной
  синергией с `H-bridge.11`, а не заменой локального хода.
