---
status: "READY_FOR_JOINT_REVIEW"
date: "2026-08-14"
main_address: "RB-GOAL-058-G3-PROLATE-RATE-FLOOR"
related_addresses: []
ancestor_addresses: ["GOAL-058-G3"]
child_or_next_addresses: ["MODE4_CLASSICAL_EVEN_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK"]
raw_address_notation: "RB-GOAL-058-G3-PROLATE-RATE-FLOOR"
normalized_addresses: ["RB-GOAL-058-G3-PROLATE-RATE-FLOOR", "GOAL-058-G3", "MODE4_CLASSICAL_EVEN_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK"]
address_status: "ACTIVE"
blocker: "Классический чётный спектр PSWF в буквальную инерцию Schur-матрицы и точная поправка конечного разбиения"
collections: ["q3_docs"]
tags: ["Goal058", "G3", "Schur"]
insight_links: []
request_nodes: ["GOAL058_G3_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_SOURCE_PACKET"]
strong_terms: ["mode4HermitianSchurMatrix negativeCount classical even spectrum", "Jacobi Weyl m-function Schur complement inertia"]
empty_terms: ["generic Schur complement"]
false_friend_terms: ["finite truncation determinant sign"]
opens_new_branch_terms: ["Haynsworth inertia additivity positive tail"]
neighbor_addresses: []
---

# RB-GOAL-058-G3-PROLATE-RATE-FLOOR — Классический чётный спектр PSWF в буквальную инерцию Schur-матрицы и точная поправка конечного разбиения

## Статус

- четыре обязательных запроса выполнены последовательно по свежему `q3_docs`;
- точного готового crosswalk в репозитории и зарегистрированной внешней Lean-базе не найдено;
- найден новый первичный discriminator: DLMF 30.16 даёт упорядоченные конечные
  матричные аппроксимации спектра и пределы собственных векторов;
- синтез записан в
  `GOAL058_G3_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_SOURCE_PACKET_2026-08-14.md`.

## Точный блокер

Классический чётный спектр PSWF в буквальную инерцию Schur-матрицы и точная поправка конечного разбиения

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`RB-GOAL-058-G3-PROLATE-RATE-FLOOR`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- буквальный consumer требует nonsingular endpoint counts `2/3` для
  `mode4HermitianSchurMatrix`, а не для похожей конечной матрицы;
- exact-tail, parameter order, simple kernel, inertia jump и root labels уже
  kernel checked;
- DLMF recurrence algebra и supplied-row-to-root consumer уже kernel checked;
- Proshka запретила молча ставить finite-split offset равным нулю.

## Что именно мы хотим узнать поиском

- есть ли готовая classical-spectrum-to-exact-Schur-count теорема;
- можно ли доказать exact offset без бесконечного unbounded Jacobi operator;
- даёт ли первичный источник более прямой indexed-row supplier.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `классический чётный спектр PSWF инерция Schur матрицы negativeCount` | `RB-GOAL-058-G3-PROLATE-RATE-FLOOR` | найти готовый мост | объект и индекс | no exact hit | текущие verdict/receivers only |
| `Jacobi Weyl m-function continued fraction exact tail Schur complement spectral counting` | `RB-GOAL-058-G3-PROLATE-RATE-FLOOR` | найти exact-tail law | Weyl/continued fraction | partial local hits | right-tail + Schur files, no count law |
| `Haynsworth inertia additivity positive tail half-line Jacobi operator` | `RB-GOAL-058-G3-PROLATE-RATE-FLOOR` | проверить offset route | finite congruence | no ready theorem | finite block-congruence leaf needed |
| `prolate Sturm Liouville Legendre coefficient Jacobi operator unitary equivalence chi_n` | `RB-GOAL-058-G3-PROLATE-RATE-FLOOR` | найти source equivalence | PSWF/Legendre | DLMF/source dossier | DLMF 30.16 finite spectral limit fork |

## Пустые / шумовые слова

- `generic Schur complement` без literal tail;
- `finite truncation determinant sign` без индексного предела;
- `Weyl m-function` без PSWF/Legendre координат.

## Новые возможные комбинации слов

- `DLMF 30.16 alpha p d finite eigenvalue limit exact Schur tail`;
- `finite tail positive definite block congruence inertia offset zero`;
- `p=3 DLMF eigenvector limit degree four coefficient function identity`.

## Переход в INSIGHTS

- пока не делался: математическая развилка должна быть проверена Mythos и
  судьёй до записи как ratified insight.

## Следующий адресный шаг

- joint review fork:
  `ROUTE_INERTIA_FINITE_LIMIT` против `ROUTE_DLMF_INDEXED_ROW_LIMIT`;
- после выбора материализовать только первый source-faithful Lean leaf.
