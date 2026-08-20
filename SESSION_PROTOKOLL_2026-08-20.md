# SESSION_PROTOKOLL 2026-08-20 — ночная петля, стена L73.2, три красных закрыты

## Kontext

Сессия начата 18.08 в 14:51 в терминале ghostty на рабочей Linux-машине,
включён Remote Control, дальше владелец работал с телефона. 20.08 окно ghostty
умерло, **процесс выжил** (разбор ниже). 30 коммитов за сутки.

Участники: Linux-тело (эта сессия) · Прошка (судья, пишет в GitHub сам) ·
Codex (весь день на лимите, не поднят) · владелец.

## Ausgangslage (что было утром)

- G6/N1 pre-anchor композер kernel-green, но **условный**: обитателей его двух
  входов не существовало.
- Счётчик до RH: 14 канатов классикой / 14 через голову 058.
- Blueprint только что стал самодостаточным (все измеренные узлы — строками).

## Aufgabe

Закрывать красные каркаса по циклу «следующая красная → судье → ядро →
строка зеленеет», не поднимая Codex.

## Erledigt

### Три красных закрыты ядром

```
№25  обитатель SelectedProlatePreAnchorData        c10c9b58
     selectedFerrersPreAnchorData, расписание k↦(k+2,k+2,K=5(k+2))
     blob 8d420f8a · гейт 3 раунда (7→1 warning→0) · q3_check ok
     РАТИФИЦИРОВАН судьёй: 5 аудитов PASS (bc65b407)
     счётчик 14/14 -> 13/13

F72.0A параметрический словарь                     a61eb04b
     G6N1SelectedFerrersPaperParameterDictionary.lean, 148 строк
     blob 10e9e972 · ноль ошибок с первого содержательного прогона
     закон степеней n=2j (chi2 = степень ЧЕТЫРЕ), gamma=2pi(k+2),
     gamma^2 = mode4JacobiG, замок пары через pair_spec
     бонус сверх директивы: gamma = mode4SlepianC — не плодим второй параметр

F72.3A сплетение операторов                        ddd9ee09
     G6N1FuchsProjectOperatorIntertwining.lean, 133 строки
     blob 59610d91 · гейт 3 раунда (2→1→0)
     F_a(U h) = sqrt(2pi)*U(T_lambda h), гипотеза одна: 0 <= lambda
     содержание: замена s = sqrt(2pi)*y, работает т.к. 2pi/sqrt(2pi)=sqrt(2pi)
```

### Стена L73.2 разложена дважды, вглубь

Порт Lemma 7.3 (строка 12) → 9 этажей L73.0–L73.8 (вердикт 26881a42).
Из них L73.2 — единственная настоящая стена → ещё 7 этажей F72.0–F72.6
(вердикт 835d7e97) с **двумя** аналитическими ядрами, а не одним:
Satz 9 (F72.1) и Fourier-eigenvalue defect (F72.3).

### Kill, который спас от ошибки

REQ-E: цель L73.5 без скаляра **математически ложна** (dfe6be5c).
Точная формула: `Mellin(E*h)(-iz) = (1/4)·centeredXi(z)`. K1 при z=0:
отношение 0.25 на 79 знаках. Судья убил **собственную формулировку** из
вчерашнего вердикта. Скаляр 4 узаконен в sourceScale, `centeredXi` трогать
запрещено.

### Fuchs 1964 добыт и прокартографирован

Владелец достал PDF через Uni-доступ (пейволл, Unpaywall `is_oa: false`).
Реестр `HAVE ✓`, карточка `FUCHS_1964_USAGE_CARDS.md`.

Theorem 1: `1 − λ_n ~ 4·√π·8ⁿ·(n!)⁻¹·a^(2n+1)·e^(−2a²)`. Константа `8ⁿ`
сверена дважды (шапка OCR битая, конец доказательства читается). Затухание
**экспоненциальное**, обе наши моды покрыты, запасной план судьи не нужен.

Crosswalk я НЕ угадывал — и правильно. Судья доказал (3abb8613):
`a = √(2π)·λ`, `Λ_n = χ_n²`. Угадали бы `a = λ` → экспонента `e^(−2λ²)`
вместо `e^(−4πλ²)`; угадали бы `Λ = χ` → константа вдвое больше.
Проектные асимптотики: `1−χ₀ ~ 2√2·π·λ·e^(−4πλ²)`,
`1−χ₂ ~ (2¹⁴/3)·√2·π⁵·λ⁹·e^(−4πλ²)`. Префактор сошёлся тремя путями.

### Инструменты и записи

- `docs/cartographer/depgraph.py` — граф зависимостей из ИСХОДНИКОВ, в реестре
  TOOLS.yaml с известным режимом отказа.
- `docs/CHAT_DIGESTS.md` — идея-лабиринт владельца + вердикт литературы;
  Эйлер-аудит (ad-hoc вопрос владельца судье).
- `docs/NIGHT_LOOP_DESIGN.md` — раздел про выживание сессии после смерти окна.

## Geprüft

**Каталог `capability` НЕ является графом.** Замер: 477 из 478 `requires` и
1165 из 1172 `provides` — человеческая проза; пересечение канонических
токенов **ноль**. Я утверждал обратное и был неправ.

**Кладбище: 171 kill.** Причины: normalization 11 + normalized 6 +
normalizer 3 + unit 5 + scale 3 = **28 про нормировки**, против path 2,
search 3, reachability 0. Типы: strategy 124, route 19, object 14, wall 11.
Вывод: наше узкое место — единицы, а не поиск пути.

**depgraph первый прогон соврал.** Без фильтра коротких имён однобуквенное
объявление `C` дало конус 49, глубину **13** и 10 разрезов. Тринадцать
совпало бы с нашим ручным счётом канатов и означало бы ничто. С фильтром:
конус 25, глубина 6, три разреза (Гурвиц-перенос, каркас, centeredXi).

**Выживание сессии измерено.** PID 2684698 жил 1д18ч; цепь
`systemd ← script -qf ← bash -i ← claude`; GUI ghostty отсутствует, пять
обёрток `script` пережили его смерть. У процесса 0 слушающих портов и 10
исходящих TLS — телефон соединяется через серверы Anthropic, не с машиной.

## Versendet

Судье: REQ-D, E, F, G, H — все отвечены, очередь **пуста**. Пять пинков
строкой «смотри очередь: REQ-…», каждая отправка верифицирована скриншотом
(оракул композера дважды поймал проглоченные пробелы до отправки).

Наружу больше ничего не уходило.

## Offen — nächste Schritte

1. **F72.1 Meixner–Schäfke Satz 9** — ЕДИНСТВЕННАЯ настоящая стена L73.2.
   Нужна одна страница 243 главы 3. Это книга (Springer 1954), скриптом не
   тянется. Без неё стена стоит.
2. **F72.0B** — привязка наших мод к литеральному `ps_n`. Развилка судьи:
   R1 (материализовать представителя, kill 10/10, цена 5/10) против
   R2 (прямой рейт с экзистенциальным скаляром, 9/10, 7/10). Вопрос ЕМУ.
3. **Вторая половина F72.3** — `Λ₀ = χ₀²`, `Λ₄ = χ₂²`. Стоит на уже
   доказанном сплетении, но требует концентрационного оператора. Кандидат
   для Codex или для этого тела.
4. **Codex не поднят.** Три задачи по порядку лежат в `docs/Codex/`:
   линк контракта → сверка пакета D → F72.0A (последняя УЖЕ закрыта, ему
   остаётся независимая сверка).
5. **Строка 12 красная** и останется до L73.8. Счётчик 13/13 не сдвинется,
   пока обитатель порта не построен.

## Wichtige Fakten

- Прошка убивает **собственные** формулировки — двусторонняя адверсариальность
  работает. За сутки два таких случая (overclaim мой, unit-ошибка его).
- Правило «не угадывать константу пересчёта» окупилось буквально: оба
  подозрения оказались ловушками с измеренной ценой.
- Наш kill REQ-E и вердикт REQ-H — один и тот же класс ошибки, пойманный
  дважды. Отсюда F72.3A: пересчёт теперь **теорема**, не соглашение.
- Идея владельца про диффузию = relaxed planning graph (Graphplan 1997) +
  h_max/h_add (Bonet & Geffner 2001). Переизобретён Беллман–Форд с
  полукольцом. Специализированной работы по диффузии на графе теорем
  разведка не нашла.
- Отрезвляющее: CSLibPremiseBench (1875 кандидатов ≈ наш масштаб) — графовый
  reranker едва обходит BM25. Планка BM25 обязана быть измерена первой.

## Dateien (absolute Pfade)

```
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPreAnchorDataInhabitant.lean
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPaperParameterDictionary.lean
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/G6N1FuchsProjectOperatorIntertwining.lean
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/FUCHS_1964_USAGE_CARDS.md
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/pdfs/fuchs_1964_bandlimited_eigenvalues.pdf
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/cartographer/depgraph.py
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/CHAT_DIGESTS.md
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/NIGHT_LOOP_DESIGN.md
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/Codex/TASK_2026-08-20_F72_0A_parameter_dictionary.md
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/PROSHKA_QUEUE.md
```

Вердикты судьи за сутки — в `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/`:
`..._CCM_LEMMA_7_3_PREANCHOR_PORT_FLOORS_...`, `..._REQ_2026_08_20_E_EXPLICIT_CCM_MELLIN_NORMALIZATION_...`,
`..._SELECTED_FERRERS_LEMMA72_RATE_FLOORS_...`, `..._REQ_2026_08_20_G_F72_0_...`,
`..._REQ_2026_08_20_H_FUCHS_F72_3_SCOPE_LOCK_...`, `..._EULER_LOGARITHMIC_REPRESENTATION_AUDIT_...`
