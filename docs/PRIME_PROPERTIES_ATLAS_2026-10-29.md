# Атлас доказанных свойств простых (1875–2026) и их пригодность для знака s_E, s_O

Запрос владельца 29.10: «дико глубокое исследование всех опубликованных и доказанных свойств простых за 150 лет,
мультиагентно, по нашим правилам; синтез». Метод: workflow `wf_224d5063-36d` — 8 исследователей по областям,
у каждого скептик, открывающий источник и пытающийся опровергнуть; критик полноты; синтез.
Полные данные (175 пунктов, у каждого URL, цитата, статус, вердикт скептика): `docs/literature/PRIME_ATLAS_2026-10-29/atlas.json`.

| Область | Пунктов | CONFIRMED | CORRECTED | UNVERIFIED | REFUTED |
|---|---|---|---|---|---|
| распределение | 21 | 15 | 6 | 0 | 0 |
| нули | 22 | 14 | 6 | 1 | 1 |
| прогрессии | 22 | 13 | 7 | 2 | 0 |
| решёта | 24 | 14 | 7 | 3 | 0 |
| узоры | 22 | 15 | 6 | 1 | 0 |
| мультипликативная структура | 22 | 8 | 13 | 1 | 0 |
| барьеры | 20 | 12 | 8 | 0 | 0 |
| 2019–2026 | 22 | 15 | 6 | 1 | 0 |
| **всего** | **175** | **106** | **59** | **9** | **1** |

Опровергнут и выброшен: «функции Дэвенпорта–Хейльбронна имеют положительную долю нулей на прямой без RH».

Сверка наблюдателем (сам, по тексту PDF):
- Zhu, arXiv:2608.24827: «support 1.6, which is 2.3 times the classical range» (стр. текста 20) и
  «Passing the resulting wall thus requires cancellation in the prime comb, a concrete arithmetic problem» (строка 62). ПОДТВЕРЖДЕНО.
- Broucke–Debruyne–Vindas, arXiv:2004.11501, введение: система DMV «also realizes the classical de la Vallée Poussin zero-free region;
  in particular, the Riemann hypothesis (RH) fails for it». ПОДТВЕРЖДЕНО.
Ошибка сценария при первом прогоне (склейка проверок по точному имени, 92 пункта остались без вердикта) исправлена;
критик и синтез пересчитаны на полных данных.

---

# Синтез атласа: какое доказанное свойство простых может дать знак

**Как читать.** Здесь только пункты с вердиктом CONFIRMED или CORRECTED, в исправленной формулировке. Непроверенное помечено «не проверено». Вердикт CONFIRMED значит «согласуется со вторичным источником». Первоисточники открыты не везде. Столбец «Бёрлинг» часто содержит вывод авторов карточек, а не теорему. Такие места помечены.

**Термины, один раз.**
- **Обобщённые простые Бёрлинга** — произвольный набор «простых» с эйлеровым произведением, но без арифметики настоящих целых чисел. Из них собирают «целые» и строят свою дзета-функцию.
- **Эйлерово произведение** — запись дзета-функции через произведение по простым.
- **Функциональное уравнение и Γ-множитель** — симметрия s ↔ 1−s и архимедова часть. В нашей матрице K они есть.
- **Знак против размера** — знак отвечает «≥ 0 или нет». Размер отвечает «насколько велико».
- **Без потерь** — точное тождество или точное представление без запаса. У нас запаса нет, поля ~1e-29.

---

## 1. Ответ одним абзацем

Доказанные свойства простых, дающие настоящий знак, есть, но все они не годятся для знака s_E ≤ 0, s_O ≥ 0 на всех окнах сразу. Вот эти свойства.
- Неотрицательность Λ(n) вместе с неравенством 3+4cos t+cos 2t = 2(1+cos t)² ≥ 0.
- Лемма Ландау о неотрицательных коэффициентах.
- Квадраты Сельберга (Σλ_d)² ≥ 0.
- Положительность логарифмических коэффициентов в стиле Рэнкина и Ленглендса.
- Положительность Вейля через эффективные циклы для кривых над конечным полем.
- Положительность Йошиды на малых окнах.

Каждое из них упирается в одну из четырёх стен.
1. Свойство верно в любой системе Бёрлинга. Тогда оно останавливается у зоны без нулей σ ≥ 1−c/log t, потому что Diamond–Montgomery–Vorhauer построили систему с этой зоной, где RH ложна.
2. Знак получается только как одностороннее неравенство с потерей множителя 2 (проблема чётности Сельберга).
3. Нужна геометрия поверхности C×C с конусом эффективных циклов. Над Z её нет.
4. Положительность доказана только для малых окон (Йошида: 2L ≤ log 2).

Доказанные свойства, которые видят корреляции разных простых, дают только асимптотику или среднее с потерей. К ним относятся Tao, Tao–Teräväinen, Green–Tao–Ziegler, Bombieri–Vinogradov и Maynard. Из них нельзя вытянуть знак при запасе 1e-29. Точные тождества (явная формула Вейля, подсчёт отрицательных собственных значений у Bombieri 2000) работают без потерь, но содержат сумму по нулям. Знак слева через них становится знаком суммы по нулям, то есть RH. Итог: сегодня нет доказанного свойства простых, которое даёт знак для всех окон. Ближе всего идея разложения «явный положительный член + сумма неотрицательных членов» (правило 18 проекта), построенного из эйлерова произведения и Γ-члена вместе.

---

## 2. Таблица свойств

Условные обозначения: ✓ да, ✗ нет, ~ частично или только в среднем, ? неизвестно, н/п не применимо.
T1: только данные простых (без нулей). T2: все окна сразу. T3: знак, не размер. T4: без потерь. T5: корреляции разных простых. T6: полюс ранга 2, не марковский. T7: доказанная теорема, не эквивалент RH.

| Свойство | Доказано? | Что даёт | Без потерь? | Бёрлинг? | T1 T2 T3 T4 T5 T6 T7 |
|---|---|---|---|---|---|
| **А. Механизмы знака** | | | | | |
| Λ(n) ≥ 0 и 3+4cos t+cos 2t = 2(1+cos t)² ≥ 0 (de la Vallée Poussin) | Да | Знак термин за термином. Итог: нет нулей на Re s=1 и зона без нулей 1−c/log t. Формулировка из Mossinghoff–Trudgian содержит опечатку (пропущен множитель ½ у cos 2φ). | Да, по членам | Да. Система DMV реализует ровно эту зону, RH там ложна. Что довод использует только Λ_P ≥ 0 и полюс, наш вывод, не проверено. | ✓ ✓ ✓ ✓ ~ ✗ ✓ |
| Лемма Ландау: неотрицательные коэффициенты дают особенность в абсциссе сходимости | Да | Знак, точный инструмент. Но естественные «знаковые» следствия ложны (Пойа, Mertens). | Да | Да | ✓ ✓ ✓ ✓ ✗ ✗ ✓ |
| Квадрат Сельберга (Σ_{d\|n}λ_d)² ≥ 0 и квадратичная форма по λ_d | Да | Механизм — знак за счёт квадрата. Результат — верхняя оценка. Потеря — множитель 2 (чётность). | Нет | ? (неравенство — чистая алгебра, источники расходятся) | ✓ ✓ ✓ ✗ ~ ✗ ✓ |
| Большое сито, неотрицательность дисперсии, Montgomery–Vaughan: N−1+δ⁻¹ (точная константа) | Да | Оценка нормы положительной матрицы Грама. Знака не даёт. Простых во входе нет. | Нет (неравенство) | н/п | – ✓ ✗ ✗ ✗ ✗ ✓ |
| Положительные log-коэффициенты \|след\|² и тензорные степени (идея Ленглендса по Рэнкину, мотивация для Deligne) | Да, как приём. Это не полное доказательство Deligne. | Точная знаковая конструкция. Для Z нужна информация о полюсах, это сила RH. | Да после m→∞ | Нет | ✓ ~ ✓ ✓ ✓ ✗ ✗ (T7 для Z не выполнен) |
| Положительность Вейля через эффективность: Tr(Z·Z') ≥ 2d'(Z) ≥ 0, Castelnuovo–Severi (D²) ≤ 2d₁d₂ | Да, для кривых над F_q | Точный знак. Источник — форма индекса 1 на C×C. | Да | Нет. Для Spec Z нет аналога C×C (van Frankenhuijsen). | ✗ ✓ ✓ ✓ ✓ ~ ✓ (только функц. поле) |
| Йошида 1992, Bombieri 2000 (повторное доказательство) | Да | Положительность формы Вейля при 2L ≤ log 2, то есть supp f ⊂ [−(log 2)/2, (log 2)/2]. Значение порога взято у Zhu, у Йошиды не читано. | Да | ? | ✓ ✗ ✓ ✓ ? ? ✓ |
| Zhu 2026, препринт, **не проверено** (не рецензировано, расчёт не пересчитан) | Препринт, сертифицированный расчёт | Q(f) ≥ 8,9·10⁻¹⁸ ‖f‖² при supp f ⊂ [−0,8; 0,8] (автокорреляция 1,6). Одно окно. | Да (точная редукция к конечной матрице) | Нет (специфика ζ) | ✓ ✗ ✓ ✓ ✗ ✓ ✓ |
| **Б. Корреляции разных простых** | | | | | |
| Tao 2016: логарифмически усреднённая двухточечная гипотеза Чоулы, o(log ω); Tao–Teräväinen (нечётный порядок); Matomäki–Radziwiłł–Tao (усреднение по сдвигам) | Да | Ломает барьер чётности для λ(n)λ(n+h). Только o(·) и усреднение. Гипотеза Чоулы без усреднения при k≥2 открыта. | Нет | ? | ✓ ✗ ✗ ✗ ✓ ✗ ✓ |
| Green–Tao–Ziegler + Green–Tao: асимптотика Харди–Литтлвуда для линейных систем конечной сложности | Да (в GTZ исправлена ошибка, Lemma 13.2, erratum 2024 и arXiv v5 2026) | Корреляции Λ вдоль сдвигов n+h. Двоичные задачи (близнецы, Гольдбах) исключены. | Нет (o(N^d)) | ? | ✓ ✓ ✗ ✗ ✓ ✗ ✓ |
| Bombieri–Vinogradov и уровни выше ½ только для частных случаев (Zhang, Polymath 1/2+7/300, Stadlmann 1/2+1/40 гладкие модули, Maynard 3/5 с весами, Lichtman 66/107, препринт) | Да | Усреднение по модулям, ошибка (log x)^{-A}. Maynard: выход за √x даёт сокращение между суммами нулей разных L-функций. | Нет | Нет (нужны характеры) | ✓ ✓ ✗ ✗ ~ ✗ ✓ |
| Формула симметрии Сельберга: Λ·log + Λ*Λ = μ*log², (1/N)ΣΛ₂ = 2 log N (1+o(1)) | Да | Единственное классическое место, где пары pq входят с главным членом. Ошибка O(x). | Нет | ? | ✓ ✓ ✗ ✗ ~ ✗ ✓ |
| Montgomery F(α) без RH (Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Acta Arith. 214 (2024)) | Да | Второй момент простой стороны для 0 ≤ α ≤ 1 вычислен безусловно. Сумма идёт по всем комплексным нулям. | Асимптотика | ? | ✓ ✓ ✗ ✗ ~ ✗ ✓ |
| Maier 1985: нерегулярность простых в коротких интервалах | Да | Реальные простые скоррелированы через малые простые. Модель Крамера этого не видит. | – (барьер) | ? | ✓ ✓ ✗ – ✓ ✗ ✓ |
| **В. Размер** | | | | | |
| ПТЧ (1896); зоны без нулей (Mossinghoff–Trudgian–Yang); плотность нулей (Guth–Maynard: N(σ,T) ≤ T^{30(1−σ)/13+o(1)}); RH проверена до высоты 3·10¹² (Platt–Trudgian) | Да | Только размер. Последнее — конечный счёт, не равномерный. | Нет | Зона dlVP — да при N=ρx+O(x^θ). Vinogradov–Korobov и плотность нулей — нет. | ✓ ~ ✗ ✗ ✗ ✗ ✓ |
| **Г. Точные тождества** | | | | | |
| Λ = μ*log; тождества Vaughan и Heath-Brown; эйлерово произведение | Да | Структура: типы I и II. Точная алгебра без знака. | Да | Да (формальные тождества) | ✓ ✓ ✗ ✓ ~ ✗ ✓ |
| Явная формула Вейля, критерий Вейля (1952), Bombieri 2000 (число отрицательных собственных значений усечения = половина числа нулей вне прямой) | Да, это эквивалент RH | Именно наша форма <v,Kv> = Σ F_v(z)². Знак слева = знак суммы по нулям. | Да | ? (нужны Γ и функц. уравнение) | ✗ ✓ ✗ ✓ ~ ✗ ✗ |
| Landau–Gonek: Σ_{0<γ≤T} X^ρ = −(T/2π)Λ(X) + O(log T) | Да | Простые как «резонансы» суммы по нулям. Словарь, не знак. | Нет | Нет | ✗ ✓ ✗ ✗ ✓ ✗ ✓ |
| Гипотеза Сельберга об ортонормальности (A, B) | **Гипотеза** (для Дирихле-L известна) | Закон независимости простых разных L-функций | – | ? | не доказано, T7 ✗ |
| **Д. Барьеры (не инструменты знака)** | | | | | |
| DMV 2006; Zhang 2007; Broucke–Debruyne–Vindas 2020; Broucke–Vindas; Hilberdink–Neamah 2020 | Да | Эйлерово произведение плюс регулярность N и π не решают RH. RH-системы существуют и без арифметики. | – | Это сами системы | – |
| Davenport–Heilbronn 1936; Saias–Weingartner 2009; Righetti 2015 | Да | Функциональное уравнение без эйлерова произведения не даёт RH. Нули при Re s > 1. | – | н/п | – |
| Voronin (универсальность); Q-независимость {log p} (Zhu, Лемма 3.2) | Да | Фазы простых свободны. Точная верхняя грань гребёнки равна A_L. | – | Q-независимость у систем Бёрлинга может нарушаться, не проверено | – |
| Пойа и Mertens ложны; Rodgers–Tao Λ ≥ 0; Littlewood | Да | Простых знаковых утверждений нет. RH, если верна, на границе без запаса. Littlewood доказан через нули. | – | ? | – |

---

## 3. Главный урок барьера: что нельзя доказать и что обязано быть в любом доказательстве

**Бёрлинг (эйлерово произведение плюс регулярные целые).**
- Diamond–Montgomery–Vorhauer (Math. Ann. 334 (2006), 1–36). Для 1/2 < θ < 1 есть система с N(x) = ρx + O(x^θ). У неё π(x) = Li(x) + Ω(x·exp(−c√log x)). Её дзета имеет бесконечно много нулей на кривой σ = 1 − a/log t, правее нулей нет, a > (4/e)(1−θ). RH для неё ложна. Саму статью мы не открывали, содержание взято из введения Broucke–Debruyne–Vindas и из карточки с аннотацией.
- Zhang (Math. Ann. 337 (2007), 671–704). Есть системы с RH и с регулярными целыми. Ошибки там порядка x^{1/2+ε}.
- Broucke–Debruyne–Vindas (Adv. Math. 370 (2020), 107240). Система с RH, π(x) = Li(x) + O(√x). Колебание целых при этом порядка x·exp(−c√(log x log log x)), c > 2√2. Эта точная форма записана по извлечению текста PDF. Её стоит сверить по оригиналу.
- Broucke–Vindas (Math. Z., 2024). RH-системы с ошибкой простых O(1) и O(log log x). RH-подобная регулярность простых не говорит ничего об арифметике.
- Hilberdink–Neamah (Int. J. Number Theory 16 (2020), 1005–1011). Два наибольших из α, β, γ равны и ≥ 1/2. Это верно для всех систем.
- Hilberdink–Lapidus (Acta Appl. Math. 94 (2006), 21–48). Аналог эквивалентности «RH ⟺ ошибка ψ(x)−x» верен в любой системе Бёрлинга. Вывод: круговорот «знак простой стороны = знак нулей» не артефакт Z.

**Вывод 1.** Любой довод, который использует только эйлерово произведение, Λ ≥ 0 и регулярность счётных функций, не докажет RH для Z. Есть системы с теми же аксиомами, где RH ложна.

**Davenport–Heilbronn.**
- Davenport–Heilbronn (1936). Дзета Гурвица ζ(s,a) при трансцендентном a или рациональном a ≠ 1/2 имеет бесконечно много нулей при σ > 1. Идея доказательства — теорема эквивалентности Бора (в изложении Bombieri–Ghosh): фазы простых можно подкручивать свободно.
- Saias–Weingartner (Acta Arith. 140 (2009), 335–344). Если ряд с периодическими коэффициентами не имеет вида P(s)·L_χ(s), то в полосе 1/2 < σ₁ < σ₂ < 1+η число нулей порядка T. Остаётся только одно направление. Равносильность «нулей при σ > 1 нет ⟺ P·L_χ» неверна: у 1+3·2^{−s} нули лежат при σ = log₂3 > 1.
- Righetti (2015). Любой «непростой» многочлен от функций с эйлеровым произведением, при выполнении ортогональности Сельберга, имеет бесконечно много нулей при σ > 1.
- Подробности для конкретной комбинации по модулю 5 (нули вне прямой, доля нулей на прямой) — **не проверено**. На них мы не опираемся.

**Вывод 2.** Функциональное уравнение и Γ-множитель без эйлерова произведения тоже не дают RH. Эйлерово произведение нужно как произведение, чтобы фазы простых были связаны мультипликативностью.

**Важная тонкость.** У систем Бёрлинга DMV нет ни функционального уравнения, ни Γ-множителя. У нашей K они есть. Поэтому барьер Бёрлинга не убивает инструменты, использующие Γ-члены. Он убивает инструменты, использующие только Λ ≥ 0 и данные уровня ПТЧ.

**Что обязан использовать любой доказательный ингредиент.**
1. Эйлерово произведение и мультипликативность (уроки DH, Saias–Weingartner, Righetti).
2. Γ-член и функциональное уравнение (урок DMV).
3. Совместное использование обоих, в одной и той же квадратичной форме. Выполнима ли RH из пары «эйлерово произведение + функциональное уравнение»? В классе Сельберга GRH остаётся гипотезой. Hilberdink–Lapidus прямо пишут, что полного ответа на вопрос о функциональном уравнении у систем Бёрлинга они не дают. Контрпримера к RH с обеими структурами мы не нашли, но это отсутствие свидетельств, а не теорема.
4. Свойство, которого нет у случайных простых. Это наш вывод, не теорема. Основания: Zhang показывает, что RH-подобная малость ошибки достигается случайным выбором. Maier показывает, что настоящие простые скоррелированы через малые простые. Zhu, Замечание 1.6, называет открытую лемму: количественная невозможность выстроить фазы (t·log p)_p в одну сторону, то есть одновременное диофантово приближение для {log p}. Она должна быть специфична для Z. Qualitative-теоремы типа Вейля тут не хватает, они выполняются и для обычных Q-независимых логарифмов.

Оговорка по Zhu. Барьер Теоремы 1.4 относится только к сертификатам, ограничивающим гребёнку поточечно. Это не общий барьер на путь через положительность. Цитата «Passing the resulting wall thus requires cancellation in the prime comb, a concrete arithmetic problem» — формулировка самого автора, не теорема.

---

## 4. Шорт-лист: до 5 кандидатов для знака s_E, s_O

> **Обновление 30.10 после вердикта MARKOV** (`docs/routeB_bus/proshka/MARKOV_AUDIT_2026-10-30.md`):
> кандидат 2 (индекс 1, аналог Ходжа) по формуле (4.19) MARKOV равносилен RH, это крыша, а не короткий путь (PAPER, §4 не проверен независимо).
> Кандидат 1 упирается в член −2·S_L·‖f‖² из (2.1): частичные суммы стартуют около −4√m, то есть знак снова разность; в старом виде не предлагается.
> Новый объект: неравенство Пуанкаре (6.9) для явного скачкового процесса с константой ровно 8; тождество (6.8) проверено численно.
> **SHAKE 30.10** (`docs/routeB_bus/thetagrade_2026-10-28/RESULT.md`): сдвиг log 2 на ε меняет нижний уровень со скоростью O(1) при запасе 1e-29 (m = 12). Сдвиг влево ломает чётный сектор, вправо — нечётный: log 2 зажат с двух сторон в окне ~1e-26. Любое свойство простых «с погрешностью» (решето, средние, плотности) знак не даст; нужна точная арифметика. **Поправка того же дня:** двусторонний зажим держится и для фальшивого атома в любой точке дальше ≈ 0.56, то есть это свойство формы нижних векторов, а не простых.

Все проверки предложены, но не запускались. Параметры m = 2..12 берутся из ваших матриц K_m.

**1. Представление без нулей: m = B₀ + Σ C_n, C_n ≥ 0 (правило 18), через свёртки Λ^{*k}(n)/√n.**
- *Почему может сработать.* При фиксированном v форма <v,Kv> линейна по Λ. Корреляции разных простых входят только через k-кратные свёртки Λ^{*k}/√n ≥ 0. Это ровно структура C_n ≥ 0. Образец знакового механизма — лемма Ландау и приём Рэнкина.
- *Предположение (наш вывод, не источник).* Производящая функция Σ_k(−ζ'/ζ)^k = ζ/(ζ+ζ'), с точностью до сдвига s→s+½. Она сходится только где |ζ'/ζ| < 1. Особенности — нули ζ+ζ', а не нули ζ или ζ'. Ближайшие доказанные теоремы — Speiser (1934) и Levinson–Montgomery (1974): RH ⟺ ζ' не имеет нулей при 0 < σ < ½. Они **не проверено** по первоисточникам.
- *Что нужно.* Теорема из одного эйлерова произведения: знак суммы Σ_{k≥1} Λ^{*k}(n)/√n по окну после вычитания полюса при s=1. Положение нулей ζ+ζ' относительно Re s = ½.
- *Первая проверка.* Для m=2..12 и K=1..K_max посчитать в arb усечённую сумму по k ≤ K и сравнить с вкладом полюса. Смотреть, сохраняют ли s_E, s_O знак при росте K и монотонны ли частичные суммы.
  - ЕСЛИ_A (знак сохраняется, суммы монотонны): появляется односторонний конечный сертификат. Остаётся поправка ранга 2 от полюса.
  - ЕСЛИ_B (колебания порядка 1e-3, как в зонде энтропии на m=40..120): ряд перенормировки не несёт знак. Перейти к кандидату 2.

**2. Разложение «явный положительный член + неотрицательные» по образцу Вейля для функциональных полей.**
- *Почему.* Там знак получается так. Добавляют главный дивизор, цикл Z становится эффективным (целые неотрицательные кратности). Дальше Tr(Z·Z') = d'(Z)·Δ + Y, Y эффективен, и оценка (4g−2)d' − (4g−4)d' = 2d'(Z) ≥ 0 даёт знак. Структура «одно положительное направление, остальное отрицательно» (индекс 1) похожа на наш расклад: полюс ранга 2 плюс PF-блок с одним отрицательным уровнем в G_E.
- *Что нужно.* Аналог эффективного конуса над Z. Connes–Consani–Marcolli прямо пишут, что аналог главных дивизоров остаётся открытым вопросом.
- *Первая проверка.* Для m=2..12 взять подпространство полюса ранга 2 и ограничить K на его ортогональное дополнение. Проверить, определена ли ограниченная форма (критерий индекса 1: есть x с Q(x,x) > 0 и Q ≤ 0 на x^⊥). Сравнить запас ограниченной формы с s_E, s_O. Отдельно проверить в подходящем базисе, образует ли −(PF-блок) Z-матрицу (внедиагональные элементы одного знака).

**3. Перенос Connes–van Suijlekom: простое чётное основное состояние ⇒ вещественные нули преобразования Фурье собственной функции.**
- *Почему.* Ваш PF-блок даёт ровно такую гипотезу: простое изолированное чётное нижнее собственное значение. Теорема в аннотации: тогда все нули преобразования Фурье собственной функции вещественны. Доказательство: Carathéodory–Fejér для тёплицевых матриц, затем теорема Гурвица.
- *Статус.* Препринт (arXiv 2511.23257), доказательство не читано, **не проверено**. Выдача о применимости к системам Бёрлинга и о «PF-типе» — вывод карточки, не источник.
- *Ограничение.* Теорема выполняется для любого распределения. Сама по себе она вещественности нулей ζ не даёт. Нужен мост от нулей собственной функции к нулям ζ. Он эквивалентен RH по силе.
- *Первая проверка.* Для m=2..12 в секторах E и O: простота и зазор нижнего собственного значения, чётность и PF-положительность собственного вектора, вещественность нулей его преобразования Фурье (численно, в arb).

**4. Усреднённые корреляции простых (Type II / билинейные формы, Tao, Matomäki–Radziwiłł, Green–Sawhney) как оценка перекрёстных членов p ≠ q.**
- *Почему.* Это единственный доказанный класс, который видит корреляции разных простых. Для Green–Sawhney (p²+nq²) асимптотика с ошибкой (log log N)²/log N, но статус «не проверено» (формулу не читали).
- *Что нужно.* Знак не получится, только размер перекрёстных членов.
- *Первая проверка.* Для m=2..12 разделить <v,Kv> на диагональ (p=q) и перекрёстные члены (p≠q). Сравнить их размер с запасом 1e-29. Если перекрёстные члены много больше запаса, никакая потеря log^{-A} не годится, и от размерных оценок можно отказаться окончательно.

**5. Неспособность выстроить фазы гребёнки: Zhu, Замечание 1.6.**
- *Почему.* Это точно сформулированная недостающая лемма о Z-специфичной диофантовой структуре {log p}. Сама форма Zhu разделяет полюс ранга 1 и смену знака в нечётном секторе, что совпадает с вашим расщеплением E/O.
- *Что нужно.* Количественное утверждение, что (t·log p)_p не могут одновременно выстроиться. Формально оно того же рода, что и информация в нулях.
- *Первая проверка.* Для m=2..12 найти sup_t гребёнки P_L(t) на фактическом носителе и сравнить с A_L. Посмотреть, на каком t мультипликатор Ψ_L(t) = Re ψ(¼+it/2) − log π − P_L(t) достигает минимума. Совпадение порядка запаса с таблицей Zhu (5,88e-30 при L=1,0, нормировки не сравнивали) — **не проверено**.

**Порядок.** 1, 2, 3, 5, 4. Кандидат 1 дешевле всего проверить и сразу различает ветки. Кандидат 2 — единственный с доказанным аналогом знака, но без перевода на Z. Кандидат 3 даёт структуру, но не мост. Кандидаты 5 и 4 определяют, что именно недостаёт.

---

## 5. Проверка фактов из памяти наблюдателя

**von Koch 1901 — ИСПРАВЛЕНО.**
- Верно: RH ⟺ ψ(x) − x = O(x^{1/2+ε}) при каждом ε > 0 (Ng 2025, ф. 1.3). RH ⇒ ψ(x) − x = O(√x log² x). Значит, ψ(x) − x = O(√x log² x) ⟺ RH.
- Статья: von Koch, Acta Math. 24 (1901), 159–182.
- Расхождение источников. Ng в тексте пишет «1905», но ссылается на работу 1901 года. Wikipedia пишет 1901. Принять 1901.
- Форму π(x) = li(x) + O(√x log x) как эквивалент RH цитируют, но саму цитату не видели. Для π-формы «RH ⇒» подтверждена, «эквивалентно» — не проверено.

**Сельберг, Λ² и чётность — ИСПРАВЛЕНО.**
- Формула симметрии. (1/N)Σ_{n≤N} Λ₂(n) = 2 log N (1+o(1)), где Λ₂ = Λ·log + Λ*Λ = μ*log² (McNamara, Теорема 2.5). Эквивалентно ψ(x) log x + Σ Λ(n) ψ(x/n) = 2x log x + O(x).
- Исправление ссылки. Сельберг, Canad. J. Math. 2 (1950), 66–78 — это про ПТЧ в прогрессиях. Erdős: J. Indian Math. Soc. 13 (1949), 131–144. Работа Сельберга в Annals of Math. 50 (1949) 305–313 — по памяти, не проверено.
- Сито Λ² (квадрат делительной суммы). a(n) = (Σ_{d|n}λ_d)² ≥ 0 при λ₁ = 1 — неравенство и квадратичная форма подтверждены по обзору Soundararajan, уравнения (5)–(6). Страницы оригинала 1947 года (64–67) — только из Wikipedia.
- Проблема чётности. Названа Сельбергом в 1949 г. Пример a_n = 1 + λ(n) (Ford 2005; Maynard, ICM 2022). Любая верхняя оценка ситом для простых промахивается минимум вдвое. Из чистых ситовых данных нет нетривиальной нижней оценки — подтверждено.
- Bombieri (1975–76): асимптотика для Σ a_n f(n) верна ⟺ f одинаково весит числа с чётным и нечётным числом простых делителей. У Λ_k, k ≥ 2, это есть. У самой Λ — нет. Ford 2005 (Trans. AMS 357, 1663–1674): R(ν) при любом фиксированном ν < 1 для этого недостаточно.

**Green–Tao — ПОДТВЕРЖДЕНО.**
- arXiv math/0404188, апрель 2004 г., v6 сентябрь 2007, Annals of Math. 167 (2008), 481–547.
- Три ингредиента: теорема Семереди, принцип переноса, мажоранта Goldston–Yıldırım.
- Уточнения. «Linear equations in primes» (Annals 171 (2010), 1753–1850) сама была условной от GI(s) и MN(s). Безусловной она стала вместе с Green–Tao (Annals 175 (2012), 541–566) и GTZ (Annals 176 (2012), 1231–1372). В GTZ исправлена ошибка (Lemma 13.2). То, что веса мажоранты — квадраты Сельберга, в аннотации не сказано, не проверено.

**Bombieri–Vinogradov — ИСПРАВЛЕНО.**
- Утверждение. Для любого A > 0: Σ_{q≤Q} max_{(a,q)=1} sup_{y≤x} |ψ(y;q,a) − y/φ(q)| ≪_A x (log x)^{−A} + x^{1/2} Q (log xQ)^6 (по заметкам Vaughan). Отсюда уровень ½: Q = x^{1/2}(log x)^{−B}. Годы 1965, Bombieri (Mathematika 12) и A. I. Vinogradov (Izv. AN SSSR 29 (1965)). Номера страниц у Bombieri не проверены.
- Исправление. Фраза «выше ½ ничего не известно» верна лишь для общего утверждения (все модули, все классы, без весов). Для частных случаев уровень выше ½ доказан: Zhang (гладкие модули); Polymath 8a: 1/2+7/300; Stadlmann: 1/2+1/40, принято в Adv. Math.; Maynard: 3/5 для хорошо факторизуемых весов (Mem. AMS 306 (2025)). Lichtman: 66/107, препринт, не проверено. Метка «форма Галлахера» источниками не подтверждена.
- Гипотеза Эллиотта–Хальберстама. Для θ = 1 ложна (Friedlander–Granville, Annals 129 (1989), 363–382).

**Цитата Zhu 2026 — ПОДТВЕРЖДЕНО (препринт).**
- arXiv 2608.24827 v2 (2 сентября 2026), один автор, без рецензии. Слово в слово из текста PDF: «Passing the resulting wall thus requires cancellation in the prime comb, a concrete arithmetic problem.»
- Окно [−0,8; 0,8] подтверждено: Q(f) ≥ 8,9·10⁻¹⁸‖f‖₂², носитель автокорреляции 1,6, то есть 2,3 классического диапазона. Для нечётных f в сертификате Q ≥ 8,2·10⁻¹⁵ (Раздел 6).
- Утверждение первой версии о носителе 2,38 автор сам отозвал (Замечание 3.3).
- Расчёт мы не пересчитывали. Закон затухания −ln λ*(L) подобран, а не выведен. Это слова автора.
- Suzuki 2606.09096 численного окна не называет. Теорема 1.4 лишь «при достаточно малом a > 0» с асимптотикой нижнего собственного значения. Любое окно, приписанное Suzuki в задании, **не проверено**.

---

**Вопрос для владельца.** Выбрать первый кандидат на проверку на m=2..12. Мой выбор — кандидат 1 (частичные суммы Λ^{*k}). Он самый дешёвый, нужен один счёт в arb. Он сразу различает ветки: при ЕСЛИ_A появляется односторонний сертификат, при ЕСЛИ_B идём к кандидату 2 (индекс 1 на дополнении к полюсу). Это ближе всего к цели «самый быстрый путь к доказательству», так как отсекает бесконечный выбор за один прогон.

---

# Приложение: критик полноты (дословно)

**Answer first.** The atlas is strong on size bounds and on barriers. It is thin in exactly the three places our tool needs: proven prime-side correlations, positivity by structure (not by size), and the number-field analogue of Weil's Hodge-index sign. Several statuses are inconsistent between domains. The one item to fix first is Davenport–Heilbronn (DH) (item 2c below).

## (1) Missing landmark classes (max 15)

Sources are the URLs from my searches. Everything else is marked «не проверено» (unverified).

1. **Averaged Hardy–Littlewood for prime pairs (Mikawa; Perelli–Pintz; Bombieri–Davenport tradition).** This is the only proven unconditional statement about Λ(n)Λ(n+h), the correlation between different primes (T5). It holds on average over h, with a small exceptional set.
   - It is also the "BHP-like" proven side of Goldston–Montgomery. The atlas has only the conditional side.
   - Source: https://www.numdam.org/item/CM_1992__82_3_355_0/ (Perelli–Pintz, Compositio 82 (1992) 355–372). Search snippet: "Hardy–Littlewood asymptotic ... for all but a small exceptional set of even shifts h".
   - The exponent range X^{1/3+ε} ≤ H ≤ X came from garbled OCR. «не проверено».
2. **Rudnick–Sarnak n-level correlations of zeros (Duke 1996), plus Hughes–Rudnick and Katz–Sarnak.** These are proven for test functions with restricted Fourier support, and they are derived from prime sums. This is the prime-pair → zero-statistics bridge.
   - Source: https://portal.mardi4nfdi.de/wiki/Publication:1919610. Survey: https://arxiv.org/pdf/2002.00595v1.
   - Degrees n ≥ 4 are conditional on "Hypothesis H". A 2025 claim to remove it (https://arxiv.org/pdf/2507.20653) is «не проверено».
3. **Speiser (1934) and Levinson–Montgomery (1974): RH ⟺ ζ′ has no zeros in 0<σ<1/2.** Levinson–Montgomery also show that ζ and ζ′ have equally many zeros there, up to O(log T).
   - It is a proven, RH-equivalent bridge between a *derivative-type* object and the zero locations. It matters for our case because the Markov renewal series is −ζ′/ζ-structured (see item 3).
   - Sources: https://projecteuclid.org/download/pdf_1/euclid.acta/1485889821 and https://arxiv.org/abs/1902.03064v1. Quote: "The Riemann Hypothesis is equivalent to ζ′(s) having no zeros in 0 < σ < 1/2."
4. **Krein extension / Carathéodory–Toeplitz / Bochner–Schoenberg theory of positive-definite functions on an interval.** Window positivity of K is positive-definiteness of a distribution on (−L, L).
   - The atlas has Bochner only inside the Weil criterion. Krein's extension theorem says: positive definite on an interval ⟹ extends to ℝ. That is a lossless structural statement.
   - «не проверено» (no source opened).
5. **de Branges spaces, Hermite–Biehler, and Lagarias's Li-type positivity.**
   - Present only as a passing mention in the project memory ("SUPPORT = Hermite–Biehler/Lagarias = RH"). The atlas has no entry.
   - «не проверено».
6. **Li's criterion, Nyman–Beurling–Báez-Duarte, Robin.** These are RH-equivalent positive-definite Gram-matrix criteria.
   - Three of the four checkers list them as missing.
   - Why they matter: Nyman–Beurling is a Gram-matrix positivity with an explicit lattice of arithmetic data. It is the closest "lossless Gram" cousin of K.
   - «не проверено».
7. **Arithmetic Hodge index / Arakelov positivity (Faltings–Hriljac; Moriwaki) and Deninger's program, Connes' adèle class space, F_1-geometry.** This is the number-field analogue of the mechanism that proves Weil's RH for curves (positivity from intersection theory, no zeros involved, so no circularity).
   - The atlas has the function-field proof but nothing on its failed or open number-field lift.
   - «не проверено», no source opened.
8. **Mean-value theorems for Dirichlet polynomials (Montgomery–Vaughan 1974) as quantitative orthogonality of p^{it}, and Selberg's central limit theorem for log ζ.**
   - They give proven near-orthogonality of distinct primes in t-averages, with an exact diagonal term.
   - Why they are not enough: they are size bounds (fail T3 and T4). But they define the correct baseline for "what cancellation between primes is provable".
   - «не проверено».
9. **Rankin–Selberg / Selberg orthogonality for GL(n) (proven for automorphic cases).**
   - The atlas lists only the *conjectures* A and B. Rankin–Selberg gives proven Σ_p a(p) conj b(p)/p asymptotics for pairs of L-functions.
   - «не проверено».
10. **Bilinear (Type II) forms: Linnik dispersion; Duke–Friedlander–Iwaniec bilinear Kloosterman-fraction estimates.** These are the proven tools that see two primes jointly. They are lossy.
    - Only the Vaughan identity is in the atlas.
    - «не проверено».
11. **Explicit PNT remainder in the style of Rosser–Schoenfeld / Dusart / Platt–Trudgian / Fiori–Kadiri–Swidinsky.** This gives a computable sign-safe envelope on [0, X]. Our "no slack" requirement (T4) rules it out, but it is the standard comparison point.
    - Three checkers list it. «не проверено».
12. **Levinson-type and Selberg-class converse theorems (Hamburger; Hecke; Kaczorowski–Perelli).** They state what the functional equation alone fixes. They are needed to say which of "Euler product" and "functional equation" a tool actually uses.
    - «не проверено».
13. **Ng, Gonek–Montgomery, Gallagher: true size of (ψ(x)−x)/√x and its moments.** They connect the prime-side variance to the zero side. «не проверено».
14. **Beurling PNT positive theory (Diamond–Zhang monograph).** The atlas has the counterexamples but not the positive theory that says which hypotheses the Beurling barrier does and does not constrain.
    - «не проверено».
15. **Guth–Maynard (2024), published in Annals per a search listing, and zero-density → short-interval primes.** The atlas lists it in some domains but not in all. Only "proven/size" matters here. «не проверено» for the publication status.

Note on the sign requirement. Only one prime-side sign datum in the entire atlas is *used*, which is Λ ≥ 0 (de la Vallée Poussin's 3 + 4cos t + cos 2t; Landau's lemma). Everything in the Markov picture is the same datum. The atlas should say so explicitly.

## (2) Overclaimed or misclassified items

a. **Inconsistent `gives` for the same theorem across domains.**
   - Littlewood is SIGN in the distribution domain and BARRIER in the multiplicative one.
   - Rubinstein–Sarnak is SIGN in the distribution domain and SIZE in the progressions one.
   - Tao's logarithmically averaged Chowla is SIZE in the sieve and patterns domains and STRUCTURE in the frontier one.
   - Selberg's Λ² sieve is SIGN in the sieve domain and SIZE in the multiplicative one. The *device* is a sign by squaring, but the *output* is a size bound.
   - The Weil-type items are inconsistent in the same way.
   - Fix: split `gives` into "mechanism" (sign by squares, by positivity of coefficients) and "output" (size, existence, equivalence).

b. **Davenport–Heilbronn verdicts conflict.** The zeros domain says REFUTED, the multiplicative domain says UNVERIFIED, and the barriers domain says CONFIRMED.
   - REFUTED looks wrong. A 2024 arXiv paper says "in the late 90s, A. Selberg proved that a positive proportion of non-trivial zeros of the Davenport–Heilbronn function lie on the critical line" (https://arxiv.org/pdf/2411.18492 or https://arxiv.org/html/2501.00551v1; my search snippet was cut off, so I do not know which of the two carries the sentence).
   - Voronin and Karatsuba lower bounds are also in the search results (https://www.mathnet.ru/eng/cheb850).
   - Recommended status: «не проверено», not REFUTED.
   - The barrier use of DH (functional equation without Euler product, off-line zeros exist) is the safe part. The "positive proportion on the line" part needs the primary Selberg source.

c. **Alpoge–Furman 2026 (AI-generated, unrefereed).** It is the nearest neighbour of our problem: a rank-trace argument on a finite compression of the Weil form.
   - It must not carry a "barrier" label ("band-width 1", "two thirds = all") as if proven. Your own checkers mark those quotes UNVERIFIED for v2.
   - Lamzouri's competing proof is also unrefereed.
   - Both should have status PREPRINT, with "gives: TOOL" for the claim only, and no downstream use.

d. **Bombieri 2000 `lossless: true`.** The "lossless" tag and the circularity reading are the item author's. Mark them as interpretation.

e. **Yoshida 1992 "only genuine unconditional K ≥ 0".** This is overstated. Bombieri's re-proof and Zhu's certified computation (preprint) also exist.

f. **Zhu 2026, "Passing the resulting wall thus requires cancellation in the prime comb".** The atlas treats it as a claim, but it is the author's own abstract wording. Also check the support figures: the zeros domain says 1.6 and the multiplicative domain says [−0.8, 0.8] (consistent only if the support is a full width of 1.6).

g. **Beurling YES/NO columns.** They are inferences by the item authors in at least four domains (zeros, frontier, multiplicative, sieve).
   - A concrete problem: the Diamond–Montgomery–Vorhauer (DMV) barrier has *no functional equation and no Γ-factor*. Our K has both.
   - So the Beurling barrier does not kill tools that use the Γ-terms. It kills tools that use only Λ ≥ 0 plus PNT-level data. Say this in the atlas.

h. **Weil criterion date.** It is 1952, not 1941/48 (already flagged by one checker).

i. **Primary papers not opened for most "CONFIRMED" items.** CONFIRMED means "consistent with a secondary source" here. Rename the verdict class.

## (3) The one question the atlas does not answer

**Is there a proven, zero-free, exact representation of the window-localized renewal measure of the prime walk, with its pole term carrying its sign?**

Why this is the question. This is my own derivation. I did not find it in any source, so treat it as предположение.

- For fixed v the form ⟨v, Kv⟩ is *linear* in Λ. Correlations between different primes can enter only through resolvent or Neumann-series terms. These are the k-fold Dirichlet convolutions Λ^{*k}(n)/√n, which are ≥ 0 termwise. That is exactly the "C_n ≥ 0" structure.
- The generating function of the walk is Σ_k (−ζ′/ζ)^k = 1/(1+ζ′/ζ) = ζ/(ζ+ζ′), up to the shift s → s+½ for the 1/√n weight. It converges only where |ζ′/ζ| < 1.
- Its singularities are the zeros of ζ+ζ′ = e^{−s}(e^{s}ζ)′. These are neither the zeros of ζ nor of ζ′.
- Speiser and Levinson–Montgomery (item 3 above) are the nearest proven theorems. They address ζ′, not ζ+ζ′.

So the missing atlas entry is a theorem of the following type, proven from the Euler product alone with no use of zeros:

- a sign for Σ_{k≥1} Λ^{*k}(n)/√n summed over n in a window, after subtraction of the pole contribution at s = 1, and
- the location of zeros of ζ+ζ′ relative to Re s = ½.

Cheapest probe, which I did not run. For m = 40..120 and small windows, compare the arb-computed truncated Σ_k Λ^{*k} mass with the residue term. See whether s_E and s_O keep their signs for k up to a modest bound.

- ЕСЛИ_A (the signs persist and the partial sums are monotone): the Markov/renewal picture gives a one-sided finite certificate. The remaining question is the pole's rank-2 correction.
- ЕСЛИ_B (the partial sums fluctuate at the 1e-3 level seen in the entropy probe): the renewal series is not the sign carrier. Go back to the Krein/Gram route (items 4–6).

## Gaps and conflicts

- I opened no primary papers. Everything above rests on search snippets and on your checkers' reports.
- Statements about Guth–Maynard, Alpoge–Furman, Lamzouri and Rezvyakova are from the checkers or from search snippets only. «не проверено».
- Conflicting verdicts for DH and for Rubinstein–Sarnak are listed in (2b) and (2a).

Sources: [Levinson–Montgomery, Acta](https://projecteuclid.org/download/pdf_1/euclid.acta/1485889821), [Garunkštis–Tamošiūnas arXiv:1902.03064](https://arxiv.org/abs/1902.03064v1), [Rudnick–Sarnak entry](https://portal.mardi4nfdi.de/wiki/Publication:1919610), [Rudnick–Sarnak survey arXiv:2002.00595](https://arxiv.org/pdf/2002.00595v1), [On Hypothesis H arXiv:2507.20653](https://arxiv.org/pdf/2507.20653), [Perelli–Pintz, Compositio 82](https://www.numdam.org/item/CM_1992__82_3_355_0/), [DH zeros, Chebyshevskii Sbornik](https://www.mathnet.ru/eng/cheb850), [Rezvyakova arXiv:2411.18492](https://arxiv.org/pdf/2411.18492), [arXiv:2501.00551](https://arxiv.org/html/2501.00551v1).