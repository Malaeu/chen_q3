# ЗАПРОС ДЛЯ ПРОШКИ: Докажи Гипотезу Римана

---

## ЗАДАЧА

Построй полное **Proof Dossier** для следующей теоремы:

**Теорема (Гипотеза Римана).**
Для всех \(s \in \mathbb{C}\) с \(0 < \text{Re}(s) < 1\):
если \(\zeta(s) = 0\), то \(\text{Re}(s) = 1/2\).

**Статус:** Доказательство в стандартной математике (ZFC + комплексный анализ).

---

## КОНТЕКСТ: Определения

### Критическая полоса и прямая
- \(\text{CriticalStrip} = \{s \in \mathbb{C} : 0 < \text{Re}(s) < 1\}\)
- \(\text{CriticalLine} = \{s \in \mathbb{C} : \text{Re}(s) = 1/2\}\)

### Конус Вейля
\[
\text{Weil\_cone} = \{\Phi : \mathbb{R} \to \mathbb{C} \mid \Phi \text{ непрерывна}, \text{supp}(\Phi) \text{ компактен}, \Phi(-x) = \overline{\Phi(x)}\}
\]

### Функционал Q (явная формула Гинанда-Вейля)
Для \(\Phi \in \text{Weil\_cone}\):
\[
Q(\Phi) = Q_{\text{arch}}(\Phi) + Q_{\text{prime}}(\Phi)
\]
где:
- \(Q_{\text{arch}}\) — архимедова часть (через дигамма-функцию)
- \(Q_{\text{prime}}\) — простая часть (через простые числа)

### Архимедова плотность
\[
a(\xi) = \log \pi - \text{Re}\,\psi\left(\frac{1}{4} + i\pi\xi\right)
\]
где \(\psi = \Gamma'/\Gamma\) — дигамма-функция.

### Окно Фейера × тепловое
\[
w(B, t, \xi) = \max(0, 1 - |\xi|/B) \cdot e^{-4\pi^2 t \xi^2}
\]

### Взвешенная плотность
\[
g(B, t, \xi) = a(\xi) \cdot w(B, t, \xi)
\]

### Архимедов символ (периодизация)
\[
P_A(B, t, \theta) = 2\pi \sum_{m \in \mathbb{Z}} g(B, t, \theta + m)
\]

---

## КОНТЕКСТ: Ключевые константы

| Константа | Значение | Смысл |
|-----------|----------|-------|
| \(B_{\min}\) | 3 | Порог ширины полосы |
| \(t_{\text{sym}}\) | 3/50 = 0.06 | Параметр теплового сглаживания |
| \(c_*\) | **1.5** | Арифметический пол (КРИТИЧНО!) |
| \(C_{SB}\) | 4 | Константа Сегё-Бёттхера |

---

## КОНТЕКСТ: Аксиомы Tier-1 (классические результаты)

### Axiom W: Критерий Вейля (1952)
\[
\left(\forall \Phi \in \text{Weil\_cone},\, Q(\Phi) \geq 0\right) \iff \text{RH}
\]
**Источник:** Weil, A. (1952). Sur les "formules explicites" de la théorie des nombres premiers.

### Axiom EF: Явная формула Гинанда-Вейля (1948)
\[
\forall \Phi \in \text{Weil\_cone},\quad Q(\Phi) = Q_{\text{arch}}(\Phi) + Q_{\text{prime}}(\Phi)
\]
**Источник:** Guinand, A.P. (1948). A summation formula in the theory of prime numbers.

### Axiom SB: Оценка Сегё-Бёттхера (1958)
Для положительного символа \(\sigma \in C(\mathbb{T})\):
\[
\lambda_{\min}(T_n(\sigma)) \geq c_0(\sigma) - O(1/n)
\]
где \(c_0(\sigma) = \min_\theta \sigma(\theta)\).

**Источник:** Grenander, Szegő. Toeplitz Forms and Their Applications (1958).

### Axiom Schur: Тест Шура (1911)
Если ядро \(K(x,y)\) удовлетворяет:
\[
\sup_x \int |K(x,y)|\,dy \leq M \quad\text{и}\quad \sup_y \int |K(x,y)|\,dx \leq M
\]
то \(\|T_K\|_{\text{op}} \leq M\).

### Axiom RKHS: Позитивность в RKHS (Aronszajn, 1950)
\[
\forall f \in \mathcal{H},\quad \langle f, f \rangle_{\mathcal{H}} \geq 0
\]

---

## КОНТЕКСТ: Аксиомы Tier-2 (результаты проекта Q3)

### Axiom A3: Архимедов пол
\[
\forall B \geq B_{\min},\quad \forall \theta \in [-1/2, 1/2],\quad P_A(B, t_{\text{sym}}, \theta) \geq c_* = 1.5
\]

**Доказательство:** Через sample-point bounds:
- \(a(1/2) \geq 0.68\)
- \(a(3/2) \geq -0.45\)
- \(a(5/2) \geq -1.00\)
- Хвост \(\leq 10^{-5}\)

### Axiom A1': Плотность Фейера × тепловых
\[
\forall \varepsilon > 0,\, \forall \Phi \in W_K,\, \exists (B, t):\quad \|\Phi - \Phi_{B,t}\|_K < \varepsilon
\]

### Axiom A2: Липшицевость Q
\[
\forall K > 0,\, \exists L:\quad \forall \Phi_1, \Phi_2 \in W_K,\quad |Q(\Phi_1) - Q(\Phi_2)| \leq L \cdot \|\Phi_1 - \Phi_2\|_K
\]

### Axiom RKHS-C: Сжатие простого оператора
\[
\forall t \geq t_{\text{sym}},\quad \|T_{\text{prime}}(t)\|_{\text{op}} < 1
\]

### Axiom T5: Перенос на компакт
\[
\forall K > 0,\, \forall \Phi \in W_K,\quad Q(\Phi) \geq c_*/4
\]

---

## ПЛАН ДОКАЗАТЕЛЬСТВА (Roadmap)

```
Шаг 1: Элементы конуса Вейля имеют компактный носитель → работаем с W_K

Шаг 2: Аппроксимация Фейером × тепловыми (A1') → приближаем любое Φ ∈ W_K

Шаг 3: Q непрерывен (A2) → Q(Φ) = lim Q(Φ_{B,t})

Шаг 4: Для Φ_{B,t} разлагаем Q = Q_arch + Q_prime

Шаг 5: Q_arch ≥ c_* (A3) → через оценку Тёплица

Шаг 6: Q_prime ≥ -c_*/4 (RKHS-C) → через сжатие ||T_P|| < 1

Шаг 7: Вместе: Q(Φ_{B,t}) ≥ c_* - c_*/4 = 3c_*/4 > 0

Шаг 8: Предельный переход: Q(Φ) ≥ 0 для всех Φ ∈ Weil_cone

Шаг 9: Применяем критерий Вейля → RH доказана
```

---

## ТВОЯ ЗАДАЧА

Используя приведённый контекст (определения, аксиомы, план), построй **полное Proof Dossier** по следующей структуре:

### Обязательные секции:

1. **§0. Theorem Title and Status** — точная формулировка + статус
2. **§1. Formal Statement** — с явными кванторами
3. **§2. Definitions and Notation** — все термины
4. **§3. Dependencies** — таблица зависимостей с источниками
5. **§4. Proof Plan** — roadmap 2-6 строк
6. **§5. Lemmas** — промежуточные леммы с полными доказательствами
7. **§6. Main Proof** — пошаговое доказательство
8. **§7. Audit-Edge Check** — проверка на типичные ошибки
9. **§8. Appendix** — ссылки на литературу

### Критические правила:

- **НИКОГДА** не начинай с вывода — сначала контекст, потом результат
- **КАЖДЫЙ** объект определён до использования
- **КАЖДЫЙ** вывод обоснован ссылкой
- **НЕТ** скрытых предположений

### AUDITOR'S KILL LIST (РАСШИРЕННЫЙ)

**ВНИМАНИЕ:** Это список типичных ошибок в попытках доказать RH (1859-2025). Каждая из них убила множество "доказательств" — от cranks до Fields Medalists.

---

#### ЧАСТЬ A: Базовые ошибки (crank proofs)

| # | Ошибка | Описание | Пример провала |
|---|--------|----------|----------------|
| E1 | **Циклическая логика** | Предполагают то, что доказывают | StackExchange 2012: "Assume RH to prove RH" |
| E2 | **Неконтролируемый log** | Комплексный логарифм без выбора ветви | Ошибки с \(\log \zeta(s)\) на критической полосе |
| E3 | **Большие параметры** | Игнорируют поведение при \(t \to \infty\) | Divergent bounds при \(\text{Im}(s) \to \infty\) |
| E4 | **Численное вместо аналитики** | "Проверил 10^13 нулей" ≠ доказательство | Odlyzko verification ≠ proof |
| E5 | **Ложные обобщения** | С конечных полей на \(\mathbb{C}\) | Weil для curves ≠ Weil для \(\zeta\) |
| E6 | **Арифметические ошибки** | Простые вычислительные ошибки | Budden 2025: AI-generated slop |
| E7 | **Incoherent arguments** | Нет понимания предмета | "Proof" без знания аналитической теории чисел |
| E8 | **Ложные положительные** | Тесты показывают "да", но это не доказательство | Weak D-analogies |
| E9 | **Curve fitting** | Подгонка под известные нули | Fitting first 100 zeros ≠ all zeros |

---

#### ЧАСТЬ B: Ошибки respected mathematicians

| # | Ошибка | Описание | Исторический пример |
|---|--------|----------|---------------------|
| E10 | **Weak solutions fail** | Слабые решения неприменимы | **Atiyah 2018**: Heidelberg presentation, debunked |
| E11 | **Positivity not satisfied** | Операторные нормы не выполняются | **de Branges 2010**: Conrey & Li debunk |
| E12 | **Vacuous bounds** | Оценки пусты при больших N | **Turán**: Large N estimates vacuous |
| E13 | **Convexity errors** | Выпуклость нарушена при больших параметрах | **Blinovsky**: Convexity fail at large params |

---

#### ЧАСТЬ C: Специфические для Q3/Weil approach

| # | Ошибка | Где проверять | Как избежать |
|---|--------|---------------|--------------|
| E14 | **Скрытые кванторы** | "пусть малое ε" | Явно: ε зависит от чего? |
| E15 | **Перестановка lim/∫/Σ** | Шаги 3, 8 | Dominated convergence theorem |
| E16 | **∃ ↔ ∀ путаница** | Аксиомы | Чётко: universal или existential? |
| E17 | **Граничные случаи** | θ = ±1/2, B = B_min | Замкнутые интервалы |
| E18 | **Деление на ноль** | Eigenvalue bounds | n ≥ 1 required |
| E19 | **Неявная компактность** | W_K, Weil cone | Compact support explicit |
| E20 | **Циклическая зависимость** | Proof chain | Linear: A3 → T5 → Main → RH |
| E21 | **Выбор ветви log/√** | digamma, a(ξ) | Re(z) > 0 satisfied |
| E22 | **Численное → общее** | c_* = 1.5 | Rigorous: sample bounds + tail |
| E23 | **Logarithmic growth** | a(ξ) при ξ → ∞ | digamma: DLMF §5.11, bounded tail |

---

#### ИНТУИЦИЯ "НА ПАЛЬЦАХ" (для E23)

**Критика:** "Твоя функция \(a(\xi)\) растёт как логарифм. На бесконечности всё взорвётся!"

**Ответ:** Нет, потому что **экспонента бьёт логарифм**.

**Метафора трубы:**
1. Да, "грязь" (вариация \(a(\xi)\)) растёт — напор воды увеличивается
2. НО! Гауссовский вес \(w(\xi) = e^{-4\pi^2 t \xi^2}\) — труба **сужается в миллион раз быстрее**
3. **Итог:** Сколько бы воды ни лил, через сужающуюся трубу пролезет только **конечное количество капель**

**Математически:**
\[
a(\xi) \sim \log(\xi) \quad \text{(растёт)}
\]
\[
w(\xi) \sim e^{-\xi^2} \quad \text{(убывает НАМНОГО быстрее)}
\]
\[
a(\xi) \cdot w(\xi) \to 0 \quad \text{при } \xi \to \infty
\]

**Конкретно:** Хвост \(\int_{5/2}^\infty |a(\xi)| \cdot w(\xi)\,d\xi \leq 10^{-5}\)

Это число доказывает что "взрыва" нет. Если бы был взрыв — было бы ∞

---

#### ИСТОРИЧЕСКИЕ ПРОВАЛЫ (для контекста)

| Год | Автор | Ошибка | Источник |
|-----|-------|--------|----------|
| 2018 | **Atiyah** (Fields Medal) | Weak solutions, logic gaps | Science.org, Times interview |
| 2010 | **de Branges** | Operator positivity fail | MathOverflow 2017, Conrey debunk |
| 1980s | **Turán** | Vacuous large N bounds | — |
| 2020s | **Blinovsky** | Convexity at large params | — |
| 2025 | **Budden** | AI-generated, no end-to-end | X roast, no peer review |

---

#### В ТВОЁМ §7 ПРОВЕРЬ КАЖДЫЙ ПУНКТ E1-E23:

Для каждой ошибки E_i напиши:
- **Где в доказательстве** это место
- **Почему ошибка НЕ возникает** (конкретная ссылка на аксиому/лемму)
- **Если применимо**: численная проверка

---

## ФОРМАТ ОТВЕТА

Markdown с LaTeX. Секции §0-§8. Каждое доказательство леммы заканчивается ∎. Основное доказательство заканчивается ∎.

**Начинай!**
