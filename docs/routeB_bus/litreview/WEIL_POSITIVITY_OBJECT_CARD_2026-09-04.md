# Объект: позитивность Вейля — что доказано сверху, что снизу, и где стоит окно CCM

Карточка объекта по методу «стена = объект» (memory `wall-as-object-method`).
Собрана 2026-09-04 для судейства вопроса:

> **«λ₁(K(m,N)) > 0 для всех m» — это эквивалент RH (позитивность Вейля, ограниченная
> на семейство окон CCM), или строго слабее?»**

Источники: локальные PDF в `docs/routeB_bus/litreview/pdfs/` (читаны глазами через
текстовый слой), плюс веб-верификация библиографии. Всё, что не сверено с
первоисточником, помечено **UNVERIFIED**.

---

## ⚠️ TL;DR — три числа и одна граница

| величина | значение | локатор |
|---|---|---|
| доказанное окно (безусловно) | `a ≤ (log 2)/2`, т.е. `λ ≤ √2`, т.е. `m = λ² ≤ 2`, длина окна `L = log m ≤ log 2 ≈ 0.693` | Yoshida 1992 Thm 1 (p.310); Bombieri 2000 Thm 12 (p.226); Connes–Consani 2021 Thm 1 |
| наше окно | `m = 13`, `L = log 13 ≈ 2.565`, 9 простых степеней внутри | CCM `arXiv:2511.22755` §6 |
| разрыв | ×3.7 по `L`; ровно тот переход, где сумма по простым перестаёт быть пустой | — |

**Доказанная область — в точности та, где сумма по простым ПУСТА.** Ни одного
безусловного результата о позитивности Вейля на окне, содержащем хотя бы одно простое,
в литературе нет. Сам Connes пишет это прямым текстом (см. §2c).

---

## 1. Критерий Вейля: точная формулировка и класс тестовых функций

### 1.1 Первоисточник

`WEIL-1952`: A. Weil, «Sur les "formules explicites" de la théorie des nombres premiers»,
*Comm. Sém. Math. Univ. Lund [Medd. Lunds Univ. Mat. Sem.]* **1952**, Tome Supplémentaire,
252–265. Продолжение: A. Weil, «Sur les formules explicites de la théorie des nombres»,
*Izv. Akad. Nauk SSSR Ser. Mat.* **36** (1972), 3–18.
*(Ссылка сверена по трём независимым библиографиям: Suzuki `2606.09096` [15],[16];
CCM `2511.22755` [16]; Connes `2602.04022` [109],[110]. Самих статей Вейля мы не читали —
**UNVERIFIED** на уровне текста, VERIFIED на уровне библиографии.)*

### 1.2 Формулировка в аддитивной (log) переменной — Suzuki

**ЛОКАТОР:** `arXiv:2606.09096` (Suzuki, «Weil's quadratic form via the screw function»),
§1.1, стр. 1–2.

**ДОСЛОВНО:**

> For test functions `f`, the Weil functional `f ↦ W(f)` is defined by
> `W(f) := ∫_{−∞}^{∞} f(x)(e^{x/2} + e^{−x/2})dx − Σ_{n≥1} (Λ(n)/√n) f(log n) − Σ_{n≥1} (Λ(n)/√n) f(−log n)
> − (log 4π + C₀)f(0) − ∫_0^∞ {f(x) + f(−x) − 2e^{−x/2}f(0)} e^{x/2}dx/(e^x − e^{−x})`
> … our primary object of interest is the symmetric (or Hermitian) quadratic form
> `Q_W(v₁,v₂) := W(v₁ * ṽ₂)`, `Q_W(v) := Q_W(v,v)`.

> A fundamental result due to Weil [15] states that RH is equivalent to the condition that
> **`Q_W(v) ≥ 0` for all `v ∈ C_c^∞(R)`**, a property known as Weil's positivity criterion
> for RH (although Weil did not formulate the criterion in terms of compactly supported
> smooth test functions; see [15, 16] and [13, Section 3.2]).

**Важно:** приписка в скобках — сам Suzuki отмечает, что класс `C_c^∞(R)` не является
классом Вейля, а стандартной современной переформулировкой.

### 1.3 Формулировка в мультипликативной переменной — Connes–Consani

**ЛОКАТОР:** `arXiv:2006.13771` (Connes–Consani, «Weil positivity and Trace formula, the
archimedean place»), Introduction, стр. 1–2, формулы (1)–(2); Appendix C, Proposition C.1.

**ДОСЛОВНО:**

> It was shown by A. Weil [33] that the Riemann Hypothesis (RH) is equivalent to the
> negativity of the right-hand side of the Riemann-Weil explicit formula …
> `f̃(0) − Σ_{ρ∈Z} f̃(ρ) + f̃(1) = Σ_v W_v(f)`, `f̃(s) := ∫_0^∞ f(x)x^{s−1}dx` (1)
> … for a precise class of complex-valued test functions on the positive half-line, of the
> form `f(x) = ∫_0^∞ g(xy)ḡ(y)dy`, `g̃(0) = 0`, `g̃(1) = 0`.

> In fact, following [34], **it is enough to prove the negativity of the right-hand side of
> (1) for functions `g` with compact support** in the (locally compact) multiplicative group
> `R*₊ = (0,∞)`. Furthermore, given any finite set of complex numbers `F ⊃ {0,1}`,
> `F ∩ Z = ∅`, using the notation `g^♯(x) := x^{−1}g(x^{−1})`, `ḡ(x) = g(x)`, one has
> (Appendix C, Proposition C.1)
> **`RH ⟺ Σ_v W_v(g * ḡ^♯) ≤ 0, ∀g ∈ C_c^∞(R*₊) | g̃(z) = 0, ∀z ∈ F`** (2)

> The key point being that the right-hand side of the explicit formula, when evaluated on a
> test function `f` with compact support, **involves only finitely many primes.**

### 1.4 Усиление Бомбьери (строгое неравенство, без условий обнуления)

**ЛОКАТОР:** Bombieri, «Remarks on Weil's quadratic functional in the theory of prime
numbers, I», *Rend. Lincei (9) Mat. Appl.* **11** (2000) no. 3, 183–233
(`eudml.org/doc/252338`), §3 «A necessary and sufficient condition for the Riemann
Hypothesis», **стр. 191, Theorem 1**. PDF: `pdfs/bombieri_weil_quadratic_functional_2000.pdf`.

**ДОСЛОВНО:**

> We have the following strengthening of Weil's criterion.
> **Theorem 1.** The Riemann Hypothesis holds if and only if
> `Σ_ρ ĝ(ρ) ĝ(1−ρ) > 0` (3.1)
> for every complex-valued `g(x) ∈ C₀^∞((0,∞))`, not identically 0.

И там же, стр. 193–194 (после Theorem 2):

> Moreover, the Riemann Hypothesis is equivalent to the statement that `T[f * f^*] ≥ 0` on
> `C₀^∞((0,∞))`, **with equality only if `f` is identically 0.**
> We have in fact proved a little more, namely that the positivity of the Weil quadratic
> functional is equivalent to the statement that `T[g_{n,ε}] > 0` for every positive integer
> `n` and `ε > 0`.

### 1.5 Локализация Yoshida: чётный/нечётный сектор — ЛОВУШКА для нас

**ЛОКАТОР:** Yoshida, «On Hermitian Forms attached to Zeta Functions», *Adv. Stud. Pure
Math.* **21** (1992), 281–325, DOI `10.2969/aspm/02110281`, §1, **стр. 285, Proposition 1**.
PDF: `pdfs/yoshida_hermitian_forms_1992.pdf`.

**ДОСЛОВНО:**

> **Proposition 1.**
> (1) `T_k` is **oddly** positive definite if and only if R.H. holds for `ζ_k(s)`.
> (2) `T_k` is **evenly** positive definite if and only if R.H. holds for `ζ_k(s)` **with
> possible exceptions of real zeros**, i.e. every non-trivial zero of `ζ_k(s)` lies on the
> critical line if it is not real.

**ПОЧЕМУ ЭТО НАША ЛОВУШКА.** CCM работают **только в чётном секторе** (`γξ = ξ`,
Definition 5.3). По Proposition 1(2) даже полная чётная позитивность даёт RH *с точностью
до вещественных нулей*. Для `ζ(s)` над `ℚ` это безобидно (вещественных нулей в `(0,1)` нет
классически), но в цепочке эквивалентностей этот шаг нельзя пропускать молча — он требует
отдельной ссылки, а не «очевидно».

И там же, локализация по носителю — **стр. 282, определение `C(a)` и утверждение**:

> `C(a) = { φ ∈ C_c^∞(R) | supp(φ) ⊆ [−a,a] }`. Then **R.H. is equivalent to the positive
> definiteness of `( , )|C(a)` for every `a > 0`** (cf. Proposition 2). It can easily be
> verified that `( , )|C(a)` is positive definite **if `a` is sufficiently small.**

Пространство `K(a)`, которое Yoshida вводит следом, — **это в точности базис CCM**
(периодические на окне, обрезанные, т.е. фурье-моды окна):

> `K(a) = { φ | φ(x) = f(x) for |x| ≤ a, φ(x) = 0 for |x| > a` with `f ∈ C^∞(R)` which has
> period `2a` `}`
> `K_N(a) = { φ ∈ K(a) : ∫_{−a}^{a} φ(x)exp(πinx/a)dx = 0` for all `n ∈ ℤ, |n| ≤ N }`

---

## 2. ДОКАЗАННЫЕ РЕЖИМЫ БЕЗ RH

### 2a. Носитель внутри `(−log 2, log 2)` / мультипликативно `[1/√2, √2]` — сумма по простым пуста

Три независимых доказательства **одного и того же режима**. Все три упираются в одну и ту
же границу — ту, где появляется простое `p = 2`.

#### (i) Yoshida 1992 — первый, и единственный с ЯВНЫМ числом

**ЛОКАТОР:** Yoshida 1992, §6 «A numerical example», **стр. 310, Theorem 1**.

**ДОСЛОВНО** (текстовый слой; формула-картинка потеряна OCR, восстановлена по контексту
§6 (6.1) и по пересказу во введении):

> **Theorem 1.** Let `a = log 2/2`. We have ⟨`(φ,φ) > 0`⟩ for every `φ ∈ K(a)`, where
> equality holds if and only if `φ = 0`.

Введение, **стр. 283**, о том же:

> In §6, we shall give a detailed sample computation, though it does not follow the algorithm
> faithfully, when `a = log 2/2`: We find `( , )|K(a)` is **positive definite for
> `a ≤ log 2/2`** (Theorem 1). The idea is to calculate the hermitian matrix on `W(a)` with
> sufficient approximation for a suitably chosen `N`.

**Механизм:** конечная матрица + оценка хвоста. §6 сводит дело к **позитивности явной
`10 × 10` матрицы `U`** (стр. ~305–307: «it suffices to prove the positive definiteness of
the `10 × 10` …», «`U` is positive definite if we can take `ε = 1/40` in (6.15)»), плюс
хвостовая оценка с `C² = 0.3321…` для `k ≥ 200`. То есть это **конечное вычисление** —
структурно ровно то же, что наш `λ₁(K(m,N))`, только на `m = 2`.

#### (ii) Bombieri 2000 — с явной ФОРМОЙ нижней границы

**ЛОКАТОР:** Bombieri 2000, §12 «Sets of positivity», **стр. 226, Theorem 12**.

**ДОСЛОВНО:**

> **Theorem 12.** If `F(x)` has compact support in an interval `I` of length `|I| < log 2`
> we have
> `T[F(x) * F(−x)] = Σ_γ F̂(γ)F̂(γ) ≥ ( log(1/|I|) − log log(1/|I|) − O(1) ) ‖F‖²`.

**ДОСЛОВНО** (начало доказательства, тот же лист):

> Since `G(x) = F(x) * F(−x)` remains unchanged if we replace `F(x)` by a translation
> `F(x+c)`, we may assume that `F(x)` is supported in the interval `[−a/2, a/2]` with
> `a < log 2`. Then `G(x)` is supported in `[−a,a] ⊂ (−log 2, log 2)`. **Thus in the Explicit
> Formula as above for `T[G]`, the contribution of the sum involving `Λ(n)` vanishes.**

**Границы применимости.** Правая часть положительна только при достаточно малом `|I|` —
`O(1)` не выписан. Так что «явная форма» ≠ «явный порог». Именно этот `O(1)` и отделяет
Bombieri от числа.

И §12 открывается признанием приоритета:

> In this section we prove the positivity statement needed for the proof of the Corollary to
> Theorem 8. **Another proof can be found in Yoshida's paper [5].**

**Тот же режим в §10, стр. 221** (там, где он нужен Бомбьери по делу):

> On the other hand, since this holds for any `t > 0`, we can choose `t < ½ log 2`, hence
> `M < √2`. It follows that `f * f^*` has compact support in `(1/2, 2)` and in particular in
> Weil's Explicit Formula **the terms involving `Λ(n)` are absent.**

Введение (**стр. 184**) — пересказ Yoshida, где явно назван проверенный им параметр:

> Moreover, he shows how the positivity of this functional for functions supported in a fixed
> interval `[−t,t]` can be reduced to a finite calculation (depending on `t`), and
> **verifies this positivity for `t = (log 2)/2`.**

#### (iii) Suzuki 2026 — асимптотика вместо порога

**ЛОКАТОР:** `arXiv:2606.09096`, **Theorem 1.4** (стр. 5), доказательство §5.1 (стр. 19).

**ДОСЛОВНО:**

> **Theorem 1.4.** For sufficiently small `a > 0`, the lowest eigenvalue `λ_a` is positive,
> simple, and satisfies
> `λ_a = log(1/a) + µ₁ − log(2π) + ψ(2) − 1 + O(a)` as `a → 0+`, for some constant `µ₁ > 0`.
> Furthermore, the corresponding eigenfunction is **even**.

**ДОСЛОВНО** (§5.1, где видна граница разложения — та же `log 2`):

> From (4.5), we have `R(a,v) = log(1/a) − (2A+1) + L(v)/‖v‖² + O(a)` (5.1)
> **for `0 < a < (1/2)log 2`** and `v ∈ H₀¹(−1,1)` …
> Therefore, **for sufficiently small `a > 0`**, we obtain `λ_a = inf_w R(a,w) > 0`.

**Что это добавляет и чего не добавляет.** Добавляет: та же логарифмическая форма, что у
Бомбьери, но выведенная из screw-функции, и **безусловно** («none of them depends on RH»,
§1.2). Не добавляет: `µ₁ > 0` не вычислена, «sufficiently small» не оцифровано. Порога
по-прежнему нет.

### 2b. Connes–Consani: тот же интервал, но КОНЦЕПТУАЛЬНАЯ причина

**ЛОКАТОР:** `arXiv:2006.13771`; опубликовано: *Selecta Math. (N.S.)* **27** (2021), Paper
No. 77, DOI `10.1007/s00029-021-00689-4`. PDF: `pdfs/2006.13771.pdf`.

**Точный интервал: `[2^{−1/2}, 2^{1/2}]` для `g`** (то есть `f = g * g^*` живёт в `(1/2, 2)`,
`L ≤ log 2`, сумма по простым пуста). Расширения за эту границу в статье нет.

**ДОСЛОВНО, Theorem 1 (стр. 2):**

> **Theorem 1.** Let `g ∈ C_c^∞(R*₊)` have support in the interval `[2^{−1/2}, 2^{1/2}]` and
> Fourier transform vanishing at `i/2` and `0`. Then one has
> `W_∞(g * g^*) ≥ Tr(ϑ(g) S ϑ(g)^*)`. (4)

**ДОСЛОВНО, точная константа (стр. 2 + §6.7, Theorem 6.11):**

> In Theorem 6.11 we show, more precisely, that there exists a finite constant `c`
> **(with `13 < c < 17`)** such that, for any `g ∈ C_c^∞([2^{−1/2}, 2^{1/2}])` whose Fourier
> transform vanishes at `i/2` (`ĝ(i/2) = 0`) one has
> `W_∞(g * g^*) ≥ Tr(ϑ(g) S ϑ(g)^*) − c |ĝ(0)|²`. (5)
> Since the evaluation of the Fourier transform at `0` defines a character of the convolution
> algebra, it follows that **`W_∞(f) ≥ 0` for any smooth positive definite function `f` with
> support in the interval `(1/2, 2) ⊂ R*₊`**, whose Fourier transform vanishes at `±i/2` and
> at `0`.

> **Theorem 6.11** Let `g ∈ C_c^∞(R*₊)` be a smooth function with support in the interval
> `[2^{−1/2}, 2^{1/2}]` and whose Fourier transform vanishes at `−i/2`. Let `S` be the
> orthogonal projection of `L²(R)_{ev}` onto the subspace of even functions which vanish as
> well as their Fourier transform in the interval `[−1,1]`. Then
> `W_∞(g * g^*) ≥ Tr(ϑ(g) S ϑ(g)^*) − c |ĝ(0)|²`, `c = 4γ/log 2`. (141)

**UNVERIFIED:** определение `γ` в формуле (141) мы не читали (оно из §6.5–6.6, максимальное
собственное значение конечно-рангового оператора). Эйлеровой постоянной это быть не может:
`4·0.5772/log 2 ≈ 3.33`, что не лежит в `(13,17)`. Перед любым использованием константы —
сверить `γ` по §6.5–6.6 глазами.

**МЕХАНИЗМ (то, ради чего статья написана) — ДОСЛОВНО, Abstract:**

> The root of the positivity is **the trace of the scaling action compressed onto the
> orthogonal complement of the range of the cutoff projections** associated to the cutoff in
> phase space, for `Λ = 1`. We express the difference between the Weil distribution and the
> Sonin trace (coming from the above compression of the scaling action) in terms of prolate
> spheroidal wave functions, and use as a key device **the theory of hermitian Toeplitz
> matrices** to control the difference.

**ДОСЛОВНО, схема (стр. 5, Introduction):**

> The essential negativity of `D ∘ Q` follows from the decomposition `−2 Id + K` (Theorem 3.6)
> of the operator … **where `K` is a compact operator of Hilbert-Schmidt class.** Hence, by
> imposing finitely many linear conditions (i.e. by restricting to a subspace of
> `L²(√I, d*ρ)` of finite codimension), one obtains a negative quadratic form. … As a
> preliminary test we prove, using a simple estimate (see Corollary 3.8 and Remark 3.9) that
> **for small enough intervals `I` the positivity holds.**

То есть: **архимедов член `= −2·Id + компакт`**, и позитивность добывается конечной
коразмерностью — ровно тот же тип аргумента, что у Yoshida (Lemma 3) и у нас в `Lock B`.

**ЧЕГО СТАТЬЯ НЕ ДАЁТ — ДОСЛОВНО, Abstract:**

> All the ingredients and tools used above make sense in the general semi-local case,
> **where Weil positivity implies RH.**

Т.е. архимедов случай сам по себе RH не влечёт; это заявка на программу.

### 2c. Позднейшие расширения (2022–2026): их НЕТ. Слова самого Connes

**ЛОКАТОР:** Connes, «The Riemann Hypothesis: Past, Present and a Letter Through Time»,
`arXiv:2602.04022`, §4.1. PDF: `pdfs/2602.04022.pdf`.

**ДОСЛОВНО** (§4.1 — Connes формулирует результат Yoshida и выносит приговор методу):

> In [111] H. Yoshida proved the following result (Theorem 1 in that paper)
> *For any smooth, positive definite function `f` with support in the interval `(1/2, 2)` and
> whose Fourier transform vanishes at `±i/2` one has: `W_∞(f) ≥ 0` where `W_∞ := −W_R`.*
> The proof is a numerical analysis of the positivity of the Weil functional `W_∞` restricted
> to the interval `(1/2, 2)`, and **therefore it does not provide any conceptual reason for
> this positivity that would have a chance to continue to hold when primes are involved.**

**ДОСЛОВНО** (§7.2 «Archimedean Weil positivity», 2026 — состояние фронта на сегодня):

> The key ingredient is the semilocal trace formula, which in our paper was used **in the
> simple case when no primes are involved.** What we found is that not only Weil's positivity
> holds in that case, as explained in §4.1, but the main source of positivity is due to the
> **Sonin space**, first introduced in the context of RH by Burnol [9–11]. …
> **Theorem 7.1.** Let `g ∈ C_c^∞(R*₊)` have support in the interval `[2^{−1/2}, 2^{1/2}]`
> and Fourier transform vanishing at `i/2` and `0`. Then the following inequality holds
> `W_∞(g * g^*) ≥ Tr(ϑ(g)Sϑ(g)^*)`.

**ВЫВОД ПО ПУНКТУ 2c.** В обзоре 2026 года, написанном самим автором программы, граница
по-прежнему `[2^{−1/2}, 2^{1/2}]`, и переход «когда появляются простые» назван открытым.
Расширения проверенного диапазона за `log 2` в литературе **не найдено**.
Проверено: Suzuki `2606.09096` (унификация Yoshida/Bombieri/CC/CCM — новых диапазонов нет,
только `a → 0+`), CCM `2511.22755` (позитивность не доказывается вообще, см. §4),
Groskin `2607.02828` (явный non-claim, см. §4), веб-поиск по расширениям.
*(Отсутствие результата — утверждение о нашем поиске, не теорема. Помечаем как
**проверено в пределах просмотренного**, список просмотренного — в «Что не прочитано».)*

### 2d. Bombieri: анализ препятствия (что мешает идти дальше)

**ЛОКАТОР:** Bombieri 2000, §8, **стр. 212–213, Theorem 8**; следствие — Введение, стр. 185.

**ДОСЛОВНО:**

> **Theorem 8.** The number of negative eigenvalues of the matrix `H(Γ;t)` equals the number
> of distinct complex conjugate pairs `(γ, γ̄)` in `Γ`.

**ЛОВУШКА:** `H(Γ;t)` строится из **конечного мультимножества нулей `Γ`**, а не из
усечённой формы Вейля в фурье-базисе окна. Это не наша `K(m,N)`. Переноса нет без crosswalk
(та же оговорка, что в `BOMBIERI_WEIL_QF_2000_USAGE_CARDS.md`, карточка 2).

**ДОСЛОВНО** (Введение, стр. 185 — препятствие названо явно):

> The results obtained for the finite dimensional case carry over to the infinite dimensional
> case, **provided we deal with negative eigenvalues bounded away from 0 and provided their
> number remains bounded.** … the main question here is to decide whether or not this
> negative eigenvalue stays bounded away from zero, as we approximate the infinite
> dimensional matrix by its finite dimensional truncations.

> We show that one of the following statements holds:
> (i) the Riemann Hypothesis is true;
> (ii) there are infinitely many complex zeros `ρ` … with `ℜ(ρ) = ½`;
> (iii) there is a linear combination `Σ_ρ c_ρ/(ρ(1−ρ)) x^{−ρ} + A + B x^{−1}` with
> `Σ|c_ρ|² = 1` and vanishing identically for `1 ≤ x ≤ M₀`, where `M₀ > 1` is an explicitly
> computable constant. Moreover, at least ½ of the `ℓ²`-mass of the coefficients is supported
> on the non-trivial zeros of `ζ(s)` off the critical line.

Это и есть его «obstruction analysis»: провал позитивности либо даёт нули вне прямой, либо
даёт нетривиальное линейное соотношение между `x^{−ρ}` — то, что он сам называет открытым и
«probably quite difficult».

---

## 3. ГЛАВНЫЙ ВОПРОС: строго ли слабее позитивность на ОГРАНИЧЕННОМ семействе?

### 3.1 «Позитивность на `[1/λ, λ]` для ВСЕХ `λ` ⟹ RH» — да, теорема; и да, тривиальна как квантор

**ЛОКАТОР:** Yoshida 1992, **стр. 282** (цитата в §1.5 выше: «R.H. is equivalent to the
positive definiteness of `( , )|C(a)` **for every `a > 0`**»), и **стр. 321, Theorem 2**.

**ДОСЛОВНО, Theorem 2:**

> **Theorem 2.** The Riemann hypothesis for `ζ_k(s)` holds if and only if the hermitian form
> `( , )` on `K̂(a)` is **non-degenerate for every `a > 0`.`

**ПОЧЕМУ ЭТО «тривиально как квантор».** `⋃_{a>0} C_c^∞(−a,a) = C_c^∞(R)`. Семейство окон
исчерпывает весь класс тестовых функций, поэтому «для всех `λ`» — это буквально критерий
Вейля, переписанный с квантором наружу. Нетривиальное содержание здесь **не** в
эквивалентности, а в двух вещах:

1. что компактного носителя вообще ДОСТАТОЧНО (Weil [34]/Bombieri Thm 1/CC (2)) — это
   и есть «локальность» RH, конечность числа простых на каждом окне;
2. что `λ_a` **непрерывна** по `a`, откуда провал RH локализуется в конкретной точке `a₀`.

**ЛОКАТОР пункта 2:** Suzuki `2606.09096`, **Theorem 1.3** (стр. 4).

**ДОСЛОВНО:**

> **Theorem 1.3.** The lowest eigenvalue `λ_a` is continuous in `a`.
> Since the continuity of `λ_a` can be established without assuming RH, Theorem 1.3
> immediately yields, as a corollary, another proof of Yoshida's result [17] that RH is
> equivalent to the nondegeneracy of `Q_W^a` for every `a > 0`. Indeed, the failure of RH is
> equivalent to the existence of some `a > 0` for which `λ_a < 0`. **Since `λ_a > 0` for
> sufficiently small `a > 0` [17, Lemma 2]**, it follows that if RH is false, then `Q_W^a`
> must be degenerate for some value of `a` by continuity of `λ_a`.

**И постановка нашего вопроса словами Yoshida, 1992, стр. 282:**

> (II) Study the deformation of `( , )|C(a)` when `a` changes. **What shall happen at the
> point `a = a₀` beyond which `( , )|C(a)` is not positive definite?**

Т.е. `a₀` (порог, за которым позитивность ломается, если RH ложна) — открытый объект с
1992 года; известно только `a₀ ≥ (log 2)/2`.

### 3.2 Позитивность на КОНЕЧНОМЕРНОМ подсемействе на фиксированном окне — строго слабее

Это ключ к адъюдикации. Три независимых свидетельства.

**(i) `λ₁` конечного среза убывает к нижней границе формы, а не равна ей.**

**ЛОКАТОР:** CCM `arXiv:2511.22755`, **Proposition 3.4** (§3.1), сразу после формулы (3.22).

**ДОСЛОВНО:**

> **Proposition 3.4.** ([4, Prop. 2.3]) The space `E` is a core for the quadratic form
> `QW_λ : L²([λ^{−1},λ], d*u) → (−∞,+∞]`, which satisfies … `QW_λ(f,f) = liminf_{g_n→f}
> QW_λ(g_n,g_n)`, `g_n ∈ E`. (3.22)
> **In particular, the lower bound of `QW_λ` is the limit, when `N → ∞`, of the smallest
> eigenvalue of the restriction of `QW_λ` to the linear span `E_N` of the functions `V_k`
> with `|k| ≤ N`.**

Так как `E_N ⊂ E_{N+1}`, последовательность `λ₁(K(m,N))` **невозрастающая по `N`** и
сходится к `λ_a` (`a = (log m)/2`). Следовательно:

* `λ₁(K(m,N)) > 0` при фиксированном `N` — заведомо **слабее**, чем `λ_a ≥ 0`;
* `λ₁(K(m,N)) > 0` **для всех `N` и всех `m`** ⟹ `λ_a ≥ 0` для всех `a` ⟹ RH
  (по Yoshida Thm 2 / Suzuki Thm 1.3, с чётной оговоркой Prop 1(2)).

**Практический смысл:** квантор по `N` **не выкидывается**. «Для всех `m`» при фиксированном
`N` — не критерий.

**(ii) Groskin: семейство `g_v` не исчерпывает тестовые функции — явный non-claim.**

**ЛОКАТОР:** `arXiv:2607.02828`, **Remark 2.6** (стр. 6).

**ДОСЛОВНО:**

> Once `g_v` is known to be admissible, the displayed identity is the explicit formula applied
> to `g_v`; in that sense the zero-sum representation is the classical mechanism of Weil [28],
> in the finite-rank setting studied by Yoshida [29] and built by Connes–van
> Suijlekom/Connes–Consani–Moscovici. The content of Theorem 2.5 is the exact closed-form
> transport `v ↦ g_v` and its calculus: the truncated matrix is not merely
> positive-semidefinite-approximating data, but evaluates exact zero sums for an explicitly
> parametrized `(N+1)`-dimensional family of band-limited test functions … **no claim is made
> about realizing arbitrary Guinand–Weil test functions this way.**

**(iii) Yoshida: чётный сектор ⟹ RH с точностью до вещественных нулей** (§1.5 выше,
Proposition 1(2)). Второй, независимый зазор.

### 3.3 «Позитивность на подсемействе ⟹ зона без нулей / плотностная оценка»: что известно

Полных теорем вида «конечномерная позитивность ⟹ zero-free region» нет. Есть три реально
работающих режима, все — про ИНЕРЦИЮ или про счётное полное семейство, не про конечное окно.

#### (a) Li 1997 / Bombieri–Lagarias 1999 — счётное семейство, ПОЛНОЕ для RH

* `LI-1997`: X.-J. Li, «The positivity of a sequence of numbers and the Riemann hypothesis»,
  *J. Number Theory* **65** (1997), no. 2, 325–333.
  RH ⟺ `λ_n > 0` для всех `n ≥ 1`, где `λ_n = Σ_ρ [1 − (1 − 1/ρ)^n]`.
* `BOMBIERI-LAGARIAS-1999`: E. Bombieri, J. C. Lagarias, «Complements to Li's criterion for
  the Riemann hypothesis», *J. Number Theory* **77** (1999), no. 2, 274–287.
  Пусть `R = {ρ}` — мультимножество комплексных чисел, не содержащее `ρ = 1`, с
  `Σ_ρ (1+|ℜρ|)/(1+|ρ|)² < ∞`. Тогда `ℜ(ρ) ≤ 1/2` для всех `ρ` **⟺**
  `Σ_ρ ℜ[1 − (1 − 1/ρ)^{−n}] ≥ 0` для всех `n ≥ 1`. Если вдобавок `R` замкнуто относительно
  `s ↦ 1−s` и комплексного сопряжения, то это эквивалентно `ℜ(ρ) = 1/2` для всех `ρ`.

**⚠️ UNVERIFIED (уровень цитаты).** Ни `LI-1997`, ни `BOMBIERI-LAGARIAS-1999` у нас нет в
`pdfs/`. Формулировки восстановлены по вторичным источникам (en.wikipedia «Li's criterion»;
Sekatskii `arXiv:1304.7895` abstract; Connes `2602.04022` §4.3 — там `λ_n` выписана
дословно и совпадает). **Перед использованием в тексте — вытянуть PDF и сверить.**

**ЧТО ЭТО ДАЁТ ПО НАШЕМУ ВОПРОСУ.** Это положительный пример «полного» подсемейства: **счётная**
последовательность конкретных тестовых функций, на которой позитивность **эквивалентна** RH.
Но полнота там достигается не обрезанием носителя, а тем, что `{(1−1/s)^n}` порождает
достаточно функций у полюса — механизм ортогонален окну CCM. И Bombieri–Lagarias показывают,
что критерий **не специфичен для дзеты** («follows as a consequence of a general set of
inequalities for an arbitrary multiset of complex numbers»), то есть арифметика в него не
входит вовсе — прямая противоположность окну CCM, куда арифметика входит списком простых.

* `LAGARIAS-2007`: J. C. Lagarias, «Li coefficients for automorphic L-functions»,
  *Ann. Inst. Fourier* **57** (2007), 1689–1740, `arXiv:math/0404394`.
  По аннотации: определяет коэффициенты для `GL(N)`, **«relates these coefficients to values
  of Weil's quadratic functional»**, выводит критерий RH через позитивность вещественных
  частей, и даёт асимптотику коэффициентов безусловно и при RH. **UNVERIFIED** — читан
  только abstract; это прямой мост «Li ↔ форма Вейля» и его надо разобрать, если линия
  понадобится.
* `VOROS-2006`: A. Voros, «Sharpenings of Li's criterion for the Riemann Hypothesis»,
  *Math. Phys. Anal. Geom.* **9** (2006), 53–63, `arXiv:math/0506326`. **UNVERIFIED**,
  не читан.
* `SEKATSKII-2014`: S. K. Sekatskii, «Generalized Bombieri–Lagarias' theorem and generalized
  Li's criterion with its arithmetic interpretation», *Ukrainian Math. J.* **66** (2014),
  `arXiv:1304.7895`. По аннотации: тот же критерий в произвольной вещественной точке, не
  только `1/2`. **UNVERIFIED**, читан только abstract.

#### (b) Инерция конечного среза ⟹ безусловное количественное утверждение о нулях — ЕСТЬ, и работает

**ЛОКАТОРЫ:**
* `arXiv:2608.13637v2` (Alpöge, Furman; аргумент написан Claude) — `pdfs/2608.13637.pdf`;
* `arXiv:2609.02882v1` (Lamzouri, 2 сен 2026) — `pdfs/2609.02882.pdf`;
* карточка: `CLAUDE_TWOTHIRDS_2026_USAGE_CARDS.md`.

**ДОСЛОВНО** (`anthropic_paper.pdf`, Abstract):

> The Riemann hypothesis, classically needed to read the zero side as a positive sum over real
> ordinates, **is replaced by linear algebra applied to a finite compression of Weil's
> Hermitian form**: Sylvester's law of inertia (an off-line pair `{ρ, 1−ρ̄}` contributes a
> block of signature `(1,1)`) and a rank–trace inequality for Hermitian matrices …

**ДОСЛОВНО** (§1.3, из карточки, сверено):

> Rather than test for positivity on the whole space, we restrict `W` to a finite-dimensional
> family `V` of `d ≈ λN` test functions — modulated copies `ϕ(u)e^{iτ_k u}` of a fixed
> compactly supported window … **That the negative index of truncations of Weil's form counts
> off-line zeros is due to Bombieri [Bom00]; we use rank and positive index.**

**ЧТО ЭТО ГОВОРИТ НАМ — и это неприятно.** Единственная известная линия, извлекающая из
конечного среза формы Вейля безусловный результат о нулях, работает **через сигнатуру**
(сколько отрицательных/положительных направлений), а не через **пол** (`λ₁ > 0`). И даёт
она **долю** (67.25%), а не RH. То есть: «конечный срез → количественное утверждение» —
доказано; «конечный срез → RH» — нет.

#### (c) Bombieri 2000: конечная позитивность → альтернатива (i)/(ii)/(iii), а не RH

См. §2d выше. Это ровно результат «позитивность/негативность на подсемействе ⟹ либо RH, либо
плотностное/структурное утверждение» — и третья ветвь `(iii)` не исключена.

### 3.4 ОТВЕТ на пункт 3, в двух предложениях

**Позитивность формы Вейля на КОНЕЧНОМЕРНОМ подсемействе (фиксированное `N`) на каждом окне
`[1/λ, λ]` НЕ известна как эквивалент RH и заведомо строго слабее: `λ₁(K(m,N))` невозрастающая
по `N` и лишь сходится к нижней границе `λ_a` формы (CCM Prop. 3.4), а порождаемое семейство
тестовых функций явно не исчерпывает допустимый класс (Groskin Rem. 2.6).**
**Эквивалентом RH становится только двойной квантор «для всех `m` И для всех `N`»
(Yoshida 1992 Thm 2 + Suzuki 2026 Thm 1.3, с оговоркой Yoshida Prop. 1(2) о чётном секторе:
чётная позитивность даёт RH лишь с точностью до вещественных нулей) — а это уже не что иное,
как критерий Вейля с квантором, вынесенным наружу, то есть не усиление, а переформулировка.**

---

## 4. Что сами CCM и Groskin говорят о позитивности своей конечной матрицы

### 4.1 CCM: `λ₁ > 0` НЕ предполагается и НЕ доказывается — предполагается «simple + even»

**Это, вероятно, главная поправка к формулировке нашего вопроса.**

**ЛОКАТОР:** `arXiv:2511.22755`, **Theorem 1.1** (стр. 1–2) и **Theorem 5.10** (§5.3).

**ДОСЛОВНО, Theorem 1.1:**

> **Theorem 1.1.** Let `ϵ_N` be the smallest eigenvalue of `QW_λ^N` **assumed simple** and `ξ`
> the corresponding eigenvector **assumed even**, normalized by `δ_N(ξ) = 1`.
> (i) The operator `D_log^{(λ,N)} = D_log^{(λ)} − |D_log^{(λ)}ξ⟩⟨δ_N|` is selfadjoint in the
> direct sum `E'_N ⊕ E_N^⊥` where on the subspace `E'_N = E_N/Cξ` the inner product is given
> by **the restriction of the quadratic form `QW_λ^N − ϵ_N ⟨|⟩`.**

**ДОСЛОВНО, доказательство Theorem 5.10:**

> (i) We apply Lemma 5.4 to **`T := QW_λ^N − ϵ_N id`** where `ϵ_N` is the smallest eigenvalue
> of `QW_λ^N` which is assumed to be simple and even.

**ДОСЛОВНО, Definition 5.3:**

> A real symmetric matrix `T` commuting with the `ℤ/2`-grading `γ` is **even-simple** if its
> smallest eigenvalue is simple and the corresponding eigenvector `ξ` satisfies `γξ = ξ`.

**ДОСЛОВНО, Proposition 5.7:**

> Let `λ > 1` and `N` such that **the truncated Weil quadratic form is even simple.**

**ВЫВОД.** Гипотеза Lemma 5.4 — `T ≥ 0`, но `T` там уже сдвинута: `T = QW_λ^N − ϵ_N·id`,
что неотрицательно **по построению**, каков бы ни был знак `ϵ_N`. Значит вся конструкция
CCM (спектральная тройка, `detreg`, вещественность нулей `ξ̂`) **не требует `λ₁ > 0`**.
Единственная неподтверждённая гипотеза у них — **простота и чётность** нижнего собственного
значения.

**ДОСЛОВНО, §8 «The missing steps» (стр. 33) — их собственный список долгов:**

> There are two essential steps still missing to justify our tentative proof of the Riemann
> Hypothesis. **The first is that, in order to apply Theorem 5.10 to the Weil quadratic form
> `QW_λ`, one must prove that its smallest eigenvalue—whose existence is ensured by Theorem
> 3.6—is simple and that its corresponding eigenvector `ξ_λ` is even.** The second step is to
> establish that `k_λ` provides a sufficiently accurate approximation to (a scalar multiple
> of) `ξ_λ` …

Позитивности в списке нет.

### 4.2 Знак `ϵ_λ`: НАБЛЮДАЕТСЯ положительным, экспоненциально малым; не доказан

**ЛОКАТОР:** CCM `2511.22755`, §8, Figure 4 подпись: «Graphs of `log(ϵ_λ)` and
`log(1 − χ(λ))` as functions of `µ = λ²`» — построение `log(ϵ_λ)` само по себе означает
наблюдение `ϵ_λ > 0` во всём просчитанном диапазоне.

**ЛОКАТОР (яснее):** Connes `arXiv:2602.04022`, §6.

**ДОСЛОВНО:**

> **The numerical computation of the smallest eigenvalue `ϵ(λ)` of `A_λ`, done in [25], shows
> that `ϵ(λ)` tends exponentially fast to `0`** as a function of `µ = λ²`. In fact a careful
> analysis reveals a striking similarity (Figure 1) between the behavior of `ϵ(λ)` and of the
> angular function `1 − χ₂(λ)`.
> In terms of the length `L = 2 log λ` of the support `[λ^{−1}, λ]` … the convergence to `0`
> of the minuscule quantities like `1 − χ₂` is **exponential of exponential**:
> `1 − χ₂ ∼ (2^{14}/3)√2 π⁵ e^{−4πe^L + 9/2 L}`.

**Направление «сверху» — ДОСЛОВНО, Connes `2602.04022`, §6.4:**

> The range of the map `E` is contained in the radical of the global Weil quadratic form (see
> [18]), but **RH implies that `QW_λ` is strictly positive and that its radical is `{0}`** …

### 4.3 Groskin: точный знак `Q_∞` на нашей ячейке, и что конечный счёт может сертифицировать

**ЛОКАТОР:** `arXiv:2607.02828`, **Theorem 2.5** (§2.2, стр. 5–6).

**ДОСЛОВНО:**

> **Theorem 2.5 (Finite Guinand–Weil dictionary).** For fixed `c > 1`, `N ≥ 0`, and every
> real even finite Galerkin vector `v ∈ R^{N+1}`,
> `⟨v, Q_∞ v⟩ = Σ_{z ∈ Z*_ζ} g_v(z)`, `Z*_ζ = {z ∈ C : 1/2 + iz` is a nontrivial zero of
> `ζ}`, with multiplicity.

Это тот же объект, что у нас записан как `K = Σ_z E(z)E(z)ᵀ` — и он **безусловен**: сумма
идёт по ВСЕМ нетривиальным нулям, без предположения об их расположении. При RH все `z`
вещественны и `g_v(z) ≥ 0` даёт позитивность; вне RH сумма содержит комплексные `z` и знак
не контролируется. **Это и есть точная формулировка «сверху» на нашем объекте.**

**ЛОКАТОР:** **Corollary 3.3 (A two-sided finite certification rule)** (§3).

**ДОСЛОВНО:**

> `λ_j(Q_T) ≥ 0` certifies `λ_j(Q_∞) > 0`; `λ_j(Q_T) < −B_T` certifies `λ_j(Q_∞) < 0`;
> **a negative eigenvalue in the band `[−B_T, 0)` certifies nothing** about the cutoff-free
> sign.

**Наша ячейка `c = 13` — ДОСЛОВНО, подпись к Figure 2:**

> The tail order in action at **`c = 13`, `N = 4`**. … Inset (`λ_min`, symmetric log scale):
> at small `T` the finite-cutoff matrix has genuinely negative eigenvalues (`−1.9·10⁻²` at
> `T = 11`, `−5.3·10⁻⁷` at `T = 14`, `−3.9·10⁻¹⁰` at `T = 18`), each far inside its
> inconclusive band `(−B_T, 0)`; **the cutoff-free limit is `+9.7·10⁻¹⁵`.**

**`c = 100` — ДОСЛОВНО (§3, «The `T = 800` correction scale»):**

> A separate cutoff-free Arb interval LDLT certificate at the same `(c,N)`, at 9000 bits,
> gives **`n₊ = 401` and `n₋ = 0`**. Thus the finite-`T` negative eigenvalues that motivated
> this paper sat deep inside the inconclusive band of the decision rule and were **tail
> artifacts, while the cutoff-free matrix is certified positive.** … driving `B_T` below a
> spectral scale of `10⁻⁵⁹` at `(c,N) = (100,200)` would require `T ≈ 8·10⁶²`.

**Явный non-claim — ДОСЛОВНО (§«Non-claims»):**

> **The paper does not prove RH, Weil positivity, a prime-location bound**, a next-prime
> theorem, or a factoring result.

**ИТОГ ПО §4.** Позитивность конечной матрицы CCM — **численно наблюдаемый факт с
сертификатами интервальной арифметики** (Groskin: `c ≤ 100`, `n₋ = 0`), а не теорема; и она
не является ни гипотезой, ни выводом теоремы CCM. `λ₁` при этом астрономически мала
(`~10⁻¹⁵` при `c = 13`, `~10⁻⁵⁹` при `c = 100`) и падает как `exp(−4π e^L)` — то есть двойной
экспонентой по длине окна.

---

## 5. CRUSHER — где стоит окно CCM относительно доказанного

**Сверху (`RH ⟹ позитивность`) доказано полностью и без оговорок**: RH влечёт `Q_W(v) ≥ 0`
на всём `C_c^∞(R)` (Weil 1952; Bombieri 2000 Thm 1, стр. 191: `Σ_ρ ĝ(ρ)ĝ(1−ρ) = Σ_ρ|ĝ(ρ)|² ≥ 0`),
а на нашем конечном объекте это же читается точно: `⟨v, Q_∞ v⟩ = Σ_{нули} g_v(z)`
(Groskin `2607.02828` Thm 2.5), и Connes формулирует следствие прямо — «RH implies that
`QW_λ` is strictly positive and that its radical is `{0}`» (`2602.04022` §6.4). **Снизу
(`позитивность ⟹ ...`) доказано ровно до `L = log 2` и ни на волос дальше**: Yoshida 1992
Thm 1 (стр. 310) — позитивность на `K(a)` при `a ≤ (log 2)/2`, полученная как конечное
вычисление `10×10` матрицы плюс хвост; Bombieri 2000 Thm 12 (стр. 226) — `|I| < log 2` с
границей `log(1/|I|) − log log(1/|I|) − O(1)`; Connes–Consani 2021 (`2006.13771`) Thm 1 и
6.11 — тот же интервал `[2^{−1/2}, 2^{1/2}]`, но с концептуальным механизмом (архимедов член
`= −2·Id + компакт Гильберта–Шмидта`, позитивность из следа сжатия на пространство Сонина);
Suzuki 2026 Thm 1.4 — асимптотика `λ_a = log(1/a) + µ₁ − log 2π + ψ(2) − 1 + O(a)` при
`a → 0+`. **Все четыре останавливаются в одной и той же точке — там, где сумма по простым
перестаёт быть пустой**, и Connes в обзоре 2026 года пишет об этом прямым текстом: метод
Yoshida «does not provide any conceptual reason for this positivity that would have a chance
to continue to hold when primes are involved» (`2602.04022` §4.1). **Окно CCM `m = 13`
(`L = log 13 ≈ 2.565`, девять простых степеней `2,3,4,5,7,8,9,11,13` внутри) стоит в 3.7 раза
дальше по `L` и на другой стороне этой границы** — в области, где доказанного нижнего
результата не существует вовсе, а есть только численность: `λ₁ ≈ +9.7·10⁻¹⁵` при `c = 13`
(Groskin Fig. 2) и `n₋ = 0` при `c = 100` (Groskin §3, Arb LDLT, 9000 бит). **И даже эта
численность — не тот объект, который эквивалентен RH:** при фиксированном `N` `λ₁(K(m,N))`
лишь мажорирует истинную нижнюю границу формы `λ_a` и убывает к ней при `N → ∞`
(CCM Prop. 3.4), порождаемое семейство `g_v` явно не исчерпывает допустимые тестовые функции
(Groskin Rem. 2.6), а чётный сектор в принципе даёт RH лишь с точностью до вещественных
нулей (Yoshida Prop. 1(2), стр. 285). Эквивалентом RH становится только двойной предел
«все `m` и все `N`», то есть критерий Вейля, переписанный с квантором наружу
(Yoshida Thm 2, стр. 321; Suzuki Thm 1.3).

---

## 6. Что это меняет в нашей постановке (CLOSES / OPENS)

**CLOSES.**
1. Вопрос «доказана ли позитивность где-нибудь безусловно» — да, и граница названа числом:
   `L ≤ log 2`, `m ≤ 2`. Ниже этой строки «мы не нашли» становится проверенным утверждением.
2. Вопрос «предполагают ли CCM `λ₁ > 0`» — **нет**. Их гипотеза — `even simple`. Если наш
   маршрут где-то опирается на «CCM предполагают позитивность», это надо снять.
3. Вопрос «эквивалентно ли `λ₁(K(m,N)) > 0 ∀m` критерию RH» — нет при фиксированном `N`;
   да только при двойном кванторе, и тогда это переформулировка, а не усиление.

**OPENS.**
1. `a₀` Yoshida (порог поломки) — открыт с 1992, известно лишь `a₀ ≥ (log 2)/2`. Это, судя
   по всему, тот же объект, что наш «абсолютный пол».
2. Мост Lagarias 2007 «Li-коэффициенты ↔ форма Вейля» (`math/0404394`) не читан — это
   единственная найденная линия, где позитивность на СЧЁТНОМ подсемействе оказывается полной
   для RH. Кандидат в батч.
3. Константа `γ` в CC Thm 6.11 (`c = 4γ/log 2`, `13 < c < 17`) не идентифицирована.

---

## Что не прочитано (границы этой карточки)

**Читано глазами по текстовому слою:** Bombieri 2000 — Введение (стр. 183–186), §3
(Theorem 1, стр. 191), §3 конец (стр. 193–194), §8 (Theorem 8 + доказательство, стр. 212–213),
§10 (стр. 221), §12 (Theorem 12 + начало доказательства, стр. 226). Yoshida 1992 — Введение
(стр. 281–283), §1 (Proposition 1, стр. 285), §3 (Proposition 2), §6 конец (Theorem 1,
стр. 310), §7–8 (Theorem 2, Proposition 7, стр. 320–322). Connes–Consani `2006.13771` —
Abstract, Introduction (стр. 1–5), Theorem 3/4.7, Theorem 6.11 (§6.7). CCM `2511.22755` —
Abstract, Introduction, §3.1–3.2 (Prop. 3.3, 3.4), §5.2 (Def. 5.3, Lemma 5.2, 5.4), §5.3
(Prop. 5.7, Thm 5.10), §6 (численность), §7 Outlook, §8. Groskin `2607.02828` — Abstract,
Introduction, §2.1–2.2 (Cor. 2.4, Thm 2.5, Rem. 2.6, Cor. 2.7), §3 (Cor. 3.3, Fig. 2,
`T=800`), Non-claims. Suzuki `2606.09096` — §1.1–1.2 целиком (Thm 1.1–1.5, Cor. 1.2, 1.6),
§5.1, §8.4. Connes `2602.04022` — §4.1, §4.3, §6 (ϵ(λ), Fact 6.2–6.4, §6.6), §7.2.

**НЕ читано:** доказательства Yoshida Theorem 1 (§6 полностью, включая `10×10` матрицу `U` и
хвостовые константы) — только результат и схема; доказательство Bombieri Theorem 12 целиком;
Bombieri §4–§7, §9, §11, §13 (численные эксперименты — там могут быть числа, сравнимые с
нашими); Connes–Consani §3–§5 и §6.1–6.6 (в частности определение `γ`); Suzuki §2–§4, §6–§7;
CCM §2, §4, §7 подробно; Groskin §4–§9. Статьи Weil 1952/1972 — не читаны вовсе.
Li 1997, Bombieri–Lagarias 1999, Lagarias 2007, Voros 2006, Sekatskii 2014 — **PDF
отсутствуют**, формулировки по вторичным источникам, помечены UNVERIFIED.

**Отрицательный результат «расширений за `log 2` нет» — это утверждение о нашем поиске**
(перечисленные выше шесть статей + веб-поиск 2026-09-04 по расширениям диапазона), а не
теорема. Если Прошка знает контрпример, он бьёт этот пункт первым.
