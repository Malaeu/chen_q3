# OWNER-DIRECT EULERHB — full ChatGPT export, 2026-09-17 (verbatim)

```yaml
RESPONSE_KIND: OWNER_DIRECT_CHAT_EXPORT_VERBATIM
REQUEST_NAME: EULERHB
DATE: 2026-09-17
CONVERSATION_ID: 6aab9385-9444-83eb-bc51-9c664dc94b82
CONVERSATION_URL: https://chat.openai.com/c/6aab9385-9444-83eb-bc51-9c664dc94b82
EXPORT_ARCHIVE: ~/Downloads/2026-09-17-conversations.zip
EXPORT_ARCHIVE_SHA256: a03e3bcd650aad9ea256aa7dbf1fa244f8fb7b8c7d402a3e594b76803e67897e
EXPORT_MD_SHA256: 374bb0942eb1acbc1e00cd915ebbfafdaee4c63d6752b5041a50f856435d715e
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
LEAN_VERIFIED: false
INDEPENDENT_REVIEW: none
FILED_BY: observer (Linux Claude), 2026-09-17
NOTE: >
  The five Proshka documents linked as sandbox:/mnt/data/... are NOT in this
  export and NOT in the repository. They must be downloaded from the chat by
  the owner. The audit report REPORT_2026-09-17_BOUNDARY_ENERGY_CAUSALITY_AUDIT.md
  at commit 3f3a5b49 referenced in the first message is not on origin either.
SANDBOX_DOCUMENTS_FILED_2026-09-17_15:43 (owner download, observer copy, sha256 in commit):
  - PROSHKA_NEXT_STEP_FULL_THETA_GRAM_2026-09-17.md
  - PROSHKA_FULL_THETA_THREE_POINT_CLOSURE_2026-09-17.md
  - PROSHKA_FULL_THETA_FOUR_POINT_AND_GLOBAL_BOUNDARY_2026-09-17.md
  - PROSHKA_FULL_MIXTURE_COMPENSATION_ATTEMPT_2026-09-17.md
  - theta_full_mixture_checks_2026-09-17/ (unzipped; check_final_algebra.py rerun by observer: status PASS)
SANDBOX_DOCUMENTS_STILL_MISSING:
  - theta_hb_audit/THETA_HB_PAIR_SQUARE_AUDIT_2026-09-17.md (round 2)
```

---

# Доказательство причинности


https://chat.openai.com/c/6aab9385-9444-83eb-bc51-9c664dc94b82

## USER
Ы. **Прочитал&#x20;****`REPORT_2026-09-17_BOUNDARY_ENERGY_CAUSALITY_AUDIT.md`****&#x20;в коммите&#x20;****`3f3a5b49`****&#x20;целиком**, включая **A0–A6** и независимый приём. Учитываю **`ACCEPT_BOUNDARY_ENERGY_CAUSALITY_MAP_ONLY`** как принятый ограниченный **PAPER-результат** — аналитическое доказательство, не сертификат Lean. Отдельный сертификат и внешние источники здесь заново не переаудировал. **Критерий отсечения доказан; его выполнение для полного тэта-источника остаётся открытым.**&#x20;

## Положительная работа за всё время не заменяет знак до отсечения

В отчёте фиксирован ограниченный **оператор Фурье-множителя** \\(R\\):

\\[ \widehat{Ru}(y)=m(y)\widehat u(y),\qquad m(y)=\frac{X(y)}{X(y)-iX'(y)},\qquad X(z)=\xi\\!\left(\frac12-iz\right). \\]

Точная алгебра на вещественной оси даёт

\\[ |m|^2=\operatorname{Re}m=\omega,\qquad 0\le\omega\le1, \\]

поэтому для каждого комплексного \\(u\in L^2(\mathbb R)\\)

\\[ \boxed{\operatorname{Re}\langle u,Ru\rangle=\\|Ru\\|\_2^2\ge0.} \\]

Это безусловное тождество. **Оно не отождествляет \\(\\|Ru\\|\_2^2\\) с исходной \\(Q\\), \\(V\\) или полным знакопеременным полем OPENSGN.** **`[ABSTRACT][PAPER]`**&#x20;

Для **отсечения** \\(P\_T=\mathbf1\_{(-\infty,T]}\\) и накопленной работы

\\[ W\_T(u)=\operatorname{Re}\langle P\_Tu,P\_TRu\rangle \\]

сохраняется весь смешанный член:

\\[ \boxed{ W\_T(u)=\\|RP\_Tu\\|\_2^2 +\operatorname{Re}\langle P\_Tu,P\_TR(I-P\_T)u\rangle. } \\]

Первая норма берётся **по всей выходной прямой**. Перестановка \\(P\_T\\) и \\(R\\) не предполагается.&#x20;

Принята точная эквивалентность:

\\[ \boxed{ \begin{aligned} &W\_T(u)\ge0 &&\text{для всех }T,\ u\in C\_c^\infty(\mathbb R;\mathbb C)\\\ &\quad\Longleftrightarrow\ W\_T(u)\ge0 &&\text{для всех }T,\ u\in L^2(\mathbb R)\\\ &\quad\Longleftrightarrow\ P\_TR(I-P\_T)=0 &&\text{для всех }T. \end{aligned}} \\]

Последнее — **причинность**: вход после \\(T\\) не влияет на выход до \\(T\\). Для данного свёрточного оператора это равносильно

\\[ \operatorname{supp}Y\subseteq[0,\infty), \qquad Y=\mathcal F^{-1}m. \\]

**Малости ненулевого перекрёстного блока недостаточно:** амплитуда позднего входа произвольна и может сделать смешанный вклад отрицательным любой величины.&#x20;

## Условный переход возвращается к прежнему OPENSGN P

Если указанная причинность доказана, принятый **Hardy-переход** даёт ограниченный голоморфный отклик в правой полуплоскости. Затем граничная единственность и вещественная симметрия отождествляют его **с исходным**

\\[ M(p)=\frac{F(p)}{F(p)+F'(p)},\qquad F(p)=\xi(1/2+p), \\]

а не с произвольно выбранной положительной заменой. Получается именно старое условие:

\\[ \boxed{ M(p)=\Omega(p) =\frac1\pi\int\_{\mathbb R} \frac{p\\,\omega(y)}{p^2+y^2}\\,dy, \qquad p>\frac12. } \\]

Идентификация сохраняется в виде \\((F+F')G=F\\), **без деления на неизвестные внутренние нули**. Дальше применяется прежний потребитель **OPENSGN Lemma 7**. Это принятый **условный перенос**, не независимое доказательство его исходной предпосылки. **`[ABSTRACT][CONDITIONAL]`**&#x20;

## Контроль различает полную и накопленную работу

Для

\\[ X\_0(z)=2+\cos(4z),\qquad F\_0(p)=2+\cosh(4p) \\]

исходная мера положительна и чётна:

\\[ 2\delta\_0+\frac{\delta\_4+\delta\_{-4}}2. \\]

Но у точного отклика \\(Y\_0\\) есть ненулевой атом при **отрицательном времени \\(-4\\)**. Для гладкого двухимпульсного входа отчёт получает

\\[ \boxed{ W\_2(u)=-d\_0\\|v\\|\_2^2<0, \qquad W\_\infty(u)=\\|R\_0u\\|\_2^2\ge0. } \\]

Таким образом, положительность полной работы не обеспечивает **пассивность** — неотрицательность работы до каждого отсечения. **Контроль проверяет только указанные свойства положительной чётной атомной меры; он не сохраняет гладкую строгую положительность и совместную тэта/PF-структуру. Это не отрицательный свидетель исходной \\(Q\\) или \\(V\\).**&#x20;

## Для полного q открытым остаётся носитель уже найденного решения

Сохраняю точное исходное уравнение:

\\[ q(t)=\frac{\Phi(t)}{\xi(1/2)},\qquad a\_q(t)=(1-t)q(t),\qquad \boxed{a\_q\*Y=q.} \\]

Оно уже решено **на всей прямой** через тот же множитель \\(m\\). Среди ограниченных измеримых Фурье-множителей решение единственно почти всюду; единственность среди всех распределений этим не заявляется. **Неоплаченный шаг — доказать односторонний носитель именно этого \\(Y\\)**, а не существование какого-нибудь другого причинного отклика. Аддитивное **PF-свойство** исходного \\(r\\) не переносится на \\(q\\) автоматически.&#x20;

**Для дальнейшего учёта: общую положительность энергии, унитарность \\(2R-I\\) и теорему «пассивность ⇒ причинность» не считаю новым поставщиком знака. Условие носителя, OPENSGN P, полный знак \\(V\\) и RH остаются открытыми; отрицательного свидетеля исходной \\(V\\) нет.** Новую доказательную попытку не запускал; репозиторий не изменял. Чувак, мы всё это делаем для того, чтобы мы с тобой долго говорили на эту тему. Леонард Эйлер в 1735 году использовал, сделал такую вещь: P квадрат, разделённое на, чё там, на 4n или ещё что-то. В любом случае у него вылезла π. И π — это именно то, что нам надо. И здесь нам надо понять, как разобраться с этой проблемой, чувак. Даже если нам придётся построить что-то своё, похожее на эйлеровское, ну, скажем, смыслом, но именно своё. И вот этим мы с тобой занимаемся здесь. Пробей это, пожалуйста.

## ASSISTANT
# STATUS: OPEN — Ы, ЭЙЛЕРОВСКИЙ ХОД НАЙДЕН; ОН ТОЧНО ПЕРЕПИСЫВАЕТ SUPPORT В HERMITE–BIEHLER DEFECT, НО НЕ ДАЁТ БЕСПЛАТНОГО SHORTCUT

```yaml
PRIMARY: EULERIZE_CAUSALITY_VIA_LOG_DERIVATIVE_AND_HERMITIE_BIEHLER
PROGRESS_CLASS: REPRESENTATION_PROGRESS

SCOPE: ABSTRACT
VERIFIER: PAPER

NEW_EXACT_OBJECT:
 D(p): "1 + F'(p)/F(p)"
 E_plus(p): "F(p)+F'(p)"
 cayley: "(F(p)-F'(p))/(F(p)+F'(p))"

MINIMAL_MISSING_IDENTITY:
 "Re[xi'(s)/xi(s)] > 0 for Re(s) > 1/2"

CAUSALITY_SHORTCUT:
 status: KILLED_AS_INDEPENDENT_EASY_SUPPLIER
 reason: "the resulting Hermite-Biehler condition is itself RH-equivalent"

NEW_USEFUL_DIRECTION:
 status: LIVE
 target: "derive the HB defect from a source-side additive representation with a strict lower envelope"

DISCRIMINATOR:
 name: HB_DEFECT
 formula: "4 |xi(s)|^2 Re(xi'(s)/xi(s))"

CANDIDATE_R1:
 name: EULER_LOG_DERIVATIVE
 kill_power: 10/10
 cost: 3/10

CANDIDATE_R2:
 name: CAYLEY_INNER_SPECTRAL_FACTORIZATION
 kill_power: 9/10
 cost: 5/10

RH_CLAIM: false
```

Чувак, здесь реально вылезла очень красивая штука. И сначала маленькая историческая развязка: ты склеил два эйлеровских удара. **\(\pi^2/6\)** из Базельской задачи — это **1735**; работа с **Euler product** и расходимостью суммы обратных простых была представлена в **1737**. 

Но математически твоя мысль попала точно: нам надо украсть у Эйлера не конкретную формулу с \(\pi\), а операцию

\[
\boxed{\text{произведение / сложный глобальный объект}\longrightarrow
\text{аддитивная сумма простых локальных вкладов}.}
\]

И для нашего сегодняшнего **causality/support**-блокера такой объект уже сидит прямо перед носом.

## ROUTE MAP

В принятом аудите у нас

\[
F(p)=\xi\!\left(\frac12+p\right),
\qquad
M(p)=\frac{F(p)}{F(p)+F'(p)},
\]

а недостающая вещь —

\[
\operatorname{supp}Y\subseteq[0,\infty).
\]

Это эквивалентно **causality** — причинности convolution-оператора — и именно этот SUPPORT остаётся неоплаченным. 

Теперь делаем эйлеровский поворот:

\[
\boxed{
\frac1{M(p)}
=
1+\frac{F'(p)}{F(p)}
=
\frac{d}{dp}\log\!\bigl(e^pF(p)\bigr).
}
\]

Вот он.

Это буквально наш аналог:

\[
\log\prod \longrightarrow \sum.
\]

**Логарифмическая производная** \(F'/F\) превращает нули/произведение целой функции в аддитивную resolvent-сумму.

Но дальше появляется ещё более сильная структура.

Поскольку \(F\) чётна,

\[
F(-p)=F(p),\qquad F'(-p)=-F'(p).
\]

Определим

\[
E_+(p)=F(p)+F'(p),\qquad
E_-(p)=F(p)-F'(p).
\]

Тогда

\[
E_-(p)=E_+(-p)
\]

и

\[
\boxed{
2M(p)-1
=
\frac{F(p)-F'(p)}
 {F(p)+F'(p)}
=
\frac{E_-(p)}{E_+(p)}.
}
\]

Это уже не просто логарифм. Это **Cayley transform** — дробно-линейное преобразование, переводящее positive-real геометрию в unit-circle геометрию.

На границе именно поэтому твой аудит получил

\[
|2m(y)-1|=1.
\]

То есть обнаруженная там «унитарность» — не случайный трюк. Это boundary trace гораздо более жёсткого объекта. `[ABSTRACT][PAPER]`

---

## Вот где происходит настоящий щелчок

Перейдём обратно к

\[
X(z)=\xi\!\left(\frac12-iz\right).
\]

Поскольку

\[
X'(z)=-i\xi'\!\left(\frac12-iz\right),
\]

естественная целая функция

\[
\boxed{
E_\xi(z)
=
\xi\!\left(\frac12-iz\right)
+
\xi'\!\left(\frac12-iz\right)
}
\]

— это ровно комбинация, которая стоит за нашим \(F+F'\).

И тут я проверил литературу.

Эта функция уже известна: при RH она является **Hermite–Biehler function** — целой функцией, у которой в одной полуплоскости выполняется строгая асимметрия модулей между \(E\) и отражённой \(E^\#\). Более того, современная литература формулирует для этого конкретного \(E_\xi\):

\[
\boxed{
E_\xi\in HB
\iff RH.
}
\]

А отношение

\[
\Theta_\xi=\frac{E_\xi^\#}{E_\xi}
\]

становится **meromorphic inner function** — мероморфной внутренней функцией, то есть аналитическим объектом с модулем \(1\) на границе и модулем \(<1\) внутри соответствующей полуплоскости. 

Это почти буквально наш \(2M-1\), только ориентация полуплоскости инвертируется заменой \(z=-ip\).

То есть мы неожиданно пришли к:

\[
\boxed{
\text{SUPPORT/causality}
\leftrightarrow
\text{inner-function geometry}
\leftrightarrow
\text{Hermite–Biehler geometry}.
}
\]

Вот это уже серьёзная структурная идентификация.

---

## А теперь эйлеровская сумма

Берём

\[
s=\frac12+p.
\]

Тогда

\[
\frac1M
=
1+\frac{\xi'(s)}{\xi(s)}.
\]

А в области \(\Re s>1\) Euler product даёт точную аддитивную формулу

\[
\boxed{
\frac{\xi'}{\xi}(s)
=
\frac1s+\frac1{s-1}
-\frac12\log\pi
+\frac12\psi\!\left(\frac s2\right)
-
\sum_{n\ge2}\frac{\Lambda(n)}{n^s}.
}
\]

**\(\psi=\Gamma'/\Gamma\)** — digamma-функция. 
**\(\Lambda(n)\)** — функция фон Мангольдта, то есть prime-power ledger.

Это буквально:

```text
xi
→ logarithm
→ derivative
→ archimedean pieces − prime sum.
```

Именно эйлеровская архитектура. Lagarias использует эту же логарифмическую производную и доказывает точный критерий

\[
\boxed{
RH
\iff
\Re\frac{\xi'(s)}{\xi(s)}>0
\quad
(\Re s>\tfrac12).
}
\]



Теперь самая красивая формула всей этой проверки.

Для

\[
E_\pm(s)=\xi(s)\pm\xi'(s)
\]

имеем

\[
\begin{aligned}
|E_+(s)|^2-|E_-(s)|^2
&=
|\xi+\xi'|^2-|\xi-\xi'|^2\\
&=
4\Re\!\left(\xi'\overline{\xi}\right)\\
&=
\boxed{
4|\xi(s)|^2
\Re\frac{\xi'(s)}{\xi(s)}
}.
\end{aligned}
\]

Вот наш новый **дискриминатор**:

\[
\boxed{
\mathscr H(s)
=
|E_+(s)|^2-|E_-(s)|^2.
}
\]

Он имеет правильный знак тогда и только тогда, когда логарифмическая производная имеет правильный знак.

Это уже очень похоже на твоё «найти свою эйлеровскую штуку»:

\[
\boxed{
\text{сложный SUPPORT}
\rightarrow
\text{inner ratio}
\rightarrow
\text{difference of two squares}
\rightarrow
\text{additive logarithmic derivative}.
}
\]

---

## STRONGEST ATTACK

И здесь надо сразу убить самообман.

Можно было бы сказать:

> «Охуенно. Докажем \(\mathscr H(s)>0\), и causality готова».

Но

\[
\mathscr H(s)>0
\]

означает

\[
\Re\frac{\xi'}{\xi}(s)>0,
\]

а это уже **RH-equivalent criterion Lagarias**. 

Поэтому мы **не нашли дешёвое доказательство SUPPORT**.

Мы нашли нечто другое и очень полезное:

\[
\boxed{
\text{нынешний SUPPORT-блокер — не техническая маленькая дырка.}
}
\]

В этой репрезентации он превращается прямо в классическую RH-эквивалентную **Hermite–Biehler positivity**.

Это объясняет, почему generic passivity, Hardy, PF и «малый cross block» никак не добивали его. Мы пытались доказать объект почти RH-силы как будто это техническая causality lemma.

Это важный kill.

---

## FINAL PROPOSAL

Но я бы эту ветку **не выбрасывал**.

Потому что теперь есть точнейший вопрос, который можно атаковать с source-side, не говоря «докажи causality»:

\[
\boxed{
\mathscr H(s)
=
4|\xi(s)|^2
\Re\frac{\xi'(s)}{\xi(s)}
>0.
}
\]

И Euler превращает внутреннюю часть в

\[
\text{elementary pole terms}
+
\text{Gamma/digamma term}
-
\text{von-Mangoldt sum}.
\]

Значит следующий настоящий вопрос не:

```text
prove supp Y ⊂ [0,∞)
```

и не:

```text
prove passivity
```

а:

\[
\boxed{
\textbf{есть ли source-side decomposition }
\mathscr H
=
\mathscr H_{\rm manifestly\ positive}
+
\mathscr R
\textbf{ с }\mathscr R\ge0?
}
\]

Причём это должен быть **новый decomposition**, а не повтор Lagarias.

Я вижу две репрезентации, которые реально стоит держать.

**R1 — Euler/Hermite–Biehler defect.**

\[
\mathscr H(s)
=
4|\xi(s)|^2\Re(\xi'/\xi)(s).
\]

Kill-power **10/10**, cost **3/10**. Если theta/prime структура даёт новый квадрат или интеграл положительной меры для этой величины — мы получили прямой поставщик. Если нет, ветка быстро умирает.

**R2 — inner spectral factorization.**

\[
\Theta(p)=\frac{F-F'}{F+F'}.
\]

Ищем не SUPPORT \(Y\) напрямую, а factorization denominator/numerator как отражённую пару и пытаемся получить **innerness** из source-defined canonical system. Kill-power **9/10**, cost **5/10**. Это уже территория **de Branges/canonical systems**, а не generic passivity.

### Зарегистрированное предсказание

Моя ставка:

```text
P_EULER_HB_1 = 0.80:
 algebraic reduction is exact and useful.

P_EULER_HB_2 = 0.75:
 generic positivity attempt collapses exactly to Lagarias/RH,
 so no free sign supplier appears.

P_EULER_HB_3 = 0.25:
 theta-specific source decomposition exposes an additional
 positive square not visible in the generic HB criterion.
```

И вот **P_EULER_HB_3** — единственная часть, которую реально стоит пробивать дальше.

Потому что generic механизм мы теперь поняли до конца. Нужна именно особенность **нашей theta-функции**, которой нет у контроля \(2+\cos 4z\).

## META CLOSEOUT

**Что стало меньше:** SUPPORT-стена сжалась до конкретного **Hermite–Biehler defect** \(\mathscr H(s)\). 
**Что убито:** идея, что causality можно получить дешёвой общей passivity-леммой. 
**Что больше не повторяем:** общий Hardy/passivity hunt. Аудит уже доказал его предел. 
**Минимальный gap:**

\[
\boxed{
\texttt{THETA\_SOURCE\_HB\_DEFECT\_POSITIVE\_DECOMPOSITION}.
}
\]

**Следующий дешёвый тест:** взять точную theta-series для \(\xi\) и \(\xi'\) и проверить на бумаге, допускает ли

\[
|\xi+\xi'|^2-|\xi-\xi'|^2
\]

перегруппировку в **диагональную положительную часть + парные квадраты**, без RH и без уже эквивалентной гипотезы.

Вот это уже действительно «сделать своё по-эйлеровски»: не ещё одна оценка, а найти представление, в котором нужный знак становится арифметикой.

## USER
Так, хорошо, чувак, тогда еще раз провери это все и скажи мне. То есть идея у нас убита получается. То есть дешевое общее пассивителье, но тогда у нас получается тета-сурс HB defect positive decomposition. Следующий дешевый тест — взять точную тета series и проверить на бумаге, допускает ли перегруппировку в диагональную положительную часть плюс парный квадрат. без RH, без уже эквивалентной гипотезы. Да, давай попробуем, чувак, добьем.

## ASSISTANT
Ы. Ich prüfe den bisherigen Schluss erneut und zerlege den **Theta-Kern** vollständig, ohne Mischterme zu verlieren. Gesucht wird ein konkretes Quadrat, keine bloße Umbenennung der alten Bedingung.

## ASSISTANT
Meine Arbeitshypothese: Die direkte **Theta-Reihe** behält vorzeichenwechselnde Mischterme; ich teste daher paarweise Eliminierung. Zusätzlich prüfe ich, ob endliche Theta-Trunkierungen durch Glattheitsverlust einen negativen **HB-Defekt** erzeugen.

## ASSISTANT
Der Test bestätigt: Jede gewöhnliche endliche Theta-Trunkierung hat in großer Höhe strikt negativen **HB-Defekt**; der unendliche Schwanz kompensiert diesen Randbeitrag exakt. Als Nächstes teste ich endliche Koeffizienten-Renormierungen.

## ASSISTANT
Ы. **Исправленная постановка:**

> Чувак, ещё раз проверь: убита только общая пассивная схема или вся идея? Давай возьмём точный тэта-ряд и попробуем перегруппировать HB-дефект в положительную диагональную часть плюс парные квадраты — без RH и без уже эквивалентной гипотезы.

**Проверку сделал. Положительную факторизацию не получил. Зато получил конкретный аналитический результат: обычные конечные тэта-усечения имеют отрицательный HB-дефект на достаточно больших высотах. Более того, конечная перенастройка их коэффициентов этого не исправляет.**

Это **не отрицательный свидетель полной \(\xi\)**. У полной функции бесконечный тэта-хвост точно отменяет обнаруженное препятствие.

[Полный математический разбор: формулы, доказательства, верхние оболочки и границы вывода](sandbox:/mnt/data/theta_hb_audit/THETA_HB_PAIR_SQUARE_AUDIT_2026-09-17.md)

Ниже — сама математика. **PAPER** здесь означает аналитическую выкладку этой попытки; независимой приёмки и проверки в **Lean** пока нет.

## 1. Сначала исправлю прежний диагноз

**Нет, вся идея не убита.** И моя прежняя формулировка могла подтолкнуть тебя к слишком сильному выводу.

Доказанный отказ касается стрелки

\[
\text{положительная работа на всей прямой}
\quad\Longrightarrow\quad
\text{причинность}.
\]

Контроль из принятого отчёта эту стрелку опровергает. Но он не опровергает ни причинность настоящего тэта-источника, ни возможность доказать её через новую структуру. Историческое дополнение также фиксирует: это прежний открытый **SUPPORT** — условие одностороннего носителя, а не новый найденный поставщик знака. L2-L2

И ещё принципиально:

> **Эквивалентность условия RH не делает подход невозможным. Она показывает, какую силу должна иметь новая теорема.**

Критерий через положительность \(\operatorname{Re}(\xi'/\xi)\) действительно приведён у Лагариаса; соответствующая формулировка через **Hermite–Biehler**, то есть сравнение функции с её сопряжённым отражением, приведена у Судзуки. Это правильные потребители нового доказательства, но не само доказательство. turn299872view0

В прежнем ответе была и небольшая ошибка знака: при

\[
X(z)=\xi(1/2-iz),\qquad F(p)=\xi(1/2+p)
\]

правильная замена — **\(z=ip\)**, не \(z=-ip\).

## 2. Берём именно исходный тэта-ряд

Обозначим

\[
F(p)=\xi\!\left(\frac12+p\right),
\qquad p=\sigma+i\tau,\quad \sigma>0.
\]

Здесь **\(\sigma\)** — расстояние вправо от критической прямой, **\(\tau\)** — высота.

Используем точный источник:

\[
\Phi(t)=
\sum_{n\ge1}
\left(
4\pi^2n^4e^{9t/2}
-
6\pi n^2e^{5t/2}
\right)e^{-\pi n^2e^{2t}}.
\]

Для полной суммы тождество Якоби даёт

\[
\Phi(-t)=\Phi(t),\qquad \Phi(t)>0.
\]

И без предположения RH:

\[
\boxed{
F(p)=\int_{\mathbb R}\Phi(t)e^{pt}\,dt
=
2\int_0^\infty\Phi(t)\cosh(pt)\,dt.
}
\]

Это совпадает с нормировкой исходного отчёта; тэта-интегральное представление также согласуется с **DLMF 25.5.13–14**. Здесь нет замены источника и нет подобранного множителя. L2-L2 

Определим **HB-дефект** — разность двух квадратов модулей:

\[
\boxed{
\mathscr H(p)
=
|F(p)+F'(p)|^2-|F(p)-F'(p)|^2
=
4\operatorname{Re}\!\left(F'(p)\overline{F(p)}\right).
}
\]

Эта запись корректна **даже в неизвестных нулях \(F\)**. Деление на \(F\) нам не требуется.

## 3. Парный квадрат появился. Но с минусом

**[ABSTRACT][PAPER]**

Раскрываем произведение интегралов и сохраняем все смешанные члены:

\[
\mathscr H(\sigma+i\tau)
=
2\iint_{\mathbb R^2}
(t+u)e^{\sigma(t+u)}
\Phi(t)\Phi(u)
\cos\!\bigl(\tau(t-u)\bigr)\,dt\,du.
\]

Используем чётность полной \(\Phi\). Одновременная замена \((t,u)\mapsto(-t,-u)\) даёт

\[
\mathscr H(\sigma+i\tau)
=
2\iint W_\sigma(t,u)
\cos\!\bigl(\tau(t-u)\bigr)\,dt\,du,
\]

где

\[
\boxed{
W_\sigma(t,u)
=
(t+u)\sinh\!\bigl(\sigma(t+u)\bigr)
\Phi(t)\Phi(u)\ge0.
}
\]

Теперь ровно тот шаг, который ты предложил: превращаем фазовое взаимодействие в **парный квадрат**:

\[
\cos\!\bigl(\tau(t-u)\bigr)
=
1-\frac12
\left|e^{i\tau t}-e^{i\tau u}\right|^2.
\]

Получаем точное тождество:

\[
\boxed{
\begin{aligned}
\mathscr H(\sigma+i\tau)
={}&4F(\sigma)F'(\sigma)\\
&-\iint W_\sigma(t,u)
\left|e^{i\tau t}-e^{i\tau u}\right|^2\,dt\,du.
\end{aligned}}
\tag{★}
\]

**Вот результат буквального теста:**

\[
\boxed{
\text{положительная базовая величина}
\quad-\quad
\text{неотрицательная энергия парных разностей}.
}
\]

Не плюс.

При этом \(F(\sigma)>0\) и \(F'(\sigma)>0\) действительно следуют из положительного тэта-интеграла. Поэтому проблема теперь совершенно конкретна:

\[
\boxed{
\iint W_\sigma(t,u)
|e^{i\tau t}-e^{i\tau u}|^2\,dt\,du
\ \le\
4F(\sigma)F'(\sigma).
}
\tag{1}
\]

**Неравенство (1) для всех \(\sigma>0,\tau\in\mathbb R\) этой выкладкой не доказано.** Тождество \((★)\) не показывает отрицательность полной формы: оно показывает точную цену фазовых различий.

И важная граница: минус в этом представлении **не запрещает существование другой факторизации в положительные квадраты**.

## 4. Проверил тэта-диагонали. Здесь получился строгий отказ

Можно было надеяться: хорошо, тогда каждый тэта-член даст положительную диагональ, а смешанные члены перегруппируем отдельно.

Проверим именно это.

Для \(t\ge0\) обозначим

\[
\phi_n(t)=
\left(
4\pi^2n^4e^{9t/2}
-
6\pi n^2e^{5t/2}
\right)e^{-\pi n^2e^{2t}},
\]

\[
g_N(t)=\sum_{n=1}^{N}\phi_n(t),
\]

и построим естественное конечное приближение предыдущего интеграла:

\[
\boxed{
F_N(p)=2\int_0^\infty g_N(t)\cosh(pt)\,dt.
}
\]

**Это явно обозначенный приближённый объект, не полная \(F\).**

### Несущая деталь находится в нуле

Положим \(a_n=\pi n^2\). Прямое дифференцирование даёт

\[
\boxed{
\phi_n'(0)
=
a_ne^{-a_n}
\left(-8a_n^2+30a_n-15\right).
}
\]

Полная \(\Phi\) гладкая и чётная, поэтому

\[
\Phi'(0)=0.
\]

Следовательно,

\[
\sum_{n\ge1}
a_ne^{-a_n}
\left(-8a_n^2+30a_n-15\right)=0.
\]

Для \(n\ge2\) каждое слагаемое этой суммы отрицательно. Поэтому для любого конечного \(N\):

\[
\boxed{
\alpha_N:=g_N'(0)
=
\sum_{n>N}
a_ne^{-a_n}
\left(8a_n^2-30a_n+15\right)
>0.
}
\tag{2}
\]

**Полная сумма имеет нулевую производную. Каждое обычное конечное усечение — ненулевую.**

Это означает, что чётное продолжение \(g_N(|t|)\) имеет **излом в нуле**. Полная \(\Phi\) этого излома не имеет: его точно устраняет бесконечный хвост. Гладкость и чётность полного источника здесь опираются на тождество Якоби, а не на расположение нулей \(\xi\). L2-L2

### Излом заставляет HB-дефект стать отрицательным

**[ABSTRACT][PAPER]**

Повторное **интегрирование по частям** при фиксированном \(\sigma>0\) даёт:

\[
F_N(p)
=
\frac{2\alpha_N}{p^2}
+
O(|\tau|^{-4}),
\]

\[
F_N'(p)
=
-\frac{4\alpha_N}{p^3}
+
O(|\tau|^{-5}).
\]

Вторая формула выводится отдельно из интеграла с \(t g_N(t)\), а не дифференцированием неизвестной ошибки.

Поэтому

\[
\boxed{
\mathscr H_N(\sigma+i\tau)
=
-\frac{32\sigma\alpha_N^2}
 {(\sigma^2+\tau^2)^3}
+
O(|\tau|^{-7}).
}
\]

В частности,

\[
\boxed{
\lim_{|\tau|\to\infty}
\tau^6\mathscr H_N(\sigma+i\tau)
=
-32\sigma\alpha_N^2<0.
}
\tag{3}
\]

**Это уже доказательство отрицательной области, а не отсутствие положительного сертификата.**

В полном документе я выписал и **верхнюю оболочку** — явную оценку сверху через интегралы производных \(g_N\). На достаточно большой высоте она строго отрицательна. Таким образом, направление вывода правильное:

\[
\mathscr H_N\le U_N<0.
\]

### Конечная перенастройка коэффициентов тоже не спасает

Получилось доказать усиление.

Возьмём **любую ненулевую конечную вещественную комбинацию**

\[
g(t)=\sum_{n=1}^{N}c_n\phi_n(t)
\]

и

\[
G(p)=2\int_0^\infty g(t)\cosh(pt)\,dt.
\]

У неё обязательно существует первая ненулевая нечётная производная

\[
a=g^{(2k-1)}(0)\ne0.
\]

Тогда для каждого фиксированного \(\sigma>0\):

\[
\boxed{
\lim_{|\tau|\to\infty}
\tau^{4k+2}
\,4\operatorname{Re}\!\left(G'(p)\overline{G(p)}\right)
=
-32k\sigma a^2<0.
}
\tag{4}
\]

Смысл простой: **конечная настройка может убрать первый излом, затем несколько следующих граничных коэффициентов. Но не все сразу.** Первый оставшийся коэффициент снова создаёт отрицательный HB-знак.

Почему нельзя убрать все нечётные производные — доказано в документе: конечная комбинация исходных \(\phi_n(t)\) имеет несовместимые с чётностью скорости убывания при \(t\to+\infty\) и \(t\to-\infty\).

**Исключён ровно этот класс конечных cosh-тэта-комбинаций. Не все возможные тэта-приближения и не все возможные положительные факторизации.**

## 5. Почему это не убивает полную тэта-функцию

Здесь нельзя перепутать объекты.

У полного источника

\[
\boxed{
\Phi^{(2j-1)}(0)=0
\qquad\text{для каждого }j\ge1.
}
\]

То есть исчезает **вся последовательность** нечётных граничных коэффициентов. Механизм доказательства (4) к полной \(\Phi\) неприменим.

Более того, можно увидеть точную компенсацию.

Обозначим

\[
R_N=F-F_N.
\]

Тогда

\[
\boxed{
\begin{aligned}
\mathscr H(F)
={}&\mathscr H(F_N)+\mathscr H(R_N)\\
&+4\operatorname{Re}
\left(
F_N'\overline{R_N}
+
R_N'\overline{F_N}
\right).
\end{aligned}}
\tag{5}
\]

На больших высотах полный гладкий источник даёт убывание быстрее любой обратной степени. Поэтому в ведущем порядке

\[
R_N\sim-F_N,\qquad R_N'\sim-F_N'.
\]

Три части правой стороны (5) имеют коэффициенты при \(\tau^{-6}\):

\[
\underbrace{-32\sigma\alpha_N^2}_{\text{голова}}
\quad+\quad
\underbrace{-32\sigma\alpha_N^2}_{\text{хвост}}
\quad+\quad
\underbrace{64\sigma\alpha_N^2}_{\text{смешанный вклад}}
=0.
\]

**Вот найденная структура полного тэта-источника: обе отдельные диагональные части могут иметь неправильный знак, а смешанный вклад точно уничтожает их ведущую отрицательность.**

Но уничтожить ведущую отрицательность — ещё не доказать положительность остатка.

Это также объясняет, почему опасно говорить: «Тэта-хвост маленький, отбросим его». Он может быть маленьким в абсолютной норме и одновременно **решающим для знака после сокращения**.

## 6. Где теперь действительно искать положительный квадрат

Не в отдельных \(\phi_n\). Следующий осмысленный объект должен сохранять **полную сумму до разложения на квадраты**.

В двойном интеграле делаем замену

\[
t=v+w,\qquad u=v-w
\]

и определяем **сопряжённое тэта-ядро** — здесь это просто функция, объединяющая два сдвинутых полных источника:

\[
\boxed{
K_\sigma(w)
=
\int_{\mathbb R}
v\sinh(2\sigma v)
\Phi(v+w)\Phi(v-w)\,dv.
}
\]

Тогда точный расчёт даёт

\[
\boxed{
\mathscr H(\sigma+i\tau)
=
8\int_{\mathbb R}
K_\sigma(w)\cos(2\tau w)\,dw.
}
\tag{6}
\]

Мы знаем непосредственно:

\[
K_\sigma(w)>0.
\]

Но этого недостаточно: **положительная функция не обязана иметь положительное преобразование Фурье**.

Настоящая факторизация в квадраты выглядела бы, например, так:

\[
\boxed{
K_\sigma
=
\int h_{\sigma,a}*\widetilde h_{\sigma,a}\,d\nu(a),
\qquad \nu\ge0,
}
\tag{7}
\]

где

\[
\widetilde h(t)=\overline{h(-t)}.
\]

Это **автокорреляционная факторизация**: ядро представлено через свёртки функций с их сопряжёнными отражениями.

При законной сходимости она дала бы

\[
\boxed{
\mathscr H(\sigma+i\tau)
=
8\int
\left|\widehat h_{\sigma,a}(2\tau)\right|^2\,d\nu(a)
\ge0.
}
\]

**Вот здесь действительно появляется плюс перед квадратами.**

Но важнейшая честная граница: **функции \(h_{\sigma,a}\) я в этой попытке не построил.** Написать (7) как желаемую формулу — не доказать её. И нельзя сначала предположить положительность преобразования \(K_\sigma\), получить из неё факторизацию, а затем объявить эту факторизацию независимым доказательством того же знака.

Две живые репрезентации теперь такие:

| Репрезентация | Что требуется | Оценка |
|---|---|---|
| **Полное ядро \(K_\sigma\)** | Явно построить исходную автокорреляционную факторизацию | Решающее действие — **10/10**; построение дорогое, ориентировочно **8/10** |
| **Совместная голова–хвостовая формула (5)** | Оценить целую комбинацию после точной модульной компенсации | Решающее действие — **9/10**; начальный тест **4/10**, глобальная стоимость неизвестна |

Это оценки исследовательской стоимости, не вероятности успеха. **Выбираю первое представление**, поскольку оно с самого начала сохраняет полный источник.

## 7. Для завершения достаточно нестрогого знака

Есть ещё полезное уточнение: нам не обязательно получать строгий запас \(\mathscr H>0\) в каждой точке.

Достаточно

\[
\mathscr H(\sigma+i\tau)\ge0
\quad\text{для всех }\sigma>0,\tau\in\mathbb R.
\]

Поскольку

\[
\mathscr H=2\,\partial_\sigma|F|^2,
\]

это означает: при движении вправо квадрат модуля не уменьшается.

Предположим, что в точке \(\sigma_0+i\tau_0\), где \(\sigma_0>0\), находится нуль. Тогда для всех \(0<\sigma<\sigma_0\):

\[
0\le |F(\sigma+i\tau_0)|^2
\le |F(\sigma_0+i\tau_0)|^2=0.
\]

Получается целый отрезок нулей. Это заставило бы \(F\) быть тождественным нулём, что неверно.

**Поэтому неотрицательная сумма квадратов действительно закрыла бы нужный запрет нулей — без деления на неизвестные нули и без отдельного доказательства строгого запаса.**

---

**Итог, чувак:** полного знака мы сейчас не добили. Но добили конкретную ложную надежду: **нельзя собрать глобальную HB-положительность из этих конечных тэта-диагоналей, просто подкручивая коэффициенты.**

При этом нашли точную причину: **полная тэта-структура работает через бесконечную согласованную компенсацию граничных коэффициентов и смешанных вкладов.** Именно её должна сохранять следующая факторизация. Не общую пассивность переименовывать и не ещё одно усечение считать положительным.

**Исходный знак \(V\), полный HB-знак и SUPPORT остаются открытыми. Отрицательного свидетеля исходной \(V\) здесь нет. Репозиторий и состояние маршрута не изменены.**

## USER
Das reicht mir nicht aus. Also du musst dann sagen: Was sind unsere nächsten Schritte? Also go. Dann was machen wir jetzt? Ich verstehe es nicht ganz. Also wo gehen wir jetzt hin? Also was machen wir jetzt?

## ASSISTANT
Ы. Ich setze jetzt direkt beim vollständigen Theta-Kern an und teste konkret, ob daraus die gesuchte positive Quadratzerlegung konstruiert werden kann – oder ob auch dieser Weg scheitert.

## ASSISTANT
Ein erster konkreter Hebel ist da: Der volle Kern ist eine Ableitung einer **Autokorrelation**; jetzt kläre ich, ob diese Ableitung einen echten positiven Quadratfaktor besitzt.

## ASSISTANT
Der Zweipunkttest ist bereits vollständig bestanden. Jetzt reduziere ich den **Dreipunkttest** auf eine konkrete Theta-Ableitungsungleichung und prüfe sie für die vollständige Summe samt Rest.

## ASSISTANT
Ы. **Wir gehen jetzt zu einem konkreten Dreipunkt-Test am vollständigen Theta-Kern.** Nicht noch einmal „irgendeinen positiven Faktor finden“. Wir prüfen eine ausdrücklich hingeschriebene Ungleichung und versuchen daraus eine Regel für beliebig viele Punkte zu gewinnen.

**Den ersten analytischen Schritt habe ich bereits ausgeführt.** Er liefert tatsächlich positive Bereiche — nicht nur einen weiteren gescheiterten Ansatz.

## 1. Was wir jetzt untersuchen

Wir behalten den **vollständigen Theta-Kern** \(K_\sigma\) aus dem letzten Ergebnis. Keine abgeschnittene Theta-Summe ersetzt ihn. Die Definition der zugrunde liegenden vollständigen Quelle \(\Phi\) ist mit dem gepinnten Projektbericht abgeglichen. L2-L2

Wir normieren:

\[
k_\sigma(w)=\frac{K_\sigma(w)}{K_\sigma(0)}.
\]

**Normierung** bedeutet hier nur: Der Wert bei \(w=0\) wird eins. Das Vorzeichenproblem bleibt unverändert.

Jetzt nehmen wir drei Positionen:

\[
-h,\qquad 0,\qquad h.
\]

Ihre Wechselwirkungen bilden die Matrix

\[
G_{\sigma,h}=
\begin{pmatrix}
1&k_\sigma(h)&k_\sigma(2h)\\
k_\sigma(h)&1&k_\sigma(h)\\
k_\sigma(2h)&k_\sigma(h)&1
\end{pmatrix}.
\]

Wir wollen wissen, ob **jede gewichtete Kombination dieser drei Positionen eine nichtnegative Energie hat**. Das bedeutet **positive Semidefinitheit** dieser Matrix.

Für unseren Kern reduziert sich die noch offene Prüfung exakt auf:

\[
\boxed{
\Delta_\sigma(h)
=
1+k_\sigma(2h)-2k_\sigma(h)^2
\ge0.
}
\]

**Das ist unser nächster konkreter Prüfgegenstand.** 
\(\sigma>0\) bezeichnet die Verschiebung rechts von der kritischen Linie. \(h>0\) bezeichnet den Abstand zwischen den drei Positionen.

## 2. Was ich dafür jetzt schon hergeleitet habe

Ich habe die vollständige Quelle als ersten Theta-Term **plus ausdrücklich kontrollierten unendlichen Rest** behandelt. Der Rest bleibt Bestandteil der Rechnung.

Daraus folgt eine quantitative Ableitungsabschätzung für die volle Quelle. Sie liefert insbesondere

\[
\boxed{
0<k_\sigma(w)\le e^{-11w^2}
\qquad(\sigma>0,\ w\in\mathbb R).
}
\]

Die vollständige Herleitung und die exakten rationalen Kontrollen stehen im [neuen Ergebnisbericht](sandbox:/mnt/data/theta_hb_next_step/NEXT_STEP_FULL_THETA_GRAM_2026-09-17.md). **PAPER** heißt hier: analytische Herleitung, deren unabhängige Prüfung und **Lean-Zertifizierung** noch ausstehen.

Diese Abschätzung bezahlt bereits zwei echte Ergebnisse.

### Ausreichend getrennte Positionen sind positiv

Wenn beliebig viele Positionen mindestens \(1/2\) voneinander entfernt liegen, gilt für ihre vollständige Kernmatrix:

\[
\boxed{
[K_\sigma(x_i-x_j)]_{i,j}
\ \succeq\
\frac67K_\sigma(0)\,I.
}
\]

Das ist eine **untere Schranke** für alle Matrixdimensionen unter dieser Abstandsbedingung. Nicht nur für eine berechnete Beispielmatrix.

**Ein negativer Zeuge kann also nicht ausschließlich aus solchen ausreichend getrennten Positionen bestehen**, sofern die vorgelegte Herleitung die unabhängige Prüfung besteht.

### Beim Dreipunkt-Test sind zwei Randbereiche positiv

Für größere Abstände ergibt sich direkt:

\[
\boxed{
h\ge\frac15
\quad\Longrightarrow\quad
\Delta_\sigma(h)>\frac16.
}
\]

Für sehr kleine Abstände liefert die zusätzliche Theta-Ableitungsabschätzung:

\[
\Delta_\sigma(h)=A_\sigma h^4+O_\sigma(h^6),
\qquad A_\sigma>135.
\]

Damit ist für jedes feste \(\sigma>0\) auch

\[
\boxed{
\Delta_\sigma(h)>0
\quad\text{für hinreichend kleine }h>0.
}
\]

**Die wichtige Einschränkung:** Ich habe noch keinen ausdrücklichen, für alle \(\sigma\) gemeinsamen kleinen Radius geliefert. Deshalb darf ich die beiden positiven Randbereiche nicht einfach miteinander verbinden.

## 3. Was wir als Nächstes tatsächlich rechnen

**Jetzt bearbeiten wir die verbleibenden kleinen, aber endlichen Abstände:**

\[
\boxed{
\Delta_\sigma(h)\ge0
\qquad
\text{für }\sigma>0,\quad 0<h<\frac15.
}
\]

Dafür haben wir bereits einen konkreten Ansatz. Weil die ersten vier Taylor-Terme bis zur Ordnung drei verschwinden, gilt exakt:

\[
\boxed{
\frac{\Delta_\sigma(h)}{h^4}
=
\frac16\int_0^1(1-u)^3
\Delta_\sigma^{(4)}(uh)\,du.
}
\]

Das ist eine **Integralrestformel**: Sie ersetzt ein unbestimmtes „höhere Terme sind klein“ durch einen ausdrücklich definierten Rest.

Der nächste Arbeitsauftrag lautet:

> **Die Ableitungen des vollständigen Theta-Kerns in diesen Integralrest einsetzen und den gesamten gekoppelten Ausdruck nach unten abschätzen.**

Dabei bleiben alle gemischten Terme zusammen. Wir zerlegen nicht wieder alles in Einzelbeträge und verlieren dadurch die Kompensation.

Es gibt drei klar getrennte Ausgänge:

**Eine nichtnegative untere Schranke** schließt diesen Dreipunkt-Test auf dem angegebenen Bereich.

**Eine strikt negative obere Schranke** wäre ein echter negativer Zeuge für den vollständigen Kern — nicht für ein Theta-Ersatzobjekt.

**Eine Schranke, die null überlappt**, entscheidet nichts. Dann ändern wir die Darstellung des Restes. Wir erklären weder den Kern für negativ noch den ganzen Ansatz für unmöglich.

## 4. Wie daraus mehr als ein Dreipunkt-Ergebnis werden soll

Hier liegt die eigentliche Richtung zum Gesamtbeweis:

\[
\boxed{
\text{Dreipunkt-Test}
\ \longrightarrow\
\text{allgemeine Regel beim Hinzufügen eines Punktes}.
}
\]

Diese allgemeine Regel heißt **Schur-Rekursion**. Sie prüft, ob eine positive Matrix positiv bleibt, wenn eine weitere Position dazukommt.

Für eine bereits positiv definite Matrix \(G_N\) lautet der entscheidende neue Rest:

\[
\boxed{
s_N=K_\sigma(0)-v^*G_N^{-1}v.
}
\]

Der Vektor \(v\) enthält die Wechselwirkungen des neuen Punktes mit den bisherigen Punkten.

**Unser konstruktives Ziel ist eine Theta-spezifische Begründung von \(s_N\ge0\)** — für beliebige Punktmengen, nicht nur für drei gleichmäßig verteilte Punkte. Bei singulären Zwischenmatrizen braucht diese Formel eine gesonderte korrekte Fassung; die Inverse wird nicht einfach vorausgesetzt.

Eine solche allgemeine Regel würde die Positivität beliebig großer Kernmatrizen liefern. Daraus folgte der vollständige **HB-Zeichenbeweis** und anschließend der bereits erklärte Ausschluss der unerwünschten Nullstellen.

**Aber:** Drei positive Punkte liefern diese allgemeine Regel noch nicht. Nach einem erfolgreichen Dreipunkt-Beweis wäre die nächste Frage deshalb nicht „rechnen wir jetzt tausend größere Matrizen?“, sondern:

> **Welcher Schritt des Dreipunkt-Beweises funktioniert unabhängig von der Anzahl der Punkte?**

Nur dieser Schritt kann den Gesamtbeweis tragen.

## Die Entscheidung

**Wir bleiben bei der vollständigen Theta-Quelle und gehen in Richtung einer quellenabhängigen Schur-Rekursion.** Der unmittelbar nächste Beweisversuch ist ihr konkreter Dreipunkt-Test, mit dem oben ausgeschriebenen Integralrest.

Der erste Lieferant dafür liegt jetzt vor: volle Theta-Ableitungsabschätzungen und daraus hergeleitete positive Bereiche. **Noch offen sind die restlichen dichten Konfigurationen und der Übergang zu beliebig vielen Punkten.** Der vollständige HB-Zeichenbeweis, **SUPPORT** und das Vorzeichen der ursprünglichen Form \(V\) sind damit noch nicht geschlossen.

**Jetzt lautet die Aufgabe also nicht mehr „finde einen positiven Quadratfaktor“, sondern: Bezahle den gekoppelten Rest von \(\Delta_\sigma(h)\). Danach prüfen wir, ob dieselbe Rechnung eine allgemeine Schur-Regel liefert.**

## USER
ok. go

## ASSISTANT
Ы. Ich prüfe jetzt den gekoppelten Dreipunkt-Rest samt Ableitungsschranken für alle Abstände; ein Dreipunkt-Erfolg wird ausdrücklich nicht als Beweis für beliebig viele Punkte gewertet.

## ASSISTANT
Ы. Die globale Theta-Krümmungsschranke hält und schließt den Dreipunkt-Test sogar für ungleiche Abstände über eine Konkavitätsstruktur. Jetzt prüfe ich den entscheidenden Übergang zur Matrix.

## ASSISTANT
Ы. Der Dreipunkt-Beweis gilt für beliebige drei Positionen und alle Verschiebungen. Der Vierpunkt-Gegencheck zeigt jedoch: Dieselbe Krümmungsinformation reicht nicht; ein Modell besteht alle Dreipunkt-Tests und scheitert dort.

## ASSISTANT
Ы. **Der angekündigte Dreipunkt-Test ist geschlossen — als ausgearbeiteter Papierbeweis, sogar für beliebige drei Positionen.** Nicht nur für gleiche Abstände und nicht nur in kleinen oder großen Randbereichen.

Die rationalen und symbolischen Kontrollen sind durchgelaufen. **Eine unabhängige mathematische Abnahme und eine Prüfung im Lean-Kernel stehen noch aus.**

[**Vollständiger Beweis, Gegenchecks und nächster Arbeitsauftrag**](sandbox:/mnt/data/theta_hb_three_point/FULL_THETA_THREE_POINT_CLOSURE_2026-09-17.md)

## 1. Was jetzt tatsächlich bewiesen ist

Für den **vollständigen Theta-Kern**

\[
K_\sigma(w)=
\int_{\mathbb R}
v\sinh(2\sigma v)\,
\Phi(v+w)\Phi(v-w)\,dv
\]

und seine Normierung

\[
k_\sigma(w)=\frac{K_\sigma(w)}{K_\sigma(0)}
\]

liefert der vorgelegte Beweis:

\[
\boxed{
1+k_\sigma(2h)-2k_\sigma(h)^2>0
\qquad
\text{für alle }\sigma>0,\ h>0.
}
\]

**Damit ist die zuletzt offene Lücke \(0<h<1/5\) geschlossen.** Wir benötigen dafür keinen unbekannten kleinen Taylor-Radius mehr.

Das stärkere Ergebnis lautet:

\[
\boxed{
[K_\sigma(x_i-x_j)]_{i,j=1}^{3}\succ0
}
\]

für jedes \(\sigma>0\) und **beliebige drei verschiedene reelle Positionen** \(x_1,x_2,x_3\).

**Positive Definitheit** bedeutet: Jede nichttriviale komplexe Gewichtung dieser drei Positionen hat strikt positive Energie. Fallen Positionen zusammen, bleibt die Matrix **positiv semidefinit**; dann sind bestimmte Nullrichtungen erlaubt.

Die verwendete Quelle ist unverändert die vollständige \(\Phi\) des gepinnten Projektberichts. Ihre Geradheit und Positivität stammen aus der Theta-Struktur, nicht aus einer Annahme über die Nullstellen von \(\xi\). L2-L2

## 2. Der entscheidende neue Schritt

Der direkte Taylorrest war umständlich. Ich habe ihn durch eine **globale Vergleichsidentität** ersetzt.

Dazu betrachten wir die **logarithmische Krümmung**

\[
q(t)=-(\log\Phi(t))''.
\]

Sie misst, wie stark sich der Logarithmus der vollständigen Quelle nach unten krümmt.

Aus der vollständigen Theta-Reihe habe ich die folgende Schranke hergeleitet:

\[
\boxed{
q(t)>11,
\qquad
44q(t)-q''(t)>\frac{526}{625}>0
\quad\text{für alle }t\in\mathbb R.
}
\]

**Die zweite Ungleichung ist der neue brauchbare Lieferant.**

Dabei wurde die Quelle nicht abgeschnitten. Die Rechnung verwendet die exakte Zerlegung

\[
\Phi=\phi_1(1+\varepsilon),
\]

wobei \(\varepsilon\) **den gesamten unendlichen Rest** enthält. Die Ableitungsschranken für diesen Rest wurden neu rekonstruiert und ihre rationalen Endvergleiche exakt kontrolliert.

Der letzte Schritt ist überschaubar. Mit \(L=\log(1+\varepsilon)\) ergibt sich

\[
|L''|<\frac{2509}{2500},
\qquad
|L''''|<275.
\]

Für die Krümmung \(q_1\) des ersten Terms zeigen zwei explizite positive Polynome:

\[
q_1>16,\qquad q_1''<24q_1.
\]

Deshalb:

\[
\begin{aligned}
44q-q''
&=44q_1-q_1''-44L''+L''''\\
&>
320-44\frac{2509}{2500}-275\\
&=\boxed{\frac{526}{625}}.
\end{aligned}
\]

**Hier entsteht ein wirklich bezahlter positiver Abstand.** Nicht aus numerischer Plausibilität und nicht aus RH.

## 3. Wie diese Schranke den Dreipunkt-Rest bezahlt

Für jeden Mittelpunkt \(v\) definieren wir das **normierte Quellenprodukt**

\[
C_v(w)=
\frac{\Phi(v+w)\Phi(v-w)}{\Phi(v)^2}
=e^{-R_v(w)}.
\]

Der zugehörige **Hilfswinkel**

\[
\alpha_v(w)=\arccos C_v(w)
\]

liegt für \(w>0\) zwischen \(0\) und \(\pi/2\). Das ist eine Rechenkoordinate, keine zusätzlich angenommene geometrische Struktur.

Die neue Krümmungsschranke liefert:

\[
\boxed{
\alpha_v'(w)>0,
\qquad
\alpha_v''(w)<0.
}
\]

Der Winkel wächst also, aber seine Wachstumsgeschwindigkeit nimmt ab.

Die entscheidende Rechnung hält die gemischten Terme zusammen. Setze

\[
B_v(w)=R_v'(w)^2-
R_v''(w)\bigl(1-e^{-2R_v(w)}\bigr).
\]

Dann gilt exakt:

\[
\boxed{
B_v'(w)=
\bigl(1-e^{-2R_v(w)}\bigr)
\bigl(2R_v'(w)R_v''(w)-R_v'''(w)\bigr).
}
\]

Beide Faktoren sind für \(w>0\) positiv. Tatsächlich ergibt sich die ausdrückliche untere Schranke

\[
B_v(w)\ge
\frac{526}{625}
\left[
w^2-\frac{1-e^{-22w^2}}{22}
\right]>0.
\]

Damit ist die Winkelkonkavität **auf der ganzen positiven Halbgeraden** bewiesen. Es bleibt kein Zwischenbereich zwischen zwei lokalen Abschätzungen offen.

Aus der Konkavität folgt insbesondere:

\[
\alpha_v(2h)<2\alpha_v(h).
\]

Und daraus:

\[
\begin{aligned}
1+C_v(2h)-2C_v(h)^2
&=
\cos\alpha_v(2h)-\cos\bigl(2\alpha_v(h)\bigr)\\
&>0.
\end{aligned}
\]

### Jetzt kommt die vollständige Quelle zurück

Der vollständige normierte Kern ist eine **positive Mischung** dieser Quellenprodukte:

\[
k_\sigma(w)=\int C_v(w)\,d\mu_\sigma(v),
\]

mit dem ausdrücklich definierten Wahrscheinlichkeitsmaß

\[
d\mu_\sigma(v)=
\frac{v\sinh(2\sigma v)\Phi(v)^2}{K_\sigma(0)}\,dv.
\]

Für unseren ursprünglichen Rest erhält man deshalb die exakte Zerlegung

\[
\boxed{
\begin{aligned}
\Delta_\sigma(h)
={}&
\int
\bigl[1+C_v(2h)-2C_v(h)^2\bigr]
\,d\mu_\sigma(v)\\
&+
2\int
\bigl[C_v(h)-k_\sigma(h)\bigr]^2
\,d\mu_\sigma(v).
\end{aligned}
}
\]

**Der erste Term ist strikt positiv. Der zweite ist ein Quadrat.**

Der zweite Term heißt **Varianz**: die mittlere quadratische Abweichung der Quellenprodukte von ihrem Mittelwert.

Das ist genau die Art von gekoppelter positiver Zerlegung, die wir gesucht haben — **für den Dreipunkt-Rest**. Nicht für den gesamten HB-Defekt.

Für ungleiche Abstände liefert dieselbe Winkelkonkavität die benötigten Dreiecksungleichungen. Daraus folgt die positive Definitheit jeder dreidimensionalen Profilmatrix. Positive Mischung über \(v\) überträgt sie auf den vollständigen \(K_\sigma\).

## 4. Den Sprung zu beliebig vielen Punkten habe ich sofort angegriffen

**Dieser Sprung ist nicht automatisch erlaubt.** Dafür habe ich einen konkreten Gegencheck gebaut.

Betrachte den eigenständigen Modellkern

\[
j(w)=e^{-w^2-w^4/8}.
\]

**Das ist nicht unser Theta-Kern.**

Für ihn funktioniert dieselbe Winkelargumentation. Daher sind **alle seine Dreipunktmatrizen positiv** — auch bei ungleichen Abständen.

Aber bei den vier Positionen

\[
0,\quad\frac14,\quad\frac12,\quad\frac34
\]

entsteht eine negative Richtung.

Mit

\[
A=j(1/4),\qquad B=j(1/2),\qquad C=j(3/4)
\]

lautet der entscheidende Zweierblock:

\[
O=
\begin{pmatrix}
1-C&A-B\\
A-B&1-A
\end{pmatrix}.
\]

Für seinen Determinantenrest wurde durch rationale Exponentialeinhüllungen bewiesen:

\[
\boxed{
(1-C)(1-A)-(A-B)^2
<
-\frac1{100000}<0.
}
\]

Das ist eine **negative obere Schranke**, also ein echter Gegenbeleg. Keine negative Untergrenze und kein numerischer Eigenwertverdacht.

Damit ist ausdrücklich widerlegt:

\[
\boxed{
\text{Alle Dreipunktmatrizen positiv}
\quad\Longrightarrow\quad
\text{alle Matrixgrößen positiv}.
}
\]

**Unser Dreipunkt-Beweis bleibt bestehen. Aber seine Winkelkonkavität ist noch keine allgemeine Schur-Rekursion.** Genau diese Verwechslung würde sonst den nächsten falschen Gesamtbeweis erzeugen.

## 5. Wo wir jetzt hingehen

**Jetzt ist der vollständige Vierpunkt-Schurrest der nächste konkrete Gegenstand.**

Der Fortschritt ist dabei praktisch nutzbar: Für drei verschiedene alte Positionen ist die vollständige Matrix \(G_3\) durch den neuen Beweis positiv und invertierbar.

Kommt ein vierter Punkt dazu, enthält der Vektor \(v\) seine Wechselwirkungen mit den drei alten Punkten. Der **Schur-Rest** lautet

\[
s_4=1-v^*G_3^{-1}v.
\]

Er entscheidet, ob die zusätzliche Position die Positivität erhält.

Wir arbeiten vorzugsweise mit der äquivalenten Form **ohne Division**:

\[
\boxed{
D_4=
\det G_3-
v^*\operatorname{adj}(G_3)v
=
\det G_4.
}
\]

Die **Adjunkte** \(\operatorname{adj}(G_3)\) besteht aus den algebraischen Kofaktoren. Da \(\det G_3>0\), haben \(D_4\) und \(s_4\) dasselbe Vorzeichen.

**Der Arbeitsauftrag ist jetzt:** Die vollständigen Theta-Produkte in diesen Ausdruck einsetzen und seine gemischten Beiträge gemeinsam behandeln. Keine unbekannte uniforme Inversenschranke einschieben.

Der erste gezielte Gegencheck einer vorgeschlagenen Erhaltungsregel ist bei vier gleichmäßig verteilten Punkten:

\[
\boxed{
(1-k_\sigma(3h))(1-k_\sigma(h))
-
(k_\sigma(h)-k_\sigma(2h))^2.
}
\]

Genau an diesem Ausdruck scheitert der Modellkern oben. Eine neue allgemeine Regel muss also erklären, **welche zusätzliche Eigenschaft der vollständigen Theta-Quelle diesen Ausfall verhindert**. Für einen vollständigen Vierpunkt-Beweis muss außerdem der zweite Symmetrieblock kontrolliert werden; er wird nicht weggelassen.

**Wir starten keinen Sammellauf immer größerer positiver Matrizen.** Gesucht ist der quellenabhängige Schritt, der sich tatsächlich auf die nächste Dimension übertragen lässt.

---

**Ergebnis dieser Runde:** Die Dreipunktlücke ist im vorgelegten Papierbeweis geschlossen, einschließlich beliebiger Abstände und aller \(\sigma>0\). Das wurde nicht bloß in eine neue offene Abschätzung verschoben.

**Noch offen:** der vollständige Vierpunktrest, eine dimensionsunabhängige Schur-Regel, der gesamte **HB-Zeichenbeweis**, **SUPPORT** und das Vorzeichen der ursprünglichen Form \(V\). Ein negativer Zeuge für \(V\) wurde nicht gefunden.

Der vollständige Beweis und die ausführbaren algebraischen Kontrollen stehen im verlinkten Dokument. **Repository und Produktionsstatus bleiben unverändert.**

## USER
Blja huwak !!! Now mache der vollständige Vierpunktrest, eine dimensionsunabhängige Schur-Regel, der gesamte **HB-Zeichenbeweis**, **SUPPORT** und das Vorzeichen der ursprünglichen Form V

## ASSISTANT
Ы. Ich prüfe zuerst den Dreipunktbeweis und greife dann den vollständigen Vierpunktrest sowie die zusätzliche Theta-Eigenschaft für eine dimensionsunabhängige Fortsetzung bis **HB**, **SUPPORT** und \(V\) an.

## ASSISTANT
Der Dreipunktbeweis hält; erste Vierpunktwerte sind positiv, aber nur diagnostisch. Entscheidend ist jetzt der vollständige **Schurrest** mit allen Mischtermen und ob die positive Mischung ihn dimensionsunabhängig kontrolliert.

## ASSISTANT
Der volle Vierpunkt-**Schurrest** zerfällt in einen gemittelten Profilrest plus nichtnegative Varianz. Für alle Dimensionen muss die Kompensation der vollständigen Mischung erhalten bleiben; einzelne Theta-Profile wären zu stark.

## ASSISTANT
Ы. **Den vollständigen Vierpunktrest schließt jetzt ein rechnergestützter Papierbeweis. Die gesamte Kette bis zum Vorzeichen von \(V\) habe ich dagegen nicht geschlossen.** Ich habe die globale Fortsetzung mitgeprüft und dabei eine entscheidende Grenze gefunden: **Die profilweise Fortsetzung unseres bisherigen Beweises auf alle Dimensionen ist für die echte Theta-Quelle unmöglich. Die vollständige Mischung bleibt davon ausdrücklich unberührt.**

Das ist der tatsächliche Stand — nicht fünf neue Namen für fünf angeblich erledigte Aufgaben.

[**Vollständiger Beweis mit rationalem Intervallzertifikat, globaler Schur-Identität und den bedingten Übergängen zu SUPPORT und \(V\)**](sandbox:/mnt/data/theta_hb_global_attempt/FULL_THETA_FOUR_POINT_AND_GLOBAL_BOUNDARY_2026-09-17.md)

**Papierbeweis** bedeutet hier: analytische Herleitung mit ausgeführten exakten Rechenkontrollen. Eine unabhängige mathematische Abnahme und eine Prüfung im **Lean-Kernel** stehen noch aus.

## 1. Deine fünf Forderungen — und was davon jetzt tatsächlich steht

| Forderung | Ergebnis |
|---|---|
| **Vollständiger Vierpunktrest von \(K_\sigma\)** | Positiver Papierbeweis für **alle \(\sigma>0\)** und **beliebige vier verschiedene Positionen**, ohne Abstandsbedingung. |
| **Dimensionsunabhängige Schur-Regel** | Eine exakte Identität und das vollständige algebraische Kriterium sind bewiesen. **Die Theta-spezifische Vorzeichenfortpflanzung bleibt unbewiesen.** |
| **Gesamtes HB-Vorzeichen** | Nicht geschlossen. Der entscheidende innere Bereich bleibt offen. |
| **SUPPORT** — einseitiger Träger des ursprünglichen \(Y\) | Aus dem vollständigen HB-Vorzeichen sauber hergeleitet. **Diese Voraussetzung ist noch nicht bezahlt.** |
| **Vorzeichen der ursprünglichen Form \(V\)** | Eine exakte bedingte Quadratdarstellung ist hergeleitet. **Ihr Einsatz für die tatsächliche Quelle benötigt weiterhin den vollständigen Vorzeichenbeweis.** |

Wichtig: **\(K_\sigma\) und \(V\) sind verschiedene Kerne.** Der Vierpunktbeweis für \(K_\sigma\) wird nicht als Vierpunktbeweis für \(V\) ausgegeben. Die ursprüngliche Definition von \(V\) bleibt die aus dem gepinnten Quellenbericht. L2-L2

## 2. Der Vierpunktrest ist wirklich geschlossen

Wir verwenden weiterhin

\[
K_\sigma(w)=
\int_{\mathbb R}
v\sinh(2\sigma v)\,
\Phi(v+w)\Phi(v-w)\,dv,
\qquad
k_\sigma(w)=\frac{K_\sigma(w)}{K_\sigma(0)}.
\]

**\(\Phi\)** bleibt die vollständige Theta-Quelle. Keine abgeschnittene Summe übernimmt ihre Rolle.

Der neue Beweis liefert

\[
\boxed{
[K_\sigma(x_i-x_j)]_{i,j=1}^{4}\succ0
}
\]

für jedes \(\sigma>0\) und alle vier verschiedenen reellen \(x_i\).

**Positive Definitheit** heißt: Jede nichttriviale komplexe Gewichtung der vier Positionen hat strikt positive Energie.

Damit gilt auch für den vollständigen **Schur-Rest** — die Energie, die nach optimaler Berücksichtigung der ersten drei Positionen übrig bleibt —

\[
\boxed{
s_4=1-b^*G_3^{-1}b>0.
}
\]

Hier ist \(G_3\) die normierte Matrix der ersten drei Positionen. Der Vektor \(b\) enthält ihre Wechselwirkungen mit der vierten Position.

Das umfasst ungleiche Abstände, beliebig nahe verschiedene Punkte und alle \(\sigma>0\). **Einen gleichmäßigen positiven Abstand von null bei kollidierenden Punkten behaupte ich nicht.**

### Woher der neue positive Beitrag kommt

Der entscheidende zusätzliche Lieferant ist eine stärkere Abschätzung der **logarithmischen Krümmung**

\[
q(t)=-(\log\Phi(t))''.
\]

Für die vollständige Quelle ergibt sich:

\[
\boxed{
q>18,\qquad
|q'|<3q,\qquad
0<q''<10q,\qquad
q^{(4)}>-200q.
}
\tag{1}
\]

Diese Aussagen wurden nicht an ausgewählten Punkten getestet. Die Rechnung umfasst eine **vollständige rationale Intervallabdeckung** des verbleibenden kompakten Bereichs und einen **analytischen Beweis für den unbeschränkten Rest**. Auch der unendliche Theta-Schwanz bleibt eingeschlossen.

Aus (1) folgt für jedes Mittelpunktprofil

\[
C_v(w)=
\frac{\Phi(v+w)\Phi(v-w)}{\Phi(v)^2}
\]

eine positive vierte **Wronski-Determinante** — eine Determinante aus der Funktion und ihren Ableitungen.

Die entscheidende Quadratergänzung liefert nach Normierung die explizite untere Schranke

\[
\boxed{
\frac{H_4}{C_v^4Q^6}\ge\frac{143}{216}>0,
\qquad Q=(-\log C_v)''.
}
\]

Eine im Dokument bewiesene **Chebyshev-Lemma** über Auswertungsdeterminanten überträgt diese Ableitungsinformation auf beliebige vier Positionen. Erst danach wird über \(v\) gemittelt.

**Das ist der zusätzliche Beweisschritt gegenüber der letzten Runde.** Nicht bloß eine weitere positive Beispielmatrix. **[ABSTRACT][PAPER]**

## 3. Die dimensionsunabhängige Identität steht ebenfalls

Hier habe ich nicht bei vier Punkten aufgehört.

Wir behalten drei feste Anker und schreiben für jedes Profil:

\[
A_v=[C_v(a_i-a_j)]_{i,j=1}^{3},
\qquad
b_v(x)=(C_v(a_i-x))_{i=1}^{3}.
\]

Für die vollständige Mischung setzen wir

\[
A=\mathbb E A_v,\qquad
b(x)=\mathbb E b_v(x),
\]

wobei \(\mathbb E\) das Mittel mit dem **festen positiven Theta-Gewicht** bezeichnet.

Definiere die optimalen Koeffizienten

\[
z_v(x)=A_v^{-1}b_v(x),
\qquad
z(x)=A^{-1}b(x).
\]

Dann gilt für den vollständigen **Restkern**

\[
r_\sigma(x,y)=k_\sigma(x-y)-b(x)^*A^{-1}b(y)
\]

die exakte Identität

\[
\boxed{
\begin{aligned}
r_\sigma(x,y)
={}&\mathbb E\,r_v(x,y)\\
&+\mathbb E\!\left[
(z_v(x)-z(x))^*
A_v
(z_v(y)-z(y))
\right].
\end{aligned}
}
\tag{2}
\]

Dabei ist

\[
r_v(x,y)=C_v(x-y)-b_v(x)^*A_v^{-1}b_v(y).
\]

Der zweite Term ist eine **Matrixvarianz**: ein echter positiver Kern aus den Abweichungen der profilweisen Koeffizienten vom gemeinsamen Optimum.

**Identität (2) gilt gleichzeitig für beliebig viele zusätzliche Positionen.** Wir brauchen dafür nicht bei jeder neuen Dimension eine andere ungeprüfte Inverse einzuführen.

Für eine zusätzliche Position \(x\) ist die Diagonale von (2) positiv: Der erste Term ist durch den Vierpunktbeweis positiv, der zweite ein Quadrat. Damit ist \(s_4>0\) bezahlt.

Aber für viele zusätzliche Positionen brauchen wir die ganze quadratische Form:

\[
\boxed{
\begin{aligned}
&\sum_{i,j}\overline{c_i}c_j\,
\mathbb E\,r_v(x_i,x_j)\\
&\quad+
\int
\left\|
\sum_i c_iA_v^{1/2}\bigl(z_v(x_i)-z(x_i)\bigr)
\right\|^2
d\mu_\sigma(v)
\ge0.
\end{aligned}
}
\tag{3}
\]

**Genau diese globale Ungleichung habe ich nicht hergeleitet.**

Die Varianz ist nichtnegativ. Daraus folgt noch nicht, dass sie jeden negativen Beitrag des gemittelten Profilrests ausgleicht.

**Die dimensionsunabhängige Identität ist bezahlt. Ihre vollständige Vorzeichenaussage ist es nicht.** **[ABSTRACT][PAPER für (2); CONDITIONAL für (3)]**

## 4. Warum wir nicht einfach dieselbe Profilrechnung bis zur Unendlichkeit fortsetzen dürfen

Hier liegt die wichtigste Korrektur unserer bisherigen Richtung.

Man könnte versuchen, den ersten Term in (2) dadurch positiv zu machen, dass **jedes einzelne \(C_v\)** in jeder Dimension positiv ist. Diese stärkere Forderung ist für unsere echte Quelle ausgeschlossen.

Betrachte

\[
\mathcal W_\Phi(v,\omega)=
\int_{\mathbb R}
\Phi(v+w)\Phi(v-w)e^{-2i\omega w}\,dw.
\]

Das ist, bis auf die positive Normierung, die **Wigner-Funktion**: die Fourier-Transformierte des Quellenprodukts um einen festen Mittelpunkt.

Wären alle Profile \(C_v\) in sämtlichen Dimensionen positiv definit, dann wäre \(\mathcal W_\Phi\) überall nichtnegativ.

**Hudsons Satz** besagt jedoch: Für einen reinen normierten Zustand ist eine überall nichtnegative Wigner-Funktion nur bei einer gaußförmigen Zustandsfunktion möglich. Der Originalsatz wurde geprüft. 

Unsere vollständige Theta-Quelle ist nicht gaußförmig. Schon \(q''>0\) aus (1) schließt eine konstante logarithmische Krümmung aus.

Daher folgt:

\[
\boxed{
\text{Mindestens ein echtes Theta-Profil besitzt
in einer höheren Dimension eine negative Richtung.}
}
\]

Nach dem neuen Vierpunktbeweis benötigt eine solche Richtung mindestens fünf verschiedene Positionen. Das ist ein **Existenzbeweis**, kein numerisch ausgegebener Zeuge mit konkreten Koordinaten.

**Und jetzt die entscheidende Trennung:**

\[
\boxed{
\text{Ein negatives Profil}
\quad\not\Rightarrow\quad
\text{eine negative vollständige Theta-Mischung}.
}
\]

Die gemeinsame Mischung kann die negativen Profilbeiträge kompensieren. Genau deshalb dürfen wir ihre gemischten Terme nicht wegwerfen.

**Damit ist die Strategie „jedes Profil separat für alle Dimensionen positiv machen“ widerlegt. Nicht der vollständige Theta-Ansatz und nicht \(V\).**

## 5. Die Übergänge zu HB und SUPPORT sind vollständig ausgeschrieben — mit sichtbarer Voraussetzung

Der Zusammenhang zum **HB-Defekt** lautet weiterhin exakt

\[
\mathscr H(\sigma+i\tau)
=
4\operatorname{Re}\!\left(F'(p)\overline{F(p)}\right)
=
8\widehat K_\sigma(2\tau).
\]

Wenn die vollständige Gram-Positivität — also (3) für alle endlichen Konfigurationen — bewiesen ist, folgt

\[
\mathscr H\ge0.
\]

Dann ist

\[
\partial_\sigma|F|^2\ge0.
\]

Ein Nullwert rechts von der imaginären Achse würde deshalb einen ganzen horizontalen Abschnitt von Nullwerten erzwingen. Das widerspricht der Identitätstheorie für die nichttriviale ganze Funktion \(F\).

Erst danach darf man im Inneren sicher teilen und erhält

\[
\operatorname{Re}\frac{F'}F\ge0,
\qquad
M(p)=\frac1{1+F'/F}.
\]

Damit ist **derselbe ursprüngliche \(M\)** holomorph und beschränkt in der rechten Halbebene. Ein im Dokument ausgeführter Konturverschiebungsbeweis zeigt dann

\[
\boxed{
\operatorname{supp}\mathcal F^{-1}m
\subseteq[0,\infty).
}
\]

Das ist **SUPPORT** für das ursprüngliche \(Y\), nicht für einen anderen positiven Ersatz. Der Multiplikator und das bereits bekannte Quellenproblem bleiben unverändert. L2-L2

Der noch offene Bereich lässt sich dabei genau festhalten:

\[
\boxed{
0<\sigma<\frac12,\qquad \tau\in\mathbb R.
}
\]

Für \(\sigma>1/2\) folgt das entsprechende vollständige Vorzeichen bereits aus der klassischen Positivität von \(\operatorname{Re}(\xi'/\xi)\) bei \(\operatorname{Re}s>1\). Das ist ein bekannter äußerer Bereich, kein neuer Erfolg dieser Runde. 

## 6. Auch für die ursprüngliche Form \(V\) gibt es jetzt die genaue bedingte Quadratdarstellung

Unter dem **vollständigen** HB-Vorzeichen liegen die Nullstellen von

\[
X(z)=\xi(1/2-iz)
\]

auf der reellen Achse. Bezeichne sie mit \(\gamma\), ihre Vielfachheiten mit \(m_\gamma\), und behalte die ursprüngliche Normierung

\[
f=\frac{\Phi}{\|\Phi\|_2}.
\]

Definiere die **Fourier-Halblinienintegrale**

\[
\psi_\gamma(x)=
\int_0^\infty f(x+t)e^{-i\gamma t}\,dt.
\]

Dann ergibt sich exakt

\[
\boxed{
V(x,y)=
\sum_{\gamma\in Z(X)}
m_\gamma\,
\overline{\psi_\gamma(x)}\psi_\gamma(y).
}
\tag{4}
\]

Damit wäre für beliebige endliche komplexe Gewichtungen

\[
\boxed{
\sum_{i,j}\overline{c_i}V(x_i,x_j)c_j
=
\sum_\gamma m_\gamma
\left|\sum_jc_j\psi_\gamma(x_j)\right|^2
\ge0.
}
\]

Im Dokument sind die Normierung, die gepaarte Summenkonvergenz, die Vielfachheiten und die Identifikation mit dem ursprünglichen Integral

\[
V(x,y)=
\int_0^\infty(x+y+2t)f(x+t)f(y+t)\,dt
\]

ausgeführt. Es wird keine Einfachheit der Nullstellen angenommen.

**Aber die Frequenzen \(\gamma\) sind hier nur wegen der noch offenen vollständigen Vorzeichenprämisse reell.** Deshalb ist (4) ein sauberer Abschluss **nach** Bezahlung dieser Prämisse — kein unabhängiger Beweis, mit dem man sie rückwärts erschleichen könnte. **[ABSTRACT][CONDITIONAL]**

## Was diese Runde tatsächlich verändert

Wir haben nicht bloß „drei Punkte“ durch „vier Punkte“ ersetzt.

**Erstens:** Der vollständige Vierpunktrest besitzt jetzt einen positiven Beweis mit kontrollierter vollständiger Quelle.

**Zweitens:** Die globale Profil-für-Profil-Fortsetzung ist mathematisch ausgeschlossen. Damit ist klar, dass eine bloße Leiter immer größerer Profilmatrizen den Gesamtbeweis nicht liefern wird.

**Drittens:** Für beliebige Dimensionen liegt die genaue gemeinsame Restformel (2) vor. Sie bewahrt die positive Varianz und sämtliche gemischten Beiträge. **Die eine noch unbezahlte Aussage ist ihre globale Quellenungleichung (3).** Die Übergänge von dort zu HB, SUPPORT und der ursprünglichen \(V\) sind ausdrücklich getrennt hergeleitet.

**Ich habe (3) nicht bewiesen und gebe die fertigen Anschlussformeln nicht als ihren Beweis aus.** Ein negativer Zeuge für den vollständigen \(K_\sigma\) oder die ursprüngliche \(V\) wurde ebenfalls nicht gefunden.

Die Richtung ist damit eindeutig: **Nicht die einzelnen Profile immer weiter positiv machen, sondern die tatsächliche Kompensation ihrer vollständigen Mischung beweisen.** Genau dort muss der globale Vorzeichenbeweis ansetzen.

## USER
Die Richtung ist damit eindeutig: **Nicht die einzelnen Profile immer weiter positiv machen, sondern die tatsächliche Kompensation ihrer vollständigen Mischung beweisen. Einverstanden! go!**

## ASSISTANT
Ы. Ich greife jetzt die vollständige Mischung an: zuerst die gemeinsame Restidentität prüfen, dann eine Quellenabschätzung suchen, die ihre negativen Beiträge tatsächlich bezahlt.

## ASSISTANT
Die Restidentität ist algebraisch bestätigt; jetzt teste ich, ob die Varianz wirklich trägt. Gegenchecks prüfen weit verschobene Testpakete und mögliche Divergenz ungefalteter Theta-Expansionen.

## ASSISTANT
Die Varianz scheitert als globaler Reparaturmechanismus: weit von festen Ankern verschwindet sie. Ich teste daher, ob negative Eigenwerte des gemittelten Rests wenigstens summierbar kontrolliert werden können.

## ASSISTANT
Ы. **Für die vollständige Mischung habe ich eine ausdrückliche positive Untergrenze auf einem ganzen Frequenzband hergeleitet. Den globalen Kompensationsbeweis habe ich nicht geschlossen.** Beim Angriff auf die gemeinsame Restformel ist außerdem eine wichtige Einschränkung sichtbar geworden: **Die positive Anker-Varianz ist keine gleichmäßig verfügbare Reserve für das globale Vorzeichen.**

[**Beweisversuch mit vollständigen Herleitungen und genauen Grenzen**](sandbox:/mnt/data/theta_full_mixture/FULL_MIXTURE_COMPENSATION_ATTEMPT_2026-09-17.md) · [**Ausgeführte Prüfprogramme und Protokolle**](sandbox:/mnt/data/theta_full_mixture_checks_2026-09-17.zip)

Die Aussagen unten sind **Papierresultate** mit ausgeführten rationalen und symbolischen Kontrollen. Eine unabhängige mathematische Abnahme und eine Prüfung im **Lean-Kernel** stehen noch aus.

## 1. Eine echte Untergrenze für die vollständige Mischung

Wir behalten unverändert

\[
F(p)=\xi\!\left(\frac12+p\right),
\qquad
\mathscr H(p)=4\operatorname{Re}\!\left(F'(p)\overline{F(p)}\right)
\]

und

\[
K_\sigma(w)=
\int_{\mathbb R}
v\sinh(2\sigma v)\,
\Phi(v+w)\Phi(v-w)\,dv.
\]

Dabei gilt

\[
\mathscr H(\sigma+i\tau)=8\widehat K_\sigma(2\tau).
\]

**\(\Phi\)** ist die vollständige Theta-Quelle des gepinnten Quellenberichts, nicht eine abgeschnittene oder positiv ersetzte Funktion. L2-L2

Das neue Ergebnis lautet:

\[
\boxed{
\mathscr H(\sigma+i\tau)
\ge
\frac{121}{6561}\,
4F(\sigma)F'(\sigma)
>0
\qquad
\left(\sigma>0,\quad |\tau|\le\sqrt{20}\right).
}
\tag{1}
\]

**Das gilt für alle \(\sigma>0\) und jedes \(\tau\) im angegebenen Band.** Es ist keine Stichprobe und keine Aussage nur über drei oder vier Punkte.

Es ist allerdings auch **kein Beweis der vollständigen Kompensation bei beliebig hohen Frequenzen**.

### Wie die untere Schranke entsteht

Ich habe das rationale Quellenzertifikat aus der letzten Runde erneut ausgeführt. Es bestätigt die benötigte Abschätzung

\[
q(t):=-(\log\Phi(t))''>18.
\]

Die Prüfung umfasst wieder sämtliche **2048 rationalen Intervalle** und den analytisch kontrollierten unbeschränkten Rest. Die analytische Herleitung dieses Quellenzertifikats bleibt Bestandteil des vorherigen Papierbeweises; der erneute Programmlauf ist keine unabhängige Begutachtung.

Aus dieser Krümmung folgt für

\[
C_v(w)=\frac{\Phi(v+w)\Phi(v-w)}{\Phi(v)^2}
=e^{-R_v(w)}
\]

die Abschätzung

\[
R_v''(w)>36.
\]

Jetzt arbeiten wir mit der **vollständigen Mischung**. Normiere sie als Wahrscheinlichkeitsdichte in \(w\):

\[
p_\sigma(w)=
\frac{K_\sigma(w)}
{\displaystyle\int_{\mathbb R}K_\sigma(u)\,du}.
\]

Das ist eine andere Normierung als \(k_\sigma=K_\sigma/K_\sigma(0)\); beide werden im Beweis getrennt gehalten.

Für ihre **Momente** — die Integrale ihrer geraden Potenzen — ergibt partielle Integration:

\[
\boxed{
m_{2r}:=\int w^{2r}p_\sigma(w)\,dw
\le
\frac{2r-1}{36}\,m_{2r-2}
\qquad(r\ge1).
}
\tag{2}
\]

Insbesondere

\[
m_2\le\frac1{36},
\qquad
m_6\le\frac5{36}m_4,
\qquad
m_4\ge m_2^2.
\]

Die letzte Ungleichung ist schlicht die Nichtnegativität der **Varianz von \(w^2\)**.

Nun verwenden wir die für alle reellen \(u\) gültige untere Hülle

\[
\cos u\ge
1-\frac{u^2}{2}
+\frac{u^4}{24}
-\frac{u^6}{720}.
\]

Damit folgt für die Fourier-Transformierte der vollständigen Mischung

\[
\frac{\widehat K_\sigma(2\tau)}
{\displaystyle\int K_\sigma}
\ge
1-2\tau^2m_2+
\frac23\tau^4
\left(1-\frac{\tau^2}{54}\right)m_2^2.
\]

Für \(s=\tau^2/18\le10/9\) ist das mindestens

\[
P(s)=1-s+\frac{s^2}{6}-\frac{s^3}{18}.
\]

Dieses Polynom fällt auf dem betreffenden Bereich, und die Endrechnung ist exakt:

\[
\boxed{
P(10/9)=\frac{121}{6561}>0.
}
\]

Das bezahlt (1).

**Der Gewinn ist eine tatsächliche untere Hülle der vollständigen Quelle.** Die Rechnung endet nicht bei „der Rest sieht klein aus“.

### Was daran dimensionsunabhängig ist

Für jede **\(L^2\)-Testfunktion**, deren Fourier-Transformierte im Band

\[
[-2\sqrt{20},\,2\sqrt{20}]
\]

liegt, erhalten wir eine positive untere Schranke ihrer vollständigen Faltungsenergie. Dieser Testraum ist unendlichdimensional.

**Er ist aber ein echter Teilraum.** Beliebige endliche Punktpakete oder beliebige kompakte Testfunktionen sind dadurch nicht abgedeckt. Daraus folgt insbesondere noch kein vollständiger Vorzeichensatz für \(V\).

## 2. Die Anker-Varianz kann nicht die globale Reserve sein

Hier muss ich unsere vorherige Arbeitsrichtung präzisieren.

Die gemeinsame **Schur-Identität** — die Zerlegung nach Berücksichtigung fester Anker — ist korrekt. Schreibe ihren positiven Varianzterm als \(\mathcal M\). Dann gilt exakt:

\[
\mathbb E r_v+\mathcal M
=
(k_\sigma-S)+(S-B)
=
k_\sigma-B.
\tag{3}
\]

Der positive \(S\)-Anteil der Varianz steht also **mit umgekehrtem Vorzeichen bereits im mittleren Profilrest**. Wir dürfen ihn nicht wie einen zusätzlichen, unabhängig gewonnenen Energiebetrag behandeln.

Ich habe das mit einer ganzen Testklasse geprüft, nicht nur mit einer Beispielmatrix.

Fixiere die drei Anker bei

\[
-1,\quad0,\quad1.
\]

Nimm ein beliebiges endliches Testpaket mit Positionen \(x_i\) und Gewichten \(c_i\). Verschiebe **das gesamte Paket** um \(T\).

Die vollständige Quellenenergie bleibt exakt gleich:

\[
\sum_{i,j}\overline{c_i}
k_\sigma\bigl((x_i+T)-(x_j+T)\bigr)c_j
=
\sum_{i,j}\overline{c_i}k_\sigma(x_i-x_j)c_j.
\]

Das ist **Translationsinvarianz**: Nur die Abstände zwischen den Testpunkten zählen.

Die Anker-Varianz verhält sich anders. Mit dem Abstand \(d(T)\) des verschobenen Pakets von den festen Ankern gilt:

\[
\boxed{
0\le
\sum_{i,j}\overline{c_i}
\mathcal M(x_i+T,x_j+T)c_j
\le
\frac{57}{17}\|c\|_1^2e^{-36d(T)^2}
\longrightarrow0.
}
\tag{4}
\]

**Die Quellenenergie bleibt bestehen. Die angebliche Reserve verschwindet.**

Damit ist die stärkere Behauptung widerlegt, ein fester positiver Anker-Varianzterm könne überall einen gleichmäßigen Energieboden bereitstellen.

Das bedeutet **nicht**, dass die vollständige Mischung negativ ist. Es bedeutet auch nicht, dass die Schur-Zerlegung nutzlos wäre. Sie kann lokale, durch die Anker verursachte Defekte exakt ausgleichen.

Aber:

> **Der globale Vorzeichenbeweis muss den translationsinvarianten Teil der vollständigen Mischung kontrollieren. Er kann nicht allein aus der Positivität einer festen Ankerkorrektur entstehen.**

Die ausführliche Rechnung zeigt sogar, dass dieser Varianzoperator **spurklassig** ist — seine gesamte Operatorgröße ist in einem präzisen Sinn summierbar. Auch das macht deutlich: Er ist eine lokalisierte Korrektur, kein neuer globaler Quellenboden.

## 3. Beim direkten Theta-Zerlegen steckt eine echte Divergenz

Danach habe ich den anderen naheliegenden Versuch geprüft: Die vollständige Mischung in **positive Theta-Diagonalen plus gemischte Beiträge** zerlegen.

Auf der ungefalteten ganzen Integrationsgeraden geht das nicht ohne Weiteres.

Für den einzelnen Theta-Summanden gilt exakt

\[
\phi_n(v)=n^{-1/2}\phi_1(v+\log n).
\]

Betrachte bei \(w=0\) seine positive Diagonalenergie:

\[
D_n(\sigma)=
\int_{\mathbb R}
v\sinh(2\sigma v)\,\phi_n(v)^2\,dv.
\]

Im relevanten Bereich \(0<\sigma<1/2\) ist jedes einzelne Integral endlich. Trotzdem ergibt sich für hinreichend große \(n\)

\[
D_n(\sigma)\ge
c_\sigma n^{2\sigma-1}\log n,
\qquad c_\sigma>0.
\]

Folglich:

\[
\boxed{
\sum_{n\ge1}D_n(\sigma)=+\infty,
\qquad
K_\sigma(0)<\infty.
}
\tag{5}
\]

**Die getrennte positive Diagonalsumme ist unendlich, während die vollständige kompensierte Größe endlich ist.**

Das widerspricht nicht der Theta-Reihe. Bei jedem festen \(v\) konvergiert sie. Aber auf der negativen Halbgeraden haben die einzelnen Summanden unterschiedliche Vorzeichen. Die vollständige modulare Kompensation ist dort bereits für die Integrabilität entscheidend.

Deshalb ist eine Rechnung der Form

> „Wir integrieren zunächst jede positive Diagonale und bezahlen anschließend den Rest“

in dieser rohen Darstellung unzulässig.

Auch dieses Ergebnis verwirft **nur diese konkrete Zerlegung**, nicht eine andere vollständige Quadratdarstellung.

### Die Konvergenz lässt sich exakt reparieren

Man muss die **Geradheit der vollständigen Quelle vor der Expansion** benutzen:

\[
\boxed{
K_\sigma(w)
=
2\int_0^\infty
v\sinh(2\sigma v)\,
\Phi(v+|w|)\,
\Phi\bigl(|v-|w||\bigr)\,dv.
}
\tag{6}
\]

Jetzt sind beide Quellenargumente nichtnegativ. Dort sind alle Theta-Summanden positiv.

Die daraus entstehende doppelte Quellenreihe konvergiert tatsächlich **absolut in \(L^1\)**. Ihre Fourier-Transformation darf deshalb mit der Summation vertauscht werden.

**Damit ist die Darstellung legal. Ihr Fourier-Vorzeichen ist dadurch noch nicht positiv.** Genau diese beiden Aussagen dürfen wir nicht wieder miteinander verwechseln.

## 4. Auch die neuen Momentabschätzungen habe ich gegen einen falschen Gesamtschluss geprüft

Es wäre verführerisch, aus der gesamten Familie (2) — immerhin unendlich vielen Momentabschätzungen — globale Fourier-Positivität abzuleiten.

Das wäre ebenfalls falsch.

Der glatte Modellkern

\[
j(w)=
\exp\!\left[-18w^2-\frac{18^2}{8}w^4\right]
\]

erfüllt dieselben Momentmajoranten. Trotzdem besitzt seine Vierpunktmatrix an den Positionen

\[
0,\quad
\frac1{4\sqrt{18}},\quad
\frac2{4\sqrt{18}},\quad
\frac3{4\sqrt{18}}
\]

eine negative Richtung.

Der relevante Determinantenrest wurde mit rationalen Exponentialeinhüllungen kontrolliert. Seine **obere Schranke** erfüllt

\[
\boxed{
D\le U<-\frac1{100000}<0.
}
\]

Das ist ein echter Gegenbeleg gegen die generische Schlussregel, kein negativer Zahlenverdacht.

**Der Modellkern ist nicht die Theta-Quelle.** Er widerlegt weder unseren bisherigen Theta-Vierpunktbeweis noch das Vorzeichen von \(V\). Er zeigt lediglich: Auch die neue Momentkontrolle darf nicht unbemerkt zum vollständigen Vorzeichenbeweis hochgestuft werden.

Der Literaturabgleich passt dazu: Csordas unterscheidet ausdrücklich zwischen der Existenz positiver assoziierter Quellenkerne und deren zusätzlicher **Fourier-Positivität**. Die entsprechenden vollständigen Zeichenbedingungen sind eigenständige mathematische Anforderungen. 

## 5. Was daraus für den vollständigen Kompensationsbeweis folgt

Die Richtung **„vollständige Mischung statt einzelne Profile“** bleibt richtig. Aber zwei vermeintliche Vereinfachungen sind jetzt ausgeschlossen:

**Die feste Anker-Varianz** liefert keinen globalen Boden. 
**Die rohe Ganzgeraden-Diagonalsumme** liefert nicht einmal ein endliches positives Budget.

Die brauchbare Darstellung ist deshalb die **vor der Fourier-Auswertung modular gefaltete vollständige Quellenreihe** aus (6). Dort müssen die Fourier-Beiträge **gemeinsam und mit ihrem Vorzeichen** kontrolliert werden.

Ein gewöhnlicher absoluter Restbetrag reicht nicht für alle Höhen: Er bleibt bei fester Abschneidung positiv, während der zu beweisende Fourier-Wert gegen null geht. Benötigt wird eine **frequenzabhängige gekoppelte Abschätzung**, welche die tatsächliche Kompensation erhält.

Der bekannte äußere Bereich \(\sigma>1/2\) ist durch die klassische Positivität von \(\operatorname{Re}(\xi'/\xi)\) bei \(\operatorname{Re}s>1\) abgedeckt. Das wird nicht als neuer Erfolg dieser Runde gezählt. 

Der in dieser Rechnung weiterhin unbezahlte Bereich ist:

\[
\boxed{
0<\sigma<\frac12,
\qquad
|\tau|>\sqrt{20}.
}
\]

**Dort habe ich die erforderliche gekoppelte Quellenabschätzung nicht gefunden.** Die Angabe dieses Bereichs ist keine Behauptung, dass andere klassische Teilresultate dort ausgeschlossen wären.

### Die Bilanz

**Bezahlt:** eine ausdrückliche untere Schranke der vollständigen Mischung auf einem ganzen Frequenzband; ein quantitativer Translationssatz für die Anker-Varianz; die Divergenzdiagnose und ihre korrekte modulare Konvergenzreparatur.

**Nicht bezahlt:** die vollständige Kompensation bei allen Frequenzen. Deshalb bleiben der globale **HB-Zeichensatz**, **SUPPORT** und das Vorzeichen der ursprünglichen Form **\(V\)** offen. Einen negativen Zeugen für die vollständige Mischung oder \(V\) habe ich ebenfalls nicht gefunden.

**Wir dürfen jetzt weder die positive Varianz noch die konvergente Quellenreihe als den fehlenden Beweis ausgeben. Der nächste tragende Schritt muss eine echte vorzeichenbewahrende Abschätzung der gefalteten Gesamtquelle sein — nicht eine fünfte Punktzahl und nicht ein neuer Name für dieselbe offene Ungleichung.**

## USER
Der nächste tragende Schritt muss eine echte vorzeichenbewahrende Abschätzung der gefalteten Gesamtquelle sein — nicht eine fünfte Punktzahl und nicht ein neuer Name für dieselbe offene Ungleichung. ok. einverstanden. go!

## ASSISTANT
Ы. Ich greife jetzt die gefaltete Gesamtquelle direkt an: zuerst die exakte Fourier-Formel, danach eine gekoppelte untere Restschranke, die alle entscheidenden Auslöschungen erhält.

## ASSISTANT
Die absolute Konvergenz legitimiert Summe–Integral-Austausch. Jetzt teste ich eine gemeinsame komplexe Konturverschiebung, die hohe Frequenzen dämpft, ohne Kopf und Schwanz getrennt abzuschätzen.

