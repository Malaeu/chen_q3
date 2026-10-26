# STATUS: TRY_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46

```yaml
OPERATIVE_CLASS: TRY_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46
REQUEST_ID: Q46_ORIGINAL_P_STRATEGIC_ROLLBACK
DATE: 2026-10-26
LANGUAGE: ru
SOURCE: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_SPARSE_BAND
SOURCE_BASE_COMMIT: 519d21fa02d65f5f60f7b5497ebc957c9dd2a4a7
PACKET_BYTES: 144321
PACKET_LF: 2537
PACKET_SHA256: f12272c56c0d65abc1a93171cad52581bbb841ee91c083523e1b0a4678101a3b
SOURCE_BODIES: 13
MANIFEST: VERIFIED
CONSUMER_PROGRESS: NO_PROGRESS
NEW_CONSUMER_EXPONENT: NOT_PROVED
NEW_PAIR_MARGIN: NOT_PROVED
AUXILIARY_RESULT: ACTUAL_PRIME_POWER_MESH_RECONSTRUCTION_WITH_FULL_SIGNED_MASS_RETURN
EXTERNAL_INPUT: BAKER_HARMAN_PINTZ_2001_THEOREM_1_STATEMENT_CHECKED
EXTERNAL_PROOF_RECERTIFICATION: NOT_PERFORMED
VERIFIER: PAPER
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
RH: OPEN_NOT_CLAIMED
PX_RH_CLAIM: NOT_MADE
ALL_P_GOAL: OPEN
CONDITIONAL_ZF78: NOT_USED_NOT_UPGRADED
CF22_PYSR: PARKED_REOPENABLE
INDEPENDENT_NEW_AUDIT: NOT_RUN
LEAN: NOT_RUN
ARB: NOT_RUN
PRODUCTION_CCM_SPECTRUM: NOT_RUN
REPOSITORY_WRITES: NONE
PACKAGE_INSTALLATIONS: NONE
NEXT_QUESTION_DISPATCH: NONE
```

Ы. **Независимого знакового арифметического входа, закрывающего исходный потребитель, в этой попытке не получено.** Проверен один отличный от Q06/Q07/Q10/Q45 перенос: использовать доказанную мелкость промежутков между настоящими простыми для совместной интерполяции исходного матричного ядра на поддержке настоящей меры Мангольдта.

Результат разделён строго:

* геометрическая ошибка такой интерполяции на **всём исходном \(P\)** оплачивается исчезающей с \(\epsilon\) степенью;
* после точного возвращения арифметических масс остаётся полная знаковая сумма с коэффициентами \(\Lambda(n)-\ell_n\), а не с нулевыми коэффициентами;
* доказанный факт о расстояниях между простыми не даёт нужного знака этой суммы. Её точный накопленный коэффициент содержит прежний \(E\) с коэффициентом **один**.

Поэтому малый интерполяционный остаток **не назван уменьшением основного арифметического долга**. Это выполненная проверка применимости конкретного внешнего входа, а не новый RH-критерий, готовый supplier или запрет CCM. Основное математическое требование Q46 — независимый направленный выигрыш — осталось невыполненным.

## 1. Source lock и границы чтения

Канонический вход:

```text
PROSHKA_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46_2026-10-26.txt
144321 bytes; 2537 LF
SHA256 f12272c56c0d65abc1a93171cad52581bbb841ee91c083523e1b0a4678101a3b
```

Прочитан весь TXT, включая все 13 source bodies и все исторические приложения S1. Проверены UTF-8, финальный LF, размер и SHA-256 каждого тела, его порядок и единственный separator LF вне тела. Общий хеш вычислен в этом запуске; в коротком сообщении Q46 он не был задан. Полный manifest приведён ниже. Исторические программы и команды из источников **не исполнялись**.

Из GitHub-коннектора прочитан `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, ветка `rh_clean`, возвращённый blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Единственное выбранное поручение — root Q46. Никакой очереди или другого OPEN-задания не выбиралось; запись в репозиторий не производилась.

Используемые статусы upstream сохраняются:

| Источник | Что используется здесь | Чего чтение не доказывает заново |
|---|---|---|
| S1–S2 | точная \(C^0\), лучший полный fallback, once-paid short/arch returns | новый знак, независимая сертификация всей Q45-цепи |
| S3 | исходный sparse carrier, три контакта, условный adverse receiver | существование внепрямого нуля или благоприятный спектральный upper |
| S4–S5 | физическое представление \(Q_M\), точный непрерывный возврат \(-H_d\) | знак центрированной арифметической формы |
| S6–S8 | уже проверенные ограничения endpoint/displacement/phase-подходов | невозможность совместного знакового сокращения |
| S9–S11 | conditional smoothing/variance и точная граница RH-зависимого импорта | безусловная strong variance |
| S12–S13 | pair-only polylog reduction и ограничение infinite-collapse | перенос аналитичности на весь \(P\), новый Gaussian receiver |

Ни S12, ни S13 не расширяются. В частности, здесь не применяется растущий порядок производных к произвольному исходному тесту и не заменяется настоящий источник одним Gaussian.

## 2. Выбранный дополнительный арифметический факт

### 2.1. E1: точная внешняя формулировка

R. C. Baker, G. Harman, J. Pintz, **The difference between consecutive primes, II**, *Proc. London Math. Soc.* (3) **83** (2001), 532–562, Theorem 1, печатная p. 532; DOI `10.1112/plms/83.3.532`.

Используется только следующее безусловное утверждение:

\[
\exists x_0\ \forall x>x_0:\quad
[x-x^{21/40},x]\text{ содержит простое.}
\tag{2.1 E1}
\]

Первичный PDF открыт, формулировка сверена по тексту и screenshot первой страницы. Источник:

```text
https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf
```

Полное внешнее доказательство, его sieve-оценки и численные интегралы не пересертифицировались. Это применение опубликованной теоремы, а не её новое доказательство. Бинарная загрузка PDF в контейнер не удалась; **SHA-256 самого внешнего PDF здесь не подтверждён**. Это ограничение не относится к проверенному manifest пользовательского TXT.

Не используется утверждение, что \(21/40\) — лучший известный показатель. Более поздние претензии на улучшение не нужны данному переносу. Не импортируются распределение весов \(\log p\), асимптотика их локальных сумм, variance или RH.

### 2.2. Точный геометрический вывод из E1

Положим \(\vartheta=21/40\). Для каждого достаточно большого вещественного \(x\) есть простое в

\[
(x,x+3x^{\vartheta}].
\tag{2.2}
\]

Действительно, применим (2.1) к \(y=x+3x^{\vartheta}\). При достаточно большом \(x\) имеем \(y\le2x\), поэтому
\(y^{\vartheta}\le2^{\vartheta}x^{\vartheta}<2x^{\vartheta}\). Значит,
\(y-y^{\vartheta}>x\). Все пороги фиксированы и не зависят от вектора в \(P\).

**Именно (2.2) — новая для выбранной попытки независимая арифметическая строка.** Она отличает настоящую поддержку простых от произвольного разреженного набора узлов. Но это информация о положении атомов, не об их массах. Весь дальнейший расчёт проверяет, достаточно ли её после возвращения \(\Lambda\).

### 2.3. Почему это не повтор ранее испытанных входов

Нет движения \(P\), как в Q06; нет вывода знака из displacement rank Q07; нет smoothing/variance-входа Q10; нет zero-selective inverse, forcing-sign или внутреннего суммирования Эйлера Q45. Интерполируется **вся исходная матрица на реальной арифметической поддержке**, без разложения её элементов на независимо оплачиваемые компоненты.

В то же время интерполяция как аналитический инструмент классическая. Более того, обычная целочисленная квадратура уже была дешёвой. Поэтому даже успешная оплата новой геометрии не считается автоматически прогрессом. Она должна была дать дополнительное независимое сравнение масс; ниже проверено, что такого сравнения из E1 не выведено.

## 3. Исходный объект и полная производная матричного теста

Все параметры неизменны:

\[
N=m,\quad L=\log m,\quad M=R=\lfloor m^\epsilon\rfloor,
\quad 0<\epsilon<1/32,\quad \Omega=2\pi M/L.
\tag{3.1}
\]

\(\epsilon\) фиксируется до \(m\to\infty\). \(P\) — исходный трёхконтактный проектор. Для \(c=Pc\) положим

\[
f(t)=L^{-1/2}\sum_{|j|\le M}c_j e^{2\pi ijt/L},\quad0\le t\le L,
\]

и продолжим \(f\) нулём вне окна. Тогда
\(\|f\|_2=\|c\|_2\), \(f(0)=f(L)=0\), оба исходных экспоненциальных контакта сохранены. Пишем

\[
\mathcal Q(s)=P Q_M(s)P,\qquad
\mathsf W(x)=x^{-1/2}\mathcal Q(\log x),\quad1\le x\le m.
\tag{3.2}
\]

Полные обе временные стороны стоят внутри \(Q_M\). Для любого комплексного \(c=Pc\)

\[
c^*\mathcal Q(s)c
=2\Re\int_{\mathbb R}\overline{f(t)}f(t+s)\,dt.
\tag{3.3}
\]

### Лемма 3.1 — ровно тот порядок гладкости, который нужен

`[ABSTRACT | PAPER]` На \([0,L]\)

\[
\|\mathcal Q(s)\|\le2,\quad
\|\mathcal Q'(s)\|\le2\Omega,\quad
\|\mathcal Q''(s)\|\le2\Omega^2.
\tag{3.4}
\]

Доказательство. Нулевое продолжение \(f\) принадлежит \(H^1(\mathbb R)\), потому что значения на обоих концах равны нулю. Для его автокорреляции первая производная спаривает \(f\) и \(f'\), а вторая — \(-f'\) и сдвиг \(f'\). Вторая производная непрерывна: эквивалентно, \(\xi^2|\widehat f(\xi)|^2\) интегрируема. Получаем для каждого \(c\)

\[
|q_c(s)|\le2\|c\|^2,\quad
|q_c'(s)|\le2\Omega\|c\|^2,\quad
|q_c''(s)|\le2\Omega^2\|c\|^2.
\]

Матрицы производных эрмитовы; оценки всех квадратичных форм дают (3.4) без платы за размерность. Это сохраняет все поляризованные mixed terms, а не только диагонали. **Глобальная \(C^\infty\)-гладкость продолжения не предполагается.**

Отсюда

\[
\mathsf W''(x)=x^{-5/2}
\left[\mathcal Q''(\log x)-2\mathcal Q'(\log x)
                       +\tfrac34\mathcal Q(\log x)\right],
\]

\[
\boxed{\|\mathsf W''(x)\|
\le D_\Omega x^{-5/2},\quad
D_\Omega=2\Omega^2+4\Omega+\tfrac32
\le2(1+\Omega)^2.}
\tag{3.5}
\]

Никакого нового \(P\) между операторами не вставлено. Этот расчёт согласуется с уже использованными derivative bounds; новизной источника (3.5) не объявляется.

### Точная исходная центрированная форма

По S4–S5,

\[
A_m=\sum_{n\le m}\Lambda(n)\mathsf W(n),\quad
\int_1^m\mathsf W(x)\,dx=-H_d,\quad0\preceq H_d\preceq4P,
\]

\[
C_m^0=A_m+H_d
=-\int_1^m E(x)\mathsf W'(x)\,dx,\qquad E(x)=\psi(x)-(x-1).
\tag{3.6}
\]

\(\mathsf W(m)=0\) — исходный physical overlap, а не бесплатно занулённый сглаженный символ. Сумма по \(\Lambda\) содержит **все** \(p^k\). Её эквивалентная \(\mu\)-запись остаётся

\[
A_m=\sum_{dk\le m}\mu(d)\log k\,\mathsf W(dk).
\tag{3.7}
\]

Далее меняется только представление непрерывной меры; ни один коэффициент (3.7) не заменяется.

## 4. Совместная интерполяция на всех настоящих prime-power узлах

### 4.1. Сетка и края

Пусть

\[
B=\lceil m^{2\epsilon}\rceil,
\qquad a=\min\{p\ge B:p\text{ простое}\}.
\tag{4.1}
\]

Для всех достаточно поздних ячеек E1 даёт
\(B\le a\le B+3B^{\vartheta}\le2B<m\). Это вспомогательный порог, **не** новый production \(R\).

Упорядочим все степени простых в \([a,m)\) и добавим конечную точку \(m\):

\[
a=x_0<x_1<\cdots<x_J=m.
\tag{4.2}
\]

Если \(m\) само является prime power, оно учитывается ровно один раз; иначе последний узел виртуален с \(\Lambda(m)=0\). Все внутренние узлы — настоящие атомы. Даже когда \(x_i\) — собственная степень простого, следующий простой из (2.2) даёт

\[
\Delta_i:=x_{i+1}-x_i\le3x_i^{\vartheta},\qquad x_{i+1}\le2x_i.
\tag{4.3}
\]

Обрезанный последний промежуток также удовлетворяет этому верху. Не требуется гипотеза о распределении prime powers по отношению друг к другу.

Пусть \(\varphi_i\) — обычные кусочно-линейные hat-функции на этой сетке, включая односторонние endpoint hats. Они удовлетворяют

\[
\sum_i\varphi_i(x)=1,\quad\sum_i x_i\varphi_i(x)=x,
\quad\varphi_i\ge0,
\]

\[
\ell_i=\int_a^m\varphi_i(x)dx,
\quad
\ell_0=\Delta_0/2,\quad
\ell_i=(\Delta_{i-1}+\Delta_i)/2\ (0<i<J),\quad
\ell_J=\Delta_{J-1}/2.
\tag{4.4}
\]

Полные массы и первые моменты точны:

\[
\sum_i\ell_i=m-a,\qquad
\sum_i\ell_i x_i=(m^2-a^2)/2.
\tag{4.5}
\]

В частности, \(\ell_i\) **не назначаются** равными \(\Lambda(x_i)\).

### 4.2. Точная матричная формула до неравенств

Определим

\[
\Gamma_{m,a}
=\sum_{i=0}^J[\Lambda(x_i)-\ell_i]\mathsf W(x_i),
\tag{4.6}
\]

\[
C_{<a}=\sum_{n<a}\Lambda(n)\mathsf W(n)-\int_1^a\mathsf W(x)dx,
\]

\[
\mathcal R_{\rm geom}
=\frac12\sum_{i=0}^{J-1}\int_{x_i}^{x_{i+1}}
(x-x_i)(x_{i+1}-x)\mathsf W''(x)\,dx.
\tag{4.7}
\]

Тогда

\[
\boxed{C_m^0=\Gamma_{m,a}+C_{<a}+\mathcal R_{\rm geom}.}
\tag{4.8}
\]

Это равенство всей матрицы, до модулей. Для его доказательства дважды интегрируем по частям на каждом промежутке:

\[
\frac{v-u}{2}[\mathsf W(u)+\mathsf W(v)]-\int_u^v\mathsf W(x)dx
=\frac12\int_u^v(x-u)(v-x)\mathsf W''(x)dx.
\tag{4.9}
\]

Сумма trapezoid coefficients есть (4.4). Из исходной дискретной меры вычитается эта **полная** сумма, а затем возвращается (4.9). Не утверждается ни \(\mathsf W''\succeq0\), ни положительность (4.7). Последний атом сохраняется в определениях, и только его исходное значение \(\mathsf W(m)=0\) зануляет вклад в форму.

## 5. Полная цена нового переноса

### Теорема 5.1 — вспомогательный all-\(P\) возврат

`[COFINAL_FAMILY | PAPER + E1]` Для каждого фиксированного \(\epsilon\in(0,1/32)\), на всех достаточно поздних исходных ячейках,

\[
\boxed{
\|C_m^0-\Gamma_{m,a}\|
\le u_{m,\epsilon}:=16\sqrt a
   +10(1+\Omega)^2a^{-9/20}.
}
\tag{5.1}
\]

Следовательно,

\[
u_{m,\epsilon}
=O_\epsilon\left(m^\epsilon+
                    \frac{m^{11\epsilon/10}}{L^2}\right)
=O_\epsilon(m^{11\epsilon/10}).
\tag{5.2}
\]

#### Доказательство нижнего блока

Применяем только унаследованный безусловный \(\sum_{n\le x}\Lambda(n)/\sqrt n\le6\sqrt x\) и \(\|\mathcal Q\|\le2\):

\[
\|C_{<a}\|
\le12\sqrt a+4(\sqrt a-1)\le16\sqrt a.
\tag{5.3}
\]

Полный \(a\)-атом находится в (4.6), а не в (5.3). В нижнем блоке сохранены все собственные степени простых.

#### Доказательство геометрической части

Из (3.5), (4.7), (4.3):

\[
\|\mathcal R_{\rm geom}\|
\le\frac{D_\Omega}{12}\sum_i\Delta_i^3x_i^{-5/2}
\le\frac{3D_\Omega}{4}\sum_i\Delta_i x_i^{-29/20}.
\]

Так как \(x\le2x_i\) на каждом промежутке,

\[
\sum_i\Delta_i x_i^{-29/20}
\le2^{29/20}\int_a^m x^{-29/20}dx
\le2^{29/20}\frac{20}{9}a^{-9/20}.
\]

Числовое неравенство \(2^{29/20}<3\) даёт

\[
\|\mathcal R_{\rm geom}\|
\le5D_\Omega a^{-9/20}
\le10(1+\Omega)^2a^{-9/20}.
\tag{5.4}
\]

Это размерностно-независимый верх для матрицы, одновременно для всех комплексных исходных векторов. Никаких новых profile/Fourier/contact errors нет: функции и пространство вообще не менялись.

Из \(a\asymp m^{2\epsilon}\), \(\Omega\asymp m^\epsilon/L\) получается (5.2). Малая добавка \(1\) в \(1+\Omega\), округление \(B\), и невычисленный фиксированный порог E1 поглощаются eventual onset и константой при фиксированном \(\epsilon\). Не предполагается onset, равномерный при \(\epsilon\downarrow0\).

### Что именно изменил E1

Без ограничения геометрии произвольная поддержка может иметь промежутки порядка \(x\), и (5.4) с отрицательной степенью нижнего порога не следует. E1 разрешил перейти к **только истинным prime-power узлам** с полной контролируемой ошибкой.

Однако на всех целых узлах интерполяционная геометрия и без E1 ещё дешевле. Значит, (5.1) не закрывает ранее неизвестную главную арифметическую обязанность: он лишь показывает, что при этой проверке проблема возникает не из-за редкости поддержки. Это важное ограничение полезности результата; реконструкционная оценка не засчитывается как новый полный показатель CCM.

## 6. Полное возвращение масс: первая неоплаченная строка

Проверим, что новое представление действительно сохранило информацию, а не спрятало её в небольшом символе.

Положим

\[
d_j=\sum_{i=0}^j[\Lambda(x_i)-\ell_i],\qquad
E(a^-)=\psi(a^-)-(a-1).
\]

Для \(j<J\) из точного телескопирования (4.4)

\[
\sum_{i=0}^j\ell_i=\frac{x_j+x_{j+1}}2-a,
\]

поэтому

\[
\boxed{d_j=E(x_j)-E(a^-)-\frac{\Delta_j}{2},\qquad j<J,}
\tag{6.1}
\]

\[
\boxed{d_J=E(m)-E(a^-).}
\tag{6.2}
\]

Никакого предположения о знаке \(E\) нет. При \(a\) prime левый след \(\psi(a^-)\) обязателен: использование \(\psi(a)\) удалило бы \(a\)-атом.

Полное дискретное Abel-равенство:

\[
\boxed{
\Gamma_{m,a}
=\sum_{j=0}^{J-1}d_j[\mathsf W(x_j)-\mathsf W(x_{j+1})]
+d_J\mathsf W(m).
}
\tag{6.3}
\]

Последний член нулевой по исходному overlap; все прочие сохраняются. Значит, после совместного восстановления настоящих масс **\(E(x_j)\) вновь имеет коэффициент один**. E1 контролирует \(\Delta_j\), но не снабжает направленной оценкой спаривание (6.3).

Первая недоказанная строка выбранного способа — не существование интерполятора, а

\[
\sup_{\substack{c=Pc\\\|c\|=1}}
\sum_i[\Lambda(x_i)-\ell_i]c^*\mathsf W(x_i)c
\le D_\epsilon m^{\theta(\epsilon)},
\qquad\theta(\epsilon)\to0.
\tag{6.4 OPEN}
\]

**(6.4) не выведено.** Оно не принимается в предпосылки, не получает нового имени supplier и не объявляется легче исходной цели. В силу (5.1) это эквивалентный долг с малой оплаченной разностью. Тем самым требование Q46 о самостоятельном неэквивалентном signed input в этом запуске **не выполнено**.

Условие E1 не приравнивает длину ячейки к \(\log p\); не даёт ни \(\sum|\Lambda-\ell|\ll m^{o(1)}\), ни знака корреляции с \(c^*\mathsf Wc\). Неравенство (6.4) требует именно этой дополнительной информации о настоящих массах и исходном тесте, которой в используемой формулировке E1 нет.

## 7. Проверки границ вывода

### 7.1. Непрерывный контроль: ноль до модулей

Нельзя после замены \(d\psi=dt\) механически оставить формулу, использовавшую атомарную поддержку. Полная карта для произвольной конечной меры \(\nu\) такова. Пусть

\[
I\mathsf W=\sum_i\varphi_i\mathsf W(x_i),\quad
r=\mathsf W-I\mathsf W,\quad
\alpha_i(\nu)=\int_{[a,m]}\varphi_i\,d\nu.
\]

Тогда точно

\[
\begin{aligned}
C^0[\nu]={}&C_{<a}[\nu]
 +\sum_i[\alpha_i(\nu)-\ell_i]\mathsf W(x_i)\\
&+\int_{[a,m]}r\,d\nu-\int_a^m r(x)dx.
\end{aligned}
\tag{7.1}
\]

Для настоящей \(\nu=d\psi\) имеем \(\alpha_i=\Lambda(x_i)\) и \(\int r\,d\nu=0\): все атомы находятся в узлах. Это возвращает (4.8). Для \(\nu=dt\) имеем \(\alpha_i=\ell_i\), два интеграла \(r\) сокращаются, и \(C_{<a}[dt]=0\). Итак,

\[
\boxed{C^0[dt]=0}
\]

**точно до оценки**. Нет раздельной оплаты большого непрерывного фона. Сам \(H_d\) не добавляется дважды при возвращении к CCM.

### 7.2. Негативный контроль вне actual source class

Он нужен только против неверного вывода «мелкая положительная атомарная сетка уже определяет знак». На той же конечной сетке возьмём массы \(\ell_i\), затем изменим одну внутреннюю массу на \(\pm\ell_i/2\). Обе меры положительны, имеют идентичную поддержку и те же промежутки. Для линейного теста \(g(x)=m-x\) исходная trapezoid формула точна, а изменение центрированной формы равно

\[
\pm\frac{\ell_i}{2}(m-x_i).
\]

Получены оба знака при неизменной геометрии. **Это не \(\Lambda\) и не допустимый CCM-тест**, поэтому контроль не опровергает (6.4), не даёт lower для спектра и не устанавливает невозможность арифметического сокращения. Он только ловит подмену mass-информации support-информацией. Нужная настоящая связь может использовать существенно больше свойств \(\Lambda\), чем E1.

### 7.3. Все mixed и prime-power члены

В формулах (4.6)–(7.1) стоит единая матрица \(\mathsf W\). Для произвольного комплексного \(c\) все \(\overline c_jc_k\) сохраняются. Ни диагонализация, ни Cauchy по Fourier-индексам не использовались. При переходе через (3.7) сохраняется полная \(dk\le m\), включая \(d=1\), \(k=1\) с нулевым логарифмом и все представления одного произведения. Proper powers присутствуют как узлы со своим весом \(\log p\), а не \(\log(p^k)\).

## 8. Законное завершение и весь CCM-бюджет

### 8.1. Доступная цена после остановки знакового хода

Не строим новый оптимизированный norm certificate ради no-go. Достаточно указать один полностью законный, но недостаточный конец расчёта.

Из \(\|\mathsf W(x)\|\le2/\sqrt x\), настоящей оценки массы и положительности только **скалярных** \(\ell_i\)

\[
\|\Gamma_{m,a}\|
\le 2\sum_{a\le n\le m}\frac{\Lambda(n)}{\sqrt n}
 +2\sum_i\frac{\ell_i}{\sqrt{x_i}}.
\tag{8.1}
\]

На каждой ячейке с \(v\le2u\)

\[
\frac{v-u}{2}(u^{-1/2}+v^{-1/2})
\le\sqrt2\int_u^v x^{-1/2}dx.
\]

Поэтому

\[
\sum_i\frac{\ell_i}{\sqrt{x_i}}
\le2\sqrt2(\sqrt m-\sqrt a),
\qquad
\boxed{\|\Gamma_{m,a}\|\le18\sqrt m.}
\tag{8.2}
\]

Это **верхняя цена** данного завершения, не необходимая цена всех методов и не lower для actual \(\Gamma\). Никакого спектрального no-go из неё не выводится.

Совместно с (5.1), (3.6)

\[
C_m^0\preceq[18\sqrt m+u_{m,\epsilon}]P,
\qquad A_m=C_m^0-H_d\preceq[18\sqrt m+u_{m,\epsilon}]P.
\tag{8.3}
\]

Полный показатель (8.3) — \(1/2\). Главная цена не стала \(11\epsilon/10\); это был лишь показатель **ошибки карты**.

### 8.2. Точный conditional return, без принятия недоказанного входа

Для проверки потребителя: **если бы** (6.4) было независимо поставлено с верхом \(s_\Gamma\), то

\[
\begin{aligned}
T_{>R}&\preceq[s_\Gamma+u_{m,\epsilon}+b_{\rm div}]P,\\
PK_mP&\succeq-[s_\Gamma+u_{m,\epsilon}+50L+8]P,
\end{aligned}
\tag{8.4 CONDITIONAL_MAP_ONLY}
\]

\[
b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\tag{8.5}
\]

При \(s_\Gamma=D_\epsilon m^{\theta(\epsilon)}\) full exponent можно было бы взять \(\max\{\theta(\epsilon),2\epsilon\}\to0\). (8.4) не является результатом с таким \(s_\Gamma\), поскольку (6.4) открыто.

Здесь нет нового projection fee: весь перенос уже на исходном \(P\). Нет отдельной pp-платы: все pp остались в (4.6). Нет pair/self-return: source-pair в этом опыте не деформировалась и не использовалась как замена all-\(P\) задачи. Архимедова плата добавляется один раз. Короткая делительная плата добавляется только в \(T_{>R}\), не ещё раз в прямую нижнюю оценку \(K_m\).

### 8.3. Сохраняется более сильный прежний fallback

Из S1–S2 сохраняем, не доказывая заново:

\[
s_{\rm keep}=W_{<}(m)+W(\lfloor\sqrt m\rfloor)
\le6\sqrt m+6m^{1/4},
\]

\[
\boxed{
T_{>R}\preceq[s_{\rm keep}+b_{\rm div}]P,\qquad
PK_mP\succeq-[s_{\rm keep}+50L+8]P.
}
\tag{8.6}
\]

Новый \(u_{m,\epsilon}\) не прибавляется к (8.6): это другой, уже прямой source upper. Платы Q32 и Q45 тоже не начисляются повторно. Условные \(3/8\) сохраняют ровно прежнюю ZF78-зависимость; здесь она не использовалась и не доказана.

### 8.4. Ledger

| Утверждение | Вывод | Scope / verifier |
|---|---|---|
| Канонический TXT и 13 тел | размеры, LF, SHA-256, границы совпали | FINITE_CELL / PAPER: точный byte-check |
| E1 | настоящий prime mesh имеет \(\Delta\le3x^{21/40}\) eventually | COFINAL_FAMILY / PAPER: внешний theorem, statement checked |
| Полная signed interpolation | (4.8), без изменения \(P\) | ABSTRACT / PAPER |
| Ошибка реконструкции | (5.1), \(O_\epsilon(m^{11\epsilon/10})\) | COFINAL_FAMILY / PAPER + E1 |
| Накопленные настоящие массы | (6.1)–(6.3), коэффициент \(E\) равен 1 | ABSTRACT / PAPER |
| Геометрия \(\Rightarrow\) нужный signed upper | не выведено | COFINAL_FAMILY / CONDITIONAL, OPEN |
| Выписанный full trial | (8.3), степень \(1/2\) | COFINAL_FAMILY / PAPER + E1 |
| Лучший full fallback | (8.6), inherited | COFINAL_FAMILY / PAPER |
| Негативный toy-контроль | оба знака при той же сетке и иных массах | ABSTRACT / PAPER; не actual source |

## 9. Обоснованный откат и точное стратегическое решение

**Завершается попытка использовать только частоту встречаемости атомов как дополнительный вход в signed comparison.** Внешняя теорема применима, её геометрический возврат посчитан. Но она не касается коэффициентов \(\Lambda(x_i)-\ell_i\), и независимого upper для них я не вывел.

Откат — к документированной в S4–S5 **первой полной центрированной физической форме до scalar discrepancy / norm completion**:

\[
\begin{aligned}
\langle c,C_m^0c\rangle
={}&2\Re\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n}
       \int_{\mathbb R}\overline{f(t)}f(t+\log n)dt\\
&-2\Re\int_0^L e^{s/2}
       \int_{\mathbb R}\overline{f(t)}f(t+s)dt\,ds,
\qquad f=F_Mc,\ c=Pc.
\end{aligned}
\tag{9.1}
\]

Карта назад точна: (4.8) с полной \(C_{<a}+\mathcal R_{\rm geom}\) возвращает (9.1), добавочная ошибка **ноль**. Откат не выдаётся за новый результат. Отличие этой точки от отвергнутых sufficient certificates — сохранён совместный знак реальных масс и достижимой корреляции, а не positive parts, отдельные интервальные нормы или максимальная пустота поддержки.

**Минимальная недоказанная строка не изменилась:** независимый upper для (9.1) с \(\eta(\epsilon)\to0\), или ранее принятый более слабый коэффициентный запас на всей настоящей паре. Нового полезного механизма для этой строки я здесь не получил. Это честная остановка, не предложение ещё раз отправить ту же норму под новым названием.

Для протокольной проверки двух вариантов представления, без запуска новой ветки:

| Представление | Проверяемый различитель | Стоимость / kill-power |
|---|---|---|
| Полная first moment (9.1), S4–S5 | новая лемма должна использовать настоящие массы до их раздельной оплаты; непрерывный контроль равен 0 | нет новой analytic-map платы; прямо проверяет требуемый знак, но supplier не найден |
| Полная long-\(\mu\) pair-сумма S12, с уже оплаченной polylog \(k\)-поддержкой | нужен количественный signed estimate на действительной комплексной \(C\), а не новый uniform Mertens upper | receiver и prefix уже paid; меньший sufficient consumer, не all-\(P\); повтор этих карт не допускается |

Эти две строки — не каталог новых попыток. Ни одна не объявлена выбранным автоматическим Q47. Ценность текущего расчёта ограничена тем, что он не позволяет перепутать доказанную мелкость prime gaps с доказанным соответствием арифметических масс.

**DISCRIMINATOR:** для любого последующего кандидата подставить его реальный верх в (8.4), вернуть все расходы и проверить конечный показатель. Успехом считается новый направленный arithmetic bound, а не малый \(u\), конечная панель или сокращение контурного/квадратурного остатка. В данной попытке этот discriminator не пройден.

## 10. Проверки, регистрация и epistemic closeout

Перед новыми исполняемыми математическими тестами сохранён `registration_q46.json`: после полного чтения пакета и предварительного PAPER-вывода, **не** до всякого рассуждения. Предсказания не редактировались по результатам тестов.

Судьба ставок: P1 подтверждена (5.1); P2 — полной mass-return (4.6)–(4.8); P3 — (6.1)–(6.3); P4 — (7.1); P5 соблюдена явным `NO_PROGRESS` и сохранением (8.6). Алгебраические тесты проверяют чувствительные места этих формул, но не подменяют их бесконечный вывод.

Новый standard-library checker выполняет:

* точную проверку canonical packet и 13 внешних source frames, без выполнения исторического кода;
* шесть конечных arithmetic-mesh configurations, включая prime / proper-power / non-power верхние концы;
* polynomial Peano, все четыре действительные компоненты комплексно-эрмитового теста, Gaussian-rational unit-vector contraction, полный lower/upper return и дискретный Abel;
* формальные точные \(\log p\)-коэффициенты \(\mu*\log=\Lambda\), включая proper powers;
* непрерывный контроль и явный toy-контроль вне настоящего класса;
* семь planted ошибок и отдельное повреждение байта.

Полиномиальные матрицы в тестах **не являются production CCM**. Они проверяют линейные тождества до каких-либо аналитических оценок. Ни конечное наличие простых, ни эти fixtures не доказывают E1 или асимптотический знак. Доказательства (3.4)–(8.2) — PAPER; проверяющий не является Lean/Arb.

Сильнейшее возражение: «малый возврат уже был доступен на целых; новая prime-power сетка лишь переписывает старый долг». **Принято.** Поэтому `CONSUMER_PROGRESS: NO_PROGRESS`; не заявляется, что неоплаченная часть стала меньше. Внешний вход был реальным и отличающимся, но нужного source/test alignment он в выполненном переносе не дал.

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_CCM_SPARSE_BAND_T_GT_R_UPPER
ACTUAL_CONSUMER_REQUIREMENT: one-sided eta(epsilon)->0 with full original-P return
ORIGINAL_REQUESTED_OBJECT: independent arithmetic signed comparison after strategic rollback
ORIGINAL_OBJECT_IS: UNKNOWN_AS_A_NECESSARY_ROUTE
KNOWN_WEAKER_INTERFACES:
  - direct full C0 upper implies T upper and K floor through (8.4)
  - accepted complete source-pair coefficient margin; not an all-P result
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: tested primary prime-gap theorem against exact actual-mass matrix reconstruction
KILL_SCOPE: NONE
IMPOSSIBILITY_EVIDENCE: NONE_FOR_CCM_OR_RH
REOPEN_TRIGGER: independently proved directed mass/test comparison not implied merely by mesh spacing
LOOP_DETECTED: analytic reconstruction shrinks while the first signed arithmetic moment remains unpaid
CURRENT_FAILED_STRATEGY: support-spacing theorem used as a proposed mass-comparison input
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 2
FORBIDDEN_FUTURE_MOVE: infer CCM exponent from (5.2), replace Lambda by cell lengths, or count this exact return as a favorable arithmetic theorem
```

Одна архивная директива: выполнить bounded PAPER-аудит (3.4)–(6.3), особенно знака Peano-остатка, левого следа \(\psi(a^-)\), prime-power/virtual-top convention и \(11\epsilon/10\) только для ошибки карты; затем воспроизвести приложения. Не повышать статус consumer без самостоятельного (6.4)/(9.1) upper. Нового независимого аудитора в этом запуске не было.

## 11. Manifest и полные воспроизводимые приложения

Ниже — полный manifest пользовательского пакета и только **новый** код этого ответа. Все пути в командах — локальные файлы пользователя; никакой repository write или установка пакетов не требуются.

| ID | Полное имя тела | Bytes / LF | SHA-256 | Строки raw TXT |
|---|---|---:|---|---:|
| S1 | `PROSHKA_CCM_ACTUAL_MOBIUS_FORCING_SEAM_Q45_VERDICT_2026-10-26.md` | 81220 / 1586 | `2f0230ab8ed7f0a38fc7935bc06c69def094ec5a347f9d893ef6d3f6d58fb4f9` | 30–1615 |
| S2 | `CCM_Q45_CONCLUSION.md` | 3436 / 55 | `fe75c23687897d58a6c891d37cf3e2968d4957d228e80bc9f02a852a86f6e070` | 1620–1674 |
| S3 | `CCM_SPARSE_BAND_RECEIVER.md` | 6174 / 69 | `0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06` | 1679–1747 |
| S4 | `CCM_CONTINUOUS_RANK_TWO_TEST.md` | 3751 / 53 | `6c917626df5d97fae5df2cc4a5b409465e23753de2c38e7b41d47e66f0eecbe1` | 1752–1804 |
| S5 | `CCM_Q09_AUTOCORRELATION_PREFLIGHT.md` | 4828 / 91 | `8714d49b1458a5075d8c3b0b25146ed693b338b01a28ec41247fe3bfabda3435` | 1809–1899 |
| S6 | `CCM_Q06_ONE_SIDED_EDGE_BUDGET.md` | 3398 / 65 | `4ffb00e4836506cb6ceac86bd45743a3036afedef94ab8776b33aed504db7f68` | 1904–1968 |
| S7 | `CCM_Q07_DISPLACEMENT_PREFLIGHT.md` | 2757 / 44 | `d983a2be3ec1025ce56725bb3a32e021e7e0f4cd3f1625e2f952d9059e83048c` | 1973–2016 |
| S8 | `CCM_PHASE_Q07_CONCLUSION.md` | 3925 / 66 | `efc9203f38c258351726fabddd665a16afa0bbdd3ee8914a1891ed9ffdf5fb45` | 2021–2086 |
| S9 | `CCM_HIGH_ORDER_Q10_CONCLUSION.md` | 5597 / 65 | `8166015d037803313da2afea542bebeaa11ba2e85ea5de79f9167c1ba33c5f9d` | 2091–2155 |
| S10 | `CCM_Q10_GEOMETRIC_AUDIT_DISCRIMINATOR.md` | 5610 / 97 | `5b522acfd372f8732b85bc80c1a205f74140fe680e795d2ef817bb9150b73831` | 2160–2256 |
| S11 | `CCM_POST_Q45_VARIANCE_SUPPLIER_SCREEN.md` | 2562 / 39 | `b21dac1a7ca11052cd86369215be07cd34447f824787f16fbb153a200d11f205` | 2261–2299 |
| S12 | `CCM_Q45_PAIR_POLYLOG_DIVISOR_REDUCTION.md` | 8129 / 148 | `b27227aec0515c8e126a7b6cab23117bc364c67cee167dfc38f23e95c40a29d7` | 2304–2451 |
| S13 | `CCM_Q45_MOBIUS_THETA_COLLAPSE_SCREEN.md` | 4568 / 79 | `b9cebd304507db06b62132e88f43a2f9e90f6644827c00bde751d56da46f10de` | 2456–2534 |

### Воспроизведение

Сохрани тело `replay_q46.py` из соответствующего приложения в файл. Команда из каталога с Markdown и каноническим TXT:

```bash
python3 replay_q46.py \
  PROSHKA_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46_VERDICT_2026-10-26.md \
  PROSHKA_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46_2026-10-26.txt \
  q46_replay
```

Первый аргумент — этот полный Markdown; второй — byte-exact исходный TXT; третий — создаваемый каталог результатов, который можно заменить своим путём. При ином расположении замени только пути. `replay_q46.py` извлекает фиксированный набор приложений, проверяет их размеры и SHA-256, выполняет только `check_q46.py` и сравнивает весь JSON побайтно со встроенным. Исторические source bodies не исполняются.

BEGIN_ASSET registration_q46.json
BYTES: 1249
SHA256: 250c08e64af0f25c8da402f9967ad2fdc18d959105f2c49c37eafc61402e1661
```json
{
  "task": "Q46_ORIGINAL_P_STRATEGIC_ROLLBACK",
  "stage": "After full source reading and preliminary derivation, before new executable mathematical checks",
  "mechanism": "Exact barycentric interpolation on the actual prime-power mesh using the Baker-Harman-Pintz interval theorem; preserve actual Mangoldt-minus-cell masses jointly",
  "predictions": {
    "P1": "The matrix reconstruction error is bounded by a constant times (1+Omega)^2 a^(-9/20), with the original projection and all matrix cross terms unchanged.",
    "P2": "Full reconstruction retains Lambda(n)-ell_n on each actual prime-power node; the gap theorem supplies no estimate for their signed pairing by itself.",
    "P3": "A cumulative node calculation retains the actual Chebyshev discrepancy with coefficient one.",
    "P4": "The continuous control measure gives zero centered form before estimates when its interpolation remainder is also retained.",
    "P5": "No favorable full exponent is inferred from the small interpolation error; the existing full-source budget is retained if the signed mass comparison remains unpaid."
  },
  "not_run": ["Lean", "Arb", "production CCM spectrum", "independent audit", "historical source scripts"],
  "repository_writes": false
}
```
END_ASSET

BEGIN_ASSET check_q46.py
BYTES: 11327
SHA256: 3d033cf6e1652adbc98a634fcf3eaf5d960136b78e15f99fe5c56d4c58f06d88
```python
#!/usr/bin/env python3
"""Q46: exact coefficient/quadrature controls and canonical-source verification.
Standard library only. No numerical CCM spectral calculation and no prime-gap
asymptotic verification. Historical embedded programs are never executed.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re
import sys

PACKET_NAME = 'PROSHKA_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46_2026-10-26.txt'
PACKET_BYTES = 144321
PACKET_LF = 2537
PACKET_SHA = 'f12272c56c0d65abc1a93171cad52581bbb841ee91c083523e1b0a4678101a3b'
HEADER = re.compile(rb'^BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n', re.M)


def verify_packet(raw: bytes) -> dict:
    if len(raw) != PACKET_BYTES or raw.count(b'\n') != PACKET_LF:
        raise ValueError('packet length or LF mismatch')
    if hashlib.sha256(raw).hexdigest() != PACKET_SHA:
        raise ValueError('packet SHA-256 mismatch')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n'):
        raise ValueError('unexpected newline convention')
    if not raw.startswith(b'OPERATIVE_CLASS: TRY_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46\n'):
        raise ValueError('wrong operative request')
    pos = 0
    entries = []
    for i in range(1, 14):
        hit = HEADER.search(raw, pos)
        if hit is None or hit[1] != f'S{i}'.encode():
            raise ValueError('missing/out-of-order source')
        start = hit.end()
        end = start + int(hit[3])
        body = raw[start:end]
        if len(body) != int(hit[3]) or body.count(b'\n') != int(hit[4]):
            raise ValueError('source length mismatch')
        if hashlib.sha256(body).hexdigest() != hit[5].decode():
            raise ValueError('source hash mismatch')
        body.decode('utf-8')
        suffix = b'\nEND_SOURCE ' + hit[1] + b'\n'
        if raw[end:end+len(suffix)] != suffix:
            raise ValueError('source boundary mismatch')
        entries.append(dict(id=hit[1].decode(), name=hit[2].decode(),
                            bytes=len(body), lf=body.count(b'\n'),
                            sha256=hashlib.sha256(body).hexdigest(),
                            start_byte=start, end_byte=end,
                            start_line=raw[:start].count(b'\n')+1,
                            end_line=raw[:end].count(b'\n')))
        pos = end + len(suffix)
    if raw[pos:].strip():
        raise ValueError('unexpected trailing content')
    return dict(packet=PACKET_NAME, bytes=len(raw), lf=PACKET_LF,
                sha256=PACKET_SHA, source_count=len(entries),
                all_source_frames_verified=True, sources=entries)


class LL:
    """Rational linear combinations of 1 and formal log(prime)."""
    def __init__(self, terms=None):
        self.t = {int(k): F(v) for k, v in (terms or {}).items() if v}
    def __add__(self, x):
        if not isinstance(x, LL):
            x = LL({0: x})
        out = self.t.copy()
        for p, v in x.t.items():
            out[p] = out.get(p, F()) + v
        return LL(out)
    __radd__ = __add__
    def __neg__(self):
        return self * -1
    def __sub__(self, x):
        return self + (-x if isinstance(x, LL) else -F(x))
    def __rsub__(self, x):
        return -self + x
    def __mul__(self, x):
        return LL({p: v*F(x) for p, v in self.t.items()})
    __rmul__ = __mul__
    def __eq__(self, x):
        if not isinstance(x, LL):
            x = LL({0: x})
        return self.t == x.t


def factor(n):
    out = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def mobius(n):
    fs = factor(n)
    return 0 if any(a > 1 for a in fs.values()) else (-1)**len(fs)


def log_form(n):
    return LL(factor(n))


def lam(n):
    fs = factor(n)
    return LL({next(iter(fs)): 1}) if len(fs) == 1 else LL()


def psi(n):
    return sum((lam(k) for k in range(2, int(n)+1)), LL())


def add(a, b):
    c = [F() for _ in range(max(len(a), len(b)))]
    for i, v in enumerate(a): c[i] += v
    for i, v in enumerate(b): c[i] += v
    return c


def scale(a, c): return [F(c)*v for v in a]


def mul(a, b):
    c = [F() for _ in range(len(a)+len(b)-1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    return c


def deriv(a): return [i*a[i] for i in range(1, len(a))] or [F()]


def ev(a, x): return sum((v*F(x)**i for i, v in enumerate(a)), F())


def integral(a, u, v):
    return sum((c*(F(v)**(i+1)-F(u)**(i+1))/F(i+1)
                for i, c in enumerate(a)), F())


def mesh(a, m):
    nodes = [a] + [n for n in range(a+1, m) if lam(n) != 0] + [m]
    weights = [F() for _ in nodes]
    for j in range(len(nodes)-1):
        half = F(nodes[j+1]-nodes[j], 2)
        weights[j] += half
        weights[j+1] += half
    return nodes, weights


def trap(poly, nodes, weights):
    return sum((w*ev(poly, x) for x, w in zip(nodes, weights)), F())


def peano(poly, nodes):
    dd = deriv(deriv(poly))
    return sum((integral(mul([F(-u*v), F(u+v), F(-1)], dd), u, v)/2
                for u, v in zip(nodes[:-1], nodes[1:])), F())


def components(poly, a, m, nodes, weights):
    full = sum((lam(n)*ev(poly, n) for n in range(2, m+1)), LL()) - integral(poly, 1, m)
    low = sum((lam(n)*ev(poly, n) for n in range(2, a)), LL()) - integral(poly, 1, a)
    signed = sum(((lam(n)-ell)*ev(poly, n) for n, ell in zip(nodes, weights)), LL())
    geom = peano(poly, nodes)
    return full, low, signed, geom


def mathematical_checks():
    cfg = [(3,20), (5,25), (5,29), (7,30), (11,64), (17,97)]
    counts = dict(mesh_configurations=len(cfg), polynomial_peano_controls=0,
                  matrix_entry_returns=0, prefix_and_abel_controls=0,
                  formal_mangoldt_coefficients=96, continuum_controls=0)
    mutations = {}
    witnesses = []
    for a, m in cfg:
        nodes, ell = mesh(a, m)
        assert sum(ell) == m-a
        assert sum((w*x for x, w in zip(nodes, ell)), F()) == F(m*m-a*a, 2)
        for degree in range(6):
            poly = [F()]*degree + [F(1)]
            assert trap(poly, nodes, ell)-integral(poly, a, m) == peano(poly, nodes)
            counts['polynomial_peano_controls'] += 1
        base = [F(m*m), F(-2*m), F(1)]
        # Four real components of a Hermitian matrix polynomial; these are
        # algebra fixtures, NOT the physical CCM kernel.
        parts = [mul(base,[F(1),F(1,7)]),
                 mul(base,[F(-2),F(),F(1,11)]),
                 mul(base,[F(-2),F(1,3)]),
                 mul(base,[F(2),F(1,5),F(1,13)])]
        returns = []
        for poly in parts:
            assert ev(poly,m) == 0 and ev(deriv(poly),m) == 0
            full, low, signed, geom = components(poly,a,m,nodes,ell)
            assert full == low + signed + geom
            returns.append((full, low, signed, geom))
            counts['matrix_entry_returns'] += 1
            cumul = []
            d = LL()
            for j,(x,w) in enumerate(zip(nodes,ell)):
                d += lam(x)-w
                cumul.append(d)
                E_at_x = psi(x)-(x-1)
                E_a_minus = psi(a-1)-(a-1)
                gap = F(nodes[j+1]-x,2) if j+1<len(nodes) else F()
                assert d == E_at_x-E_a_minus-gap
            abel = sum((d*(ev(poly,nodes[j])-ev(poly,nodes[j+1]))
                        for j,d in enumerate(cumul[:-1])),LL()) + cumul[-1]*ev(poly,m)
            assert signed == abel
            counts['prefix_and_abel_controls'] += 1
            # Full continuum control: both interpolation errors, not only one.
            interp_error = integral(poly,a,m)-trap(poly,nodes,ell)
            assert interp_error + geom == 0
            counts['continuum_controls'] += 1
        # c=(3/5, 12/25+16i/25) is a Gaussian-rational unit vector.
        assert F(3,5)**2+F(12,25)**2+F(16,25)**2 == 1
        coeff = [F(9,25),F(16,25),F(72,125),F(-96,125)]
        contracted = [F()]
        for k,poly in zip(coeff,parts): contracted = add(contracted,scale(poly,k))
        direct = components(contracted,a,m,nodes,ell)
        for j in range(4):
            assert direct[j] == sum((k*returns[i][j] for i,k in enumerate(coeff)),LL())
        # One finite negative control: the same mesh with different positive
        # masses has either sign for the affine centered test m-x.
        affine = [F(m),F(-1)]
        middle = min(1,len(nodes)-2)
        amp = ell[middle]/2
        pos = amp*ev(affine,nodes[middle])
        neg = -pos
        assert amp>0 and ell[middle]-amp>=0 and pos>0 and neg<0
        witnesses.append(dict(a=a,m=m,nodes=len(nodes),positive_extra=str(pos),negative_extra=str(neg)))
    for n in range(1,97):
        got = sum((mobius(d)*log_form(n//d) for d in range(1,n+1) if n%d==0),LL())
        assert got == lam(n)
    # Exponent and constant controls, exact rational arithmetic.
    theta=F(21,40)
    assert F(3,2)-2*theta == F(9,20)
    assert 2-2*(F(3,2)-2*theta) == F(11,10)
    assert 2**29 < 3**20
    assert (F(7,3)-F(1,2))*(F(7,3)-F(3,2)) == F(7,3)**2-2*F(7,3)+F(3,4)
    a,m=cfg[0]
    nodes,ell=mesh(a,m)
    poly=[F(m*m),F(-2*m),F(1)]
    full,low,signed,geom=components(poly,a,m,nodes,ell)
    mutations['reverse_peano_sign'] = full != low+signed-geom
    mutations['omit_lower_prefix'] = full != signed+geom
    prime_only=sum((lam(n)*ev(poly,n) for n in range(2,m+1)
                    if len(factor(n))==1 and next(iter(factor(n).values()))==1),LL())
    mutations['delete_proper_prime_powers'] = prime_only != full+integral(poly,1,m)
    mutations['delete_virtual_endpoint_mass'] = sum(ell[:-1]) != m-a
    mutations['replace_Lambda_by_cell_mass'] = signed != 0
    mutations['omit_continuum_reconstruction'] = geom != 0
    # Removing complex mixed terms changes this exact full-source contraction.
    base=[F(m*m),F(-2*m),F(1)]
    imaginary=mul(base,[F(2),F(1,5),F(1,13)])
    mutations['drop_complex_cross_term'] = components(imaginary,a,m,nodes,ell)[0] != 0
    assert all(mutations.values())
    return dict(scope='Exact algebra on finite polynomial fixtures and true arithmetic coefficients; not original-P spectra or BHP asymptotic verification',
                passed=True, counts=counts, planted_errors_detected=mutations,
                negative_control_outside_actual_source=witnesses,
                finite_tests_do_not_prove_asymptotic_sign=True)


def main():
    if len(sys.argv)!=2:
        raise SystemExit('usage: python3 check_q46.py PATH_TO_CANONICAL_Q46.txt')
    raw=Path(sys.argv[1]).read_bytes()
    provenance=verify_packet(raw)
    bad=bytearray(raw)
    bad[provenance['sources'][0]['start_byte']+100] ^= 1
    try:
        verify_packet(bytes(bad))
    except ValueError:
        provenance['single_byte_corruption_detected']=True
    else:
        raise AssertionError('undetected corruption')
    result=dict(provenance=provenance,mathematics=mathematical_checks(),
                historical_programs_executed=False,production_spectrum_run=False,
                lean_run=False,arb_run=False)
    text=json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q46_checks.json').write_text(text,encoding='utf-8')
    print(text,end='')

if __name__=='__main__':
    main()
```
END_ASSET

BEGIN_ASSET q46_checks.json
BYTES: 6452
SHA256: 01d38e18063a37f7ea9ff588358c02b87a3f9529a2281dea058850c24df51922
```json
{
  "arb_run": false,
  "historical_programs_executed": false,
  "lean_run": false,
  "mathematics": {
    "counts": {
      "continuum_controls": 24,
      "formal_mangoldt_coefficients": 96,
      "matrix_entry_returns": 24,
      "mesh_configurations": 6,
      "polynomial_peano_controls": 36,
      "prefix_and_abel_controls": 24
    },
    "finite_tests_do_not_prove_asymptotic_sign": true,
    "negative_control_outside_actual_source": [
      {
        "a": 3,
        "m": 20,
        "negative_extra": "-8",
        "nodes": 12,
        "positive_extra": "8"
      },
      {
        "a": 5,
        "m": 25,
        "negative_extra": "-27/2",
        "nodes": 11,
        "positive_extra": "27/2"
      },
      {
        "a": 5,
        "m": 29,
        "negative_extra": "-33/2",
        "nodes": 13,
        "positive_extra": "33/2"
      },
      {
        "a": 7,
        "m": 30,
        "negative_extra": "-11",
        "nodes": 13,
        "positive_extra": "11"
      },
      {
        "a": 11,
        "m": 64,
        "negative_extra": "-255/4",
        "nodes": 20,
        "positive_extra": "255/4"
      },
      {
        "a": 17,
        "m": 97,
        "negative_extra": "-117",
        "nodes": 25,
        "positive_extra": "117"
      }
    ],
    "passed": true,
    "planted_errors_detected": {
      "delete_proper_prime_powers": true,
      "delete_virtual_endpoint_mass": true,
      "drop_complex_cross_term": true,
      "omit_continuum_reconstruction": true,
      "omit_lower_prefix": true,
      "replace_Lambda_by_cell_mass": true,
      "reverse_peano_sign": true
    },
    "scope": "Exact algebra on finite polynomial fixtures and true arithmetic coefficients; not original-P spectra or BHP asymptotic verification"
  },
  "production_spectrum_run": false,
  "provenance": {
    "all_source_frames_verified": true,
    "bytes": 144321,
    "lf": 2537,
    "packet": "PROSHKA_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46_2026-10-26.txt",
    "sha256": "f12272c56c0d65abc1a93171cad52581bbb841ee91c083523e1b0a4678101a3b",
    "single_byte_corruption_detected": true,
    "source_count": 13,
    "sources": [
      {
        "bytes": 81220,
        "end_byte": 87698,
        "end_line": 1615,
        "id": "S1",
        "lf": 1586,
        "name": "PROSHKA_CCM_ACTUAL_MOBIUS_FORCING_SEAM_Q45_VERDICT_2026-10-26.md",
        "sha256": "2f0230ab8ed7f0a38fc7935bc06c69def094ec5a347f9d893ef6d3f6d58fb4f9",
        "start_byte": 6478,
        "start_line": 30
      },
      {
        "bytes": 3436,
        "end_byte": 91277,
        "end_line": 1674,
        "id": "S2",
        "lf": 55,
        "name": "CCM_Q45_CONCLUSION.md",
        "sha256": "fe75c23687897d58a6c891d37cf3e2968d4957d228e80bc9f02a852a86f6e070",
        "start_byte": 87841,
        "start_line": 1620
      },
      {
        "bytes": 6174,
        "end_byte": 97600,
        "end_line": 1747,
        "id": "S3",
        "lf": 69,
        "name": "CCM_SPARSE_BAND_RECEIVER.md",
        "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
        "start_byte": 91426,
        "start_line": 1679
      },
      {
        "bytes": 3751,
        "end_byte": 101504,
        "end_line": 1804,
        "id": "S4",
        "lf": 53,
        "name": "CCM_CONTINUOUS_RANK_TWO_TEST.md",
        "sha256": "6c917626df5d97fae5df2cc4a5b409465e23753de2c38e7b41d47e66f0eecbe1",
        "start_byte": 97753,
        "start_line": 1752
      },
      {
        "bytes": 4828,
        "end_byte": 106490,
        "end_line": 1899,
        "id": "S5",
        "lf": 91,
        "name": "CCM_Q09_AUTOCORRELATION_PREFLIGHT.md",
        "sha256": "8714d49b1458a5075d8c3b0b25146ed693b338b01a28ec41247fe3bfabda3435",
        "start_byte": 101662,
        "start_line": 1809
      },
      {
        "bytes": 3398,
        "end_byte": 110042,
        "end_line": 1968,
        "id": "S6",
        "lf": 65,
        "name": "CCM_Q06_ONE_SIDED_EDGE_BUDGET.md",
        "sha256": "4ffb00e4836506cb6ceac86bd45743a3036afedef94ab8776b33aed504db7f68",
        "start_byte": 106644,
        "start_line": 1904
      },
      {
        "bytes": 2757,
        "end_byte": 112954,
        "end_line": 2016,
        "id": "S7",
        "lf": 44,
        "name": "CCM_Q07_DISPLACEMENT_PREFLIGHT.md",
        "sha256": "d983a2be3ec1025ce56725bb3a32e021e7e0f4cd3f1625e2f952d9059e83048c",
        "start_byte": 110197,
        "start_line": 1973
      },
      {
        "bytes": 3925,
        "end_byte": 117028,
        "end_line": 2086,
        "id": "S8",
        "lf": 66,
        "name": "CCM_PHASE_Q07_CONCLUSION.md",
        "sha256": "efc9203f38c258351726fabddd665a16afa0bbdd3ee8914a1891ed9ffdf5fb45",
        "start_byte": 113103,
        "start_line": 2021
      },
      {
        "bytes": 5597,
        "end_byte": 122779,
        "end_line": 2155,
        "id": "S9",
        "lf": 65,
        "name": "CCM_HIGH_ORDER_Q10_CONCLUSION.md",
        "sha256": "8166015d037803313da2afea542bebeaa11ba2e85ea5de79f9167c1ba33c5f9d",
        "start_byte": 117182,
        "start_line": 2091
      },
      {
        "bytes": 5610,
        "end_byte": 128552,
        "end_line": 2256,
        "id": "S10",
        "lf": 97,
        "name": "CCM_Q10_GEOMETRIC_AUDIT_DISCRIMINATOR.md",
        "sha256": "5b522acfd372f8732b85bc80c1a205f74140fe680e795d2ef817bb9150b73831",
        "start_byte": 122942,
        "start_line": 2160
      },
      {
        "bytes": 2562,
        "end_byte": 131278,
        "end_line": 2299,
        "id": "S11",
        "lf": 39,
        "name": "CCM_POST_Q45_VARIANCE_SUPPLIER_SCREEN.md",
        "sha256": "b21dac1a7ca11052cd86369215be07cd34447f824787f16fbb153a200d11f205",
        "start_byte": 128716,
        "start_line": 2261
      },
      {
        "bytes": 8129,
        "end_byte": 139573,
        "end_line": 2451,
        "id": "S12",
        "lf": 148,
        "name": "CCM_Q45_PAIR_POLYLOG_DIVISOR_REDUCTION.md",
        "sha256": "b27227aec0515c8e126a7b6cab23117bc364c67cee167dfc38f23e95c40a29d7",
        "start_byte": 131444,
        "start_line": 2304
      },
      {
        "bytes": 4568,
        "end_byte": 144304,
        "end_line": 2534,
        "id": "S13",
        "lf": 79,
        "name": "CCM_Q45_MOBIUS_THETA_COLLAPSE_SCREEN.md",
        "sha256": "b9cebd304507db06b62132e88f43a2f9e90f6644827c00bde751d56da46f10de",
        "start_byte": 139736,
        "start_line": 2456
      }
    ]
  }
}
```
END_ASSET

BEGIN_ASSET replay_q46.py
BYTES: 2754
SHA256: 44e89f4075334c8445183210559fa3a0d87f03ed46f7579909089f9ae6129b82
```python
#!/usr/bin/env python3
"""Extract and replay only the four Q46 assets from the full verdict.
Usage: python3 replay_q46.py VERDICT.md CANONICAL_Q46.txt [OUTPUT_DIRECTORY]
No historical program in the canonical packet is executed.
"""
from __future__ import annotations
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HEAD = re.compile(
    rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\n'
    rb'SHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n', re.M)
EXPECTED = {'registration_q46.json', 'check_q46.py',
            'q46_checks.json', 'replay_q46.py'}


def extract(raw: bytes) -> dict[str, bytes]:
    pos = 0
    assets = {}
    while True:
        hit = HEAD.search(raw, pos)
        if hit is None:
            break
        name = hit[1].decode('ascii')
        size = int(hit[2])
        start = hit.end()
        end = start + size
        body = raw[start:end]
        if name in assets:
            raise ValueError('duplicate asset: ' + name)
        if len(body) != size or hashlib.sha256(body).hexdigest() != hit[3].decode():
            raise ValueError('asset length/hash mismatch: ' + name)
        suffix = b'```\nEND_ASSET\n'
        if raw[end:end + len(suffix)] != suffix:
            raise ValueError('asset boundary mismatch: ' + name)
        assets[name] = body
        pos = end + len(suffix)
    if set(assets) != EXPECTED:
        raise ValueError('unexpected asset set')
    return assets


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q46.py VERDICT.md CANONICAL_Q46.txt [OUTPUT_DIRECTORY]')
    verdict = Path(sys.argv[1]).resolve()
    canonical = Path(sys.argv[2]).resolve()
    out = Path(sys.argv[3] if len(sys.argv) == 4 else 'q46_replay').resolve()
    if not canonical.is_file():
        raise FileNotFoundError(canonical)
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        (out / name).write_bytes(body)
    run = subprocess.run(
        [sys.executable, str(out / 'check_q46.py'), str(canonical)],
        cwd=out, check=True, capture_output=True, text=True)
    (out / 'check_q46.stdout').write_text(run.stdout, encoding='utf-8')
    if (out / 'q46_checks.json').read_bytes() != assets['q46_checks.json']:
        raise ValueError('reproduced JSON differs from the embedded result')
    result = {
        'all_asset_hashes_match': True,
        'asset_count': len(assets),
        'checker_run': True,
        'historical_programs_executed': False,
        'output_byte_identical': True,
        'production_spectrum_run': False,
    }
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
```
END_ASSET


### Фактически выполненное воспроизведение

```json
{
  "all_asset_hashes_match": true,
  "asset_count": 4,
  "checker_run": true,
  "historical_programs_executed": false,
  "output_byte_identical": true,
  "production_spectrum_run": false
}
```

Это собственное повторное исполнение извлечённого кода, не независимый математический аудит. Репозиторий не изменялся. Бинарный primary PDF не хеширован; входной TXT и все 13 тел хешированы. **Новый полный арифметический показатель, source-pair margin и RH остаются недоказанными.**
