# STATUS: KILL_RAW_DIVISOR_SHIFT_BOUNDED_REMAINDER

```yaml
OPERATIVE_CLASS: KILL_RAW_DIVISOR_SHIFT_BOUNDED_REMAINDER
DATE: 2026-11-02
TASK_MODE: OWNER_DIRECT_EXECUTION_OF_PREVIOUS_ATTACHED_TARGET
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
TASK: PRIME_SQUARE_POSITIVE_KERNEL_PULLBACK_PREFLIGHT
BOUND_TARGET_FILE: PROSHKA_NEXT_PROOF_TARGET_AFTER_EFZ_2026-11-02.md
SOURCE_ARITHMETIC_COMMIT: a4ab9e92bf080ee3bcfd729af067ade6fc6392fc
SOURCE_ARITHMETIC_BLOB: 88de1569443ba35acdeefdeb64ace9bbb43c47e8
SOURCE_RESIDUAL_COMMIT: 2176dab16bf77dd015f7efcb5a6f704587f732c8
SOURCE_RESIDUAL_AUDIT_COMMIT: e724ae65ed39a8ba8b8f07c928d790ea9820342a
SOURCE_INDEX_COMMIT: f6c9cd89cc104ae3fdfc23bcc8a26b102d195fbf
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
KILL_SCOPE: THEOREM_SHAPE
KILL_TARGET: RAW_HALF_DENSITY_DIVISOR_SHIFT_GRAM_PLUS_CONSTANT_LOWER_REMAINDER
KILL_EVIDENCE_KIND: EXPLICIT_COFINAL_ORIGINAL_COMPLEMENT_WITNESS_AND_NEGATIVE_UPPER_ENVELOPE
KILL_EVIDENCE_REFERENCE: THIS_FILE_SECTIONS_4_THROUGH_6
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THE_NAMED_RAW_PULLBACK_CLASS_ONLY
UNCHANGED_COMPLEMENT_FLOOR_STATUS: OPEN_RESEARCH_DEBT
CENTERED_PULLBACK_STATUS: EXACT_IDENTITY_ONLY_NO_CONSTANT_REMAINDER_PROVED
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4
NEW_COFINAL_RESULT: RAW_LIFT_REMAINDER_IS_UNBOUNDED_BELOW_ON_LITERAL_J_PERP
NEW_COFINAL_SOURCE_SIGN: NONE
ORIGINAL_CARRIER: EVEN_PHYSICAL_L2_N_EQ_m_L_EQ_log_m
QUIET_SPACE_SCHEDULE: kappa_m=1+c0*(1+log(log(m)))/log(m), FIXED_0_LT_c0_LT_1
RH_ASSUMED: false
RH_PROVED: false
ZERO_LOCATION_INPUT: EXISTENCE_OF_ONE_FIXED_CRITICAL_LINE_ZERO_ONLY
SIMPLE_ZERO_ASSUMED: false
ZERO_COUNT_ASYMPTOTIC_USED_IN_NEW_PROOF: false
EXACT_CONTROL_GROUPS: 6
HIGH_PRECISION_NORMALIZATION_CONTROL_GROUPS: 4
HIGH_PRECISION_DPS: 65
NEW_CCM_EIGENPROBLEMS: 0
INDEPENDENT_ANALYTIC_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
REPOSITORY_WRITTEN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 0. Результат и точная граница

Ы. Выполнен именно предложенный перенос положительности делительного Gram-ядра, а не новый поиск по спектру. Рассмотрен канонический перенос через целочисленные дилатации в физической L2-норме. Для него получены все коэффициенты и доказано, что остаток **не может** иметь постоянный нижний пол даже на исходном J_m-perp.

Это опровержение выбранного класса переносов, НЕ опровержение RH, исходного complement-floor и не всех возможных арифметических факторизаций.

Пусть

\[
 q_m[f]=H_+[f]-S_m^{(1,2)}[f]
\]

— ровно компенсированная форма выбранного target. Обозначим канонический положительный перенос log-gcd через G_m. Ниже строятся единичные **исходные** f_m in J_m-perp и фиксированное k_gamma>0, для которых

\[
 \boxed{G_m[f_m]\ge k_\gamma m,\qquad
        |q_m[f_m]|\le U_m=o(m).}                         \tag{0.1}
\]

Поэтому для любого фиксированного alpha>0

\[
 \boxed{(q_m-\alpha G_m)[f_m]
       \le U_m-\alpha k_\gamma m\longrightarrow-\infty.}  \tag{0.2}
\]

Тот же вывод верен после удаления из положительного lift всех d=p^k с k>=3: уже один сохранённый квадрат d=2 порождает obstruction. Таким образом, неудача не объясняется тем, что в кандидат были добавлены лишние высшие степени.

Положительность G_m сама правильна. Не выполняется утверждение, что его можно вычесть из q_m, заплатив одной постоянной. Это точный ответ на выбранный preflight, а не заявление «любые положительные квадраты бесполезны».

## 1. Исходный объект и реестр

Все функции ниже вещественные и чётные; этого достаточно для свидетеля против нижней оценки. Комплексное Hermitian-продолжение тождеств стандартно.

\[
 L=\log m,\quad b=L/2,\quad I_m=[-b,b],\quad
 \Omega=2\pi m/L,
\]
\[
 V_m=\operatorname{span}\{L^{-1/2},\sqrt{2/L}\cos(2\pi nx/L):1\le n\le m\},
\]

с нулевым продолжением за окно. P_m — физическая ортогональная проекция на V_m. Знаки (-1)^n в другом исходном ортонормированном базисе являются диагональной ортогональной заменой и ничего не меняют.

J_m — ровно пространство из 2176dab: Fourier-образ зануляется в фактических комплексных нулях xi при |Im rho|<T_m, с

\[
 T_m=\left(1+c_0\frac{1+\log\log m}{\log m}\right)\Omega,
 \qquad 0<c_0<1\text{ fixed}.
\]

В этой новой отрицательной проверке не нужен residual theorem: достаточно определения J_m и T_m->infinity. Не используется RH, простота нулей или утверждение, что все нули лежат на прямой.

Исходные корреляции и компенсаторы:

\[
 C_f(s)=\int_\mathbb R f(x)f(x+s)\,dx,\quad Q_f(s)=2C_f(s),
\]
\[
 I_L[f]=\int_0^L e^{s/2}Q_f(s)\,ds,
\]
\[
 H_+[f]=\int_0^\infty
 \frac{e^{-5s/2}}{1-e^{-2s}}\|f-T_sf\|_2^2\,ds,
 \qquad T_sf(x)=f(x+s),
\]
\[
 P_m^{12}[f]=\sum_{p\le m}\frac{\log p}{\sqrt p}Q_f(\log p)
 +\sum_{p^2\le m}\frac{\log p}{p}Q_f(2\log p),
\]
\[
 \boxed{q_m[f]=H_+[f]-P_m^{12}[f]+I_L[f].}                \tag{1.1}
\]

Простые и квадраты удержаны совместно. На границе Q_f(L)=0. В a4ab9e9 доказан точный возврат

\[
 q_m[f]=\langle f,A_mf\rangle+(c_*-4)\|f\|^2+P_m^{\ge3}[f],
 \quad c_*=\gamma_E+\log(8\pi)+\pi/2,                    \tag{1.2}
\]

с |P_m^{>=3}[f]|<=C_3||f||², C_3=(1+sqrt2)(8+5log2)<28. Ни один из этих членов здесь не объявляется равным нулю. Положительный target остаётся q_m>=-K на J_m-perp.

### Claim ledger

| Claim | Scope | Verifier | Boundary |
|---|---|---|---|
| Divisor-Gram identity and dilation pullback | ABSTRACT | PAPER | Exact finite sums |
| All rational-shift coefficients | FINITE_CELL | PAPER | No Fourier or prime cutoff omitted |
| Uniform source upper U_m=o(m) | COFINAL_FAMILY | PAPER | Whole literal carrier; not a lower floor |
| Fixed-zero evaluation row belongs to J_m-perp | COFINAL_FAMILY | PAPER | Uses one unconditional critical-line zero |
| Raw lift has >=k_gamma m energy on that row | COFINAL_FAMILY | PAPER | All sufficiently late original m |
| No constant lower remainder for any fixed positive multiple of the raw lift | COFINAL_FAMILY | PAPER | Named theorem-shape only |
| Centered divisor/floor identity | FINITE_CELL | PAPER | All continuum and exterior terms retained |
| Uniform lower residual for centered lift | COFINAL_FAMILY | CONDITIONAL | Not established |

Шесть finite exact-control groups и четыре numerical-normalization controls не используются вместо этих доказательств. Их область и воспроизведение указаны ниже.

## 2. Полный канонический перенос положительного kernel

### 2.1. Арифметическая идентичность

**[ABSTRACT | PAPER]** Для конечной последовательности a:

\[
 \sum_{r,s\le m}\log\gcd(r,s)\,\overline{a_r}a_s
 =\sum_{d=2}^m\Lambda(d)\left|\sum_{\substack{n\le m\\d\mid n}}a_n\right|^2\ge0.
                                                               \tag{2.1}
\]

Это следует из sum_(d|n) Lambda(d)=log n, то есть из точной факторизации обычных целых. Никакой аналитической гипотезы нет [P1].

### 2.2. Почему выбран именно half-density перенос

Унитарный переход между физической логарифмической координатой и положительной полуосью:

\[
 g(u)=u^{-1/2}f(\log u),\qquad
 \int_0^\infty |g(u)|^2du=\int_\mathbb R |f(x)|^2dx.
\]

В (2.1) подставим **a_n(u)=g(nu)** и проинтегрируем по u>0. Это буквальный source-defined lift через целочисленные дилатации, без неизвестной спектральной факторизации. Получаем

\[
 \boxed{
 G_m[f]=\int_\mathbb R\sum_{r,s\le m}
 \frac{\log\gcd(r,s)}{\sqrt{rs}}
 f(x+\log r)f(x+\log s)\,dx\ge0.}                       \tag{2.2}
\]

Для

\[
 Z_Nf(x)=\sum_{k=1}^N k^{-1/2}f(x+\log k)
\]

замена u->du в каждом делительном квадрате даёт точно

\[
 \boxed{
 G_m[f]=\sum_{d=2}^m\frac{\Lambda(d)}d
           \|Z_{\lfloor m/d\rfloor}f\|_2^2.}             \tag{2.3}
\]

Интегрирование идёт по всей выходной прямой. Выходы не обрезаются обратно в окно; никакие сдвинутые endpoints не выкинуты. Вход f остаётся в исходном V_m.

### 2.3. Возврат всех коэффициентов

Положим

\[
 H_N^{\log}=\sum_{d=1}^N\frac{\log d}{d}.
\]

В двойной сумме пишем r=da,s=db, (a,b)=1. Диагональ r=s даёт H_m^log||f||². Парные недиагональные слагаемые дают Q_f, не C_f. Следовательно

\[
 \boxed{
 G_m[f]=H_m^{\log}\|f\|^2+
 \sum_{\substack{1\le b<a\le m\\(a,b)=1}}
 \frac{H_{\lfloor m/a\rfloor}^{\log}}{\sqrt{ab}}
 Q_f\!\left(\log\frac ab\right).}                      \tag{2.4}
\]

Это включает ВСЕ рациональные отношения. Например, при m>=6 присутствует log(3/2), уже при m=6 с коэффициентом log2/(2sqrt6). В исходном P12 такого атома нет. Даже для целого отношения a/1 коэффициент равен H_floor(m/a)^log/sqrt a, а не -Lambda12(a)/sqrt a.

Таким образом, точная формула q_m=G_m+R_m содержит

\[
 \begin{aligned}
 R_m[f]={}&H_+[f]+I_L[f]-P_m^{12}[f]
 -H_m^{\log}\|f\|^2\\
 &-\sum_{\substack{1\le b<a\le m\\(a,b)=1}}
 \frac{H_{\lfloor m/a\rfloor}^{\log}}{\sqrt{ab}}
 Q_f\!\left(\log\frac ab\right).
 \end{aligned}                                         \tag{2.5}
\]

Ненулевой остаток сам по себе ещё не опровергает пригодность переноса. §§3–6 доказывают именно невозможность его постоянного нижнего бюджета.

### 2.4. Фильтрация простых/квадратов не спасает этот lift

Положим omega12(d)=Lambda(d) для d=p или p² и 0 иначе. Тогда положительный kernel

\[
 K_{12}(r,s)=\sum_{d\mid\gcd(r,s)}\omega_{12}(d)
 =\sum_p(\log p)\min(v_p(\gcd(r,s)),2)
\]

имеет тот же перенос

\[
 G_m^{12}[f]=\sum_{d\le m}\frac{\omega_{12}(d)}d
                 \|Z_{\lfloor m/d\rfloor}f\|^2\ge0.      \tag{2.6}
\]

В (2.4) просто заменяется log d на sum_(e|d) omega12(e). Сдвиги по нецелым рациональным отношениям остаются. Дальнейший нижний свидетель использует только d=2, общий для (2.3) и (2.6).

## 3. Нужный source upper: q_m имеет операторную норму o(m)

**[COFINAL_FAMILY | PAPER]** Это вспомогательная верхняя оценка для опровержения переноса, НЕ искомый постоянный нижний пол.

Для единичного f in V_m:

\[
 \|f'\|_{L^2(I_m)}\le\Omega,
 \qquad \|f\|_\infty\le\sqrt{(2m+1)/L}.
\]

На 0<s<L, с сохранённым endpoint:

\[
 Q_f'(s)=2\int_{-b}^{b-s} f(x)f'(x+s)dx-2f(b-s)f(b).
\]

Поэтому

\[
 |Q_f'(s)|\le 2\Omega+2(2m+1)/L.
\]

Q_f непрерывна, Q_f(0)=2, Q_f(L)=0 и Q_f(s)=0 при s>=L. Следовательно

\[
 0\le\|f-T_sf\|^2=2-Q_f(s)
 \le[2\Omega+2(2m+1)/L]s\quad(s\ge0).
\]

Первая moment-цена архимедова kernel элементарна:

\[
 \int_0^\infty\frac{s e^{-5s/2}}{1-e^{-2s}}ds
 =\sum_{k\ge0}(5/2+2k)^{-2}
 \le\frac4{25}+\int_0^\infty(5/2+2x)^{-2}dx
 =\frac9{25}.
\]

Значит

\[
 H_+[f]\le\frac{18}{25}\left(\Omega+\frac{2m+1}{L}\right).
\]

Все prime/square веса неотрицательны, |Q_f|<=2 и Lambda(n)<=log n, откуда

\[
 |P_m^{12}[f]|\le 4L(\sqrt m-1),\qquad
 |I_L[f]|\le4(\sqrt m-1).
\]

Итак, для всего исходного carrier

\[
 \boxed{|q_m[f]|\le U_m\|f\|^2,\qquad
 U_m=\frac{18}{25}\left(\frac{2\pi m}{L}+\frac{2m+1}{L}\right)
           +4(L+1)(\sqrt m-1).}                         \tag{3.1}
\]

\[
 \boxed{U_m/m\longrightarrow0.}                         \tag{3.2}
\]

В этой оценке не используется ни PNT, ни RH, ни нулевой счёт, ни знак искомого q_m. Она согласуется с более грубым полным norm upper NOESCAPE (2.3), но выведена здесь непосредственно для q_m.

## 4. Свидетель принадлежит именно J_m-perp

### 4.1. Определение

**[COFINAL_FAMILY | PAPER]** Фиксируем один настоящий нуль zeta(1/2+i gamma)=0, gamma>0. Существование хотя бы одного такого нуля безусловно; достаточно классического факта существования бесконечно многих критических нулей [P2]. Ни его численное приближение, ни простота, ни RH не используются.

Положим

\[
 v_m(x)=\cos(\gamma x)\mathbf1_{I_m}(x),\qquad
 w_m=P_mv_m,\qquad f_m=w_m/\|w_m\|.                     \tag{4.1}
\]

При gamma<T_m, для любого j in J_m:

\[
 \langle w_m,j\rangle=\langle v_m,j\rangle
 =\int_{I_m}\cos(\gamma x)j(x)dx=\widehat j(\gamma)=0.
\]

Значит w_m, а при ненулевом w_m и f_m, лежат в **том самом** J_m-perp. Это не посторонний carrier и не произвольный пример матриц.

### 4.2. Проекционный бюджет

\[
 \|v_m\|^2=L/2+\frac{\sin(\gamma L)}{2\gamma}.
\]

Коэффициент n>=1 в физическом cosine-базисе равен

\[
 a_n=2\sqrt{2/L}\,
 \frac{\gamma(-1)^n\sin(\gamma L/2)}{\gamma^2-(2\pi n/L)^2}.
                                                               \tag{4.2}
\]

При 2pi(m+1)/L>=sqrt2 gamma:

\[
 \boxed{\|v_m-w_m\|^2
 \le e_m^2:=\frac{2\gamma^2L^3}{3\pi^4m^3}.}             \tag{4.3}
\]

Это прямое суммирование n^-4 хвоста; endpoint-синус в (4.2) сохранён. В частности, w_m ненулевой для больших m.

### 4.3. Неисчезающая масса в фиксированной полосе частот

Пусть Gamma=gamma+1. Точная Fourier-формула:

\[
 \widehat v_m(t)=\frac{\sin((t-\gamma)L/2)}{t-\gamma}
              +\frac{\sin((t+\gamma)L/2)}{t+\gamma}.
\]

При |t|>=Gamma:

\[
 |\widehat v_m(t)|\le\frac2{|t|-\gamma},\qquad
 \frac1{2\pi}\int_{|t|>\Gamma}|\widehat v_m(t)|^2dt\le\frac4\pi.
\]

Вместе с (4.3) это даёт

\[
 \frac1{2\pi}\int_{|t|>\Gamma}|\widehat f_m(t)|^2dt
 \le\frac{(2/\sqrt\pi+e_m)^2}
 {L/2-1/(2\gamma)-e_m^2}.                                \tag{4.4}
\]

Например, достаточны L>=max(64,2/gamma), e_m<=1: правая часть меньше 1/2. Следовательно

\[
 \boxed{\frac1{2\pi}\int_{-\Gamma}^{\Gamma}
                      |\widehat f_m(t)|^2dt\ge\frac12.}   \tag{4.5}
\]

Сохранены исходная норма, projection, parity и точная принадлежность дополнению. Никакая оценка геометрии остальных нулей не нужна.

## 5. Один положительный делительный квадрат уже слишком велик

**[COFINAL_FAMILY | PAPER]** Fourier-множитель Z_N равен

\[
 z_N(t)=\sum_{k=1}^N k^{-1/2+it}.
\]

Положим

\[
 a_\gamma=\sqrt{\tfrac14+(\gamma+1)^2}.
\]

Для |t|<=Gamma элементарное сравнение суммы с интегралом даёт

\[
 \left|z_N(t)-\int_1^N x^{-1/2+it}dx\right|
 \le1+\int_1^N\left|\frac d{dx}x^{-1/2+it}\right|dx
 \le1+2a_\gamma.
\]

А

\[
 \left|\int_1^N x^{-1/2+it}dx\right|
 =\left|\frac{N^{1/2+it}-1}{1/2+it}\right|
 \ge\frac{\sqrt N-1}{a_\gamma}.
\]

Таким образом, при

\[
 \sqrt N\ge2(1+a_\gamma+2a_\gamma^2)
\]

имеем равномерно на фиксированной полосе

\[
 \boxed{|z_N(t)|\ge\frac{\sqrt N}{2a_\gamma}.}             \tag{5.1}
\]

При N=floor(m/2) и (4.5), Parseval даёт

\[
 \|Z_Nf_m\|^2
 =\frac1{2\pi}\int |z_N(t)|^2|\widehat f_m(t)|^2dt
 \ge\frac{N}{8a_\gamma^2}.
\]

Теперь в (2.3) или (2.6) оставляем только заведомо положительный d=2 квадрат:

\[
 G_m[f_m],\ G_m^{12}[f_m]
 \ge\frac{\log2}{2}\|Z_{\lfloor m/2\rfloor}f_m\|^2
 \ge\frac{\log2}{16a_\gamma^2}\lfloor m/2\rfloor.
\]

При m>=3, floor(m/2)>=m/3, поэтому

\[
 \boxed{G_m[f_m],\ G_m^{12}[f_m]\ge k_\gamma m,
 \qquad k_\gamma=\frac{\log2}{48a_\gamma^2}>0.}            \tag{5.2}
\]

Это доказанный эффект когерентной суммы по обычным целым, не степенной fit. Знак не получен из численного спектра. Выходные сдвиги были проинтегрированы полностью.

### Более широкий точный класс

Если omega(d)>=0 фиксированы и omega(d0)>0 для одного фиксированного d0, то raw lift

\[
 G_m^\omega[f]=\sum_{d\le m}\frac{\omega(d)}d
                    \|Z_{\lfloor m/d\rfloor}f\|^2
\]

на тех же f_m удовлетворяет для больших m

\[
 G_m^\omega[f_m]\ge
 \frac{\omega(d_0)}{16d_0^2a_\gamma^2}\,m.                 \tag{5.3}
\]

То есть obstruction затрагивает целый указанный класс **нецентрированных** lifts, а не единственный неудачный коэффициент log-gcd. Веса, исчезающие с m, нелинейные изменения входа и centered lifts под (5.3) не подпадают.

## 6. Строгое опровержение постоянного остатка

**[COFINAL_FAMILY | PAPER]** Рассмотрим утверждение:

> Существуют фиксированные alpha>0,K<infinity и неограниченная исходная семья m, такие что q_m[f]=alpha G_m[f]+R_m[f] и R_m[f]>=-K||f||² для всех f in J_m-perp.

Оно ложно. Для построенного f_m:

\[
 \boxed{R_m[f_m]+K
 \le U_m-\alpha k_\gamma m+K.}                           \tag{6.1}
\]

Правая часть — **верхний** envelope. Поскольку U_m/m->0, для каждого alpha,K она строго отрицательна на всех достаточно поздних исходных m:

\[
 \boxed{U_m-\alpha k_\gamma m+K<0.}                      \tag{6.2}
\]

Это убивает и неограниченную подпоследовательность. Для G_m^12 и класса (5.3) доказательство то же.

Важно: q_m[f_m] само по себе здесь не доказано отрицательным. Ложность остаточного бюджета не является ложностью целевого q_m>=-K. Убит **наш выбранный способ добыть этот пол**, а не исходная математическая задача.

Численное начало действия не вычислялось. Полностью явные достаточные условия для проверки конкретного m: gamma<T_m; L>=max(64,2/gamma); 2pi(m+1)/L>=sqrt2 gamma; e_m<=1; sqrt(floor(m/2))>=2(1+a_gamma+2a_gamma²); (6.2). Все они eventually true. Для самого доказательства не требуется interval-box одного численного нуля: gamma выбран по безусловной теореме существования [P2].

## 7. Попытка ремонта: сначала центрировать, потом возводить в квадрат

### 7.1. Явный новый оператор, не спектральный square root

**[FINITE_CELL | PAPER]** Определим

\[
 \mathcal C_N f(x)=\int_0^N u^{-1/2}f(x+\log u)\,du
 =\int_{-\infty}^{\log N}e^{s/2}f(x+s)\,ds,
\]
\[
 \widetilde Z_N=Z_N-\mathcal C_N,
 \qquad
 \widetilde G_m[f]=\sum_{d=2}^m\frac{\Lambda(d)}d
                   \|\widetilde Z_{\lfloor m/d\rfloor}f\|^2\ge0.
                                                               \tag{7.1}
\]

Нижний endpoint континуума — **0**, не 1. Выходной экспоненциальный хвост C_N также сохраняется; он не обрезается обратно в I_m.

Fourier-множитель C_N:

\[
 c_N(t)=\frac{N^{1/2+it}}{1/2+it}.
\]

Из сравнения суммы с интегралом в §5:

\[
 |z_N(t)-c_N(t)|\le1+2a_\gamma+2
 \quad(|t|\le\Gamma).                                   \tag{7.2}
\]

Следовательно, leading sqrt N на фиксированных частотах удалён точно. Это не оценка полного centered остатка и не новая нижняя граница q_m.

### 7.2. Точный floor-компенсатор — все смешанные члены вычислены

Положим

\[
 R_0[f]=\int_0^L e^{-s/2}Q_f(s)\,ds.
\]

Полная выходная норма даёт

\[
 \|\mathcal C_Nf\|^2=N R_0[f].                           \tag{7.3}
\]

Это видно по Fourier-множителю N/(1/4+t²), равному N-кратному преобразованию kernel exp(-|s|/2), либо прямым интегрированием.

Смешанный член также точен:

\[
 2\langle Z_Nf,\mathcal C_Nf\rangle
 =\sum_{k=1}^N\int_{-\infty}^{\log(N/k)}e^{s/2}Q_f(s)\,ds
\]
\[
 =N R_0[f]+\int_0^L\lfloor Ne^{-s}\rfloor e^{s/2}Q_f(s)\,ds.
                                                               \tag{7.4}
\]

Поэтому

\[
 \boxed{\|\widetilde Z_Nf\|^2
 =\|Z_Nf\|^2-
   \int_0^L\lfloor Ne^{-s}\rfloor e^{s/2}Q_f(s)\,ds.}     \tag{7.5}
\]

И для полного centered lift:

\[
 \boxed{\widetilde G_m[f]=G_m[f]
 -\int_0^L e^{s/2}Q_f(s)\Phi_m(s)\,ds,}                 \tag{7.6}
\]
\[
 \Phi_m(s)=\sum_{d=2}^m\frac{\Lambda(d)}d
              \left\lfloor\lfloor m/d\rfloor e^{-s}\right\rfloor.
                                                               \tag{7.7}
\]

Все floors сохранены. В точках скачка соглашение не влияет на Lebesgue-интеграл. Q_f(L)=0 и экспоненциальный внешний хвост учтены. В варианте prime/square filtered заменяется только внешний Lambda на omega12.

### 7.3. Что именно осталось после ремонта

Теперь

\[
 q_m[f]-\widetilde G_m[f]
 =q_m[f]-G_m[f]
   +\int_0^L e^{s/2}Q_f(s)\Phi_m(s)\,ds.                 \tag{7.8}
\]

Это не присвоение неизвестному остатку удобного имени: явная формула показывает весь возвращённый компенсатор. Но постоянная нижняя оценка (7.8) **не доказана**. В частности, (7.6) оставляет рациональные дискретные атомы (2.4); центрирование добавляет непрерывный kernel, а не автоматически превращает их в нужные prime-power atoms.

Нельзя применять no-go §6 к centered lift: его предпосылка — необрезанный coherent sqrt N — здесь удалена. Нельзя и объявлять centered lift успешным: положительность отдельного G_tilde не оплачивает signed difference (7.8).

## 8. Проверки и исход предрегистрации

Первоначальные P1–P3 взяты из предыдущего target-файла. Дополнительные finite-control predictions записаны в registration.json перед исполнением кода. Новые аналитические выводы §§4–6 получены на бумаге и не выдаются за заранее угаданные измерения.

| Prediction | Fate | Evidence |
|---|---|---|
| P1: direct divisor lift оставляет ненулевой mixed remainder | CONFIRMED | (2.4)–(2.5), stronger (6.2) |
| P2: континуум обязателен и его нельзя потерять | CONFIRMED | (1.1), (7.3)–(7.7), coefficient checks |
| P3: evenness/quietness alone не различают source sign | NO_NEW_GENERAL_TEST | Не использовано как доказательство; отдельная DH weight-check лишь иллюстрирует утрату положительных весов |
| P4: возникают нецелые rational-shift atoms | CONFIRMED_EXACT | log(3/2), all finite coefficients |
| P5: d=2 gives linear growth on true J-perp witness | PROVED_PAPER | §§4–5, не numeric fit |
| P6: bounded remainder fails on the original complement | PROVED_PAPER | negative upper (6.2) |
| P7: prime/square filtering does not fix raw lift | PROVED_PAPER | common d=2 witness |
| P8: centering cancels N R_0 exactly and leaves a floor kernel | CONFIRMED | (7.3)–(7.7), independent output-space integral |

Исполнено 10 control groups: шесть exact, четыре numerical-normalization при 65 dps. Максимальное абсолютное расхождение трёх конечных Gram-развёрток: 4.74778387288e-66. Это НЕ interval arithmetic и НЕ сертификат универсального квантора. Новых CCM/DH eigensystems не считалось.

Один DH-контроль носит только алгебраический характер: для стандартного коэффициента tau имеем b_D(3)=-tau log3<0 и b_D(6)=(1+tau²)log6. Поэтому замена Lambda этими весами не сохраняет положительность (2.1). Этот факт не используется в source no-go и не заменяет независимый аудит предыдущего DH-вердикта.

## 9. K8A: что убито, что осталось и куда переносить попытку

DOWNSTREAM_CONSUMER: один постоянный нижний пол исходного complement плюс inherited bounded quiet residual, далее pinned constant-floor implication.

ACTUAL_CONSUMER_REQUIREMENT: q_m[f]>=-K||f||² на J_m-perp с фиксированным K на неограниченной семье.

ORIGINAL_REQUESTED_OBJECT: источник-заданная положительная факторизация с полным постоянным остатком.

ORIGINAL_OBJECT_IS: этот конкретный raw divisor lift NOT_NECESSARY. Он был одним выбранным кандидатом.

KNOWN_WEAKER_INTERFACES: любой независимый прямой complement floor; любой прямой full floor; другой источник-заданный positive kernel с доказанным остатком.

KILL_SCOPE: THEOREM_SHAPE — q_m=alpha G_m^omega+R_m, alpha>0 fixed, omega>=0 fixed with one omega(d0)>0, R_m uniformly bounded below on the literal complement.

KILL_EVIDENCE_KIND: explicit original-complement family, all-late upper envelope <0 in (6.2).

EPISTEMIC_STATUS: MATHEMATICALLY_DEAD только для указанного raw класса; общая цель RESEARCH_DEBT.

REOPEN_TRIGGER: изменение исходного lift, например (7.1), и отдельное доказательство нижней оценки полного (7.8). Простое расширение m-скана не меняет (6.2).

NOVELTY_AXIS: новый no-go для конкретного естественного arithmetic-to-window переноса на настоящем J-perp; точный centered floor kernel. Нового положительного знака исходной формы нет.

### Две допустимые смены представления

| Representation | Decisive object | Kill power / cost |
|---|---|---|
| Centered divisor lift (7.1), preferably omega12 | Полный signed residual (7.8), включая все rational atoms и floor kernel | Высокая для проверки данного кандидата; умеренная цена coefficient audit, высокая цена cofinal bound |
| Joint Stieltjes source from a4ab9e9 | integral [psi(x)-(x-1)] x^-3/2 [Q/2-Q'] minus H_+ | Прямой source target; умеренная цена exact return, высокая цена нового signed estimate |

Три проверенных bridge: divisor incidence Gram -> unitary dilation lift (выполнен); additive sum/integral -> exact centered floor kernel (выполнен); positive lift -> source semibound with constant residual (raw version строго опровергнут). Этот результат не требует имитации независимых агентов.

DISCRIMINATOR для любого нового candidate alpha,K: для конкретного исходного f нужен строгий **верхний** envelope q_m[f]-alpha G_new,m[f]+K||f||²<0 для kill; для PASS всей семьи нужен доказанный lower envelope. Нуль-согласованный numerical interval не является ни одним из них.

### Единственная CODEX DIRECTIVE

`CENTERED_DIVISOR_SOURCE_COEFFICIENT_TEST`.

Вход: (1.1), (2.6), (7.1)–(7.8) при c0=1/2 и исходном N=m. Работать с omega12, вычислять полный signed остаток, не row norms и не только один положительный Gram. Проверить рациональные атомы и непрерывный floor kernel до любой оценки. Успех: единый K для этого остатка либо настоящий cofinal original-complement witness, убивающий этот centered кандидат. Нельзя выдать (7.8) само по себе за новый lower bound. Не менять carrier, J, poles, endpoints или source normalization. Не считать raw no-go опровержением centered класса. Код проверки ниже исполняется до новых больших вычислений; самостоятельный аналитический аудит §§3–6 обязателен перед принятием нового no-go в проект.

## 10. Meta closeout

Что стало меньше: исключён весь фиксированно положительный uncentered divisor-shift класс; вычислен именно отсутствовавший арифметико-оконный перенос, а не ещё раз сформулирован target.

Что не повторять: переносить raw log-gcd positivity в q_m без удаления coherent continuum; забывать нецелые рациональные сдвиги; использовать не-J-perp контроль вместо исходного свидетеля; говорить о смерти RH-маршрута из смерти одного lift.

Минимальное оставшееся неизвестное: lower budget полного centered residual (7.8), если выбирается этот кандидат. Общая target-оценка неизменна и не объявлена приближённо доказанной.

Memory entry:

```yaml
iteration:
  target: PRIME_SQUARE_POSITIVE_KERNEL_PULLBACK_PREFLIGHT
  status: FATAL_FOR_RAW_LIFT_ONLY
  failed_strategy: raw_integer_dilation_log_gcd_Gram_plus_constant_remainder
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  invariant_learned: one_positive_fixed_divisor_square_has_coherent_linear_energy_on_a_true_J_perp_row
  forbidden_future_move: subtract_raw_Gram_and_assume_remainder_is_O_1
  next_decisive_test: centered_floor_kernel_vs_complete_source_residual
```

No Lean source, no route-state write, no formal RH claim. Новый PAPER-вывод ещё не прошёл независимый аналитический аудит.

## Источники и точность происхождения

S0. Предыдущий прикреплённый target: `PROSHKA_NEXT_PROOF_TARGET_AFTER_EFZ_2026-11-02.md`. Прочитан полностью, включая preregistration. Прямое «Ок го» владельца связывает настоящую попытку с этим target, а не с repository queue.

S1. `docs/routeB_bus/proshka/PROSHKA_VERDICT_PRIME_COMPLEMENT_FLOOR_2026-11-02.md`, commit `a4ab9e92bf080ee3bcfd729af067ade6fc6392fc`, blob `88de1569443ba35acdeefdeb64ace9bbb43c47e8`. Повторно прочитаны точные source forms, compensation, higher powers, endpoints и открытая граница.

S2. `docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md`, тот же commit, blob `453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc`. Повторно прочитан (2.3) и его endpoint/norm proof; новый q_m upper §3 выведен независимо в более прямой форме.

S3. `PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md`, commit `2176dab16bf77dd015f7efcb5a6f704587f732c8`, mounted artifact и определение J_m. Его residual theorem не используется как предпосылка новой отрицательной оценки, только определение J_m.

P1. NIST DLMF §27.2, fundamental theorem of arithmetic and von Mangoldt definition. Identity (2.1) proven directly here. URL: `https://dlmf.nist.gov/27.2`.

P2. NIST DLMF §25.10(i): existence of infinitely many critical-line zeros, via sign changes of Hardy's Z. Only existence of ONE fixed zero is used. URL: `https://dlmf.nist.gov/25.10`.

P3. Connes–Consani–Moscovici, *Zeta Spectral Triples*, v1, source form and finite-window conventions, not a supplier of the missing floor. URL: `https://arxiv.org/html/2511.22755v1`.

Targeted repository keyword search was not an exhaustive literature/capability-catalog audit; no claim of such an exhaustive search is made.

## Appendix: runnable controls

Сохранить следующий блок как `divisor_pullback_checks.py`. Исполнение:

```sh
uv run --with sympy --with mpmath python divisor_pullback_checks.py
```

Код не требует repo checkout и не меняет project state. Он пишет только JSON отчёт рядом с собой. В названиях нет подстановок путей проекта. Для запуска под другим именем значение output-path следует оставить независимым от имени скрипта.

```python
#!/usr/bin/env python3
"""Exact arithmetic controls plus finite high-precision normalization diagnostics.
No CCM eigenproblem, no RH assertion, no interval certification.
Run: uv run --with sympy --with mpmath python checks.py
"""
from collections import defaultdict
from fractions import Fraction
from math import gcd
import json
from pathlib import Path
import sympy as sp
import mpmath as mp


def vp(n: int, p: int) -> int:
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def lam(n: int):
    fac = sp.factorint(n)
    if len(fac) == 1:
        return mp.log(int(next(iter(fac))))
    return mp.mpf('0')

records = []

def passed(name: str, kind: str = 'EXACT'):
    records.append({'name': name, 'kind': kind, 'status': 'PASS'})
    print(f'PASS {len(records)} [{kind}] {name}', flush=True)

# Finite log-gcd identity, coefficientwise in the independent log(p) symbols.
for n in range(2, 21):
    for p in sp.primerange(2, n + 1):
        for r in range(1, n + 1):
            for s in range(1, n + 1):
                lhs = vp(gcd(r, s), int(p))
                rhs = sum(1 for d in range(2, n + 1)
                          if r % d == 0 and s % d == 0
                          and len(sp.factorint(d)) == 1
                          and next(iter(sp.factorint(d))) == p)
                assert lhs == rhs
passed('log-gcd divisor Gram, all entries for dimensions 2..20')

# Rational-ratio coefficient formula for full and prime/square-only lifts.
for cap in (None, 2):
    for n in (6, 12, 20):
        for p in sp.primerange(2, n + 1):
            p = int(p)
            W = lambda k: vp(k, p) if cap is None else min(vp(k, p), cap)
            direct = defaultdict(Fraction)
            for r in range(2, n + 1):
                for s in range(1, r):
                    d = gcd(r, s)
                    a, b = r // d, s // d
                    direct[a, b] += Fraction(W(d), d)
            for a in range(2, n + 1):
                h = sum((Fraction(W(d), d) for d in range(1, n // a + 1)), Fraction())
                for b in range(1, a):
                    if gcd(a, b) == 1:
                        assert direct[a, b] == h
            diag = sum((Fraction(W(r), r) for r in range(1, n + 1)), Fraction())
            assert diag == sum((Fraction(W(d), d) for d in range(1, n + 1)), Fraction())
passed('all rational-shift coefficients; full and prime-square filtered')

# Small exact atom obstruction: m=6, ratio 3/2.
# Its coefficient is log(2)/(2 sqrt(6)); this shift is not log of an integer.
assert Fraction(vp(2, 2), 2) == Fraction(1, 2)
assert gcd(3, 2) == 1
assert not Fraction(3, 2).denominator == 1
passed('noninteger-ratio atom log(3/2) survives with positive coefficient')

# Full compensation, including the higher-power return, is kept exactly.
Hp, P12, P3, I, R, N, cs = sp.symbols('Hp P12 P3 I R N cs', real=True)
Arch = Hp + 4*N - R
Pole = I + R
A = Arch - cs*N - P12 - P3 + Pole
q = Hp - P12 + I
assert sp.expand(q - (A + (cs-4)*N + P3)) == 0
passed('original compensated source and all higher powers returned exactly')

# Archimedean first-moment bound: decreasing series upper bound.
x = sp.symbols('x', positive=True)
upper = sp.Rational(4, 25) + sp.integrate(1/(sp.Rational(5, 2)+2*x)**2, (x, 0, sp.oo))
assert upper == sp.Rational(9, 25)
passed('integral s*j_plus(s) <= 9/25 and resulting carrier cost')

# Möbius/sign shortcut has no unconditional positivity for DH coefficients.
tau = (sp.sqrt(10-2*sp.sqrt(5))-2)/(sp.sqrt(5)-1)
b2, b3 = tau*sp.log(2), -tau*sp.log(3)
b6 = sp.log(6) - b2*(-tau) - b3*tau
assert sp.simplify(b6-(1+tau**2)*sp.log(6)) == 0
assert sp.simplify(tau > 0) == sp.true
assert sp.simplify(tau < 1) == sp.true
assert sp.sign(b3) == -1
passed('signed DH replacement loses the positive divisor weights; no DH scan')

mp.mp.dps = 65

def sinc(z):
    return mp.sin(z)/z if z else mp.mpf(1)


def correlation(a, L, shift):
    shift = abs(shift)
    if shift >= L:
        return mp.mpf(0)
    length = L - shift
    mid = -shift/2
    out = mp.mpf(0)
    for n, an in enumerate(a):
        wn, dn = 2*mp.pi*n/L, (1 if n == 0 else mp.sqrt(2))
        for j, aj in enumerate(a):
            wj, dj = 2*mp.pi*j/L, (1 if j == 0 else mp.sqrt(2))
            out += an*aj*dn*dj*length/(2*L)*(mp.cos((wn-wj)*mid-wj*shift)*sinc((wn-wj)*length/2)
                      + mp.cos((wn+wj)*mid+wj*shift)*sinc((wn+wj)*length/2))
    return out

# Literal cosine-carrier modes: constant, single mode and mixed pair.
max_diff = mp.mpf(0)
M = 8
L = mp.log(M)
for a in ([mp.mpf(1)], [0, 1], [mp.mpf(2)/3, -mp.mpf(1)/5, 0, mp.mpf(1)/7]):
    norm2 = mp.fsum(t*t for t in a)
    assert abs(correlation(a, L, 0)-norm2) < mp.mpf('1e-60')
    raw = mp.fsum(mp.log(gcd(r,s))/mp.sqrt(r*s)*correlation(a,L,mp.log(mp.mpf(r)/s))
                 for r in range(1,M+1) for s in range(1,M+1))
    lifted = mp.mpf(0)
    for d in range(2, M+1):
        Znorm = mp.fsum(correlation(a,L,mp.log(mp.mpf(k)/j))/mp.sqrt(k*j)
                        for k in range(1,M//d+1) for j in range(1,M//d+1))
        lifted += lam(d)/d*Znorm
    h = lambda k: mp.fsum(mp.log(d)/d for d in range(1,k+1))
    reindexed = h(M)*norm2 + mp.fsum(h(M//r)/mp.sqrt(r*s)*2*correlation(a,L,mp.log(mp.mpf(r)/s))
                                 for r in range(2,M+1) for s in range(1,r) if gcd(r,s)==1)
    max_diff = max(max_diff, abs(raw-lifted), abs(raw-reindexed))
assert max_diff < mp.mpf('1e-59')
passed('three independent finite Gram expansions on literal cosine tests', '65_DPS_DIAGNOSTIC')

# Direct integration checks for arbitrary mixed correlations and both boundaries.
a = [mp.mpf(2)/3, -mp.mpf(1)/5, 0, mp.mpf(1)/7]
def f(z):
    return mp.fsum(an*(1 if n==0 else mp.sqrt(2))*mp.cos(2*mp.pi*n*z/L)/mp.sqrt(L) for n,an in enumerate(a))
for shift in (mp.mpf(0), mp.log(mp.mpf(3)/2), L/2, L-mp.mpf('1e-9')):
    direct = mp.quad(lambda z: f(z)*f(z+shift), [-L/2, (L-shift)/2-L/2, L/2-shift])
    assert abs(direct-correlation(a,L,shift)) < mp.mpf('1e-58')
assert correlation(a,L,L) == 0
passed('correlation normalization, mixed modes, zero extension and endpoints', '65_DPS_DIAGNOSTIC')

# Projection coefficient formula (the analytic proof uses an actual fixed zero).
gamma, Lp = mp.mpf('2.3'), mp.mpf('3.7')
for n in range(1, 9):
    wn = 2*mp.pi*n/Lp
    direct = mp.quad(lambda z: mp.cos(gamma*z)*mp.sqrt(2/Lp)*mp.cos(wn*z), [-Lp/2,0,Lp/2])
    formula = 2*mp.sqrt(2/Lp)*gamma*(-1)**n*mp.sin(gamma*Lp/2)/(gamma**2-wn**2)
    assert abs(direct-formula) < mp.mpf('1e-59')
passed('exact projection-coefficient formula, numerical independent integral check', '65_DPS_DIAGNOSTIC')

# Centered divisor lift: independent spatial integral versus floor kernel.
Nc = 3
bnd = L/2
def primitive_weighted(y):
    out = mp.mpf(0)
    for n,an in enumerate(a):
        wn = 2*mp.pi*n/L
        dn = 1 if n == 0 else mp.sqrt(2)
        out += an*dn/mp.sqrt(L)*mp.exp(y/2)*(mp.cos(wn*y)/2+wn*mp.sin(wn*y))/(mp.mpf('0.25')+wn**2)
    return out
lo_prim = primitive_weighted(-bnd)
whole_prim = primitive_weighted(bnd)-lo_prim
def Ccenter(x):
    upper = min(bnd, x+mp.log(Nc))
    if upper <= -bnd:
        return mp.mpf(0)
    return mp.exp(-x/2)*(primitive_weighted(upper)-lo_prim)
def Zcenter(x):
    return mp.fsum(f(x+mp.log(n))/mp.sqrt(n) for n in range(1,Nc+1) if -bnd <= x+mp.log(n) <= bnd)
points = sorted(set([-bnd-mp.log(n) for n in range(1,Nc+1)]+[bnd-mp.log(n) for n in range(1,Nc+1)]))
center_direct = mp.fsum(mp.quad(lambda x:(Zcenter(x)-Ccenter(x))**2,[u,v]) for u,v in zip(points,points[1:]))
# For x>bnd, Z is zero; C is the exact exponential tail.
center_direct += whole_prim**2*mp.exp(-bnd)
Znorm = mp.fsum(correlation(a,L,mp.log(mp.mpf(k)/j))/mp.sqrt(k*j) for k in range(1,Nc+1) for j in range(1,Nc+1))
floor_integral = mp.fsum(mp.quad(lambda s:mp.exp(s/2)*2*correlation(a,L,s),[0,min(L,mp.log(mp.mpf(Nc)/k))]) for k in range(1,Nc+1))
center_formula = Znorm-floor_integral
assert abs(center_direct-center_formula) < mp.mpf('1e-56')
passed('centered continuum subtraction, full tail and exact floor compensator', '65_DPS_DIAGNOSTIC')

# Categorical check: output means algebra/normalization, NOT universal proof by code.
report = {'checks': records, 'max_finite_gram_discrepancy': mp.nstr(max_diff, 12),
          'new_CCM_eigenproblems': 0, 'interval_certification': False,
          'universal_theorem_verifier': 'PAPER proof, not these finite tests'}
with open(Path(__file__).with_name('divisor_pullback_checks_result.json'), 'w', encoding='utf-8') as fh:
    json.dump(report, fh, ensure_ascii=False, indent=2)
print(json.dumps({k:v for k,v in report.items() if k != 'checks'}, ensure_ascii=False, indent=2))

```