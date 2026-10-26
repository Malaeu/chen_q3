# STATUS: TRY_CCM_SOURCE_DEPENDENT_SIGNED_COMPARISON_Q33
```yaml
OPERATIVE_CLASS: TRY_CCM_SOURCE_DEPENDENT_SIGNED_COMPARISON_Q33
VERDICT_CODE: RAMANUJAN_MAJORANT_EXACT_SQUARE_RETURN_RETAINS_HALF_POWER
DATE: '2026-10-26'
REQUEST_COMMIT_AS_SUPPLIED: 129d0d5e22e1bd6ff8e3a39ff10d81dcc49d05f5
REQUEST_FILE: PROSHKA_CCM_SOURCE_DEPENDENT_SIGNED_COMPARISON_Q33_2026-10-26.txt
REQUEST_BYTES: 130202
REQUEST_LF: 2286
REQUEST_SHA256: 285fe8f99a75e0a858cb5e61e72584efe45181c36f8899489a95238b5bfa3ae0
READ: COMPLETE_REQUEST_AND_EIGHT_COMPLETE_SOURCE_BODIES
MANIFEST: EIGHT_BYTE_COUNTS_AND_SHA256_MATCH
BOOTSTRAP: Malaeu/chen_q3; rh_clean; docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
OBJECT: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_P
SCHEDULE: 'N=m; L=log(m); M=R=floor(m^epsilon); fixed 0<epsilon<1/32'
EXECUTED_ROLLBACK: 'S5 sections 5-7: finite prime-matching Ramanujan model, before disposal of its signed composite correction'
SELECTED_COMPARISON: 'Actual prime-power coefficient majorant, tested on the full positive shift square; all compensating diagonals returned'
NEW_REQUIRED_SOURCE_TEST_ALIGNMENT: NOT_OBTAINED
NEW_FAVORABLE_FULL_POWER: NOT_OBTAINED
NEW_ACTUAL_PAIR_MARGIN: NOT_OBTAINED
AUXILIARY_RESULT: 'Full-window model norm <= e^2 Z^2 (16+8 Omega)(1+log Z), for Z^2<=m'
COMPLETED_CERTIFICATE: 'F_Z+2 B_Z_scalar-2 W+4 W_smallbase; negative actual mass retained'
COMPLETED_CERTIFICATE_ASYMPTOTIC: '(16/epsilon-4+o(1))*sqrt(m), at Z=floor(m^(epsilon/4))'
ASYMPTOTIC_SCOPE: DISPLAYED_CERTIFICATE_PRICE_NOT_ACTUAL_SPECTRUM
PROGRESS_ON_PRIMARY_CONSUMER: NO_PROGRESS
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
PRIMARY_GOAL: OPEN
RH: OPEN
CF22_PYSR: PARKED_REOPENABLE
ZF78_USED: false
EXTERNAL_INPUT: 'Ordinary PNT only to sharpen the certificate leading constant; half-power failure also follows without PNT'
REGISTRATION_STAGE: 'After preliminary PAPER derivation, before new executable controls'
EXACT_LOCAL_CONTROLS: 211
PLANTED_ERRORS_DETECTED: 8
NEW_INDEPENDENT_AUDIT: false
LEAN_RUN: false
ARB_RUN: false
PRODUCTION_CCM_SPECTRUM_RUN: false
REPOSITORY_WRITES: NONE
AUTOMATIC_Q34: false
```

# Q33. Конечная арифметическая мажоранта: полный возврат не даёт нужного знака

## 0. Ответ на поставленный вопрос

**Первое требуемое неравенство, использующее тонкую связь настоящей арифметики со знаком исходного теста и дающее нужный полный бюджет, не получено.** Ни степень \(\eta(\epsilon)\to0\), ни независимый коэффициентный запас на настоящей паре не доказаны.

Выполнен один конкретный тест после обоснованного отката. Вместо повторения второй первообразной или выпуклого исправления теста взята **уже документированная в S5 §§5–7 конечная Ramanujan-модель**. Она точно совпадает с \(\Lambda\) на больших простых. Добавлена явная поправка за **все степени малых простых**, после чего выведено настоящее коэффициентное неравенство. Оно перенесено на исходный тест через полный квадрат сдвига, с возвращением каждой добавленной диагонали.

Результат имеет две разные границы:

* **Аналитическая часть:** модель на всём исходном окне, а не только на гладком верхнем блоке S5, действительно имеет малую полную норму. При выбранном вспомогательном расписании её цена \(O_\epsilon(m^{3\epsilon/2})\).
* **Полное знаковое сравнение:** возвращённая диагональная плата, даже после точного сохранения выгодного \(-2\sum\Lambda(n)/\sqrt n\), остаётся \((16/\epsilon-4+o(1))\sqrt m\). Это хуже старого конверта.

Новая запись положительного квадрата **не названа независимым поставщиком CCM**. Полученное коэффициентное неравенство различает настоящий источник и произвольные положительные атомы, но после переноса не сохраняет достаточно связи с фазой теста. Именно это и есть точный отказ выбранного завершения.

### 0.1. Что не повторяется

S1 и S4 уже устанавливают: raw-тесты не монотонны и не выпуклы, а сохранение знака выпуклой поправки возвращает старый \(\Delta_2\). Эти результаты используются как проверка дубликата, не доказываются заново и не считаются новым отказом. S6 уже показывает, что контактные множители не исправляют сжатый блок; они не вводятся.

Ramanujan-модель, её среднее по периоду и совпадение на простых — также **старые входы S5**, а не открытия этого ответа. Новый расчёт ниже — проверка конкретного полного сравнения и его расходов. В частности, ограничение старого Poisson-возврата \(Z^2\le L/8\) не переносится молча на степенной \(Z\): вместо него отдельно доказывается другой, полный Euler-возврат.

## 1. Источник, область и неизменный потребитель

**[COFINAL_FAMILY | PAPER; исходные входы S1–S4, S7]** Фиксируем \(0<\epsilon<1/32\), затем увеличиваем целое \(m\). Все начала областей и константы могут зависеть от фиксированного \(\epsilon\), не от вектора:
\[
L=\log m,\qquad M=R=\lfloor m^\epsilon\rfloor,
\qquad \Omega=2\pi M/L.
\]
Синтез \(F_M\), нулевое продолжение с \([0,L]\), физическая \(L^2\)-норма и **тот же** проектор \(P\) сохраняются. Для \(c=Pc\), \(f=F_Mc\), имеем
\[
\|f\|_2=\|c\|_2,\quad f(0)=f(L)=0,
\quad \int_0^Le^{t/2}f(t)dt=\int_0^Le^{-t/2}f(t)dt=0.
\tag{1.1}
\]
Все формулы ниже допускают комплексные \(c\). Введём
\[
Q_P(s)=P Q_M(s)P,
\qquad h(x)=x^{-1/2}Q_P(\log x),
\tag{1.2}
\]
\[
A=\sum_{1\le n\le m}\Lambda(n)h(n),\qquad
C^0=A-\int_1^m h(x)dx=A+H_d,
\qquad 0\preceq H_d\preceq4P.
\tag{1.3}
\]
Принятые оценки, используемые в точной исходной области:
\[
\|Q_P(s)\|\le2,\quad
\|h(x)\|\le2x^{-1/2},\quad
\|h'(x)\|\le(1+2\Omega)x^{-3/2},
\quad h(m)=h'(m)=0.
\tag{1.4}
\]
Элементарный арифметический вход из S3:
\[
W_0(x):=\sum_{n\le x}\frac{\Lambda(n)}{\sqrt n}\le6\sqrt x.
\tag{1.5}
\]
Здесь и далее \(\Lambda(1)=0\). Производственные \(N=m\) и делительный \(R\) не меняются.

Для доказанного \(A\preceq sP\) буквальный возврат:
\[
T_{>R}\preceq(s+b_{\rm div})P,\qquad
PK_mP\succeq-[s+50L+8]P,
\tag{1.6}
\]
\[
b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\tag{1.7}
\]
Короткая плата не начисляется снова во второй формуле. Все собственные степени уже находятся в \(A\); отдельного повторного proper-power-return нет.

## 2. Ранний откат и выбранное арифметическое неравенство

### 2.1. Полная конечная модель S5, без бесконечного Ramanujan-ряда

**[FINITE_CELL | PAPER]** Пусть вспомогательное целое \(Z\ge2\) удовлетворяет \(Z^2\le m\). Это **не** \(R\). Положим
\[
\lambda_Z(n)=\sum_{q\le Z}\frac{\mu(q)c_q(n)}{\varphi(q)},\qquad
C_Z=\sum_{q\le Z}\frac{\mu(q)^2}{\varphi(q)},
\tag{2.1}
\]
\[
b_Z(n)=\frac{\lambda_Z(n)^2}{C_Z^2}\log n,
\qquad b_Z(1)=0.
\tag{2.2}
\]
\(c_q(n)\) — действительная сумма Рамануджана. Её нормировка
\[
c_q(n)=\sum_{d\mid(q,n)}d\mu(q/d)
\tag{2.3}
\]
согласуется с NIST DLMF 27.10.5. Формула также следует непосредственно из включения–исключения в сумме по взаимно простым остаткам. Ни один бесконечный ряд не вводится.

Если у \(n\) нет простого делителя \(\le Z\), то для каждого \(q\le Z\) имеем \((q,n)=1\), откуда
\[
\lambda_Z(n)=C_Z,\qquad b_Z(n)=\log n.
\tag{2.4}
\]
Для \(n=p^k\), \(p>Z\), это **\(k\log p\)**, а не \(\log p\).

### 2.2. Дополнительное коэффициентное неравенство и его точная область

Определим поправку по **основанию** простого:
\[
\ell_Z(n)=
\begin{cases}
\log p,&n=p^k,\ p\le Z,\ k\ge1,\\
0,&\text{иначе}.
\end{cases}
\tag{2.5}
\]
Она включает все \(p^k\le m\), в том числе \(p^k>Z\). Тогда
\[
\boxed{D_Z(n):=b_Z(n)+\ell_Z(n)-\Lambda(n)\ge0.}
\tag{2.6}
\]

**Доказательство.** При \(n=p^k\), \(p>Z\), (2.4) даёт \(D_Z(n)=(k-1)\log p\). При \(p\le Z\) поправка \(\ell_Z\) точно равна \(\Lambda\), так что \(D_Z(n)=b_Z(n)\ge0\). У остальных \(n>1\) обе \(\ell_Z,\Lambda\) равны нулю. При \(n=1\) все три значения нулевые. Это исчерпывает случаи. □

Это первая арифметическая **неравенственная** строка выбранного кандидата. Она использует фактическую prime-power-поддержку и вес \(\log p\). Она неверна для произвольной положительной меры той же массы, если перенести её массу на несогласованный атом. Но (2.6) **не является** ещё Loewner-сравнением \(\sum\Lambda h\) и \(\sum b_Zh\): \(h(n)\) не положительна.

### 2.3. Контроль на настоящем исходном \(P\)

Нельзя автоматически придать знаку \(b_Z-\Lambda\) знак матрицы. Это проверяется без синтетической подмены арифметики. При \(\omega=2\pi/L\) возьмём исходный допустимый профиль
\[
f(t)=a\sin\omega t+b\sin2\omega t,
\quad a=\tfrac14+\omega^2,
\quad b=-\tfrac12(\tfrac14+4\omega^2).
\tag{2.7}
\]
Оба экспоненциальных контакта сокращаются, поскольку
\[
\frac{a\omega}{1/4+\omega^2}
+\frac{2b\omega}{1/4+4\omega^2}=0.
\]
На сдвиге \(L/2\) нормированная корреляция равна
\[
\frac{2\Re\langle f,\tau_{L/2}f\rangle}{\|f\|^2}
=\frac{b^2-a^2}{a^2+b^2},
\qquad b^2-a^2=3(\omega^4-1/64)<0
\tag{2.8}
\]
при \(\omega^2<1/8\).

Например, в целых ячейках \(m=p^4\), для достаточно больших настоящих простых \(p\), атом \(n=p^2\) имеет \(\log n=L/2\). На выбранном ниже расписании \(Z<p\), \(M\ge2\) со временем; (2.7) лежит в исходном \(P\). Между тем
\[
\Lambda(p^2)-b_Z(p^2)=-\log p.
\]
Его отдельный вклад в поправку \(\sum(\Lambda-b_Z)h\) строго **положителен** по (2.8). Это проверяет только незаконный поатомный вывод. Он не устанавливает знак суммы поправок и не является нижней оценкой полной CCM.

## 3. Перенос неравенства через полный квадрат сдвига

### 3.1. Точная положительная поправка, без предполагаемого знака CCM

**[ABSTRACT | PAPER]** Обозначим через \(\tau_s\) унитарный сдвиг на \(L^2(\mathbb R)\). Функция \(f\) продолжена нулём, но сам \(\tau_s\) не заменяется сжатым, неунитарным сдвигом на \([0,L]\). Поэтому
\[
\|f+\tau_s f\|^2=2\|f\|^2+2\Re\langle f,\tau_s f\rangle.
\tag{3.1}
\]
Следовательно,
\[
J_n:=h(n)+\frac2{\sqrt n}P
=\frac1{\sqrt n}(F_MP)^*(I+\tau_{\log n})^*
(I+\tau_{\log n})F_MP\succeq0.
\tag{3.2}
\]
Никакого квадратного корня неизвестной положительной CCM здесь нет. Обе временные стороны и все комплексные смешанные коэффициенты находятся в буквальном квадрате (3.1).

Обозначим
\[
\mathcal B_Z=\sum_{n\le m}b_Z(n)h(n),\qquad
\mathcal A_{s,Z}=\sum_{n\le m}\ell_Z(n)h(n),
\tag{3.3}
\]
\[
\mathfrak b_Z=\sum_{n\le m}\frac{b_Z(n)}{\sqrt n},\qquad
W=\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n},\qquad
W_s=\sum_{n\le m}\frac{\ell_Z(n)}{\sqrt n},
\tag{3.4}
\]
\[
\mathcal E_Z=\sum_{n\le m}D_Z(n)J_n\succeq0,
\qquad D_{
m mass}=\mathfrak b_Z+W_s-W\ge0.
\tag{3.5}
\]
Тогда **до треугольника или отдельной оплаты модели** имеем
\[
\boxed{
C^0=\mathcal B_Z+H_d+\mathcal A_{s,Z}
+2D_{
m mass}P-\mathcal E_Z.
}
\tag{3.6}
\]
В частности, законно
\[
\boxed{
C^0\preceq\mathcal B_Z+H_d+\mathcal A_{s,Z}
+2(\mathfrak b_Z+W_s-W)P.
}
\tag{3.7}
\]
Выгодная настоящая масса \(-2W\) сохранена точно. Нельзя заменить (3.7) строкой без этой массы и затем объявить полученную лишнюю цену неизбежной.

**Граница:** (3.7) использует арифметическое (2.6), но после отбрасывания \(\mathcal E_Z\) сохраняет лишь его знак, не величину на реальном образе \(F_M(\operatorname{ran}P)\). Нужное более тонкое source/test-согласование этим ещё не доказано.

### 3.2. Края и смешанные члены в точном равенстве

При \(n=m\), даже если \(m\) — степень простого,
\[
h(m)=0,\qquad J_m=2m^{-1/2}P.
\]
Таким образом, верхняя диагональ \(2D_Z(m)m^{-1/2}P\) отменяется **своим слагаемым в \(\mathcal E_Z\)**. Нулевой overlap не разрешает удалить только вторую часть этой пары.

Никаких атомов \(n>m\) в (3.3)–(3.6) нет. Периодическое определение модели не означает бесконечной физической суммы. \(b_Z(1)=\ell_Z(1)=\Lambda(1)=0\), поэтому нижний атом возвращён без скрытой массы.

Если \(f=\alpha f_1+\beta f_2\), каждый квадрат в (3.5) содержит полный член
\(2\Re(\bar\alpha\beta\langle f_1+\tau f_1,f_2+\tau f_2\rangle)\).
Он не зануляется. Проектор применяется к исходному входу; между сдвигами, при разложении модели и при формировании квадратов промежуточного \(P\) нет.

## 4. Полный возврат модели на исходном окне

Здесь доказывается новый для этой попытки полный бюджет, а не используется вне области старый S5(R6). Достаточно \(Z^2\le m\); условия \(Z^2\le L/8\), гладкой верхней оболочки или дополнительного Fourier-cutoff нет.

### 4.1. Один оплаченный логарифмический непрерывный момент

**[FINITE_CELL | PAPER]** Из исходных двух экспоненциальных контактов следует
\[
\boxed{\left\|\int_1^m \log x\,h(x)\,dx\right\|\le8.}
\tag{4.1}
\]
Для доказательства сохраняем \(P\) фиксированным и вводим
\[
G_a=\int_0^L e^{as}Q_P(s)ds,\qquad
H_a=\int_0^L e^{-as}Q_P(s)ds.
\]
Несжатое ядро \(G_a+H_a\) равно
\(e^{a(t-u)}+e^{-a(t-u)}\). В точке \(a=1/2\) оба его вектора уничтожаются контактами. В производной каждого внешнего произведения тоже остаётся один такой уничтоженный множитель. Поэтому
\[
G'_{1/2}+H'_{1/2}=0,
\qquad
\int_0^L s e^{s/2}Q_P(s)ds
=\int_0^L s e^{-s/2}Q_P(s)ds.
\]
Правая норма не больше \(2\int_0^\infty s e^{-s/2}ds=8\). Это и есть (4.1). Контакты не дифференцируются вместе с \(a\), не меняется \(P\).

Эта непрерывная отмена — бухгалтерский вход модели, **не новая арифметическая знаковая оценка**.

### 4.2. Euler-возврат каждого полного делительного луча

Для любой абсолютно непрерывной матричной \(g\) на \([1,Y]\) имеем
\[
\sum_{1\le k\le Y}g(k)-\int_1^Yg(t)dt
=(1-\{Y\})g(1)+
\int_1^Y(\{t\}-\{Y\})g'(t)dt.
\tag{4.2}
\]
Отсюда норма не больше \(\|g(1)\|+\int_1^Y\|g'\|\). Формула верна и при целой верхней границе; последний неполный отрезок в ней не исчезает.

Положим \(F(x)=\log x\,h(x)\). По (1.4)
\[
\|F'(x)\|\le[2+(1+2\Omega)\log x]x^{-3/2}.
\]
Для целого \(1\le d\le m\) из (4.1)
\[
\left\|\frac1d\int_d^m F(x)dx\right\|
\le\frac{8+4\log d}{\sqrt d}.
\tag{4.3}
\]
Применив (4.2) к \(g(t)=F(dt)\), получаем
\[
\left\|\sum_{dk\le m}F(dk)-\frac1d\int_d^mF(x)dx\right\|
\le\frac{8+8\Omega+(4+4\Omega)\log d}{\sqrt d}.
\]
Следовательно,
\[
\boxed{
\left\|\sum_{dk\le m}\log(dk)h(dk)\right\|
\le\frac{16+8\Omega+(8+4\Omega)\log d}{\sqrt d}.
}
\tag{4.4}
\]
Нижний кусок \([1,d]\), нецелое \(m/d\), обе временные стороны и все матричные элементы оплачены. Равенство \(F(m)=0\) сохраняется, но в универсальной формуле (4.2) не требуется фиктивное зануление скалярного верхнего следа.

### 4.3. Все делительные пары и цена модели

Из (2.3)
\[
\lambda_Z(n)=\sum_{d\mid n,\ d\le Z}a_d,
\quad
a_d=d\sum_{q\le Z,\ d\mid q}\frac{\mu(q)\mu(q/d)}{\varphi(q)}.
\tag{4.5}
\]
Для квадратсвободного \(d\)
\[
a_d=\frac{d\mu(d)}{\varphi(d)}
\sum_{\substack{r\le Z/d\\(r,d)=1}}
\frac{\mu(r)^2}{\varphi(r)};
\]
иначе \(a_d=0\). Поэтому
\[
|a_d|\le C_Z\frac d{\varphi(d)},\qquad
\sum_{d\le Z}|a_d|\le e C_ZZ.
\tag{4.6}
\]
Последняя граница элементарна:
\[
\sum_{d\le Z}\frac d{\varphi(d)}
=\sum_{d\le Z}\sum_{r\mid d}\frac{\mu(r)^2}{\varphi(r)}
\le Z\prod_p\left(1+\frac1{p(p-1)}\right)\le eZ.
\]
В последнем шаге сумма по простым ограничена \(\sum_{n\ge2}1/[n(n-1)]=1\).

Полная модель, **со всеми разными \(d,e\)**, равна
\[
\mathcal B_Z=\frac1{C_Z^2}
\sum_{d,e\le Z}a_da_e
\sum_{[d,e]k\le m}\log([d,e]k)h([d,e]k).
\tag{4.7}
\]
Здесь стоит НОК \([d,e]\), не произведение \(de\); гиперболическая верхняя граница буквальная. Поскольку \([d,e]\le Z^2\le m\), применима (4.4). Только теперь оплачиваем модель нормой:
\[
\boxed{
\|\mathcal B_Z\|\le
F_Z:=e^2Z^2(16+8\Omega)(1+\log Z).
}
\tag{4.8}
\]
Это одновременная оценка на **всём исходном \(P\)**, без множителя его размерности. Замена \(a_da_e\) модулями в (4.8) не выдаётся за сокращение; её цена явно включена и окажется малой степенью.

## 5. Скалярная масса поправки: её нельзя заменить нормой модели

### 5.1. Точное среднее и конечный скалярный возврат

**[FINITE_CELL | PAPER]** Из конечной ортогональности сумм Рамануджана, уже принятой в S5, либо усреднения (4.5) по одному полному периоду,
\[
\boxed{\sum_{d,e\le Z}\frac{a_da_e}{[d,e]}=C_Z.}
\tag{5.1}
\]
Это алгебраическая проверка коэффициента, **не** приближение конечного отрезка \([1,m]\) средним по огромному периоду.

Для \(F_s(x)=\log x/\sqrt x\) имеем
\[
I(m):=\int_1^mF_s(x)dx=2\sqrt m\log m-4\sqrt m+4.
\tag{5.2}
\]
Формула (4.2) и
\( |F_s'(x)|\le(1+\tfrac12\log x)x^{-3/2}\)
дают, с запасом,
\[
\left|\sum_{dk\le m}\frac{\log(dk)}{\sqrt{dk}}-\frac{I(m)}d\right|
\le\frac{8+4\log d}{\sqrt d}.
\tag{5.3}
\]
В отличие от матричного \(F\), скалярный \(F_s(m)\) не равен нулю; (4.2) сохраняет его конечный возврат. Применяя (5.3) ко всем \([d,e]\) и используя (4.6), (5.1), получаем
\[
\boxed{
\mathfrak b_Z=\frac{I(m)}{C_Z}+e_Z,
\qquad |e_Z|\le G_Z:=e^2Z^2(8+8\log Z).
}
\tag{5.4}
\]
Таким образом, малая **операторная** модель (4.8) может иметь большую **скалярную** массу (5.4). Их смешивать нельзя: контакты сократили матричный интеграл, а не добавленную диагональ.

### 5.2. Асимптотика \(C_Z\) без гипотезы Мертенса

**[COFINAL_FAMILY | PAPER]** Для полноты достаточно элементарно доказать
\[
C_Z=\log Z+O(1).
\tag{5.5}
\]
Даже существует постоянный второй член. Введём мультипликативную вспомогательную последовательность \(v\):
\[
v(p)=\frac1{p(p-1)},\qquad
v(p^2)=-\frac1{p(p-1)},\qquad v(p^j)=0\quad(j\ge3).
\]
Сравнение локальных коэффициентов даёт
\[
\frac{\mu(n)^2}{\varphi(n)}
=\sum_{d\mid n}\frac{v(d)}{n/d}.
\tag{5.6}
\]
При этом \(\sum|v(d)|\) и \(\sum|v(d)|\log(2d)\) сходятся: их простые локальные суммы ограничены рядами \(\sum_p1/p^2\) и \(\sum_p\log p/p^2\). Также \(\sum v(d)=1\) по абсолютно сходящемуся произведению.

Отсюда
\[
C_Z=\sum_{d\le Z}v(d)\,H_{\lfloor Z/d\rfloor},
\]
где \(H_n\) — гармоническая сумма. Подставим
\(H_{\lfloor t\rfloor}=\log t+\gamma+O(1/t)\), \(t\ge1\).
Остаток \(\sum_{d\le Z}|v(d)|d/Z\to0\) по доминированной сходимости. Также
\(\log Z\sum_{d>Z}|v(d)|\le\sum_{d>Z}|v(d)|\log d\to0\).
Следовательно,
\[
C_Z=\log Z+\gamma-\sum_dv(d)\log d+o(1).
\tag{5.7}
\]
Это не оценка префикса настоящей \(\mu\) и не новая Mertens-предпосылка. Абсолютно сходится специально выписанная \(v\), а не ряд, чья сходимость требует RH.

### 5.3. Все степени малых простых

Из (2.5), с сохранением конечной суммы и её положительным верхом,
\[
\begin{aligned}
W_s
&\le\sum_{p\le Z}\log p\sum_{k\ge1}p^{-k/2}\\
&\le\frac1{1-1/\sqrt2}\sum_{p\le Z}\frac{\log p}{\sqrt p}
\le24\sqrt Z.
\end{aligned}
\tag{5.8}
\]
Бесконечная геометрическая сумма здесь только мажоранта конечного положительного скаляра. В исходный оператор не добавляются новые атомы. Также
\(\mathcal A_{s,Z}\preceq2W_sP\).

## 6. Полный бюджет попытки и отсутствие выигрыша

### 6.1. Односторонняя оценка с сохранённым \(-2W\)

Из (3.7), (4.8), (5.8) получаем
\[
\boxed{
C^0\preceq s_ZP+H_d,
\qquad
A\preceq s_ZP,
\qquad
s_Z=F_Z+2\mathfrak b_Z-2W+4W_s.
}
\tag{6.1}
\]
Это действительно полный вычисленный односторонний верх; \(\mathfrak b_Z,W,W_s\) — конкретные конечные суммы. Для чисто явного верхнего allowance можно заменить \(\mathfrak b_Z\) на \(I(m)/C_Z+G_Z\), сохранив \(-2W\). Такой вариант отличается от (6.1) не более чем \(4G_Z\) по цене и имеет тот же итоговый показатель.

Если требуется только скалярный верх для \(C^0\), он равен \(s_Z+4\). Но при прямом возврате к \(A=C^0-H_d\) этот дополнительный 4 **не начисляется**: в (6.1) сохранена вся \(H_d\).

Выберем одно законное расписание
\[
\boxed{Z=\lfloor m^{\epsilon/4}\rfloor.}
\tag{6.2}
\]
Для всех достаточно поздних ячеек \(Z\ge2\), \(Z^2\le m\). Из (4.8)
\[
F_Z=O_\epsilon(m^{3\epsilon/2}),\quad
G_Z=O_\epsilon(m^{\epsilon/2}L),\quad
W_s=O(m^{\epsilon/8}).
\tag{6.3}
\]
Все эти расходы имеют показатели, стремящиеся к нулю. **Но они не составляют весь \(s_Z\).**

### 6.2. Главная возвращённая цена

Сначала граница, **не использующая PNT**. Из (5.4), (5.7), (6.2)
\(\mathfrak b_Z=(8/\epsilon+o(1))\sqrt m\). Поскольку \(F_Z,W_s=o(\sqrt m)\), они неотрицательны, а \(0\le W\le6\sqrt m\), уже имеем
\[
\boxed{
16/\epsilon-12
\le\liminf_{m\to\infty}\frac{s_Z}{\sqrt m}
\le\limsup_{m\to\infty}\frac{s_Z}{\sqrt m}
\le16/\epsilon.
}
\tag{6.3a}
\]
То есть половинная цена этого завершения установлена элементарными входами. Следующая обычная PNT только уточняет её коэффициент; она не является новым арифметическим поставщиком.

Для классификации **цены сертификата**, не для получения благоприятного знака, используем обычную безусловную PNT [E1]. Она даёт \(\psi(x)\sim x\). Частичное суммирование с сохранёнными степенями простых:
\[
W=\frac{\psi(m)}{\sqrt m}
+\frac12\int_1^m\frac{\psi(t)}{t^{3/2}}dt
=(2+o(1))\sqrt m.
\tag{6.4}
\]
Переход от стандартной PNT для \(\pi\) к \(\psi\) использует частичное суммирование с \(\log p\); все высшие степени в суммарной \(\psi\) дают \(O(\sqrt x\log^2x)=o(x)\), не удаляются из точных формул.

По (5.4), (5.7), для любого фиксированного \(\kappa>0\) и \(Z=\lfloor m^\kappa\rfloor\), при \(2\kappa<1/2\),
\[
\mathfrak b_Z=(2/\kappa+o(1))\sqrt m.
\tag{6.5}
\]
Для нашего \(\kappa=\epsilon/4\) все платы (6.3) — \(o(\sqrt m)\). Поэтому
\[
\boxed{
s_Z=(16/\epsilon-4+o(1))\sqrt m.
}
\tag{6.6}
\]
Таким образом, сохранённая выгодная масса \(-2W\) уменьшила константу, но **не устранила половинную степень**. Это результат о выписанном \(s_Z\), не о \(\|C^0\|\), \(\lambda_{\max}(A)\) или отрицательном спектре \(K_m\).

Более общий вариант того же завершения при фиксированном \(\kappa>0\), \(2\kappa+\epsilon<1/2\), даёт
\(s_Z=(4/\kappa-4+o(1))\sqrt m\).
Если выбрать \(\kappa(\epsilon)\to0\) ради малой степени модельного возврата, константа растёт, но показатель не меняется. Это **не** доказательство оптимальности по всем решетным весам или всем способам сохранения \(\mathcal E_Z\); исследовано только указанное завершение.

### 6.3. Полная исходная CCM и альтернативная настоящая пара

Рабочий верх не ухудшаем:
\[
s_{\rm use}=\min\{12\sqrt m,\,\max(0,s_Z)\}.
\]
Тогда
\[
\boxed{
T_{>R}\preceq[s_{\rm use}+b_{\rm div}]P,
\qquad PK_mP\succeq-[s_{\rm use}+50L+8]P.
}
\tag{6.7}
\]
На расписании (6.2) новый \(s_Z\) со временем хуже старого \(12\sqrt m\). Короткая плата имеет показатель \(3\epsilon/2\) с логарифмами, архимедова — логарифмическая. Они не отменяют главную половинную степень.

**[COFINAL_FAMILY | CONDITIONAL; S8]** Применение (6.7) к целому возвращённому свидетелю S8 не меняет комплексной фазы настоящих сепараторов: неравенство верно для любого комплексного \(c\) в исходном \(P\), без отдельной оплаты его двух частей. Унаследованная ошибка S8
\[
C_wm^{1-2\pi}+m^{C_w}e^{-c_wL^2}=o(1)
\]
остаётся в своей области. Но allowance порядка \(\sqrt m\) при фиксированном верхе нормы, относительно сигнала \(m^\delta/L^{2\delta}\), имеет дефицит
\(m^{1/2-\delta}L^{2\delta}\).
Поэтому уменьшение числа мод и этот оплаченный возврат не превращают (6.7) в коэффициентный запас. Никакого найденного внепрямого нуля здесь не утверждается.

## 7. Первая неоплаченная строка и содержательная остановка

### 7.1. Где именно потеряна нужная связь

Доказанное положительное \(\mathcal E_Z\) нельзя считать малым: оно содержит компенсацию большой диагонали. Из (3.6) нужное сравнение было бы, например,
\[
\mathcal E_Z\succeq
\mathcal B_Z+H_d+\mathcal A_{s,Z}
+2D_{
m mass}P-sP
\tag{7.1}
\]
при \(s=D_\epsilon m^{\theta(\epsilon)}\), \(\theta(\epsilon)\to0\).
**(7.1) не доказано. По (3.6) это ровно исходная \(C^0\preceq sP\), а не новый поставщик.**

Первый решающий отказ завершения — переход (3.6) → (3.7): на настоящем образе остаётся только \(\mathcal E_Z\ge0\). Дополнительная потеря знаков в (4.8) законна и полностью оплачена малой степенью; она не объясняет большой диагональный член (6.6).

Не найдено независимое количественное свойство, связывающее **величину** этой энергии с её диагональной массой и текущей фазой \(F_Mc\). Не принимаем его в предпосылки. Таким образом, требуемая Q33 тонкая source/test-оценка отсутствует, хотя слабое коэффициентное сравнение (2.6) и его конечный перенос доказаны.

### 7.2. Какой откат действительно выполнен

Откат — к **S5 §§5–7, до удаления rough-composite остатка**, а не к \(\Delta_2\), новой выпуклой мажоранте или очередной частотной полосе. Его полный исходный возврат здесь выписан:
\[
C^0=\mathcal B_Z+H_d+\mathcal U_Z,
\quad
\mathcal U_Z=\sum_{n\le m}(\Lambda(n)-b_Z(n))h(n)
=\mathcal A_{s,Z}+2D_{
m mass}P-\mathcal E_Z.
\tag{7.2}
\]
Добавочная ошибка этого равенства нулевая. Модельный бюджет теперь известен на всём окне по (4.8), но \(\mathcal U_Z\) по-прежнему надо оценивать **со знаком**. На rough-составных с двумя разными простыми его коэффициент \(-\log n\); на rough-степенях \(p^k\) — \(-(k-1)\log p\). На small-base-степенях сохраняется полный \(\Lambda-b_Z\). Эти случаи не объединяются неправильно.

Нет основания продолжать то же завершение увеличением \(Z\), точности или числа прогоняемых ячеек. В частности, маленькая \(\mathcal B_Z\) не означает маленькую \(\mathfrak b_Z\), и (6.6) не исправляется переименованием последней.

### 7.3. Проверки границ и два допустимых представления для следующего аудита

Это не каталог новых попыток и не два новых поручения. Для ограниченной проверки остаются две точные формы одного остатка:

| Форма | Что она различает | Цена/способ проверки и предел |
|---|---|---|
| \(\mathcal U_Z=\sum(\Lambda-b_Z)h\) | правильные коэффициенты \(p\), \(p^k\), rough-составных; сохранённый знак каждого \(h\) | конечная арифметика, малая стоимость; не даёт асимптотического знака всей суммы |
| \(\mathcal A_{s,Z}+2D_{\rm mass}P-\mathcal E_Z\) | сохранена ли компенсация полной диагонали, включая \(n=m\), на одной исходной функции | точная алгебра квадрата, малая стоимость; для улучшения нужен независимый совместный контроль, которого нет |

**Дискриминатор:** нулевой верхний overlap должен давать нулевой общий атом после сборки диагонали и \(\mathcal E_Z\); исходный вектор (2.7) должен сохранять противоположный знак поатомной rough-prime-power поправки. Исправление, нарушающее любой из этих тестов, потеряло реальный член. Кроме того, полный непрерывный фон всегда возвращается как \(-H_d\), а не оплачивается заново величиной \(\sqrt m\).

**Одно следующее действие:** ограниченный независимый PAPER-аудит (2.6), (3.6), (4.4)–(4.8), (5.4) и итоговой (6.6). Он должен проверить, не пропущены ли малые основания с большими степенями, верхняя диагональ и нецелые концы делительных лучей. Это проверка текущего результата, не автоматический Q34 и не поручение формализовать открытый знак.

## 8. Реестр результата и эпистемическая граница

| Утверждение | Scope | Verifier | Статус |
|---|---|---|---|
| Полные байты запроса и восемь тел совпали | FINITE_CELL | PAPER | воспроизведённая проверка происхождения, не проверка всех старых доказательств |
| (2.6), все prime-power случаи | ABSTRACT | PAPER | доказано выше |
| (3.6), полный комплексный квадрат и верхний атом | FINITE_CELL | PAPER | точное равенство, не знак CCM |
| (4.8), полный модельный оператор при \(Z^2\le m\) | FINITE_CELL | PAPER | доказанный модельный конверт |
| (5.4), скалярная масса с полным краем | FINITE_CELL | PAPER | доказано выше |
| (6.6), цена выбранного завершения | COFINAL_FAMILY | PAPER | обычная PNT [E1] лишь для классификации цены |
| S8, гипотетическая настоящая пара | COFINAL_FAMILY | CONDITIONAL | прежний принятый receiver, не новая сертификация upstream |
| Нужный общий знак (7.1) | COFINAL_FAMILY | CONDITIONAL | **не доказан и не потреблён** |

**DOWNSTREAM_CONSUMER:** исходный all-\(P\) верх \(T_{>R}\) со степенью, стремящейся к нулю.

**ACTUAL_CONSUMER_REQUIREMENT:** полный подписанный верх, а не малость модели или большой положительный квадрат отдельно.

**ORIGINAL_REQUESTED_OBJECT:** \(C^0\) и его исходный возврат (1.6).

**ORIGINAL_OBJECT_IS:** связь с требуемым \(T\) дана источником; конкретный Ramanujan-сертификат **NOT_NECESSARY**. Его неудача не исключает иное доказательство.

**KNOWN_WEAKER_INTERFACE:** действительный независимый coefficient margin на целой паре S8 с оплаченным receiver был бы достаточным альтернативным выходом; здесь он не получен и не заменяет all-\(P\) цель.

**FAILURE_TYPE / EPISTEMIC_STATUS:** NO_DERIVATION / RESEARCH_DEBT. Нет доказательства невозможности CCM или всех Ramanujan-методов.

**NOVELTY_AXIS:** полный расчёт конкретной модели и её возвращённой диагонали в текущем исходном пространстве; не заявление мировой новизны и не новый арифметический закон сокращения.

**REOPEN_TRIGGER:** независимое знаковое неравенство, контролирующее \(\mathcal U_Z\) либо сохранённую комбинацию в (7.2) до модулей и улучшающее **полный** бюджет. Формула существования такого неравенства, finite fit или точная перестановка сумм не являются этим входом.

**META CLOSEOUT:** источник и тест не заменены; модельный расход посчитан, но исходная знаковая обязанность не уменьшена. По основному потребителю **NO_PROGRESS**. Не повторять положительную поправку с отбрасыванием \(\mathcal E_Z\), выдавая её за независимое решение. Первая недоказанная строка названа в (7.1), но её новое имя не считается продвижением. Сильнейшая атака на попытку — большая диагональ после полного возврата; (6.6) подтверждает её на уровне сертификата, не спектра.

Три структурные проверки относятся к одному механизму, а не считаются тремя новыми неудачами: конечные Ramanujan-фазы дают точный делительный переход; унитарный shift-square даёт действительное одностороннее сравнение; исходные контакты оплачивают модельные непрерывные моменты. Ни один из этих переходов не поставляет потерянный совместный кредит после (3.7).

## 9. Верификация, внешние зависимости и воспроизведение

### 9.1. Что прочитано и что не сертифицировано заново

Прочитан канонический TXT целиком, включая все восемь полных тел и встроенный код прежнего Q32. Их размеры и хеши приведены ниже. Это не новая независимая сертификация всего проекта: исходные \(P\), kernel/derivative/receiver-входы используются в границах, явно записанных в источниках.

Внешние справочные проверки:

- **E1:** NIST DLMF §27.12, формула 27.12.5; используется только её обычное следствие PNT для (6.4). Полная внешняя PNT-proof здесь не воспроизводится. Не импортируется RH-эквивалентная ошибка и не заявляется новый факт о текущем статусе RH. URL: <https://dlmf.nist.gov/27.12>.
- **E2:** NIST DLMF §27.10, формулы 27.10.4–5 — проверка нормировки конечной суммы Рамануджана. Используемое включение–исключение и конечные коэффициенты также выведены в (2.3), (4.5). URL: <https://dlmf.nist.gov/27.10>.

Brun–Titchmarsh, BV, quantitative \(U^2\), новая zero-free область, ZF78, Mertens и variance в доказательство этого ответа **не входят**. Ранее условные результаты остаются условными.

### 9.2. Что реально запускалось

`check_q33.py` выполнил **211 точных локальных контролей** и обнаружил **8 намеренно неверных подстановок**. Из 211 контролей значительная часть — перебор небольших целых \(Z,n\) для проверки арифметических формул. Это не 211 независимых доказательств и не доказательство асимптотики конечным перебором.

Проверены: конечное делительное раскрытие; знак (2.6) по формальным коэффициентам \(\log p\); НОК и среднее модели; вспомогательная свёртка (5.6); полный квадрат с двумя временами и комплексными смешанными членами; сохранение верхней диагонали; первообразные для Euler-возврата; коэффициенты исходного sine-теста; арифметика показателей.

В shift-контролях используется точная конечная модель нулевого продолжения на целочисленной решётке — **только прибор для проверки алгебры (3.1)**, не production-ячейка CCM. Исходный sine-тест проверяет символические коэффициенты и контакты, без численного спектрального расчёта.

`verify_sources_q33.py` проверил канонический SHA-256 и восемь byte-locked тел. Нового независимого аудитора не запускал. Lean, Arb и production-спектр не запускались. Репозиторий не менялся.

Регистрация трёх ожиданий выполнена **после предварительного PAPER-вывода, но до новых исполняемых контролей**; она приложена как отдельное тело. Это не ретроактивная регистрация до выбора механизма. P1 и P2 подтверждены точной алгеброй; P3 — арифметикой конечных констант/показателей и PAPER-выводом §§4–6, не численной оценкой бесконечного семейства.

### 9.3. Команды воспроизведения

Сохранить тела файлов из приложения в один каталог, рядом положить точный исходный TXT. В существующем окружении с Python и SymPy выполнить:

```bash
python check_q33.py
python verify_sources_q33.py PROSHKA_CCM_SOURCE_DEPENDENT_SIGNED_COMPARISON_Q33_2026-10-26.txt
```

`check_q33.py` создаёт `q33_checks.json`; второй скрипт — `q33_sources.json`. Аргумент второго скрипта — путь к **оригинальному** каноническому TXT; нельзя подставлять этот Markdown вместо него. Скрипты не требуют сети, не изменяют репозиторий и не считают настоящий спектр.

В приложении приведены точные исполняемые тела, результаты и регистрация. После окончательной сборки они извлечены из этого Markdown, хеши проверены, оба скрипта повторно исполнены; результаты совпали побайтно. Это утверждение относится только к перечисленным исполняемым контролям.

## 10. Манифест прочитанных источников

Общий запрос: **130202 bytes; 2286 LF; SHA256 285fe8f99a75e0a858cb5e61e72584efe45181c36f8899489a95238b5bfa3ae0**. После каждого тела источника один разделительный LF, не входящий в объявленное число байтов.

| ID | Полное имя | Bytes | LF | SHA-256 |
|---|---|---:|---:|---|
| S1 | `CCM_POST_Q32_ORDER_TRANSPORT_PREFLIGHT.md` | 7069 | 133 | `11a87906708c9aee0cdfb23d53d0a37bfbbd0b2f7843845efaa4bce68339edb1` |
| S2 | `CCM_Q32_CONCLUSION.md` | 3625 | 64 | `183d938014b47b8ac21e83ee13e5e605908f27f1198011a26513b365ed127245` |
| S3 | `PROSHKA_CCM_SIGNED_NEAR_FREQUENCY_Q32_VERDICT_2026-10-26.md` | 77294 | 1247 | `1ed7b9b55f29658fa1022f95ef4e89d183be0a1bdac6abaa8ff93cd040fe4f50` |
| S4 | `CCM_Q04_CENTERED_SECOND_PRIMITIVE.md` | 2920 | 55 | `ca6e4213fdf7a94168fa6cbca3f5f3a60a1c887e5fbc8159a64683de1f4bfc85` |
| S5 | `CCM_DENSITY_PAIRING_TEST.md` | 17206 | 350 | `c22768413fa17d0282f4f1b5338ee51a80fa035a31ebec4a42d6a755628dbae3` |
| S6 | `CCM_POST_Q29_CONTACT_CERTIFICATE_TEST.md` | 2736 | 56 | `2b3652b512ce5a4ffe9433262cffce44086c36e24f1320286fcc5b4f5235eef6` |
| S7 | `CCM_POST_Q27_ORIGINAL_P_CONTOUR.md` | 5633 | 123 | `109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2` |
| S8 | `CCM_POST_Q26_POLYLOG_WITNESS.md` | 8064 | 154 | `c7db024c1a5b17bcc5af53c427ccd3dd586c12229e4f9306ad045df9f6ba4681` |

Полный request hash закрепляет также исходное задание и границы тел. Этим восьми источникам соответствуют ссылки S1–S8 в доказательстве; встроенные исторические директивы не были новыми поручениями.

## Приложение A. Точные исполняемые тела и результаты

### `registered_predictions.json`

Bytes: 692; SHA-256: `70591a685709b580a528a865592d433b8bd0f2701cd5b41955b1c8f72dbe11d1`.

<!-- BEGIN_FILE registered_predictions.json BYTES=692 SHA256=70591a685709b580a528a865592d433b8bd0f2701cd5b41955b1c8f72dbe11d1 -->
```json
{
  "stage": "after preliminary PAPER derivation; before new executable checks",
  "P1": "Finite Ramanujan divisor coefficients and full-period mean agree exactly; majorant fails if small-base prime powers are omitted.",
  "P2": "Full signed shift-square return agrees for complex vectors, including the no-overlap upper atom; deleting its square term creates a mismatch.",
  "P3": "The stated elementary Euler and exponent algebra is consistent; the completed certificate at Z=floor(m^(epsilon/4)) retains power one half, not a vanishing power.",
  "scope": "These predictions concern finite algebra and the displayed proof budget, not a numerical original CCM sign or independent audit."
}
```
<!-- END_FILE registered_predictions.json -->

### `check_q33.py`

Bytes: 6600; SHA-256: `855e750b9eb221275dfc7fc2eeb1e52ff63171746cb3ab2923c16437e812d050`.

<!-- BEGIN_FILE check_q33.py BYTES=6600 SHA256=855e750b9eb221275dfc7fc2eeb1e52ff63171746cb3ab2923c16437e812d050 -->
```python
#!/usr/bin/env python3
"""Exact finite controls for Q33. Not a CCM spectral or asymptotic proof."""
from collections import Counter
from fractions import Fraction as Q
from math import gcd, lcm
import json
from pathlib import Path
import sympy as s

counts = Counter()
planted = []
def check(group, proposition):
    if not bool(proposition):
        raise AssertionError(f'failed control: {group}')
    counts[group] += 1

def reject(name, wrong_claim):
    if bool(wrong_claim):
        raise AssertionError(f'planted error was not detected: {name}')
    planted.append(name)

def mu(n): return int(s.mobius(n))
def phi(n): return int(s.totient(n))
def ram(q,n):
    return sum(d*mu(q//d) for d in s.divisors(gcd(q,n)))
def cz(z):
    return sum((Q(mu(q)**2, phi(q)) for q in range(1,z+1)), Q(0))
def lam(z,n):
    return sum((Q(mu(q)*ram(q,n),phi(q)) for q in range(1,z+1)), Q(0))
def coeff(z,d):
    return sum((Q(d*mu(q)*mu(q//d),phi(q)) for q in range(d,z+1,d)),Q(0))
def logvec(n): return {int(p):Q(int(k)) for p,k in s.factorint(n).items()}
def mangvec(n):
    fs=s.factorint(n)
    return {int(next(iter(fs))):Q(1)} if len(fs)==1 else {}
def ellvec(z,n):
    v=mangvec(n)
    return v if v and next(iter(v))<=z else {}
def diffvec(z,n,omit_high_small=False):
    r=lam(z,n)**2/cz(z)**2
    ans={p:r*k for p,k in logvec(n).items()}
    ell=ellvec(z,n) if not (omit_high_small and n>z) else {}
    for v,sign in ((ell,1),(mangvec(n),-1)):
        for p,k in v.items(): ans[p]=ans.get(p,Q(0))+sign*k
    return ans

for z in (2,3,5):
    aa={d:coeff(z,d) for d in range(1,z+1)}
    for n in range(1,25):
        check('finite_Ramanujan_divisor_map',lam(z,n)==sum((aa[d] for d in aa if n%d==0),Q(0)))
        check('actual_prime_power_coefficient_majorant',all(v>=0 for v in diffvec(z,n).values()))
    mean=sum((aa[d]*aa[e]/lcm(d,e) for d in aa for e in aa),Q(0))
    check('exact_model_mean',mean==cz(z))
    period=lcm(*range(1,z+1))
    check('period_orthogonality',sum(lam(z,n)**2 for n in range(1,period+1))/period==cz(z))
    for d in aa:
        alt=Q(d*mu(d),phi(d))*sum((Q(mu(r)**2,phi(r)) for r in range(1,z//d+1) if gcd(d,r)==1),Q(0))
        check('coefficient_closed_form',aa[d]==alt)

# Absolutely summable auxiliary convolution, not a Mertens premise.
def vv(n):
    ans=Q(1)
    for p,k in s.factorint(n).items():
        p=int(p);k=int(k)
        if k>2:return Q(0)
        ans*=Q(1 if k==1 else -1,p*(p-1))
    return ans
for n in range(1,25):
    check('auxiliary_convolution',sum((vv(d)/Q(n//d) for d in s.divisors(n)),Q(0))==Q(mu(n)**2,phi(n)))

# Zero-extended translations on a finite physical lattice: only algebra model.
d=4; P=s.eye(d)-s.ones(d,d)/d
for shift in (0,1,3,4,6):
    ext=d+2*shift
    F=s.zeros(ext,d); U=s.zeros(ext,d)
    for j in range(d):F[j+shift,j]=1;U[j+2*shift,j]=1
    Qs=F.T*U+U.T*F
    square=P*(F+U).T*(F+U)*P
    check('both_time_shift_square',s.simplify(square-P*(2*s.eye(d)+Qs)*P)==s.zeros(d))
    c=P*s.Matrix([1+s.I,2-s.I,-1+2*s.I,3])
    check('complex_cross_term',s.simplify((c.conjugate().T*square*c)[0]-((F+U)*c).dot(((F+U)*c).conjugate()))==0)
    if shift>=d:check('zero_overlap_keeps_energy_diagonal',square==2*P)

# Complete signed source return, with the negative true mass retained.
Q1=s.Matrix([[0,1+s.I],[1-s.I,0]])
Q2=s.Matrix([[1,s.I],[-s.I,-1]])
I=s.eye(2); a,b,l,ds=s.symbols('a b l ds',real=True)
D=b+l-a
A=a*Q1;B=b*Q1;As=l*Q1;E=D*(Q1+2*I)
check('full_signed_return',s.expand(B+As+2*D*I-E-A)==s.zeros(2))
A2=a*Q1+ds*Q2
check('mixed_labels_return',s.expand((B+As+2*D*I-E)+ds*Q2-A2)==s.zeros(2))

# Integrals entering finite Euler returns.
x=s.symbols('x',positive=True)
primitive=2*s.sqrt(x)*s.log(x)-4*s.sqrt(x)
check('Euler_integrals',s.simplify(s.diff(primitive,x)-s.log(x)/s.sqrt(x))==0)
primitive2=(-2*s.log(x)-4)/s.sqrt(x)
check('Euler_integrals',s.simplify(s.diff(primitive2,x)-s.log(x)/x**s.Rational(3,2))==0)
check('Euler_integrals',s.simplify((primitive.subs(x,1)))==-4)
O,z=s.symbols('O z',nonnegative=True)
check('Euler_constants',s.expand((8+4*z)+(8+8*O+(4+4*O)*z)-(16+8*O+(8+4*O)*z))==0)
P0=s.diag(0,0,1,1)
v0=s.Matrix([1,0,0,0]);w0=s.Matrix([0,1,0,0])
v1=s.Matrix(s.symbols('v0:4'));w1=s.Matrix(s.symbols('w0:4'))
rank_deriv=v1*w0.T+v0*w1.T+w1*v0.T+w0*v1.T
check('log_contact_rank_two_derivative',P0*rank_deriv*P0==s.zeros(4))

# Actual original-P sine-vector coefficients; no numerical production cell.
u=s.symbols('u',positive=True)
a0=s.Rational(1,4)+u**2;b0=-(s.Rational(1,4)+4*u**2)/2
check('actual_contact_sine',s.simplify(a0*u/(s.Rational(1,4)+u**2)+b0*2*u/(s.Rational(1,4)+4*u**2))==0)
check('actual_contact_sine',s.expand(b0**2-a0**2)==3*(u**4-s.Rational(1,64)))
check('actual_contact_sine', (b0**2-a0**2).subs(u,s.Rational(1,4))<0)

# Fixed exponent budgets. These arithmetic controls do not prove asymptotics.
e=s.symbols('epsilon',positive=True); k=e/4
check('exponent_algebra',s.simplify(2*k+e-3*e/2)==0)
check('exponent_algebra',s.simplify(k/2-e/8)==0)
check('exponent_algebra',s.simplify(4/k-4-(16/e-4))==0)
check('exponent_algebra',s.Rational(3,2)*s.Rational(1,32)<s.Rational(1,2))

# Planted failures; each tests an actual change in the displayed formulas.
reject('omit_small_base_high_prime_powers',all(v>=0 for v in diffvec(2,4,True).values()))
reject('rough_prime_square_matches_Lambda',lam(2,9)**2/cz(2)**2*2==1)
reject('replace_lcm_by_product',sum((coeff(2,d)*coeff(2,e)/Q(d*e) for d in (1,2) for e in (1,2)),Q(0))==cz(2))
reject('drop_square_in_nonnegative_model',lam(3,6)/cz(3)>=0)
reject('forget_negative_actual_mass',s.expand(B+As+2*(b+l)*I-E-A)==s.zeros(2))
top_coefficient=diffvec(2,9)[3] # coefficient of actual log(3)
top_diagonal=2*s.Rational(top_coefficient.numerator,top_coefficient.denominator)/s.sqrt(9)
top_energy=top_diagonal
check('actual_top_atom_cancellation',s.simplify(top_diagonal-top_energy)==0)
reject('delete_top_square_only',s.simplify(top_diagonal)==0)
V=s.Matrix([[0,0],[1,0]])
reject('truncated_shift_is_unitary',(s.eye(2)+V).T*(s.eye(2)+V)==2*s.eye(2)+V+V.T)
zv=s.Matrix([1+s.I,2-s.I])
reject('transpose_for_complex_norm',(zv.T*zv)[0]==(zv.conjugate().T*zv)[0])

out={
 'status':'EXACT_LOCAL_CONTROLS_COMPLETED',
 'checks':dict(counts),'total_checks':sum(counts.values()),
 'planted_errors_detected':planted,'planted_count':len(planted),
 'scope':'finite algebra and exponent checks only; no asymptotic sign or original CCM spectrum certification',
 'independent_audit':False,'lean':False,'arb':False
}
Path('q33_checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,ensure_ascii=False,indent=2))
```
<!-- END_FILE check_q33.py -->

### `q33_checks.json`

Bytes: 1181; SHA-256: `fbeeaaeb8f17dd3b7d5badead5221ddd553dfa2389604e9516f35454a0f09ac0`.

<!-- BEGIN_FILE q33_checks.json BYTES=1181 SHA256=fbeeaaeb8f17dd3b7d5badead5221ddd553dfa2389604e9516f35454a0f09ac0 -->
```json
{
  "status": "EXACT_LOCAL_CONTROLS_COMPLETED",
  "checks": {
    "finite_Ramanujan_divisor_map": 72,
    "actual_prime_power_coefficient_majorant": 72,
    "exact_model_mean": 3,
    "period_orthogonality": 3,
    "coefficient_closed_form": 10,
    "auxiliary_convolution": 24,
    "both_time_shift_square": 5,
    "complex_cross_term": 5,
    "zero_overlap_keeps_energy_diagonal": 2,
    "full_signed_return": 1,
    "mixed_labels_return": 1,
    "Euler_integrals": 3,
    "Euler_constants": 1,
    "log_contact_rank_two_derivative": 1,
    "actual_contact_sine": 3,
    "exponent_algebra": 4,
    "actual_top_atom_cancellation": 1
  },
  "total_checks": 211,
  "planted_errors_detected": [
    "omit_small_base_high_prime_powers",
    "rough_prime_square_matches_Lambda",
    "replace_lcm_by_product",
    "drop_square_in_nonnegative_model",
    "forget_negative_actual_mass",
    "delete_top_square_only",
    "truncated_shift_is_unitary",
    "transpose_for_complex_norm"
  ],
  "planted_count": 8,
  "scope": "finite algebra and exponent checks only; no asymptotic sign or original CCM spectrum certification",
  "independent_audit": false,
  "lean": false,
  "arb": false
}
```
<!-- END_FILE q33_checks.json -->

### `verify_sources_q33.py`

Bytes: 1667; SHA-256: `e3e9e0b388c463ab801389bd8341cc6f60ea82a6c16671ffdb251198aea75fe4`.

<!-- BEGIN_FILE verify_sources_q33.py BYTES=1667 SHA256=e3e9e0b388c463ab801389bd8341cc6f60ea82a6c16671ffdb251198aea75fe4 -->
```python
#!/usr/bin/env python3
"""Verify exact Q33 bytes and eight declared full source bodies."""
import argparse
import hashlib
import json
from pathlib import Path
import re
EXPECTED='285fe8f99a75e0a858cb5e61e72584efe45181c36f8899489a95238b5bfa3ae0'
def digest(b):return hashlib.sha256(b).hexdigest()
p=argparse.ArgumentParser()
p.add_argument('packet',type=Path)
p.add_argument('--output',type=Path,default=Path('q33_sources.json'))
a=p.parse_args()
raw=a.packet.read_bytes()
if digest(raw)!=EXPECTED:raise SystemExit('Q33 request SHA256 mismatch')
raw.decode('utf-8',errors='strict')
pat=rb'^=== SOURCE (S\d+): (.*?) \| BYTES (\d+) \| SHA256 ([a-f0-9]{64}) ===\n'
entries=[]
for h in re.finditer(pat,raw,re.M):
    sid,name,n,sha=h.groups();n=int(n)
    body=raw[h.end():h.end()+n]
    if len(body)!=n or digest(body)!=sha.decode():
        raise SystemExit('Body mismatch: '+sid.decode())
    ending=b'\n=== END SOURCE '+sid+b' ==='
    if not raw[h.end()+n:].startswith(ending):
        raise SystemExit('Body boundary mismatch: '+sid.decode())
    body.decode('utf-8',errors='strict')
    entries.append({'id':sid.decode(),'name':name.decode(),'bytes':n,
                    'lf':body.count(b'\n'),'sha256':digest(body)})
if [e['id'] for e in entries]!=['S'+str(i) for i in range(1,9)]:
    raise SystemExit('Source ID/count mismatch')
out={'request_bytes':len(raw),'request_lf':raw.count(b'\n'),
     'request_sha256':digest(raw),'source_count':len(entries),'sources':entries}
a.output.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'request_sha256':digest(raw),'source_count':len(entries),'all_hashes_match':True}))
```
<!-- END_FILE verify_sources_q33.py -->

### `q33_sources.json`

Bytes: 1829; SHA-256: `79bc60374d4003259db879d03feac0ae016cee10b09a31973d471d6111159e06`.

<!-- BEGIN_FILE q33_sources.json BYTES=1829 SHA256=79bc60374d4003259db879d03feac0ae016cee10b09a31973d471d6111159e06 -->
```json
{
  "request_bytes": 130202,
  "request_lf": 2286,
  "request_sha256": "285fe8f99a75e0a858cb5e61e72584efe45181c36f8899489a95238b5bfa3ae0",
  "source_count": 8,
  "sources": [
    {
      "id": "S1",
      "name": "CCM_POST_Q32_ORDER_TRANSPORT_PREFLIGHT.md",
      "bytes": 7069,
      "lf": 133,
      "sha256": "11a87906708c9aee0cdfb23d53d0a37bfbbd0b2f7843845efaa4bce68339edb1"
    },
    {
      "id": "S2",
      "name": "CCM_Q32_CONCLUSION.md",
      "bytes": 3625,
      "lf": 64,
      "sha256": "183d938014b47b8ac21e83ee13e5e605908f27f1198011a26513b365ed127245"
    },
    {
      "id": "S3",
      "name": "PROSHKA_CCM_SIGNED_NEAR_FREQUENCY_Q32_VERDICT_2026-10-26.md",
      "bytes": 77294,
      "lf": 1247,
      "sha256": "1ed7b9b55f29658fa1022f95ef4e89d183be0a1bdac6abaa8ff93cd040fe4f50"
    },
    {
      "id": "S4",
      "name": "CCM_Q04_CENTERED_SECOND_PRIMITIVE.md",
      "bytes": 2920,
      "lf": 55,
      "sha256": "ca6e4213fdf7a94168fa6cbca3f5f3a60a1c887e5fbc8159a64683de1f4bfc85"
    },
    {
      "id": "S5",
      "name": "CCM_DENSITY_PAIRING_TEST.md",
      "bytes": 17206,
      "lf": 350,
      "sha256": "c22768413fa17d0282f4f1b5338ee51a80fa035a31ebec4a42d6a755628dbae3"
    },
    {
      "id": "S6",
      "name": "CCM_POST_Q29_CONTACT_CERTIFICATE_TEST.md",
      "bytes": 2736,
      "lf": 56,
      "sha256": "2b3652b512ce5a4ffe9433262cffce44086c36e24f1320286fcc5b4f5235eef6"
    },
    {
      "id": "S7",
      "name": "CCM_POST_Q27_ORIGINAL_P_CONTOUR.md",
      "bytes": 5633,
      "lf": 123,
      "sha256": "109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2"
    },
    {
      "id": "S8",
      "name": "CCM_POST_Q26_POLYLOG_WITNESS.md",
      "bytes": 8064,
      "lf": 154,
      "sha256": "c7db024c1a5b17bcc5af53c427ccd3dd586c12229e4f9306ad045df9f6ba4681"
    }
  ]
}
```
<!-- END_FILE q33_sources.json -->

## Финальная граница

**Модельный и геометрический возвраты выполнены. Требуемая источникозависимая знаковая оценка полной CCM не доказана.** Положительный арифметический majorant становится законным операторным сравнением лишь вместе с возвращённой диагональю; её цена после всех выгодных скалярных вычитаний всё ещё имеет степень \(1/2\). Никакого доказательства невозможности реального сокращения, нового RH-результата или автоматического следующего запроса из этого не следует.
