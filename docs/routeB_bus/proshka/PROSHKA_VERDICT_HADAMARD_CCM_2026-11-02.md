# STATUS: TRY_CCM_HADAMARD_WINDOW_VARIATION
```yaml
OPERATIVE_CLASS: TRY_CCM_HADAMARD_WINDOW_VARIATION
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_REQUEST_FOR_LITERAL_CCM_WINDOW_VARIATION
SOURCE_BRANCH: rh_clean
SOURCE_COMMIT: 36e9555645afa80aaf0560f55a5f2f3fee6b48fe
SOURCE_NOESCAPE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md
SOURCE_NOESCAPE_SHA256: fdfd384345b69d7565100b93ef57348eb6944bdbaf014a01c001df007129aded
SOURCE_NOESCAPE_GIT_BLOB: 453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc
SOURCE_NOESCAPE_HASH_CHECK: MATCH_LOCAL_BYTES_AND_REMOTE_BLOB
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: VARIATION_FORMULA_PROVED_PAPER_WITH_NONSMOOTH_GUARDS
FIXED_N_INTERPOLATION: SAME_FULL_SOURCE_AND_NORMALIZED_FOURIER_BASIS
ORIGINAL_VALUES: K_E_N_EQUALS_M_AT_L_EQUALS_LOG_M
FIXED_N_ATOMIC_VALUE_JUMP: ZERO
FIXED_N_ATOMIC_DERIVATIVE_JUMP: NEGATIVE_RANK_ONE_ENDPOINT_FORM
SIMPLE_BOTTOM_FORMULA: EXACT
MULTIPLE_BOTTOM: ONE_SIDED_COMPRESSED_MIN_MAX_FORMULAS
MOVING_DIMENSION: SEPARATE_NONPOSITIVE_PRINCIPAL_EXTENSION_JUMPS
PROGRESS_CLASS: REPRESENTATION_PROGRESS
PROGRESS_SCOPE: SOURCE_EXACT_WINDOW_DERIVATIVE_NOT_A_COFINAL_SIGN_BOUND
VERIFIER: PAPER
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
T_PROVED: false
BACKGROUND_SECOND_MOMENT_PROVED: false
ROUTE_PROMOTION: false
```

## 0. Точный ответ и граница утверждения

**[FINITE_CELL | PAPER]** Ниже доказана формула первой вариации нижнего уровня **буквального чётного CCM-блока**, со всеми степенями простых, полюсным вкладом, бесконечным архимедовым хвостом, обоими концами окна и нормировкой базиса.

Есть три обязательных различия.

1. Источник задаёт дискретные ячейки `N=m, L=log m`. Производная по непрерывному L сначала определяется при **фиксированном N** в той же форме. Это явно заданная интерполяция; при `N=m, L=log m` она возвращает исходную матрицу точно.
2. При `L=log n` новый prime-power атом имеет **нулевую энергию в момент входа**: корреляция при сдвиге на всю длину окна равна нулю. Поэтому матрица и её нижний уровень при фиксированном N непрерывны. Скачок имеет **производная**, а не значение. У K' нет дельта-атома; он появляется в распределительной K''.
3. Для кратного нижнего уровня обычная производная может не существовать. Правильная замена — минимальное/максимальное собственное значение сжатой односторонней производной. Если N тоже увеличивается, добавляется отдельный скачок расширения носителя.

Последняя попытка (★) не объявляется закрытой или опровергнутой: в предыдущем вердикте её совместная исходниковая оценка оставлена открытой. Неудача абсолютной оценки ошибки простых не является доказательством невозможности ветви. Настоящий батч **не** использует (★), RH, quasi-RH, PNT, положения нулей, theta-радикальность или предположение о простоте всех нижних уровней.

## 1. Source lock

Прочитаны через GitHub connector:

- **S1:** `docs/NOESCAPE_STORY_2026-10-30.md`, §2 и контекст, на указанном SOURCE_COMMIT; Git blob `b3bb563a52776c2ff1747e83cbacbf41765b036a`. Этот файл вне bus открыт именно по явному адресу владельца. Он задаёт размерность, окно и происхождение исходной матрицы.
- **S2:** `docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md`, §1, в том же коммите; полная форма (1.4), базис (1.1), отсутствие безусловного предположения простоты. Локальный файл: 64 077 bytes, 1084 LF; SHA-256 и Git blob совпадают с запросом/удалённым объектом.
- **S3:** `docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py`, в том же коммите; Git blob `5cbd156db9be84caa938cdbabd4e9ec0b5a6d2f3`. Прочитан как явно названный в S1 источник независимой формулы `W02-WR-Prime`; численная реализация в S3 сама помечена диагностической.
- **P:** `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, `rh_clean`, blob в header; прочитан, включая конец. Управляющая задача — текущая прямая команда владельца, не очередь других батчей.
- **E1:** T. Tao, *254A, Notes 3a: Eigenvalues and sums of Hermitian matrices*, 12 January 2010, §4, equations (18)–(22), и §5 о главных подматрицах. Проверена стандартная матричная формула Адамара. Вся её нужная здесь реализация и кратный случай доказаны ниже; никакая PDE-формула Дирихле не импортирована.
  URL: https://terrytao.wordpress.com/2010/01/12/254a-notes-3a-eigenvalues-and-sums-of-hermitian-matrices/

## 2. Непрерывное окно без подмены формы

### Лемма 1. Фиксированный carrier и точный возврат к исходному расписанию

**[FINITE_CELL | PAPER]** Фиксируем целое `N>=0`. Для `L>0` положим
\[
b=L/2,\quad I_L=[-b,b],\qquad d_0=1,\quad d_j=\sqrt2\ (j\ge1),
\]
\[
e_{j,L}(x)=\frac{d_j}{\sqrt L}
 \cos\!\left(\frac{2\pi j(x+b)}L\right)\mathbf1_{I_L}(x),
\qquad 0\le j\le N.
\tag{2.1}
\]
Это вещественный чётный ортонормированный базис. Он ровно равен чётной компрессии фазированного signed-mode базиса S2: `e0=psi0`, `ej=(psi_j+psi_-j)/sqrt2`.

Для `c in R^(N+1)` обозначим
\[
v_c(y)=\sum_{j=0}^N d_jc_j\cos(2\pi j(y+1/2)),\quad |y|\le1/2,
\]
\[
f_{L,c}(x)=L^{-1/2}v_c(x/L)\mathbf1_{I_L}(x),
\quad \|f_{L,c}\|_2^2=\|c\|_2^2.
\tag{2.2}
\]
Матрица `K_N^E(L)` **определяется ограничением неизменённой полной формы S2** на (2.1). В частности,
\[
K_m^E(\log m)=A_m.
\tag{2.3}
\]
Все будущие L-производные матрицы берутся в этих фиксированных коэффициентных координатах. Физическое f может иметь ненулевые граничные значения; его нулевое продолжение не считается глобально H¹-гладким.

### Лемма 2. Корреляция и её граничный след

**[FINITE_CELL | PAPER]** Для вещественного f положим
\[
Q_f(s)=2\int_{\mathbb R}f(x)f(x+s)dx.
\]
Для (2.2) существует симметричная матрица `mathcal Q_N(r)` на `0<=r<=1`, такая что
\[
Q_{f_{L,c}}(s)=c^T\mathcal Q_N(s/L)c\quad(0\le s\le L),
\quad Q_f(s)=0\quad(s\ge L).
\tag{2.4}
\]
Если `d=(1,sqrt2,...,sqrt2)^T`, то
\[
\boxed{
\mathcal Q_N(0)=2I,\quad \mathcal Q_N(1)=0,\quad
\mathcal Q_N'(1^-)=-2dd^T.
}
\tag{2.5}
\]
Также `mathcal Q_N'(0^+)=-2dd^T`.

**Доказательство.** Замена `x=Ly` даёт
\[
q_c(r):=c^T\mathcal Q_N(r)c
=2\int_{-1/2}^{1/2-r}v_c(y)v_c(y+r)dy.
\]
При `r=0` это `2||c||²`, при `r=1` интервал имеет нулевую длину. Дифференцируя конечный интеграл,
\[
q_c'(r)=2\int_{-1/2}^{1/2-r}v_c(y)v_c'(y+r)dy
-2v_c(1/2-r)v_c(1/2).
\tag{2.6}
\]
На концах `v_c(-1/2)=v_c(1/2)=d^Tc`. При r→1 внутренний интеграл исчезает; при r→0 он равен половине разности одинаковых квадратов на концах и тоже исчезает. Поляризация доказывает (2.5). ∎

Полностью вычислимые элементы получаются чётной компрессией матрицы
\[
q_{ij}^{raw}(r)=
\begin{cases}
2(1-r)\cos(2\pi i r),&i=j,\\
\dfrac{\sin(2\pi j r)-\sin(2\pi i r)}{\pi(i-j)},&i\ne j,
\end{cases}
\quad -N\le i,j\le N.
\tag{2.7}
\]
Это именно корреляционный kernel исходного S3. Таким образом (2.5) — тождество настоящего базиса, не гипотеза о выбранном векторе.

## 3. Полная производная матрицы

Обозначим, как в S2,
\[
j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad
c_*=\gamma+\log(8\pi)+\pi/2,\quad
\omega_n=\frac{\Lambda(n)}{\sqrt n},\quad a_n=\log n,
\]
\[
p(x)=\sqrt2\cosh(x/2),\qquad q(x)=\sqrt2\sinh(x/2).
\]
Здесь `q(x)` — нечётный полюсный профиль, не корреляционная матрица.
Чётность **доказывает** `⟨q,f⟩=0`; этот полюс не отбрасывается на произвольных тестах.

Положим `u_j(L)=⟨p,e_(j,L)⟩`. Прямое интегрирование даёт
\[
u_j(L)=\frac{4\sqrt2\,d_j L^{3/2}\sinh(L/4)}{L^2+16\pi^2j^2},
\]
\[
u_j'(L)=u_j(L)\left[
\frac3{2L}+\frac14\coth(L/4)-\frac{2L}{L^2+16\pi^2j^2}
\right].
\tag{3.1}
\]

### Теорема 3. Исходниковая матричная вариация

**[FINITE_CELL | PAPER]** При `L notin {log n: Lambda(n)>0}`:
\[
\boxed{
\begin{aligned}
(K_N^E)'(L)={}&u'(L)u(L)^T+u(L)u'(L)^T\\
&+\frac1{L^2}\int_0^L s j(s)\mathcal Q_N'(s/L)ds\\
&+\frac1{L^2}\sum_{a_n<L}\omega_n a_n\mathcal Q_N'(a_n/L).
\end{aligned}}
\tag{3.2}
\]
Все `n=p^k` включены. Эквивалентная архимедова строка:
\[
\int_0^1 rj(Lr)\mathcal Q_N'(r)dr.
\tag{3.3}
\]
Матрица `K_N^E` непрерывна и локально Lipschitz на `(0,infinity)`; между prime-power порогами она вещественно-аналитична.

**Доказательство.** Из полной формы S2 и (2.4) точно
\[
\begin{aligned}
K_N^E(L)={}&-c_*I+u(L)u(L)^T\\
&+\int_0^L j(s)[2I-\mathcal Q_N(s/L)]ds
+2I\int_L^\infty j(s)ds\\
&-\sum_{a_n\le L}\omega_n\mathcal Q_N(a_n/L).
\end{aligned}
\tag{3.4}
\]
При каждом конечном L простые вне окна дают ноль **из-за отсутствия перекрытия поддержек**, а не из-за аналитического усечения.

Производная внутреннего аргумента равна
\[
\partial_L\mathcal Q_N(s/L)=-\frac{s}{L^2}\mathcal Q_N'(s/L).
\tag{3.5}
\]
Около s=0 исходная разность `2I-mathcal Q_N(s/L)=O(s)`; для её L-производной множитель `s j(s)` имеет конечный предел `1/2`. Дифференцирование под интегралом допустимо равномерно на компактных L-интервалах.

**Бесконечный архимедов хвост нужен для точной отмены двух концов:**
\[
 j(L)[2I-\mathcal Q_N(1)]-2I j(L)=0.
\tag{3.6}
\]
Нельзя оставлять первый член и забывать второй. Остаётся ровно интегральная строка (3.2). В каждой открытой ячейке конечный набор prime-power атомов фиксирован; дифференцирование каждой строки даёт последнюю сумму. Производная константы `-c_*I` равна нулю, поскольку Gram-матрица остаётся I. Полюс даёт первые две строки произведения u.

Входящий атом имеет `mathcal Q_N(1)=0`, поэтому значения с двух сторон совпадают. Его односторонние производные конечны, что даёт локальную Lipschitz-регулярность. Аналитичность внутри ячейки следует из конечной суммы и устранимого архимедова singularity после подстановки `s=Lr`. ∎

## 4. Нижний уровень: Адамар и физическая граничная форма

### Теорема 4. Простой нижний уровень

**[FINITE_CELL | PAPER]** Пусть нижнее собственное значение `lambda_(N,0)(L)` простое в рассматриваемой точке, не являющейся prime-power порогом. Пусть `c(L)` — его единичный вещественный коэффициентный вектор, `f=f_(L,c(L))`. Тогда
\[
\boxed{
\lambda_{N,0}'(L)=c(L)^T(K_N^E)'(L)c(L).
}
\tag{4.1}
\]
Это требуемое `⟨f,K'(L)f⟩` **после ортонормированного переноса на фиксированный carrier**. У нулевого продолжения f движется граница, поэтому нельзя трактовать K' как неоплаченную обычную производную полного оператора на неподвижном `L²(R)`.

**Доказательство.** Для простого собственного значения можно выбрать локально дифференцируемые c и λ. Дифференцируем `Kc=λc`, умножаем слева на cᵀ и используем `cᵀK=λcᵀ`:
`cᵀK'c+λcᵀc'=λ'+λcᵀc'`. Получаем (4.1). Нормировка и изменение базиса уже включены в (3.2); второго неучтённого члена от движения f нет. Альтернативное доказательство из min–max, не требующее выбора c', содержится в Теореме 6. ∎

### Полная физическая формула

**[FINITE_CELL | PAPER]** В следующей формуле `Q_f'(s)` означает производную по **сдвигу s** при фиксированном физическом f на текущем окне; это не L-производная движущегося eigenvector. Положим
\[
a_f=\langle p,f\rangle,\qquad b_f=\langle xq,f\rangle.
\]
Тогда (4.1)–(3.2) равносильны
\[
\boxed{
\lambda_{N,0}'(L)=
\frac{a_f^2+a_fb_f}{L}
+\frac1L\int_0^L s j(s)Q_f'(s)ds
+\frac1L\sum_{a_n<L}\omega_n a_nQ_f'(a_n).
}
\tag{4.2}
\]

**Проверка полюсной строки.** При замороженных коэффициентах
\[
a_f=\sqrt{2L}\int_{-1/2}^{1/2}v_c(y)\cosh(Ly/2)dy,
\quad \partial_La_f=\frac{a_f+b_f}{2L}.
\tag{4.3}
\]
Поэтому `∂_L(a_f²)=(a_f²+a_fb_f)/L`. В остальных строках
`Q_f'(s)=L^{-1} cᵀmathcal Q_N'(s/L)c`, что даёт все множители L в (4.2).

**Оба края окна внутри точной корреляционной производной.** Для `0<s<L`:
\[
\boxed{
Q_f'(s)=2\int_{-b}^{b-s}f(x)f'_{\rm int}(x+s)dx
-2f(b-s)f(b).
}
\tag{4.4}
\]
Это правило Лейбница с движущимся правым концом. При `s→L^-` граничный множитель становится `f(-b)f(b)`; таким образом второй конец не потерян. Равенство `f(-b)=f(b)` используется только после установления чётности.

Обозначим
\[
A_f(s)=\int_{-b}^{b-s}f(x)f'_{\rm int}(x+s)dx,\qquad F_b=f(b)=f(-b).
\]
Полностью разложенная граничная/архимедова/арифметическая запись:
\[
\boxed{\begin{aligned}
\lambda_{N,0}'(L)
={}&\frac{a_f^2+a_fb_f}{L}\\
&+\frac2L\int_0^L s j(s)A_f(s)ds
-\frac{2F_b}{L}\int_0^L s j(s)f(b-s)ds\\
&+\frac2L\sum_{a_n<L}\omega_na_n A_f(a_n)
-\frac{2F_b}{L}\sum_{a_n<L}\omega_na_n f(b-a_n).
\end{aligned}}
\tag{4.5}
\]
В (4.4)–(4.5) используется **внутренняя** производная конечного тригонометрического полинома. Все суммы конечны на текущем окне и сохраняют полную prime-power историю. Оконный перенос не заменяет её лишь последним атомом.

Для ориентира: формальная L-производная нулевого продолжения имеет дельта-массы на обоих движущихся концах. Отдельно подставлять их в сингулярную Weil-форму было бы необоснованно. Формулы (2.6), (3.6), (4.4) выполняют всю эту операцию над конечными корреляциями и избегают произведений распределений.

**Не чистая Dirichlet-формула.** Здесь не доказано и не используется, что f обращается в ноль на границе или что внутренние строки (4.5) можно удалить. Конечный Fourier-eigenvector решает только сжатое eigen-equation; он не является решением полной непрерывной краевой задачи на всех направлениях. В частности, чисто граничный закон без этих строк потребовал бы нового тождества.

## 5. Что именно скачет при L=log n

### Теорема 5. Prime-power kick при фиксированном N

**[FINITE_CELL | PAPER; literal source.]** Пусть `a=log n`, `n>=2`. Тогда
\[
\boxed{K_N^E(a+)=K_N^E(a-)=K_N^E(a),}
\tag{5.1}
\]
а односторонние матричные производные удовлетворяют
\[
\boxed{
(K_N^E)'_+(a)-(K_N^E)'_-(a)
=-\frac{2\Lambda(n)}{\sqrt n\log n}\,dd^T.
}
\tag{5.2}
\]
При `n=p^k` коэффициент равен `-2/(k p^(k/2))`; при остальных n он нулевой.

**Доказательство.** Все старые атомы, полюс и архимедова часть имеют одинаковую производную с двух сторон. Новая строка энергии равна
`-omega_n 1_(L>=a) mathcal Q_N(a/L)`.
Её значение в a равно нулю. Производная справа в a равна
`(omega_n/a) mathcal Q_N'(1)`, слева ноль. Применяем (2.5). ∎

Если нижний уровень в a прост, его eigenvector c и физический f имеют один и тот же предел с двух сторон с точностью до безразличного знака. Поэтому
\[
\boxed{
\lambda_{N,0}'(a+)-\lambda_{N,0}'(a-)
=-\frac{2\Lambda(n)}{\sqrt n\log n}|d^Tc|^2
=-\frac{2\Lambda(n)}{\sqrt n}|f(a/2)|^2\le0.
}
\tag{5.3}
\]
Это **падение наклона**, а не скачок значения lambda. Даже в простом случае нулевой граничный след может занулить этот скачок. Простота и ненулевой след не утверждаются кофинально.

**Распределительная формулировка для фиксированной матрицы.** Производная (3.2), со ступенчатым набором атомов, является обычной локально ограниченной функцией; дельта-части в первой производной нет. Во второй производной:
\[
\boxed{
\left.\partial_L^2 K_N^E\right|_{\rm atoms}
=-\sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n\log n}\,dd^T\,
\delta_{\log n}.
}
\tag{5.4}
\]
Сумма локально конечна. Для простого eigenbranch аналогичный атом lambda'' имеет коэффициент (5.3). При пересечениях eigenbranches возможны дополнительные изломы; они рассматриваются отдельно ниже.

## 6. Кратность: формула без скрытой гипотезы простоты

### Теорема 6. Односторонние производные нижнего уровня

**[FINITE_CELL | PAPER]** Пусть `L0>0`,
\[
\lambda_0=\lambda_{N,0}(L_0),\qquad
E=\ker(K_N^E(L_0)-\lambda_0 I),
\]
а `Pi` — ортогональная проекция на E. Пусть
`B_+=(K_N^E)'_+(L0)`, `B_-=(K_N^E)'_-(L0)`, где обе производные относятся к одному фиксированному N. Тогда
\[
\boxed{
\lambda_{N,0}'(L_0+)=\lambda_{\min}(\Pi B_+\Pi|_E),
\qquad
\lambda_{N,0}'(L_0-)=\lambda_{\max}(\Pi B_-\Pi|_E).
}
\tag{6.1}
\]
В гладкой точке `B_+=B_-=B`. Обычная производная существует тогда и только тогда, когда `Pi B Pi|_E` — скалярная матрица; тогда каждое единичное c∈E даёт одинаковое `cᵀBc`.

**Доказательство.** Для `h>0` имеем `K(L0+h)=K0+hB_++o(h)` в конечномерной операторной норме. Min–max на единичных векторах E даёт верхнюю оценку `λ0+h λmin(B_+|E)+o(h)`.
Если E не всё пространство, у K0 на E⊥ есть строго положительный **локальный** gap g. Из projected eigen-equation для единичного bottom `c_h=e_h+z_h`, `e_h∈E, z_h∈E⊥`, следует `||z_h||=O(h)`; инверсия на E⊥ легальна при достаточно малом h, потому что `λ(h)→λ0`. Тогда
\[
\lambda(h)=\lambda_0+h\langle e_h,B_+e_h\rangle+o(h),\qquad
\|e_h\|\to1.
\]
Это даёт совпадающую нижнюю оценку. Если E всё пространство, та же оценка немедленна из min–max без инверсии. При h<0 знак h меняет минимум на максимум, что доказывает левую формулу. Никакой равномерный gap по N или L не предполагался. ∎

В prime-power точке подставляется точно
\[
\Pi B_+\Pi|_E
=\Pi B_-\Pi|_E-
\frac{2\Lambda(n)}{\sqrt n\log n}(\Pi d)(\Pi d)^T|_E.
\tag{6.2}
\]
В частности, правая производная не больше левой, но её величину при кратности нельзя вычислять по произвольно выбранному старому ground vector. Контроль `diag(t,-t)` имеет нижний уровень `-|t|`: справа наклон −1, слева +1, хотя в t=0 любой единичный вектор является eigenvector. Это точный общий контртест, не CCM-контрпример.

## 7. Возврат к N=m, L=log m: отдельные скачки размерности

### Теорема 7. Точная склейка исходных ячеек

**[COFINAL_FAMILY | PAPER; interpolation convention stated explicitly.]** Источник сам не задаёт значения между целыми ячейками. Одна естественная правосторонняя интерполяция, совпадающая со всеми исходными данными, есть
\[
\lambda_{\rm diag}(L):=
\lambda_{\lfloor e^L\rfloor,0}(L),\qquad L\ge\log2.
\tag{7.1}
\]
На открытом интервале `(log m,log(m+1))` применяется (4.2) с N=m, либо (6.1) в точке кратности.

При `a_n=log n`, `n>=3`, происходит переход N=n−1→n. Старый блок является главной подматрицей нового в **том же** L=a_n. Новый prime-power атом в самой матрице в этот момент всё ещё равен нулю. Поэтому
\[
\boxed{
\Delta_n^{\rm mode}:=
\lambda_{n,0}(a_n)-\lambda_{n-1,0}(a_n)\le0.
}
\tag{7.2}
\]
Это не атомный kick (5.3). Он может существовать даже при `Lambda(n)=0`, поскольку новая Fourier-мода добавляется при каждом целом n.

Если записать новый блок как
\[
K_n^E(a_n)=\begin{pmatrix}A&v\\v^T&d\end{pmatrix},
\qquad A=K_{n-1}^E(a_n),\quad\ell=\lambda_{\min}(A),
\]
то при строгом падении `z=ell+Delta_n^mode<ell` его точное значение определяется
\[
d-z-v^T(A-zI)^{-1}v=0.
\tag{7.3}
\]
При отсутствии строгого падения `z=ell`; нельзя использовать (7.3) через сингулярный inverse. Эквивалентный guard для отсутствия падения:
`v ⟂ ker(A-ell I)` и `d-ell-vᵀ(A-ell I)^†v >= 0`, где † — псевдообратная на дополнении ядра. Это обычный конечный Schur-guard, не новая исходниковая оценка его знака.

**Доказательство.** Вложение коэффициентных векторов `c↦(c,0)` сохраняет все старые базисные функции и все элементы формы в том же L. Min–max даёт (7.2). При z<ell первая блоковая строка eigen-equation даёт `x=-(A-zI)^(-1)vt`; t≠0, иначе z был бы собственным значением A. Подстановка во вторую строку даёт (7.3). Сингулярный guard следует из положительности сдвинутой блоковой формы и завершения квадрата на E⊥. ∎

**Полный баланс первоначального расписания.** На любом компактном L-интервале внутри `(log2,infinity)` функция (7.1) имеет ограниченную вариацию. Её распределительная первая производная равна
\[
\boxed{
D_L\lambda_{\rm diag}=
\lambda'_{\lfloor e^L\rfloor,0}(L)\,dL
+\sum_{n\ge3}\Delta_n^{\rm mode}\,\delta_{\log n}.
}
\tag{7.4}
\]
Плотность понимается почти всюду; матричные изломы и кратные пересечения уже учтены (6.1). Для `A<B`, с правосторонними значениями на концах,
\[
\lambda_{\rm diag}(B)-\lambda_{\rm diag}(A)
=\int_A^B\lambda'_{\lfloor e^L\rfloor,0}(L)dL
+\sum_{A<\log n\le B}\Delta_n^{\rm mode}.
\tag{7.5}
\]
Таким образом, перенос fixed-N формулы на исходную диагональ **без** (7.2)–(7.5) был бы сменой задачи. Здесь оба механизма сохранены.

## 8. Проверки и их точная сила

До исполнения проверок зарегистрированы P1–P5 в `hadamard_work/predictions.json`:

| Прогноз | Проверка | Результат |
|---|---|---|
| P1: Q(0)=2I, Q(1)=0, Q'(1)=−2ddᵀ | точная алгебра N=0,1,2,3; общее доказательство — Лемма 2 | CONFIRMED |
| P2: полная K' совпадёт с разностной производной независимых raw-элементов | N=2, L=1.25, 60 dps, шаг 10⁻¹² | согласование max-entry 2.528·10⁻²³; FLOATING |
| P3: энергия непрерывна, slope-kick в log4; в log6 атома нет | сравнение обоих наборов атомов в той же матрице | согласование rank-one jump 3.112·10⁻⁶¹; log6 ровно 0 в реализации |
| P4: простой ground подчиняется (4.1); кратность требует guard | eigenvalue finite difference + точный diag(t,−t) | разность slope 5.132·10⁻²⁷; guard PASSED |
| P5: расширение N отдельно от атома | N=2→3 в L=log3, principal submatrix check | principal entries совпали; bottom drop ≈−1.1352·10⁻⁵, FLOATING |

Исполнено **6 групп точных SymPy-проверок** и один небольшой диагностический прогон. Нормировка u', архимедов хвост на постоянной моде и prime-power коэффициент проверены отдельно. Численные результаты не используются как доказательство аналитических формул, cofinal sign, простоты или RH. Это авторская самопроверка, не независимый аудит; ни Lean, ни Arb не запускались.

Независимая raw-матрица в коде использует `W02-WR-Prime` из S3, а аналитическая производная — (3.2), не численное дифференцирование той же функции. Код в приложении полностью воспроизводит проверки. Абсолютные ошибки квадратуры и округления диагностического прогона не сертифицированы.

## 9. Что этот результат закрывает и чего не закрывает

**[ABSTRACT | PAPER; dependency ledger]**

- **CLOSES:** точная derivative-формула для каждого fixed-N чётного блока, full source/body/edge разложение, prime-power kink, кратностные guards, склейка исходного N=m расписания.
- **Не закрыто:** source-derived нижний предел для lambda вдоль исходной диагонали, NOESCAPE, (★), RH. Никакого знака всей правой части (4.5) или ограниченности суммы потерь (7.5) не выведено.
- **DOWNSTREAM_CONSUMER:** возможность использовать геометрическое изменение того же нижнего уровня в RH/NOESCAPE линии.
- **ACTUAL_CONSUMER_REQUIREMENT:** новая количественная source-оценка полной вариации или другой ранее допустимый достаточный интерфейс, а не сама известная матричная формула Адамара.
- **ORIGINAL_REQUESTED_OBJECT:** lambda' с гранично-архимедовой и атомной структурой.
- **ORIGINAL_OBJECT_IS:** точное вычислимое представление, не доказанная необходимость для RH.
- **FAILURE_TYPE / EPISTEMIC_STATUS** для cofinal sign: NO_DERIVATION / RESEARCH_DEBT. Никакой смерти математического маршрута не объявлено.
- **NOVELTY_AXIS:** полный исходниковый Hadamard ledger и различение atom-entry versus mode-entry.
- **DISCRIMINATOR:** Q(1)=0 при ненулевом Q'(1); arbitrary bottom selection в кратном E; обязательный mode-entry jump на исходном расписании.

Два допустимых представления для дальнейшей проверки, без объявления нового доказательства: (a) гранично-корреляционное (4.5), высокая sign-чувствительность, высокая цена исходникового сравнения; (b) конечная матричная производная (3.2) с rank-one kicks (5.2) и Schur-guard (7.3), низкая цена конечной проверки, но cofinal bound всё ещё требует арифметики. Чистую PDE-формулу Дирихле и аргумент «окно растёт, значит finite Fourier-bottom автоматически монотонен» не импортировать: допустимые пространства между окнами не вложены.

**Одна CODEX DIRECTIVE:** независимо проверить (3.2), (4.5), (5.2)–(5.3), кратностные min/max в (6.1) и различение распределительных (5.4)/(7.4), сверяя непосредственно S2 (1.4) и S3 raw entries на указанном коммите. Прогнать Appendix A; ни finite replay, ни знак атомного kick не считать кофинальной нижней границей. Проверка не должна менять `rh_clean`, Lean или route-state.

META CLOSEOUT: предыдущий второй момент не объявлен опровергнутым; новая запрошенная вариационная формула получена. Исправлены два потенциальных ошибочных усиления — value-jump от входящего атома и single-vector derivative при кратности. Предсказания P1–P5 проверены в указанных scope. Следующий математический пробел — знак/суммируемость **полного** баланса, а не отсутствие формулы для K'.

## Appendix A. Исполняемые проверки

Команды (имя `.py` — файл приложения; `hadamard_probe.json` — выбираемый путь вывода):

```bash
uv run --with sympy PROSHKA_HADAMARD_CHECKS_2026-11-02.py
uv run --with sympy --with mpmath PROSHKA_HADAMARD_CHECKS_2026-11-02.py \
  --diagnostic --output hadamard_probe.json
```

Следующий блок побайтно совпадает с приложенным `.py`.

```python
#!/usr/bin/env python3
"""CCM window-variation checks. Exact algebra plus OPTIONAL floating diagnosis.

  uv run --with sympy PROSHKA_HADAMARD_CHECKS_2026-11-02.py
  uv run --with sympy --with mpmath PROSHKA_HADAMARD_CHECKS_2026-11-02.py --diagnostic

--output names the JSON diagnostic file (default hadamard_probe.json).
No finite computation establishes a cofinal spectral sign, RH or simplicity.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def exact_checks() -> None:
    import sympy as s
    r = s.symbols('r', real=True)
    L, a = s.symbols('L a', positive=True)
    Q = s.Function('Q')
    assert s.simplify(s.diff(Q(a/L), L) + a/L**2 * s.Subs(s.diff(Q(r),r),r,a/L)) == 0
    print('PASS chain rule at frozen coefficient vector')

    def raw(i: int, j: int):
        if i == j:
            return 2*(1-r)*s.cos(2*s.pi*i*r)
        return (s.sin(2*s.pi*j*r)-s.sin(2*s.pi*i*r))/(s.pi*(i-j))
    for N in range(4):
        modes = list(range(-N,N+1))
        U = s.zeros(2*N+1,N+1); U[N,0] = 1
        for j in range(1,N+1):
            U[N-j,j]=U[N+j,j]=1/s.sqrt(2)
        R = s.Matrix([[raw(i,j) for j in modes] for i in modes])
        E = s.simplify(U.T*R*U)
        d = s.Matrix([1]+[s.sqrt(2)]*N)
        assert E.subs(r,0) == 2*s.eye(N+1)
        assert E.subs(r,1) == s.zeros(N+1)
        assert s.simplify(s.diff(E,r).subs(r,1)+2*d*d.T)==s.zeros(N+1)
        assert s.simplify(s.diff(E,r).subs(r,0)+2*d*d.T)==s.zeros(N+1)
    print('PASS full even correlation, both endpoints, rank-one slope for N=0..3')

    for j in range(4):
        dj = 1 if j == 0 else s.sqrt(2)
        u = 4*s.sqrt(2)*dj*L**s.Rational(3,2)*s.sinh(L/4)/(L**2+16*s.pi**2*j*j)
        beta = 3/(2*L)+s.coth(L/4)/4-2*L/(L**2+16*s.pi**2*j*j)
        assert s.simplify(s.diff(u,L)-u*beta)==0
    print('PASS pole-vector derivative including normalization and endpoint transport')

    jfun=s.Function('j')
    arch=2/L*s.Integral(a*jfun(a),(a,0,L))+2*s.Integral(jfun(a),(a,L,s.oo))
    expected=-2/L**2*s.Integral(a*jfun(a),(a,0,L))
    assert s.simplify(s.diff(arch,L)-expected)==0
    print('PASS constant mode: finite arch endpoint cancels infinite arch tail endpoint')

    k=s.symbols('k',integer=True,positive=True)
    p=s.symbols('p',positive=True)
    assert s.simplify(2*s.log(p)/(p**(k/2)*(k*s.log(p)))-2/(k*p**(k/2)))==0
    print('PASS prime-power coefficient 2/(k p^(k/2))')

    B=s.diag(1,-1)
    assert min(B.eigenvals())==-1 and max(B.eigenvals())==1
    A=s.Matrix([[1,1],[1,1]])
    assert min(A.eigenvals())==0 < 1
    print('PASS degenerate slope guard and independent rank-enlargement control')
    print('ALL 6 EXACT GROUPS PASSED')


def diagnostic(output: Path) -> None:
    import mpmath as mp
    mp.mp.dps=60
    pi=mp.pi
    def vm(n: int):
        if n<2: return mp.mpf(0)
        for p in range(2,n+1):
            if n%p==0:
                x=n
                while x%p==0: x//=p
                return mp.log(p) if x==1 else mp.mpf(0)
        raise AssertionError('unreachable')
    def compress(A,N):
        U=mp.zeros(2*N+1,N+1); U[N,0]=1
        for j in range(1,N+1): U[N-j,j]=U[N+j,j]=1/mp.sqrt(2)
        return U.T*A*U
    def raw_q(r,i,j):
        if i==j: return 2*(1-r)*mp.cos(2*pi*i*r)
        return (mp.sin(2*pi*j*r)-mp.sin(2*pi*i*r))/(pi*(i-j))
    def raw_dq(r,i,j):
        if i==j:
            return -2*mp.cos(2*pi*i*r)-4*pi*i*(1-r)*mp.sin(2*pi*i*r)
        return 2*(j*mp.cos(2*pi*j*r)-i*mp.cos(2*pi*i*r))/(i-j)
    # Independent raw-source entry implementation: W02 - WR - full prime sum.
    def Kraw(N,L,cap=None):
        if cap is None: cap=int(mp.floor(mp.exp(L)))
        modes=list(range(-N,N+1)); out=mp.zeros(2*N+1)
        grid=[L*i/8 for i in range(9)]
        moments={0:mp.mpf(0)}; diagonal={}
        for n in range(N+1):
            om=2*pi*n/L
            if n:
                val=mp.quad(lambda x: om/2 if not x else mp.exp(x/2)*mp.sin(om*x)/(2*mp.sinh(x)),grid)
                moments[n]=val; moments[-n]=-val
            def integrand(x):
                if not x: return mp.mpf('.5')-1/L
                e=mp.exp(x/2)
                return (mp.expm1(x/2)-e*x/L-2*e*(1-x/L)*mp.sin(om*x/2)**2)/mp.sinh(x)
            diagonal[n]=mp.quad(integrand,grid)
        const=mp.euler+mp.log(4*pi*mp.tanh(L/2))
        atoms=[(n,vm(n)/mp.sqrt(n)) for n in range(2,cap+1) if vm(n)]
        for i,n in enumerate(modes):
            for j,k in enumerate(modes):
                pole=32*L*mp.sinh(L/4)**2*(L**2-16*pi**2*n*k)/((L**2+16*pi**2*n*n)*(L**2+16*pi**2*k*k))
                arch=const+diagonal[abs(n)] if n==k else (moments[k]-moments[n])/(pi*(n-k))
                prime=mp.fsum(c*raw_q(mp.log(nn)/L,n,k) for nn,c in atoms)
                out[i,j]=pole-arch-prime
        return compress(out,N)
    # Direct derived derivative, not differentiating Kraw numerically.
    def Kprime(N,L,cap=None):
        if cap is None: cap=int(mp.floor(mp.exp(L)))
        modes=list(range(-N,N+1)); out=mp.zeros(2*N+1)
        def integrand(r,i,j):
            if not r: return raw_dq(0,i,j)/(2*L)
            return r*mp.exp(-L*r/2)/(-mp.expm1(-2*L*r))*raw_dq(r,i,j)
        atoms=[(n,vm(n)/mp.sqrt(n)) for n in range(2,cap+1) if vm(n)]
        for ii,i in enumerate(modes):
            for jj,j in enumerate(modes):
                out[ii,jj]=mp.quad(lambda r:integrand(r,i,j),[mp.mpf(k)/8 for k in range(9)])
                out[ii,jj]+=mp.fsum(c*mp.log(n)/L**2*raw_dq(mp.log(n)/L,i,j) for n,c in atoms)
        out=compress(out,N)
        u=mp.matrix([4*mp.sqrt(2)*(1 if j==0 else mp.sqrt(2))*L**mp.mpf('1.5')*mp.sinh(L/4)/(L**2+16*pi*pi*j*j) for j in range(N+1)])
        du=mp.matrix([u[j]*(3/(2*L)+mp.coth(L/4)/4-2*L/(L**2+16*pi*pi*j*j)) for j in range(N+1)])
        return out+du*u.T+u*du.T
    def maxentry(A): return max(abs(x) for x in A)
    N=2; L=mp.mpf('1.25'); eps=mp.mpf('1e-12')
    A=Kraw(N,L); D=Kprime(N,L)
    Ap=Kraw(N,L+eps); Am=Kraw(N,L-eps)
    fd=(Ap-Am)/(2*eps)
    ev,V=mp.eigsy(A); c=V[:,0]
    predicted=(c.T*D*c)[0]
    slope=(mp.eigsy(Ap,eigvals_only=True)[0]-mp.eigsy(Am,eigvals_only=True)[0])/(2*eps)
    d=mp.matrix([1]+[mp.sqrt(2)]*N)
    a4=mp.log(4)
    continuity=maxentry(Kraw(N,a4,4)-Kraw(N,a4,3))
    jump=Kprime(N,a4,4)-Kprime(N,a4,3)
    jump_ref=-2*vm(4)/(mp.sqrt(4)*a4)*d*d.T
    ev4,V4=mp.eigsy(Kraw(N,a4,4)); c4=V4[:,0]
    jump_slope=(c4.T*jump*c4)[0]
    trace_ref=-2*vm(4)/(mp.sqrt(4)*a4)*(d.T*c4)[0]**2
    a6=mp.log(6)
    no_atom=maxentry(Kprime(N,a6,6)-Kprime(N,a6,5))
    a3=mp.log(3)
    old=Kraw(2,a3,3); new=Kraw(3,a3,3)
    principal=maxentry(new[:3,:3]-old)
    modejump=mp.eigsy(new,eigvals_only=True)[0]-mp.eigsy(old,eigvals_only=True)[0]
    vals={
       'matrix_derivative_max_error':maxentry(fd-D),
       'simple_ground_gap':ev[1]-ev[0],
       'ground_derivative_hadamard':predicted,
       'ground_derivative_finite_difference':slope,
       'ground_derivative_error':abs(slope-predicted),
       'at_log4_matrix_continuity_error':continuity,
       'at_log4_derivative_jump_max_error':maxentry(jump-jump_ref),
       'at_log4_simple_ground_gap':ev4[1]-ev4[0],
       'at_log4_ground_slope_jump':jump_slope,
       'at_log4_ground_slope_trace_error':abs(jump_slope-trace_ref),
       'at_log6_non_prime_power_jump_error':no_atom,
       'at_log3_rank_extension_principal_error':principal,
       'at_log3_rank_extension_ground_jump':modejump
    }
    assert vals['matrix_derivative_max_error']<mp.mpf('1e-20')
    assert vals['ground_derivative_error']<mp.mpf('1e-20')
    assert continuity<mp.mpf('1e-50')
    assert vals['at_log4_derivative_jump_max_error']<mp.mpf('1e-50')
    assert no_atom<mp.mpf('1e-50') and principal<mp.mpf('1e-50')
    assert modejump<=mp.mpf('1e-50')
    result={'status':'FLOATING_DIAGNOSTIC_NOT_CERTIFICATE','dps':mp.mp.dps,'fixed_N':N,
      'regular_L':'1.25','finite_difference_step':'1e-12',
      'values':{k:mp.nstr(v,30) for k,v in vals.items()}}
    output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,ensure_ascii=False,indent=2))


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--diagnostic',action='store_true')
    ap.add_argument('--output',type=Path,default=Path('hadamard_probe.json'))
    args=ap.parse_args()
    exact_checks()
    if args.diagnostic: diagnostic(args.output)


if __name__=='__main__': main()
```

Script SHA-256: `3ffdfe2712c5a7ced4f0fca08133e911357d94ba90dd567b2571d7d071736b26`.

## Appendix B. Фактический диагностический вывод

```json
{
  "status": "FLOATING_DIAGNOSTIC_NOT_CERTIFICATE",
  "dps": 60,
  "fixed_N": 2,
  "regular_L": "1.25",
  "finite_difference_step": "1e-12",
  "values": {
    "matrix_derivative_max_error": "2.52798723708140332755339830991e-23",
    "simple_ground_gap": "0.00656044463560579375429020201471",
    "ground_derivative_hadamard": "0.0000125902948544199307782224686687",
    "ground_derivative_finite_difference": "0.0000125902948544199307782173375933",
    "ground_derivative_error": "5.13107542422049989623471370866e-27",
    "at_log4_matrix_continuity_error": "3.88938454866321356696504003361e-62",
    "at_log4_derivative_jump_max_error": "3.11150763893057085357203202689e-61",
    "at_log4_simple_ground_gap": "0.00159617784597424509620809685791",
    "at_log4_ground_slope_jump": "-0.0000053827860852587064865768108231",
    "at_log4_ground_slope_trace_error": "9.03894963178557442520412273192e-62",
    "at_log6_non_prime_power_jump_error": "0.0",
    "at_log3_rank_extension_principal_error": "0.0",
    "at_log3_rank_extension_ground_jump": "-0.0000113520864944380181459048415757"
  }
}
```
