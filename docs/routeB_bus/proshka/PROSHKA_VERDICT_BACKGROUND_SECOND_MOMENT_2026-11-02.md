# STATUS: TRY_BACKGROUND_SECOND_MOMENT_SOURCE_CANCELLATION
```yaml
OPERATIVE_CLASS: TRY_BACKGROUND_SECOND_MOMENT_SOURCE_CANCELLATION
REQUEST: DIRECT_OWNER_PROVE_STAR_2026_11_02
SOURCE_REPO: Malaeu/chen_q3
SOURCE_BRANCH: proshka_inbox_2026-10-31
SOURCE_COMMIT: 290c5dee3199c9e273a3c97bae14c56335f32890
SOURCE_FILE: docs/routeB_bus/proshka/PROSHKA_NEXT_STEP_BACKGROUND_SECOND_MOMENT_2026-11-01.md
SOURCE_SHA256: 812106f5b16f2c2d0a4d65c1d86a32a749dcef127d2243e92e6dded2129a3006
SOURCE_GIT_BLOB: e7f2b07e9922bcc6680ebbaa3b4a14a6b22ba266
SOURCE_HASH_CHECK: MATCH
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
STAR_UNCONDITIONALLY_PROVED: false
RH_PROVED: false
STAR_IMPLIES_RH: INHERITED_CODEX_CONFIRMED_THEOREM_6
RH_IMPLIES_STAR: PROVED_HERE_CONDITIONALLY_ON_RH_AND_EXPLICIT_FORMULA
RH_CASE: ALL_M_LARGE_AND_CONVERGENT_SECOND_MOMENT
NOT_RH_CASE: SECOND_MOMENT_DIVERGES_BY_INHERITED_THEOREM_6
SOURCE_SQUARED_NORM_IDENTITY: PROVED_HERE
UNCONDITIONAL_LOCAL_CONVERGENCE: PROVED_HERE
CHEBYSHEV_ERROR_TO_MOMENT_POWER_LOSS: PROVED_HERE
PRIME_PRIME_DIAGONAL: LOG_M_SQUARED_ASYMPTOTIC_USING_CLASSICAL_PNT
UNIFORM_JOINT_ARITHMETIC_CANCELLATION: NOT_PROVED
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 3
VERIFIER: PAPER
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
REPOSITORY_WRITTEN: false
PX_RH_CLAIM: NOT_MADE
```

## 0. Вердикт и предел доказанного

**Запрошенное безусловное (★) НЕ ДОКАЗАНО.** Если его доказать для буквальной меры фон Мангольдта, получим RH через объявленную владельцем отдельно проверенной Кодексом теорему 6 (`NEGATIVE_LEAKAGE`, (6.1)–(6.6)). Нельзя использовать RH для безусловного вывода (★).

Выполнены две полноценные самостоятельные аналитические проверки и один негативный арифметический тест:

1. При RH (★) выполнено **даже при всех поздних M**, и второй момент имеет конечный предел. Доказательство не предполагает простоту/разделённость нулей и оплачивает все частоты.
2. Без RH полный источник в (†) есть квадрат нормы одной **арифметической волны**; локально эта волна сходится с явной скоростью `O_R(1/log M)` без предположений о нулях. Однако её глобальная внешняя масса не оплачена.
3. Абсолютный Chebyshev/PNT-бюджет даёт степенной рост. Кроме того, одна только простая диагональ в (†) растёт как `Q_h(0) (log M)^2/12`; нужная отмена обязана быть совместной, включая off-diagonal, prime–continuum и continuum–continuum.

Это **не** новое доказательство RH, не самостоятельное закрытие её арифметического критерия и не результат вычислительного сканирования.

## 1. Source lock и настройки

Использован байтовый файл по закреплённому пути на коммите `290c5dee`; его SHA-256 проверен как `812106f5b16f2c2d0a4d65c1d86a32a749dcef127d2243e92e6dded2129a3006`. GitHub connector возвращает blob `e7f2b07e9922bcc6680ebbaa3b4a14a6b22ba266`. Прочитан `PROSHKA_SYSTEM_PROMPT_v2.md` на `rh_clean` (blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`). Обязательный consumer — RH, причём проверку `NEGATIVE_LEAKAGE` Theorem 6 пользователь сообщает как `CONFIRMED`; здесь её независимое повторное доказательство **не** заявляется.

**[FINITE_CELL | PAPER]** Для целого `M>=3` фиксируем
\[
\ell=\log M,\quad L_+=\log(2M),\quad L_m=\log m,\quad
q_M(s)=\frac1{M+1}\sum_{m=M}^{2M}(1-s/L_m)_+,
\quad s_0=\log2.
\tag{1.1}
\]
При каждом слагаемом исходный carrier сохраняет **`N=m`, `L=log m`**. Здесь только вспомогательное неотрицательное усреднение символов; исходные матрицы не изменены.

\[
H(t)=\widehat h(t)=4\xi(\tfrac12-it),\quad
p_h(t)=\frac{|H(t)|^2}{2\pi},\quad
G_h=\int_{\mathbb R}w(t)p_h(t)dt>0,
\tag{1.2}
\]
\[
d\nu(s)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}(ds)
-e^{s/2}ds,\qquad
\overline B_M(t)=2\int_{(s_0,\infty)}q_M(s)\cos(ts)d\nu(s),
\tag{1.3}
\]
\[
\boxed{\mathcal V_M=\frac1{G_h}\int_{\mathbb R}p_h(t)\overline B_M(t)^2dt.}
\tag{1.4}
\]
Здесь квадрат действительный, так как `B` вещественна. Все `n=p^k` остаются в сумме; атом `n=2` находится в фиксированной **near**-части, а не в дальней. Атом `n=m` имеет нулевой треугольный коэффициент в каждом исходном `m`.

Требуется неограниченная последовательность `M_j` и **одна** константа `C_2` с `V_(M_j)<=C_2`. Внешние условные оценки `psi(x)-x=O(x^(theta+epsilon))` используются ниже **только как диагностика**, не как доказанный вход. Нулевая сторона при RH используется только в направлении **RH⇒(★)**.

## 2. Точная физическая форма двойной корреляции

### Лемма 1. (†) — квадрат одной полной signed-source волны

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]** Введём сдвиги `T_s h(x)=h(x+s)` и физическую функцию
\[
 b_M(x)=\int_{(s_0,\infty)}q_M(s)
      [h(x+s)+h(x-s)]\,d\nu(s).
 \tag{2.1}
\]
Для каждого конечного M это корректный Bochner-интеграл в `L²(R)` (мера ограничена на компактном носителе `q_M`). Тогда
\[
\boxed{G_h\mathcal V_M=\|b_M\|_2^2.}
\tag{2.2}
\]
И, при `Q_h(v)=2\int h(x)h(x+v)dx`, раскрытие квадрата даёт **именно**
\[
\boxed{
G_h\mathcal V_M=
\iint q_M(s)q_M(u)[Q_h(s-u)+Q_h(s+u)]d\nu(s)d\nu(u).
}
\tag{2.3}
\]

**Доказательство.** При Fourier-конвенции `\hat f(t)=\int f(x)e^{-itx}dx` имеем
`\widehat{T_s h}(t)=e^{its}H(t)` и, следовательно,
`\widehat b_M(t)=H(t)\overline B_M(t)`. Plancherel даёт (2.2). Для (2.3) используем, с сохранением обоих сдвигов,
\[
\langle T_s h+T_{-s}h,T_u h+T_{-u}h\rangle
 =Q_h(s-u)+Q_h(s+u).
\]
Финитность полной вариации `q_M dnu` обеспечивает Fubini. Это также независимо проверяет фактор `2` между `Q_h` и косинусным ядром. ∎

**Структура сохранена:** source, все proper powers, continuum, signed prime–continuum terms, геометрия сдвигов и физическая нормировка. **Не доказано** ограничение нормы `b_M`.

### Лемма 2. Истинная цена элементарного Chebyshev-бюджета

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER, conditional arithmetic hypothesis used only where explicitly indicated.]** Обозначим
\[
E(s)=\psi(e^s)-e^s,\qquad \psi(x)=\sum_{n\le x}\Lambda(n).
\]
Как мера Стилтьеса, точно
\[
\boxed{d\nu(s)=e^{-s/2}\,dE(s).}
\tag{2.4}
\]
Положим `f_s=T_s h+T_{-s}h`, `g_M(s)=q_M(s)e^{-s/2}f_s`. Поскольку `q_M(L_+)=0`, интегрирование по частям на `(s0,L_+]` даёт **полную** формулу
\[
\boxed{
 b_M=-E(s_0)g_M(s_0)-\int_{s_0}^{L_+}E(s)g_M'(s)ds,
}
\tag{2.5}
\]
включая граничный вклад при `s0`; у верхнего конца остаток равен нулю. Производная вычисляется точно:
\[
g_M'(s)=e^{-s/2}\left[(q'_M(s)-\tfrac12q_M(s))f_s
 +q_M(s)(T_s h'-T_{-s}h')\right].
\tag{2.6}
\]
Здесь `q'_M` берётся почти всюду; скачки производной не создают атомов у непрерывной `q_M`.

Для `s0<=s<=L_+` верны
\[
0\le q_M(s)\le\frac{(L_+-s)_+}{\ell},\qquad
|q'_M(s)|\le\frac1\ell\quad\text{a.e.}
\tag{2.7}
\]
Пусть **условно** `|E(s)|<=C_\vartheta e^{\vartheta s}` с фиксированным `\vartheta>1/2` (в частности `\vartheta=11/12+epsilon`). При `a=\vartheta-1/2>0`:
\[
\int_{s_0}^{L_+}e^{as}|q'_M(s)|ds
\le\frac{e^{aL_+}}{a\ell},\qquad
\int_{s_0}^{L_+}e^{as}q_M(s)ds
\le\frac{e^{aL_+}}{a^2\ell}.
\tag{2.8}
\]
Поскольку `||f_s||₂<=2||h||₂`, `||f_s'||₂<=2||h'||₂`, (2.5)–(2.8) дают
\[
\boxed{
 \|b_M\|_2\le2e^{-s_0/2}|E(s_0)|\|h\|_2
 +2C_\vartheta\frac{e^{aL_+}}\ell
  \left(\frac{\|h\|_2}{a}
  +\frac{\|h\|_2+2\|h'\|_2}{2a^2}\right)
}
\tag{2.9}
\]
(безвредная дополнительная постоянная допускается при другом выборе конвенции на `s0`). Поэтому
\[
\boxed{
 \mathcal V_M\ll_{h,s_0,\vartheta}
 1+\frac{M^{2\vartheta-1}}{(\log M)^2}.
}
\tag{2.10}
\]
Подставляя условный `\vartheta=11/12+epsilon`:
\[
\boxed{\mathcal V_M\ll_\epsilon 1+\frac{M^{5/6+2\epsilon}}{(\log M)^2}.}
\tag{2.11}
\]
Безусловная элементарная граница `psi(x)<<x` даёт тот же метод с `\vartheta=1`, то есть только `V_M<<1+M/(log M)^2`.

**Что здесь не оплачено:** (2.9) использует **модуль ошибки `E` до интегрирования**; запрещённая потеря происходит в первой же норме правой части (2.5). Ни `11/12`, ни PNT, ни одно лишь `\psi(x)-x<<x^(1/2)log^A x` не дают отсюда равномерной `C_2`. Это ограничение конкретной абсолютной попытки, **не** нижняя граница действительного `V_M`.

## 3. Где локальная часть уже доказана без RH

### Лемма 3. Локальная сильная сходимость с точной скоростью

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER; literal source.]** Для каждого фиксированного `R>0` определим
\[
 b_\infty(x)=\int_{(s_0,\infty)}[h(x+s)+h(x-s)]d\nu(s),
\tag{3.1}
\]
абсолютно на каждом конечном физическом интервале. Тогда
\[
\boxed{\|\mathbf1_{[-R,R]}(b_M-b_\infty)\|_2
\le\frac{C_R}{\log M},}
\tag{3.2}
\]
где
\[
C_R=\int_{(s_0,\infty)}s\|
 \mathbf1_{[-R,R]}(T_s h+T_{-s}h)\|_2d|\nu|(s)<\infty.
\tag{3.3}
\]
**Доказательство.** Физическая theta-функция и все фиксированные производные убывают быстрее любого экспоненциального множителя на обеих полуосях. Поэтому для фиксированного R корреляция с его компактом в (3.3) убывает быстрее `e^{-As}` при любом `A`; при `A>1/2` это интегрируемо и против полного prime-power хвоста, и против `e^{s/2}ds`.

Для `s<=ell` все индикаторы в q активны, так что `1-q_M(s)=\beta_Ms` с `\beta_M=\sum a_m/L_m<=1/ell`. При `s>ell` неравенство `0<=1-q_M(s)<=1<=s/ell` также верно. Значит **для всех** `s>=s0`, `|1-q_M(s)|<=s/ell`. Неравенство Минковского для абсолютного интеграла даёт (3.2). Ни RH, ни условная quasi-RH здесь не используются. ∎

**[ABSTRACT | PAPER; inherited radical identity.]** Более того, полная theta-радикальность `k(h,g)=0`, вместе с точной полной Weil-формой, даёт в смысле распределений
\[
\boxed{
 b_\infty=c_0h+\mathcal A_+h-b_{\rm near},
}
\tag{3.4}
\]
\[
 \mathcal A_+h=\int_0^\infty j_+(s)
 [2h-T_sh-T_{-s}h]ds,
\quad
 b_{\rm near}=\int_{(0,s_0]}(T_sh+T_{-s}h)d\nu(s).
\]
Это `L²`-функция: `h` и `b_near` в `L²`, а `\mathcal A_+h` корректна в `L²` по `||2h-T_sh-T_-sh||<=s²||h''||` для `s<=1` и `<=4||h||` для `s>=1`. Её Fourier-образ
\[
 \widehat b_\infty(t)=H(t)A_{s_0}(t),
\quad A_{s_0}(t)=a_+(t)+c_0-\Phi_{\rm near}(t),
\quad a_+=w-1,
\tag{3.5}
\]
\[
\Phi_{\rm near}(t)=2\int_{(0,s_0]}\cos(ts)d\nu(s).
\]
Таким образом, **локальная часть `b_M` уже удержана** без RH. Неизвестный вклад в (★) — глобальная масса, которая может уйти в движущуюся физическую область `|x|\sim log M`.

Для любого фиксированного R эквивалентно требовать в (★) верхний контроль
\[
\sup_j\|\mathbf1_{|x|>R}b_{M_j}\|_2<\infty,
\tag{3.6}
\]
поскольку (3.2) даёт равномерную ограниченность внутренней части. Формула (3.6) — **альтернативный объект, не новая доказанная оценка**.

## 4. Критическая положительная диагональ: обязательная цена компенсации

### Лемма 4. Диагональ prime×prime уже растёт как `(log M)^2`

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER; CLASSICAL PNT spent.]** В (2.3) выделим точную диагональ `n=k` из `\nu_p\otimes\nu_p`:
\[
D_M=\sum_{\substack{n\ge2\\s_0<\log n\le L_+}}
 \frac{\Lambda(n)^2}{n}q_M(\log n)^2
 [Q_h(0)+Q_h(2\log n)].
\tag{4.1}
\]
Тогда
\[
\boxed{D_M=\frac{Q_h(0)}{12}(\log M)^2+o((\log M)^2).}
\tag{4.2}
\]
**Доказательство.** Для `s<=ell`, `q_M(s)=1-\beta_Ms`, где `\beta_M=1/ell+O(ell^{-2})`, так как `L_m in[ell,ell+log2]`. По классической PNT и суммированию по частям,
\[
\sum_{p\le M}\frac{(\log p)^2}{p}
 \left(1-\frac{\log p}{\ell}\right)^2
=\ell^2\int_0^1u(1-u)^2du+o(\ell^2)
=\frac{\ell^2}{12}+o(\ell^2).
\tag{4.3}
\]
Изменение `1-s/ell` на `1-beta_M s` даёт `O(ell)`; вклад `M<n<=2M` оценивается `q_M=O(1/ell)` и суммой `\sum (\log n)^2/n`, что даёт `O(1)`. Вклад proper powers `n=p^k,k>=2` ограничен абсолютно, поскольку `\sum_{p,k>=2}(\log p)^2/p^k<infty`. Наконец `Q_h(2log n)` убывает быстрее любой обратной степени n и вносит `O(1)` в (4.1). Получаем (4.2). Здесь `Q_h(0)=2||h||²>0`. ∎

**Сильнейшая проверка против наивного доказательства:** даже если диагональ считать «ошибкой» и оценивать только положительные части, уже получается неограниченная стоимость `~(log M)^2`. При RH весь (2.3) ограничен (теорема 5 ниже), так что настоящая компенсация должна оплачивать диагональ **совместно** с двумя смешанными prime–continuum вкладами, continuum-square и остальными prime-pair terms. Поскольку h положительна на R, ядро `Q_h(s-u)+Q_h(s+u)` неотрицательно для вещественных s,u; это подчёркивает необходимость реального источникового отрицательного cross-term, а не удаления знака.

## 5. Проверка силы цели: при RH (★) даже сходится

### Теорема 5. RH ⇒ конечный предел второго момента, без предположений о расстояниях между нулями

**THIS STEP IS PROVED HERE under the explicit hypothesis RH. [COFINAL_FAMILY | CONDITIONAL/PAPER.]** Пусть `a_{M,m}` — любые неотрицательные веса суммы 1 с минимальным `L_m->infty` (включая (1.1)). Тогда
\[
\boxed{
\mathcal V_M\longrightarrow
V_\infty:=\frac1{G_h}\int_{\mathbb R}p_h(t)A_{s_0}(t)^2dt<\infty
\qquad\text{ПРИ RH}.}
\tag{5.1}
\]
Итак, RH действительно достаточна для (★); оно **не является ложным усилением** RH.

**Доказательство.** Из точной явной формулы для оконного комплексного теста и положительного Fejér-усреднения получаем, как в `NEGATIVE_LEAKAGE` (2.2),
\[
 \overline B_M(t)=\sum_m a_{M,m}(a_+*K_{L_m})(t)+c_0
 -N_M^{\rm near}(t)-\sum_{H(\gamma)=0}\overline\kappa_M(t-\gamma),
\tag{5.2}
\]
при RH все `\gamma` вещественны, с кратностями,
\[
K_L(u)=\frac{L}{2\pi}\operatorname{sinc}^2(Lu/2),\quad
\kappa_L(u)=2\pi K_L(u)=\frac{2(1-\cos Lu)}{Lu^2},\quad
\overline\kappa_M=\sum_m a_{M,m}\kappa_{L_m}.
\tag{5.3}
\]
При `u=0` берём предел `\kappa_L(0)=L`. В (5.2) сохранена короткая часть
`N_M^near(t)=2\int_{(0,s_0]}q_M(s)cos(ts)dnu(s)`.

Без RH `H` — целая вещественная функция; её Fourier-представление из theta даёт для некоторого фиксированного `c>0`
\[
 |H(t)|+|H'(t)|\le C_he^{-c|t|}\quad(t\in\mathbb R).
\tag{5.4}
\]
По Riemann–von Mangoldt с кратностями,
\[
\#\{\gamma: |\gamma-t|\le1\}\le C_z\log(3+|t|),
\quad
\sum_{|\gamma-t|>1}\frac1{(t-\gamma)^2}
\le C_z\log(3+|t|).
\tag{5.5}
\]
Вторая граница следует разбиением в единичные кольца и суммой `\sum_{j>=1}\log(3+|t|+j)/j²`. Здесь **нет** предположения о простоте, минимальном расстоянии или отделённости нулей.

Для `u\ne0` и `L>=ell`:
\[
 0\le\kappa_L(u)\le\min\{L,4/(Lu^2)\},
\qquad |u|\kappa_L(u)\le2.
\tag{5.6}
\]
Зафиксируем вещественное t. Если `|t-\gamma|<=1`, то `H(\gamma)=0` и
`|H(t)|<=|t-\gamma|D(t)`, где `D(t)=sup_{|v-t|<=1}|H'(v)|`. Поэтому по (5.6) каждое близкое слагаемое удовлетворяет
\[
 |H(t)|\overline\kappa_M(t-\gamma)\le2D(t).
\]
Для `|t-\gamma|>1` имеем
`\overline\kappa_M(t-\gamma)<=4/[ell(t-\gamma)^2]`. Вместе с (5.5):
\[
\boxed{
 |H(t)|\sum_\gamma\overline\kappa_M(t-\gamma)
\le C\log(3+|t|)\bigl(D(t)+|H(t)|/\ell\bigr).
}
\tag{5.7}
\]
Правая часть принадлежит `L²(R)` с нормой, независимой от M, вследствие (5.4). Для каждого t с `H(t)ne0` сумма в левой части стремится к нулю, так как `\sum_\gamma1/(t-\gamma)^2<infty` и каждый `L_m>=ell->infty`; при `H(t)=0` произведение тождественно нулю. Следовательно по dominated convergence
\[
\boxed{\left\|H\sum_\gamma\overline\kappa_M(\cdot-\gamma)\right\|_2\to0.}
\tag{5.8}
\]

Кроме того, из `a_+(t)=2\int_0^\infty j_+(s)(1-\cos ts)ds` и (5.3),
\[
 \sup_t|(a_+*K_{L_m})(t)-a_+(t)|
 \le\frac2{L_m}\int_0^\infty s j_+(s)ds=O(L_m^{-1}).
\tag{5.9}
\]
Near-мера фиксирована, и при `s<=s0<ell` имеем `q_M(s)=1-\beta_M s`, `beta_M<=ell^-1`, поэтому
`\sup_t|N_M^{near}-\Phi_{near}|=O(ell^-1)`.
Из (5.2), (5.8), (5.9):
\[
 \|H(\overline B_M-A_{s_0})\|_2\to0.
\tag{5.10}
\]
И `H A_(s0) in L²` из (5.4) и `a_+(t)<<log(2+|t|)`. По Plancherel (5.10) даёт (5.1). ∎

**Важный диагностический факт:** при RH у каждого вещественного нуля `\gamma` символ `\overline B_M(\gamma)` содержит отрицательный пик `-\sum_m a_{M,m}L_m<=-ell`, с ограниченными остальными smooth terms. Поэтому равномерная **двухсторонняя** точечная оценка `|B_M|<=Cw` вообще ложна даже в случае RH; вес `p_h` убивает эти нулевые пики. Не заменять (★) на непроверенную absolute sup-оценку.

### Следствие 6. Точная дихотомия второго момента при принятой теореме 6

**[COFINAL_FAMILY | CONDITIONAL на уже аудированном владельцем consumer.]** По подтверждённой владельцем теореме `NEGATIVE_LEAKAGE` §6, ограниченность
\[
 \mathcal N_M(h)=G_h^{-1}\int p_h(-\overline B_M)_+
\]
на любой последовательности поздних положительных средних влечёт RH; при `not RH` величина `N_M(h)->infty` для любой такой семьи. Cauchy–Schwarz даёт
\[
 \mathcal N_M(h)\le\frac{\|h\|_2}{\sqrt{G_h}}\sqrt{\mathcal V_M}.
\tag{5.11}
\]
Поэтому, вместе с теоремой 5:
\[
\boxed{
\begin{cases}
\mathrm{RH}:&\mathcal V_M\to V_\infty<\infty,\\
\neg\mathrm{RH}:&\mathcal V_M\to+\infty,
\end{cases}
\quad\text{и}\quad
 (\star)\Longleftrightarrow\mathrm{RH}.
}
\tag{5.12}
\]
Последняя эквивалентность использует независимый аудит теоремы 6 **как вход, сообщённый владельцем**, а не как самостоятельно выполненную здесь проверку. Никакая из ветвей (5.12) не устанавливает, какая из альтернатив истинна.

## 6. Самоатака, минимальная математическая задолженность и выбор продолжения

**Самая сильная атака 1 (подмена доказательства).** Теорема 5 предполагает RH; она подтверждает лишь, что поставленная цель имеет правильную силу. Подставить (5.2) с вещественными нулями в безусловное доказательство (★) было бы использованием того, что требуется доказать. Вне RH нули `z=\gamma+i\delta` дают complex Fejér terms, где `|\kappa_L(t-z)|` имеет допустимый фактор `e^{|\delta|L}/L`. Их совместный upper без предположения `delta=0` здесь не получен.

**Самая сильная атака 2 (бюджет PNT).** Доказанная (2.10) применяет модуль к `E(s)` в (2.5). Предел постоянной исчезает уже при `theta>1/2`. Улучшать только exponent `11/12` до любого фиксированного `theta>1/2` не закрывает (★). Даже значение `theta=1/2` с логарифмическими потерями в этом absolute подходе недостаточно: integral `q` имеет растущую длину. Нужна совместная signed cancellation.

**Самая сильная атака 3 (диагональ).** Простой diagonal `D_M` растёт как `(log M)^2`, независимо от RH. Из (†) нельзя выкинуть смешанные и непрерывные части, получить неотрицательное слагаемое и на этом объявить upper. При условной RH вся сумма ограничена именно из-за тонкой корреляции.

**MINIMAL MISSING SOURCE INEQUALITY:** не доказано одно из эквивалентных по (2.2) утверждений: `sup_j ||b_(M_j)||₂<infty` либо равномерный верхний предел полного joint quadratic form (2.3) на неограниченном M-подмножестве. Это исходная (★), но (2.5) определяет конкретный непокрытый термин: **знаковую корреляцию полного Hilbert-valued Stieltjes-интеграла `E(s)g'_M(s)` после добавления граничного вектора**. Источник точен, показатель потери (2.11) вычислен.

Два неэквивалентных *исследовательских представления*, не два заявленных доказательства:

| Ветка | Минимальный дискриминатор | Потенциальная kill-power / цена |
|---|---|---|
| Hilbert-valued Stieltjes / physical exterior | Доказать uniform upper для полного `b_M`, начиная с зоны `|x|>R`, тогда как (3.2) уже платит компакт | Решающая / высокая: нужна signed арифметическая оценка, не модуль `E` |
| Prime-pair covariance (2.3) | Контролировать сочетание off-diagonal `p×p`, двух `p×c` и `c×c`, включая положительную диагональ (4.2) | Решающая / очень высокая: двухточечная корреляция до `O(1)` |

**NEXT DISCRIMINATOR:** независимый источник-специфический тест именно совместного остатка в (2.5) или (2.3), который на planted `dnu -> dnu+A b(s)ds` выдает дополнительный `A²`-член, но на буквальной `Lambda(p^k)` использует отдельную арифметическую структуру. Точная величина, которую надо *улучшить*, — правая часть (2.9), а не её переименование.

**Consumer-first ledger.** DOWNSTREAM_CONSUMER: RH через `NEGATIVE_LEAKAGE` Theorem 6 (аудит владельца). ACTUAL_CONSUMER_REQUIREMENT: ограниченная отрицательная h-масса; (★) сильнее и не является необходимым промежуточным интерфейсом. ORIGINAL_REQUESTED_OBJECT: фиксированный second moment (★). ORIGINAL_OBJECT_IS: NOT_NECESSARY. KNOWN_WEAKER_INTERFACES: direct negative-L1 on h. FAILURE_TYPE: NO_DERIVATION для (★); EPISTEMIC_STATUS: RESEARCH_DEBT, не MATHEMATICALLY_DEAD. NOVELTY_AXIS: HILBERT_VALUED_PRIME_CONTINUUM_ERROR_AND_CONDITIONAL_RH_LIMIT. REOPEN_TRIGGER: реально доказанная signed pair-correlation или иной `L²` upper на исходной мере. RH-route не убит.

**Registered predictions / closeout:** P1 из NEXT_STEP (совместимость ★ с RH) CONFIRMED аналитически в §5. P2 (абсолютные раздельные бюджеты теряют компенсацию) CONFIRMED источниковым диагональным ростом и (2.10), но *все* возможные декомпозиции не объявлены бессильными. P3 (null perturbation попадает во второй момент с `A²>0`) уже проверен в NEXT_STEP и здесь использован как adversarial discriminator, не как prime-counterexample. Что стало меньше: RH-case полностью оплачена и local physical part оплачена с rate; самый первый неоплаченный член — signed global Stieltjes variance. Никаких новых аксиом, Lean, Arb или CCM-сканирования.

## 7. Приложение: два алгебраических контроля и источники

Первый контроль: для Gaussian `h(x)=exp(-x²/2)` имеем `p_h(t)=exp(-t²)`, `Q_h(v)=2sqrt(pi)exp(-v²/4)`. Поэтому для конечных атомов `s,u`:
\[
4\int_{\mathbb R}e^{-t²}\cos(ts)\cos(tu)dt
=Q_h(s-u)+Q_h(s+u).
\]
Второй контроль: `int_0^1v(1-v)²dv=1/12`. Оба выполнены символически в SymPy. Это контроль коэффициентов, не подтверждение кофинального upper.

Фактически прочитаны: указанный owner-pinned Markdown на commit `290c5de`; протокол `PROSHKA_SYSTEM_PROMPT_v2.md` из `rh_clean`; формулы `NEGATIVE_LEAKAGE` §§2,6 из текущего project context, как наследуемые вместе с переданным владельцем статусом аудита. Внешние классические поставщики: Riemann–von Mangoldt `N(T)=T/(2pi)log(T/(2pi))-T/(2pi)+O(log T)` и PNT; условно использовано RH **только в §5**. Никакие quasi-RH, удалённые вычисления, theorem-free аксиомы или независимый reviewer не заявлены.

**CODEX DIRECTIVE (read-only, single target):** Проверить независимо (5.2)–(5.10) и (2.5) с точной `s0=log2` конвенцией; затем попытаться получить source-specific signed `L²`-bound для (2.5), сохранив prime–prime diagonal (4.2), оба prime–continuum и continuum-square. Успех — действительная `C_2<infty` с unbounded `M_j`; неуспех — `BACKGROUND_SECOND_MOMENT_FIRST_UNPAID_SIGNED_STIELTJES_PAIRING` с явно указанием потерянной корреляции и масштабом. Запрещены RH как предпосылка, замена `psi-x` на его модуль до спаривания, удаление proper powers и численный finite-to-global скачок.

**META CLOSEOUT:** математический исход `PARTIAL_WITH_PRECISE_REMAINDER`; о доказанной RH не заявлено. Настоящее (★) всё ещё открыто.
