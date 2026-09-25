# STATUS: TRY_GOAL058_SELECTED_FERRERS_COUPLED_DEFECT_SIGN

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SELECTED_FERRERS_COUPLED_DEFECT_SIGN
OUTCOME: OPEN_COUPLED_DEFECT_SIGN
REQUEST_ID: REQ-2026-09-25-COUPLED-DEFECT-SIGN
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_COUPLED_DEFECT_SIGN
SOURCE_COMMIT: 9c4b3dc9a95ffeaa098cbf0c97fe3307d0f7d902
PREDECESSOR: REQ-2026-09-25-NULLPLANE-LEAKAGE-SIGN
PREDECESSOR_SHA256_VERIFIED: df41def262b2f320509e1630f88c1821f63b8c381720d5efc2c20ba5326f1dd7
PREDECESSOR_GIT_BLOB_VERIFIED: 0525db608e3898083a4ffc99c238618ab4676f97
BOOTSTRAP_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
TEST: TEST_SELECTED_FERRERS_COUPLED_DEFECT_SIGN
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
UNIFORM_SOURCE_TAIL_ENCLOSURE: DERIVED_IN_THIS_REVIEW
UNIFORM_COUPLED_ENERGY_ENCLOSURE: DERIVED_IN_THIS_REVIEW
SOURCE_PREFIX_SIGN: NOT_ESTABLISHED
SIGN_SEPARATION: NOT_ESTABLISHED
INTERVAL_ACTUALLY_CONTAINS_ZERO: NOT_ASSERTED
NONPOSITIVE_COFINAL_WITNESS: NOT_ESTABLISHED
EVENTUAL_POSITIVE_LOWER_FUNCTION: NOT_ESTABLISHED
SCHUR_FLOOR: OPEN
SOURCE_FERRERS_SPLICE: 5m_UNCHANGED
AUXILIARY_ESTIMATION_CUTOFF: k_less_than_6m_NOT_A_SOURCE_REPLACEMENT
SOURCE_FAMILY_CHANGED: false
PROLATE_GAP_USED: false
RH_ASSUMED: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 3
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
REPOSITORY_WRITTEN: false
LOCAL_FILE_IO_AND_HASHING: true
DELIVERY_MARKDOWN_CREATED: true
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_COUPLED_DEFECT_SIGN.** Получен один явный равномерный сертификат
\[
\boxed{\mathfrak L_m=T(m)+\mathcal R(m),\qquad -B(m)\le\mathcal R(m)\le B(m)}
\]
из **настоящих Ferrers-коэффициентов** и полной CCM-формы. Однако **ни \(T(m)>B(m)\) на неограниченных выбранных индексах, ни \(T(m)<-B(m)\) на всём хвосте не доказано**. Нельзя объявить ни KILL, ни POSITIVE.

Бесконечный Ferrers-хвост получает явный бюджет одновременно на всех \(|n|\le m\); зависимость исходного \(z_j\) от строки устраняется точным двумерным следом; неоплаченный знак остаётся в явно выписанной **конечной форме четвёртой степени по исходниковым коэффициентам**. Её один конкретный смешанный член раскрыт в (MIX).

**Не утверждаю, что полученный интервал действительно содержит ноль.** Аналитическое сравнение его концов с нулём не установлено; численного вычисления этих концов не было.

## 1. Источник, обозначения и область

**[COFINAL_FAMILY | PAPER]** Сохраняю исходный \(P\),
\[
m=m_j=N_j=J_P+j+2,\quad \lambda=\sqrt m,\quad L=\log m,
\quad s_n=\tfrac12-2\pi i n/L,\quad -m\le n\le m.
\]
Чтобы не смешивать длину окна с искомой энергией, пользовательское \(L_m\) обозначаю \(\mathfrak L_m\). Все \(q_j,z_j,\rho_m,R_m,S_m,T_m\) имеют прежний смысл. В частности,
\[
v_m=T_mR_m+(T_m-I)S_m=f_{\mathbf a_m}-S_m,
\qquad q_j=\sigma_m\mathbf a_m/\rho_m,
\qquad \rho_m=\|\mathbf a_m\|_2.
\]
\(f_x\) означает синтез коэффициентной строки \(x\) в прежнем базисе \(\psi_{n,L}\).

Прочитан приложенный предшественник целиком: **33 136 байт, 503 текстовые строки**. Его SHA-256 вычислен и совпал с запросом; вычисленный Git blob совпал с blob файла, прочитанного через GitHub на нынешнем pin. Формулы (F2), (F5), (Q6), (D1)–(D4), (W1) и предмет §7 сохранены. fileciteturn17file0L2-L2 fileciteturn18file0L2-L2 fileciteturn27file0L2-L2

На том же pin перечитаны трёхчленная рекурсия, нормировка и склейка выбранного типа Ferrers-решения, геометрический tail supplier и полный CCM-источник. Нормировка строки решения:
\[
\sum_{k\ge0}\frac{|a^{(i)}_{m,k}|^2}{4k+1}=1,
\qquad i=0,4.
\]
Склейка находится в \(k=5m-1\); она **не обнуляет** дальнейшие коэффициенты. fileciteturn23file0L2-L2 fileciteturn19file0L2-L2

Новые индексы далее разделены: \(k\) — Ferrers-коэффициент; \(n,n'\) — Fourier-моды; \(r\) — индекс конечной Mellin-суммы; \(\nu\) — целое число в prime-power сумме.

## 2. Равномерное раскрытие (F5), без мономиального взрыва

**[FINITE_CELL | PAPER]** Оставляем буквально (F2):
\[
c_{m,k}=\frac{6\sqrt m(-1)^k}{A_{0,m}A_{4,m}}
\left(a^{(4)}_{m,0}a^{(0)}_{m,k}-a^{(0)}_{m,0}a^{(4)}_{m,k}\right),
\qquad c_{m,0}=0.
\tag{1}
\]
Вместо оценки отдельных мономиальных коэффициентов внутри (F5) определим **сгруппированный неполный момент**
\[
\mathcal M_{m,k}(s)=
\sum_{r=1}^{m}r^{-s}\int_{r/m}^{1}P_{2k}(x)x^{s-1}\,dx.
\tag{2}
\]
На исходной сетке это в точности внутренняя скобка (F5), а не новый полный Mellin-момент:
\[
\mathcal M_{m,k}(s_n)=
\sum_{h=0}^{k}\frac{L_{kh}}{s_n+2h}
\left[D_m(s_n)-m^{-1/2-2h}S_{2h}(m)\right].
\]
Следовательно,
\[
\mathbf a_m(n)=\frac{m^{1/4}}{\sqrt L}
\sum_{k\ge1}c_{m,k}\mathcal M_{m,k}(s_n).
\tag{3}
\]
Это сохраняет оба конца каждого интеграла и \((-1)^n\)-фазу: именно на этой сетке \((-1)^n\lambda^{s_n}=m^{1/4}\).

Из \(|P_{2k}(x)|\le1\) при \(0\le x\le1\) получаем **одновременно для всех \(k\ge0\), \(|n|\le m\)**:
\[
\begin{aligned}
|\mathcal M_{m,k}(s_n)|
&\le2\sum_{r=1}^{m}r^{-1/2}\bigl(1-\sqrt{r/m}\bigr)\\
&=2\bigl(D_m(1/2)-\sqrt m\bigr)\le2\sqrt m.
\end{aligned}
\tag{4}
\]
В отличие от низкочастотной асимптотики, (4) не теряет силу при \(|n|\asymp m\). Оно используется **только для оставшегося Ferrers-хвоста**, не для объявления знака основной суммы.

### Источниковый хвост, а не Gaussian trial

**[COFINAL_FAMILY | PAPER]** Из точной склейки и принятой геометрической оценки:
\[
|a^{(i)}_{m,5m-1+t}|\le |a^{(i)}_{m,5m-1}|2^{-t},\qquad t\ge0.
\]
Поэтому при
\[
C_m^{\rm tail}:=\frac{6\sqrt m}{|A_{0,m}A_{4,m}|}
\left(|a^{(4)}_{m,0}a^{(0)}_{m,5m-1}|+
|a^{(0)}_{m,0}a^{(4)}_{m,5m-1}|\right)
\]
имеем
\[
\boxed{\sum_{k\ge6m}|c_{m,k}|\le C_m^{\rm tail}2^{-m}.}
\tag{5}
\]
Проверка индекса: \(6m=(5m-1)+(m+1)\), а \(\sum_{t\ge m+1}2^{-t}=2^{-m}\). Источниковый supplier именно такой, с якорем \(K-1\), не с якорем \(K\). fileciteturn19file0L2-L2

Введём **вспомогательную конечную часть**, не новый источник:
\[
x_m(n)=\frac{m^{1/4}}{\sqrt L}
\sum_{k=1}^{6m-1}c_{m,k}\mathcal M_{m,k}(s_n),
\qquad e_m=\mathbf a_m-x_m.
\tag{6}
\]
\(e_m\) здесь — хвост этой оценки, не прежний spectral residual и не физические \(e_{n,m}\).

Получается покоординатный сертификат
\[
|e_m(n)|\le\frac{2m^{3/4}}{\sqrt L}C_m^{\rm tail}2^{-m}
\quad(-m\le n\le m).
\tag{7a}
\]
Для нормы всей строки можно сделать лучше, чем суммировать (7a). Физическая хвостовая функция
\[
H_m^{\rm tail}(x)=\mathbf1_{[-\sqrt m,\sqrt m]}(x)
\sum_{k\ge6m}c_{m,k}P_{2k}(x/\sqrt m)
\]
ограничена по модулю правой частью (5). На логарифмическом окне
\[
|\mathcal E H_m^{\rm tail}(t)|
\le \sqrt m\,e^{-t/2}C_m^{\rm tail}2^{-m}.
\]
Интегрирование по \(dt\) и сжатие ортогональной проекции дают
\[
\boxed{
\|e_m\|_2\le\eta_m:={\sqrt{m(\sqrt m-m^{-1/2})}}
C_m^{\rm tail}2^{-m}.
}
\tag{7b}
\]
**Никакой коммутативности проекции с \(\mathcal W\) в этом шаге нет:** это только её сжатие в \(L^2\).

### Почему бюджет действительно равномерен по выбранному хвосту

**[COFINAL_FAMILY | PAPER]** Обозначим константы принятого hmode через \(C_0,C_4\). На его хвосте
\[
\|f_{i,m}\|_2\le F_i(m):=\|\mathscr D_i\|_2+\sqrt2 C_i m^{-3/4}.
\]
Источник нормирован так, что
\[
\|f_{0,m}\|_2=\frac{\sqrt{2\sqrt m}}{|A_{0,m}|},\qquad
\|f_{4,m}\|_2=\frac{3\sqrt{2\sqrt m}}{|A_{4,m}|}.
\]
Отсюда, пользуясь \(|a^{(i)}_{m,k}|\le\sqrt{4k+1}\),
\[
\boxed{C_m^{\rm tail}\le2\sqrt{20m-3}\,F_0(m)F_4(m).}
\tag{8}
\]
Значит (7b) имеет явный полиномиальный множитель перед \(2^{-m}\), а не скрытую константу, зависящую произвольно от ячейки. Это использование hmode для нормы и центральной нормировки; **ни CCM-позитивность, ни пролатный зазор не используются**.

## 3. Точный учёт исходного z через двумерный след

**[FINITE_CELL | PAPER]** Пусть \(\Pi_m\) — ортогональный проектор на **ту же** \(U_j\), а
\[
\theta_m=\operatorname{tr}_{U_j}(\Pi_mK_j\Pi_m)
=u_j^*K_ju_j+v_j^*K_jv_j.
\]
Для любого \(x\) с \(Y(x):=\|\Pi_mx\|_2>0\) введём скалярную функцию
\[
\mathcal F_m(x)=x^*K_jx-\|x\|_2^2\theta_m
+\frac{\|x\|_2^2}{\|\Pi_mx\|_2^2}
x^*\Pi_mK_j\Pi_mx.
\tag{9}
\]
В двумерной плоскости нормированная проекция \(\Pi_m\mathbf a_m\) и исходный \(z_j\) ортогональны. Поэтому
\[
z_j^*K_jz_j=\theta_m-
\frac{\mathbf a_m^*\Pi_mK_j\Pi_m\mathbf a_m}
{\|\Pi_m\mathbf a_m\|_2^2}.
\]
Следовательно, **для исходного, не перенормированного объекта**
\[
\boxed{\mathfrak L_m=\mathcal F_m(\mathbf a_m).}
\tag{10}
\]
Это устраняет чувствительную зависимость \(z_j\) от \(q_j\) из последующего error budget. **Новый trial или новый \(z_j\) не вводится.** В (9) лишь вычисляется вспомогательная скалярная функция на конечной части (6).

Формула работает над \(\mathbb C\). При \(\mathbf a\mapsto e^{i\varphi}\mathbf a\) её значение не меняется; при ненулевом общем скаляре оно умножается на его модуль в квадрате. Нормировка \(\rho_m\) в \(\tau_j=-\mathfrak L_m/\rho_m^2\) остаётся первоначальной.

## 4. Полный CCM-бюджет, необходимый только для остатка

**[FINITE_CELL | PAPER]** Из полного источника выводится следующая явная оценка без предположения о знаке матрицы:
\[
\boxed{
\|K_j\|\le\Gamma_m:=
2\sqrt m+4\sqrt m\log m+9+
\frac{20\pi m+20m+10}{\log m},\qquad m\ge2.
}
\tag{11}
\]
Здесь не удалены ни диагональная ветвь, ни архимедова константа, ни prime powers. Определения полной формы и этих частей сверены на pin. fileciteturn26file0L2-L2

**Доказательство.** Для единичного конечного синтеза \(f\) положим
\(Q_f(x)=2\Re\int_{-L/2}^{L/2-x}\overline{f(t)}f(t+x)dt\), \(0\le x\le L\).
Тогда
\[
|Q_f|\le2,\quad Q_f(0)=2,\quad
|Q_f(x)-2|\le D_m^{\rm Lip}x,
\quad D_m^{\rm Lip}=2\omega_m+2(2m+1)/L.
\]
Последний член включает край: при дифференцировании корреляции появляется
\(-\overline{f(L/2-x)}f(L/2)\). Использованы
\(\|f'\|_2\le\omega_m\), \(\|f\|_\infty^2\le(2m+1)/L\).

Полюсная часть равна \(2\Re(\overline{\int f e^{-t/2}}\int f e^{t/2})\), её модуль не превосходит \(2\sqrt m\). Для Prime:
\[
\left|\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}Q_f(\log\nu)\right|
\le4\sqrt m\log m.
\]
Все ненулевые von-Mangoldt слагаемые, в том числе степени простых, включены.

Для WR используем
\[
\int_0^\infty\frac{x e^{x/2}}{e^x-e^{-x}}dx
=\sum_{r\ge0}\frac1{(2r+1/2)^2}\le5,
\qquad e^{x/2}-1\le\tfrac{x}{2}e^{x/2}.
\]
Архимедова константа удовлетворяет
\(0<\gamma+\log(4\pi(m-1)/(m+1))<4\).
Следовательно,
\[
|WR[f]|\le4+5D_m^{\rm Lip}+5
=9+10\omega_m+10(2m+1)/L.
\]
Сложение даёт (11). Это bound модуля **остаточного** вклада; основная совместная форма в следующем разделе не заменяется суммой модулей.

## 5. Один полученный сертификат T + R

**[COFINAL_FAMILY | PAPER]** Возьмём буквально \(x_m\) из (6), положим
\[
X_m=\|x_m\|_2,\qquad Y_m=\|\Pi_mx_m\|_2.
\]
Работаем на хвосте, где \(Y_m>\eta_m\). Он существует: принятый hmode вместе с исходниковым \(\mathcal E\)-переносом даёт \(\mathbf a_m-\operatorname{coeff}(T_mG)\to0\); (7b)–(8) дают \(e_m\to0\); проекция \(G\) лежит в \(U_j\) и её норма стремится к \(\|G\|_2>0\). Отсюда \(X_m,Y_m\to\|G\|_2\). Это утверждение о норме строки, **не о пределе её Rayleigh-значения**.

Определим
\[
\boxed{T(m):=\mathcal F_m(x_m),}
\tag{12}
\]
\[
\boxed{
B(m):=2\Gamma_m\eta_m(2X_m+\eta_m)
+4\Gamma_m\frac{X_m^2\eta_m}{Y_m}.
}
\tag{13}
\]
Все коэффициенты (12) — выбранные Ferrers-коэффициенты (1), сгруппированные моменты (2), прежняя плоскость и полный источниковый \(K_j\). Это не энергия Gaussian trial. Центральные множители из (1) сохранены точно; общий ненулевой скаляр входит в \(T\) и \(B\) квадратично.

Тогда
\[
\boxed{
\mathfrak L_m=T(m)+\mathcal R(m),\qquad
\underline R(m)=-B(m)\le\mathcal R(m)\le B(m)=\overline R(m).
}
\tag{CERT}
\]
Это **один** сертификат на всех выбранных \(m\) указанного хвоста, одновременно на полном carrier. Дополнительный cutoff \(6m\) — только место разбиения бесконечной суммы для оценки. Источник по-прежнему имеет splice \(5m\), и его коэффициенты \(k\ge6m\) остаются в \(\mathcal R\).

### Проверка error budget

**[ABSTRACT | PAPER]** Для \(x=x_m\), \(a=x+e_m\) определим
\[
s(x)=\theta_m-
\frac{x^*\Pi_mK_j\Pi_mx}{\|\Pi_mx\|_2^2}.
\]
Это Rayleigh-значение единичного направления, ортогонального \(\Pi_mx\) внутри двумерной плоскости; поэтому \(|s(x)|\le\Gamma_m\), и то же верно для \(s(a)\).

Нормированные проекции удовлетворяют
\[
\left\|\frac{\Pi_ma}{\|\Pi_ma\|}-
\frac{\Pi_mx}{\|\Pi_mx\|}\right\|\le\frac{2\eta_m}{Y_m},
\]
следовательно,
\[
|s(a)-s(x)|\le\frac{4\Gamma_m\eta_m}{Y_m}.
\]
Кроме того,
\[
|a^*K_ja-x^*K_jx|\le\Gamma_m\eta_m(2X_m+\eta_m),
\quad |\|a\|^2-X_m^2|\le\eta_m(2X_m+\eta_m).
\]
Подстановка в \(\mathcal F_m(a)=a^*K_ja-\|a\|^2s(a)\) даёт (13).

Здесь ограничены только члены с хотя бы одним **удалённым для оценки Ferrers-хвостом** \(e_m\) и изменение рационального plane-выражения. Смешанные члены основной части \(T(m)\) остаются со своими знаками.

## 6. Где в CERT находятся W1, Q6, края и prime powers за m

**[FINITE_CELL | PAPER]** Для недопущения скрытой замены полной формы приведём \(T(m)\) непосредственно на стороне (W1).

Пусть \(U_m^\circ,V_m^\circ\in\operatorname{span}\{G,G''\}\) — прежние единственные глобальные подъёмы \(u_j,v_j\), а
\[
\delta_u=f_{u_j}-U_m^\circ,\qquad
\delta_v=f_{v_j}-V_m^\circ.
\]
Для \(x=x_m\) положим
\[
D_x=(u_j^*x)\delta_u+(v_j^*x)\delta_v,
\qquad V_x=f_x-S_m.
\]
Из принятого **полного радикального тождества**, а не коммутирования проекции, получаем
\[
\boxed{
T(m)=\mathcal W(V_x,V_x)
-X_m^2\bigl[\mathcal W(\delta_u,\delta_u)+\mathcal W(\delta_v,\delta_v)\bigr]
+\frac{X_m^2}{Y_m^2}\mathcal W(D_x,D_x).
}
\tag{14}
\]
Таким образом, в (W1) для \(T\) подставляется **единая корреляция**
\[
\Omega_T=Q_{V_x}-X_m^2(Q_{\delta_u}+Q_{\delta_v})
+\frac{X_m^2}{Y_m^2}Q_{D_x};
\qquad \Omega_{\mathcal R}=\Omega_m-\Omega_T.
\tag{15}
\]
Обе обрабатываются одним полным функционалом (W1). Нормировки, сопряжения и конвенция полной формы согласованы с CCM §§2–4; её положительность не импортируется. citeturn960756view0

| Часть ledger | Что именно сохранено |
|---|---|
| **W02** | Полный интеграл \(\int_0^\infty2\cosh(x/2)\Omega(x)dx\) для каждой корреляции (15). Нулевая физическая масса не объявляет этот интеграл нулём. |
| **Диагональ WR** | Член \(-[\gamma+\log(4\pi)]\Omega(0)/2\), а также вычитание \(\Omega(0)\) внутри интеграла. У ошибок в (15) нет единичной нормировки; \(\Omega_T(0)\) вообще не равна нулю. |
| **Края и Q6** | При вычислении \(\Pi_m\) и \(S_m\) используется \(\operatorname{coeff}(T_mG'')(n)=-\omega_n^2\mathbf b_m(n)+2G'(L/2)/\sqrt L\). Значит член \(+G'(L/2)/(8\pi m\sqrt L)\) в строке остатка Q6 не потерян. Нулевое продолжение конечных синтезов сохраняет оба скачка. |
| **Prime** | Для (15) суммирование идёт по всем \(\nu\ge2\) с весом \(\Lambda(\nu)/\sqrt\nu\). В частности, \(\nu>m\) не отбрасываются и \(\Omega_T(L)=0\) не предполагается. |

Снаружи окна \(V_x=-S_m\), \(\delta_u=-U_m^\circ\), \(\delta_v=-V_m^\circ\), а \(D_x\) — минус соответствующий глобальный подъём. Их хвосты сохраняются в (15).

**Почему (11) можно использовать, не теряя возвращённые prime powers.** При переходе от (14) к (12) каждый удаляемый глобальный шаблон принадлежит радикалу **всей** \(\mathcal W\). Его полюсная, архимедова и prime-части не объявляются нулевыми отдельно. Поэтому (11) ограничивает уже точно сложенную полную разность. Это uniform budget всей комбинации, включая возвращённые хвосты, а не применение фиксированно-ячеечного (W3) с неконтролируемой константой.

## 7. Первый конкретный недоказанный знак

### 7.1. Он находится в конечной части настоящей рекурсии

**[FINITE_CELL | PAPER]** Положим \(G_m=4\pi^2m^2\). Исходниковые коэффициенты трёхчленной рекурсии, при \(N=2k\), равны
\[
\begin{aligned}
\ell_k&=-G_m\frac{(N-1)N}{(2N-3)(2N-1)},\\
d_k&=N(N+1)+G_m\frac{2N(N+1)-1}{(2N-1)(2N+3)},\\
u_k&=-G_m\frac{(N+1)(N+2)}{(2N+3)(2N+5)}\ne0.
\end{aligned}
\]
Здесь символ \(u_k\) — верхний коэффициент рекурсии, не вектор \(u_j\). Для выбранных энергетических параметров \(E_{i,m}=\Lambda_{i,m}+G_m\) зададим полиномы
\[
\mathcal P_{-1}=0,\quad\mathcal P_0=1,\quad
\mathcal P_{k+1}(E)=\frac{(E-d_k)\mathcal P_k(E)-\ell_k\mathcal P_{k-1}(E)}{u_k}.
\]
Тогда точно
\[
a^{(i)}_{m,k}=a^{(i)}_{m,0}\mathcal P_k(E_{i,m}),
\]
и
\[
\boxed{
c_{m,k}=\frac{6\sqrt m\,a^{(0)}_{m,0}a^{(4)}_{m,0}}{A_{0,m}A_{4,m}}
(-1)^k\bigl[\mathcal P_k(E_{0,m})-\mathcal P_k(E_{4,m})\bigr].
}
\tag{16}
\]
Это точное сведение к двум **источниковым** энергиям и их рекурсии; не независимый выбор коэффициентов. Сдвиг \(+G_m\) сохранён. Формулы взяты из source crosswalk и recurrence-поля выбранного типа. fileciteturn25file0L2-L2 fileciteturn23file0L2-L2

Теперь зададим матрицу моментов с **точным диапазоном**
\[
F_{nk}=\frac{m^{1/4}}{\sqrt L}\mathcal M_{m,k}(s_n),
\quad -m\le n\le m,\quad1\le k<6m,
\]
и вектор \(c=(c_{m,k})_{1\le k<6m}\). Таким образом, \(x_m=Fc\). Введём четыре конечные матрицы
\[
J=F^*F,\quad P_U=F^*\Pi_mF,\quad
A=F^*K_jF,\quad H=F^*\Pi_mK_j\Pi_mF.
\]
Непосредственно из (12):
\[
T(m)=\frac{\mathcal Q_m(c)}{c^*P_Uc},
\]
\[
\boxed{
\mathcal Q_m(c)=
(c^*P_Uc)(c^*Ac)
-(c^*Jc)(c^*P_Uc)\theta_m
+(c^*Jc)(c^*Hc).
}
\tag{17}
\]
**Первое не установленное равномерное неравенство** теперь полностью конечное и источниковое:
\[
\boxed{
\mathcal Q_m(c)>(c^*P_Uc)B(m)
\quad\text{на неограниченных выбранных }m,
}
\tag{18-}
\]
либо
\[
\boxed{
\mathcal Q_m(c)<-(c^*P_Uc)B(m)
\quad\text{на всём выбранном хвосте}.
}
\tag{18+}
\]
Это не выдаётся за доказанное. В отличие от исходного (SIGN), (17) имеет только \(1\le k,k'<6m\), \(-m\le n,n'\le m\), конкретные recurrence-полиномы (16) и **уже доказанный** error budget бесконечного Ferrers-хвоста. Но знак этой конечной формы на выбранной паре энергий не получен.

### 7.2. Какой смешанный член не позволяет объявить знак

**[FINITE_CELL | PAPER]** Пусть \(\mathbf d_m=\operatorname{coeff}(T_mS_m)\), вычисленная с Q6, и \(w_m=x_m-\mathbf d_m\). В (14)
\[
V_x=f_{w_m}+(T_m-I)S_m.
\]
При сохранении смешанных членов полная форма даёт
\[
\mathcal W(V_x,V_x)=w_m^*K_jw_m+
2\Re(w_m^*K_j\mathbf d_m)+\mathbf d_m^*K_j\mathbf d_m.
\tag{19}
\]
Здесь использовано \(\mathcal W(f_{w_m},S_m)=0\), а не положительность и не отдельно занулённая Prime-часть.

Конкретный линейный по основной Ferrers-части смешанный член:
\[
\boxed{
\begin{aligned}
\mathcal C_m:=2\Re(w_m^*K_j\mathbf d_m)
=2\Re\Bigg[&\frac{m^{1/4}}{\sqrt L}
\sum_{k=1}^{6m-1}\overline{c_{m,k}}
\sum_{n=-m}^{m}\overline{\mathcal M_{m,k}(s_n)}
(K_j\mathbf d_m)_n\\
&-\mathbf d_m^*K_j\mathbf d_m\Bigg].
\end{aligned}
}
\tag{MIX}
\]
**Ни знак (MIX), ни его одностороннее доминирование в полной комбинации (17) не доказаны.** Он не заменён \(\pm\|w_m\|\|K_j\mathbf d_m\|\) в \(T(m)\). Такая оценка потеряла бы знак смешанного члена.

Указание одного знака (MIX) само по себе также не закрывает (18): квадратичный член \(w_m^*K_jw_m\) и plane-коррекция обязаны остаться в том же совместном сравнении. **Первый долг — источниковая односторонняя оценка этой комбинации, не произвольный floor для \(w_m\).**

### 7.3. Почему имеющиеся hmode и tail bounds этого не дают

**[COFINAL_FAMILY | PAPER]** Tail bounds оплачивают \(k\ge6m\) в (5)–(8). Они не устанавливают знак колебательной комбинации двух recurrence-решений (16) в диапазоне \(1\le k<6m\). Абсолютная оценка \(|a_{m,k}|\le\sqrt{4k+1}\) теряет именно эти сокращения.

Hmode ограничивает физические функции, но не даёт односторонней ошибки неполных комплексных Mellin-моментов, спаренных с \((K_j\mathbf d_m)_n\). Даже получаемое из него приближение строки к проекции \(G\) в \(L^2\) не выделяет знак (MIX). В (19) ведущие глобальные шаблоны уже принадлежат радикалу; размер оставшегося знакового запаса не задан нормовым приближением.

Есть и конкретная проверка равномерности непосредственно через источниковое дифференциальное уравнение. Для каждой выбранной безразмерной функции \(\Phi_{i,m}\) положим
\[
I_{i,m}(s,a)=\int_a^1\Phi_{i,m}(x)x^{s-1}dx,
\qquad a=r/m>0.
\]
Дважды интегрируя полное ODE и используя **нулевой поток**, не нулевое значение на правом конце, получаем
\[
\begin{aligned}
&G_mI_{i,m}(s+2,a)+[s(s-1)-E_{i,m}]I_{i,m}(s,a)
-(s-1)(s-2)I_{i,m}(s-2,a)\\
&\qquad=-(1-a^2)a^{s-2}
\bigl[a\Phi'_{i,m}(a)-(s-1)\Phi_{i,m}(a)\bigr].
\end{aligned}
\tag{20}
\]
Это верно для \(1\le r<m\); при \(r=m\) член понимается как нулевой граничный предел. Все сдвинутые моменты существуют, поскольку \(a>0\).

На точной сетке \(s=s_n\) взвешенная сумма правых граничных множителей, **до общего минуса**, равна
\[
\boxed{
m^{3/2}\sum_{r=1}^{m-1}\frac{1-r^2/m^2}{r^2}
\left[\frac r m\Phi'_{i,m}(r/m)-(s_n-1)\Phi_{i,m}(r/m)\right].
}
\tag{21}
\]
Здесь фаза \(r^{-s_n}(r/m)^{s_n}\) сокращается точно; этот boundary forcing нельзя усреднить как независимые осцилляции по \(r\).

На крайнем Fourier-индексе \(|s_n|\) достигает порядка \(m/\log m\). Уравнение (20) содержит \(s_n(s_n-1)\), сдвинутые моменты и весь нижний граничный ряд (21). Hmode не оценивает нужные производные и их **совместное сокращение** с моментами с таким знаковым разрешением. Существование всех полиномиально взвешенных Ferrers-tail сумм обеспечивает допустимость дифференцирования, но не требуемый знак этого выражения по \(m,n,r\). Именно поэтому fixed-\(n\) разложение не заменяет отсутствующую оценку в (18).

## 8. Диспозиция теста и следующий дискриминатор

**[COFINAL_FAMILY | PAPER]** У сертификата (CERT) правильные направления:
\[
T(m)-B(m)>0\Longrightarrow
\tau_j\le-\frac{T(m)-B(m)}{\rho_m^2}<0,
\]
\[
T(m)+B(m)<0\Longrightarrow
\tau_j\ge-\frac{T(m)+B(m)}{\rho_m^2}>0.
\]
Первый случай на неограниченной подпоследовательности дал бы KILL_NULLPLANE; второй на всём хвосте дал бы POSITIVE_NULLPLANE с указанной нижней функцией. **Ни одного такого набора индексов или eventual-оценки я не доказал.**

**Один следующий PAPER-дискриминатор:** установить одностороннее сравнение (18) для source-defined (16), удерживая (MIX) в полной форме (17). При попытке через рекурсию необходимо оценить объединённые неполные моменты и forcing (21), а не только геометрическую склейку. Если запас меньше бюджета (13), требуется более точное совместное tail-раскрытие; не следует из этого, что знак отсутствует.

Две допустимые репрезентации **этого же теста**, не две задачи:

| Представление | Kill-power / стоимость | Главный риск |
|---|---|---|
| **Выбрано: (16)–(18), сгруппированные моменты, полный совместный Gram-блок.** | Один равномерный margin решает первый скалярный знак на семье. Требуются \(O(m)\) recurrence-данных и аналитический знак связанных конечных сумм, не серия отдельных PSD-сертификатов. | Большие взаимно сокращающиеся слагаемые; нельзя оценить основную часть по модулям. |
| **Сопряжённая трёхчленная рекурсия для весов в (MIX).** | Потенциально переводит всё смешанное суммирование в граничный Green-терм; цена — одна неоднородная adjoint-recurrence с двумя выбранными спектральными параметрами. | Знак граничного pairing и uniform remainder пока не доказаны; наличие рекурсии само по себе их не даёт. |

Ни числовая сетка, ни запуск Lean, ни вычислительный sweep этим не разрешаются.

## 9. Сильнейшая атака, проверка и closeout

**[ABSTRACT | PAPER]** Сильнейшее возражение: «\(T\) — опять исходный неизвестный знак в другой записи». **Частично верно и существенно:** знаковый результат действительно не получен. Отличие от пустого повторения — доказанные uniform bounds (5)–(8), перенос до полной энергии (CERT), finite-prefix зависимость (16)–(17) и конкретный mixed-term долг (MIX). Это не основание выставлять знак или закрывать Schur-floor.

Проверены на бумаге следующие уязвимости сертификата. Проекция нормируется по \(Y_m\), не по \(\rho_m\); двумерный след учитывает исходное комплексное \(z_j\); изменение его энергии при perturbation не забыто — это второй член (13). При \(e_m=0\) сертификат становится точным. При общей комплексной фазе все формы инвариантны. Пропуск изменения plane-направления оставил бы ошибочный бюджет без \(4\Gamma_mX_m^2\eta_m/Y_m\). Глобальное вычитание не даёт права занулить отдельные prime-хвосты или \(\Omega_T(0)\).

**Регистрации.** В начале были объявлены три проверяемых вопроса: uniform неполные моменты, mixed-term cancellation и предел силы tail bounds. Направленная ставка на итоговый знак не регистрировалась; HIT для KILL/POSITIVE не приписывается. Результаты: uniform tail-перенос доказан; mixed terms основной части сохранены, их знак открыт; tail bounds контролируют бесконечный хвост, но не prefix pairing. Последующая объявленная проверка комплексной фазы и возвращённых ledger-членов не выявила несогласованности в приведённых формулах. Независимый аудит **нового** сертификата не заявляется.

**Что закрыто:** вспомогательный uniform Ferrers-tail-to-full-energy budget на всей сетке, не fixed-\(n\) результат. **Что не закрыто:** знак source-prefix формы (17) с margin (18); первый скалярный знак \(\tau_j\); Schur-floor. **Что не опровергнуто:** eventual cellwise positivity самой буквальной семьи.

```yaml
DOWNSTREAM_CONSUMER: first_scalar_gate_for_unchanged_cellwise_complement
ACTUAL_CONSUMER_REQUIREMENT: eventual_tau_positive_is_necessary_not_sufficient_for_d_positive
ORIGINAL_REQUESTED_OBJECT: signed_uniform_coupled_defect_certificate
ORIGINAL_OBJECT_IS: UNKNOWN
QUALIFICATION: this_prefix_certificate_is_a_sufficient_method_not_a_proved_necessary_interface
KNOWN_WEAKER_INTERFACES:
  - any_unbounded_selected_tau_nonpositive_witness_refutes_eventual_d_positive
  - any_eventual_positive_tau_lower_function_closes_only_the_scalar_gate
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
MINIMAL_MISSING_ESTIMATE: signed_source_recurrence_prefix_margin_in_18_with_MIX_retained
DISCRIMINATOR: source_prefix_quartic_17_against_explicit_energy_budget_13
REOPEN_TRIGGER: one_sided_source_bound_proving_18_or_a_sharper_joint_remainder_with_separated_sign
KILLED_THEOREM_SHAPE: NONE
NOVELTY_AXIS: uniform_grouped_Mellin_tail_plus_exact_nullplane_trace_plus_full_ledger_energy_enclosure
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
MEMORY_ENTRY:
  target: TEST_SELECTED_FERRERS_COUPLED_DEFECT_SIGN
  status: OPEN
  invariant_learned: control_of_the_Ferrers_tail_does_not_supply_a_sign_for_the_two_energy_prefix_pairing
  forbidden_future_move: repeat_norm_only_hmode_or_tail_bounds_as_a_supplier_of_18
  next_decisive_test: prove_source_prefix_margin_with_MIX_and_boundary_forcing_retained
```

**Итог ровно один: OPEN_COUPLED_DEFECT_SIGN.** Выполнены чтение источников, бумажные выводы и доставка этого Markdown. Lean, математические численные/символьные прогоны и проектный runtime не запускались; репозиторий и route-state не менялись; RH-claim отсутствует.
