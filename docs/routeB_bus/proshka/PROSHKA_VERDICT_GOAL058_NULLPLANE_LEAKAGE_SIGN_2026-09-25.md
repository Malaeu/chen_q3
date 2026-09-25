# STATUS: TRY_GOAL058_FERRERS_DEFLATED_LEAKAGE_SIGN

```yaml
OPERATIVE_CLASS: TRY_GOAL058_FERRERS_DEFLATED_LEAKAGE_SIGN
OUTCOME: OPEN_SIGNED_LEAKAGE
REQUEST_ID: REQ-2026-09-25-NULLPLANE-LEAKAGE-SIGN
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_FULL_CCM_NULLPLANE_LEAKAGE_SIGN
SOURCE_COMMIT: 388f070de85d9f93f69c37ee81e9536f2341d669
PREDECESSOR: REQ-2026-09-25-CELLWISE-COMPLEMENT-SIGN
PREDECESSOR_SHA256_AUDIT_REPORTED: 970c8b37a7e70c7c2ce94c35779bd8f360dc8085cef4d88f03004e1db6f6b556
BOOTSTRAP_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_LOCK: GITHUB_CONNECTOR_READ_AT_REQUESTED_COMMIT
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
SIGN_OF_TAU: NOT_ESTABLISHED
NONPOSITIVE_COFINAL_WITNESS: NOT_ESTABLISHED
EVENTUAL_POSITIVE_LOWER_FUNCTION: NOT_ESTABLISHED
SCHUR_FLOOR: OPEN
SOURCE_FAMILY_CHANGED: false
HMODE_USED: ACCEPTED_PAPER_INPUT_AND_ITS_EXPLICIT_QUASIMODE_POLYNOMIALS
PROLATE_GAP_USED: false
RH_ASSUMED: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 3
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
REPOSITORY_WRITTEN: false
DELIVERY_MARKDOWN_CREATED: true
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_SIGNED_LEAKAGE. Ни неположительную кофинальную подпоследовательность, ни eventual-положительную нижнюю функцию для \(\tau_j\) здесь не доказал.**

Но раскрытие выбранных коэффициентов даёт существенное сокращение: **явная поправка порядка \(1/m\), выписанная в доказательстве hmode, после \(\mathcal E\) целиком лежит в той же плоскости \(\operatorname{span}\{G,G''\}\)**. Поэтому её конечная проекция не является утечкой из \(U_j\). При совместном раскрытии полной формы и \(E_j\) остаётся разность энергий **двух явно определённых ошибок**, а не положительность энергии этой гауссовой поправки.

Это точное утверждение о выписанном шаблоне. **Оно само по себе не доказывает, что настоящая утечка начинается с \(m^{-2}\)**: для этого ещё нужна равномерная оценка остатка выбранных мод на нужном диапазоне.

## 1. Источник и неизменяемые объекты

**[COFINAL_FAMILY | PAPER]** Всюду фиксирован исходный \(P\), и
\[
m=m_j=N_j=J_P+j+2,\qquad \lambda=\sqrt m,\qquad L=\log m,\qquad b=L/2.
\]
Сохраняются исходниковый Ferrers splice \(K=5m\), все Fourier-моды \(-m,\ldots,m\), мера \(dt=du/u\), комплексное дополнение и фаза
\[
\psi_{n,L}(t)=L^{-1/2}e^{2\pi in(t+b)/L}\mathbf1_{[-b,b]}(t).
\]
Здесь \(K=5m\) — параметр источникового склеивания Ferrers-ряда, **не разрешение отбросить все его коэффициенты после \(5m\)**.

Прочитаны на указанном pin: определения выбранной строки, production-пары, нормированного нулевого продолжения, полного CCM-ядра, Ferrers-ряда, оба независимых аудита и явные полиномы hmode. `selectedFerrersFiniteCCMRow` действительно использует именно нормированную проекцию `prolateCombination` выбранной пары. fileciteturn27file0L2-L2 fileciteturn17file0L2-L2

Предшествующий SHA-256 указан как **сообщённый независимым аудитом**, а не как заново вычисленный в этой сессии. Аудит также явно оставляет оба знака утечки недоказанными. fileciteturn15file0L2-L2

## 2. Настоящие Ferrers-коэффициенты выбранной строки

### 2.1. Коэффициент нулевой Legendre-моды сокращается точно

**[FINITE_CELL | PAPER]** Пусть \(a^{(0)}_{m,k}\), \(a^{(4)}_{m,k}\) — поля `coefficients` именно двух выбранных regular Ferrers witnesses: carrier-индексы \(0\) и \(2\), соответственно. Пишем
\[
\Phi_{n,m}(x)=\sum_{k\ge0}(-1)^k a^{(n)}_{m,k}P_{2k}(x),\qquad n\in\{0,4\}.
\]
Это буквальная источниковая фазовая конвенция. Абсолютная суммируемость коэффициентов даёт равномерную сходимость на \([-1,1]\), поэтому последующие интегралы разрешено брать по сгруппированным Legendre-слагаемым. fileciteturn24file0L2-L2

Обозначим \(A_{0,m}=\Phi_{0,m}(0)\), \(A_{4,m}=\Phi_{4,m}(0)\). Центрированные физические функции из предыдущего PAPER-входа равны
\[
f_{0,m}(x)=\frac{\Phi_{0,m}(x/\lambda)}{A_{0,m}}\mathbf1_{[-\lambda,\lambda]}(x),\quad
f_{4,m}(x)=\frac{3\Phi_{4,m}(x/\lambda)}{A_{4,m}}\mathbf1_{[-\lambda,\lambda]}(x).
\]
Здесь \(L^2\)-нормировка production-мод сокращается в отношении к значению в центре; само нулевое продолжение сохраняется. fileciteturn21file0L2-L2

Положим
\[
J_{0,m}=\int_{\mathbb R}f_{0,m},\quad J_{4,m}=\int_{\mathbb R}f_{4,m},\quad
H_m=J_{4,m}f_{0,m}-J_{0,m}f_{4,m}.
\]
Из ортогональности Legendre-полиномов к константе:
\[
J_{0,m}=\frac{2\lambda a^{(0)}_{m,0}}{A_{0,m}},\qquad
J_{4,m}=\frac{6\lambda a^{(4)}_{m,0}}{A_{4,m}}.
\]
Следовательно, на физическом окне
\[
\boxed{H_m(x)=\sum_{k\ge1}c_{m,k}P_{2k}(x/\lambda),}
\tag{F1}
\]
\[
\boxed{
c_{m,k}=\frac{6\lambda(-1)^k}{A_{0,m}A_{4,m}}
\left(a^{(4)}_{m,0}a^{(0)}_{m,k}-a^{(0)}_{m,0}a^{(4)}_{m,k}\right),
\qquad c_{m,0}=0.
}
\tag{F2}
\]
Это **не произвольный малый вектор**: в (F2) стоят настоящие выбранные recurrence rows. Ни один их хвост не заменён нулём.

Точная связь с `prolateCombination`:
\[
\operatorname{prolateCombination}
=\frac{h_{0,m}(0)h_{4,m}(0)}{3\sqrt{I_{0,m}^2+I_{4,m}^2}}\,H_m.
\]
Обозначим фазу этого ненулевого скаляра через \(\sigma_m\), \(|\sigma_m|=1\); она сохраняется ниже. Кроме того, источник даёт **точно**, не асимптотически,
\[
J_{0,m}=\chi_{0,m},\qquad J_{4,m}=3\chi_{2,m}.
\tag{F3}
\]
Подмены \(J_0=1\), \(J_4=3\) для настоящей пары нет. fileciteturn25file0L2-L2

### 2.2. Все коэффициенты Fourier-проекции раскрываются через конечные моменты

**[FINITE_CELL | PAPER]** На логарифмическом окне определим
\[
F_m(t)=e^{t/2}\sum_{r\ge1}H_m(re^t),\qquad
\omega_n=\frac{2\pi n}{L},\quad s_n=\frac12-i\omega_n.
\]
Пусть \(\mathbf a_m(n)=\langle\psi_{n,L},F_m\rangle\). Замена \(x=re^t\) даёт
\[
\boxed{
\mathbf a_m(n)=\frac{(-1)^n}{\sqrt L}
\sum_{r=1}^{m}r^{-s_n}\int_{r/\lambda}^{\lambda}H_m(x)x^{s_n-1}\,dx.
}
\tag{F4}
\]
Верхний предел \(r=m\), нижние края \(r/\lambda\) и верхний край \(\lambda\) здесь буквальные. Значения на конечном числе точек не меняют интеграл; **скачки нулевого продолжения не объявляются отсутствующими**.

Для полностью раскрытой формулы положим
\[
P_{2k}(x)=\sum_{h=0}^k L_{kh}x^{2h},\quad
L_{kh}=\frac{(-1)^{k-h}(2k+2h)!}
{2^{2k}(k-h)!(k+h)!(2h)!},
\]
\[
D_m(s)=\sum_{r=1}^m r^{-s},\qquad S_{2h}(m)=\sum_{r=1}^m r^{2h}.
\]
Поскольку на **точной** Fourier-сетке
\((-1)^n\lambda^{s_n}=m^{1/4}\) и \(m^{-s_n}=m^{-1/2}\), (F4) становится
\[
\boxed{
\mathbf a_m(n)=\frac{m^{1/4}}{\sqrt L}
\sum_{k\ge1}c_{m,k}
\sum_{h=0}^{k}\frac{L_{kh}}{s_n+2h}
\left[D_m(s_n)-m^{-1/2-2h}S_{2h}(m)\right].
}
\tag{F5}
\]
Сумма по \(h\) остаётся сгруппированной внутри каждого \(k\): абсолютная оценка развёрнутых мономиальных коэффициентов не подменяет исходниковую сходимость Legendre-ряда. Ни один знаменатель не обращается в ноль, поскольку \(\Re s_n=1/2\).

Полезная проверка полных моментов:
\[
\int_0^1P_{2k}(x)x^{s-1}\,dx
=\frac{\prod_{h=1}^{k}(s-(2h-1))}{\prod_{h=0}^{k}(s+2h)},\qquad \Re s>0.
\tag{F6}
\]
Но **второй член квадратной скобки (F5) нельзя выбросить**, заменив неполные моменты полными.

Наконец,
\[
\rho_m=\|\mathbf a_m\|_2>0,\qquad
\boxed{q_j=\sigma_m\mathbf a_m/\rho_m.}
\tag{F7}
\]
Таким образом, последующее раскрытие относится к исходному \(q_j\), а не к новому нормированному trial.

## 3. Что действительно сокращается в первой поправке

### 3.1. Явный полином попадает именно в прежнюю нулевую плоскость

**[ABSTRACT | PAPER]** Пишем \(v=\pi x^2\). Полиномы из принятого PAPER-доказательства hmode:
\[
\mathscr D_0=e^{-v},\qquad \mathscr D_4=(3-24v+16v^2)e^{-v},
\]
\[
B_0=e^{-v}\left(\frac38v-\frac14v^2\right),
\]
\[
B_4=e^{-v}\left(\frac{129}{8}v-\frac{183}{4}v^2+28v^3-4v^4\right).
\]
Это именно его поправки \(\mathscr D_n+B_n/(\pi m)\), не новые подобранные моды. Их использование ниже — проверка полиномиальных тождеств, **не импорт пролатного зазора**. fileciteturn18file0L2-L2

Гауссовы моменты дают \(\int B_0=\int B_4=0\). При
\[
h_*=(24v-16v^2)e^{-v},\qquad \mathcal A=x\partial_x+\frac12
\]
прямое дифференцирование даёт
\[
\boxed{
3B_0-B_4=(-15v+45v^2-28v^3+4v^4)e^{-v}
=-\frac1{16}\left(\mathcal A^2+\frac{15}{4}\right)h_*.
}
\tag{Q1}
\]
Для \(\mathcal E h(t)=e^{t/2}\sum_{r\ge1}h(re^t)\) имеем
\(\partial_t\mathcal E h=\mathcal E\mathcal A h\) на этих гауссовых функциях. Поэтому
\[
\boxed{
S_m(t):=\mathcal E\left(h_*+\frac{3B_0-B_4}{\pi m}\right)(t)
=G(t)-\frac{G''(t)+(15/4)G(t)}{16\pi m}.
}
\tag{Q2}
\]
**Шаблон \(S_m\) лежит точно в \(\mathcal N=\operatorname{span}_{\mathbb C}\{G,G''\}\).** Его конечная проекция лежит в той же \(U_j\), поскольку \(U_j\) построена из проекций \(G\) и линейной комбинации \(G,G''\).

### 3.2. Остаток выбранного источника не спрятан в символе O

**[FINITE_CELL | PAPER]** Определим на всей физической прямой
\[
e_{n,m}=f_{n,m}-\mathscr D_n-\frac{B_n}{\pi m},\qquad n=0,4.
\]
Внешний гауссов хвост включён в \(e_{n,m}\), поскольку \(f_{n,m}\) имеет исходниковое нулевое продолжение. Тогда точный остаток равен
\[
\boxed{
\mathscr R_m=3e_{0,m}-e_{4,m}
+(J_{4,m}-3)f_{0,m}-(J_{0,m}-1)f_{4,m},
}
\tag{Q3}
\]
\[
H_m=h_*+\frac{3B_0-B_4}{\pi m}+\mathscr R_m.
\]
В частности, \(\int\mathscr R_m=0\), но
\[
\mathscr R_m(0)=J_{4,m}-3J_{0,m}=3(\chi_{2,m}-\chi_{0,m})
\]
**не объявляется нулём**. Две конечные Fourier-собственные величины не отождествлены.

Обозначим через \(T_m\) ортогональную проекцию ограничения на \([-b,b]\) в span \(\psi_{-m},\ldots,\psi_m\), с последующим нулевым продолжением. Для \(R_m=\mathcal E\mathscr R_m\) на этом окне имеем точно
\[
F_m=S_m+R_m,\qquad
\mathbf t_m:=\operatorname{coeff}(T_mR_m)=\mathbf a_m-\mathbf d_m,
\quad \mathbf d_m:=\operatorname{coeff}(T_mS_m).
\tag{Q4}
\]
Здесь \(\mathbf t_m\) — **остаток коэффициентной строки**, не spectral residual \((K_j-a_jI)q_j\).

### 3.3. Край не позволяет заменить проекцию производной умножением

**[FINITE_CELL | PAPER]** Пусть
\[
\mathbf b_m(n)=\frac{(-1)^n}{\sqrt L}\int_{-b}^{b}G(t)e^{-i\omega_nt}\,dt.
\]
Дважды интегрируя по частям, используя чётность \(G\), получаем
\[
\boxed{
\operatorname{coeff}(T_mG'')(n)
=-\omega_n^2\mathbf b_m(n)+\frac{2G'(b)}{\sqrt L}.
}
\tag{Q5}
\]
Поэтому остаток в (Q4) полностью раскрыт формулами (F2), (F5) и
\[
\boxed{
\mathbf t_m(n)=\mathbf a_m(n)
-\left(1+\frac{\omega_n^2-15/4}{16\pi m}\right)\mathbf b_m(n)
+\frac{G'(b)}{8\pi m\sqrt L}.
}
\tag{Q6}
\]

Контроль ошибочного коммутирования уже на \(n=0\): настоящий коэффициент \(T_mG''\) равен \(2G'(b)/\sqrt L\), а не нулю. Более того, \(G'(b)>0\) при \(m\ge2\): в его гауссовой сумме стоит
\((60v-120v^2+32v^3)e^{-v}\) при \(v=\pi r^2m>6\), и каждое слагаемое положительно.

**[COFINAL_FAMILY | PAPER]** На крайней моде
\[
\frac{\omega_m^2}{16\pi m}=\frac{\pi m}{4(\log m)^2}\longrightarrow\infty.
\tag{Q7}
\]
Это не доказательство роста самой строки: \(\mathbf b_m(n)\) мала. Но это прямое предупреждение против использования низкочастотного разложения по \(1/m\) как равномерной относительной асимптотики по всем \(|n|\le m\). Такая равномерность **не вытекает** из hmode.

### 3.4. Буквальное раскрытие p и ell

**[FINITE_CELL | PAPER]** Возьмём матрицу из двух столбцов
\[
\mathbb B_m=\bigl[\operatorname{coeff}(T_mG),\operatorname{coeff}(T_mG'')\bigr],
\quad M_m=\mathbb B_m^*\mathbb B_m,
\quad \Pi_m^U=\mathbb B_mM_m^{-1}\mathbb B_m^*.
\]
На уже принятом хвосте \(M_m\) обратима; её образ — **тот же** \(U_j\), не новая плоскость. Поскольку \(\mathbf d_m\in U_j\),
\[
\boxed{
p_j=\frac{\sigma_m}{\rho_m}\left(\mathbf d_m+\Pi_m^U\mathbf t_m\right),\qquad
\ell_j=\frac{\sigma_m}{\rho_m}(I-\Pi_m^U)\mathbf t_m.
}
\tag{Q8}
\]
Это и есть раскрытие выбранной утечки: \(\mathbf t_m\) дана непосредственно через Ferrers-коэффициенты в (F2), (F5), (Q6). **Ни \(\ell_j=O(m^{-2})\), ни знак её энергии из (Q8) не заявляются.**

## 4. Совместное сокращение полной формы и E

### 4.1. Вычитается глобальный радикал, а не «ядро конечной матрицы»

**[ABSTRACT | PAPER]** Используется уже независимо проверенное
\[
\mathcal W(G,f)=\mathcal W(G'',f)=0
\]
для конечных оконных синтезов. Это следует из \(\widehat G(z)=-4\xi_\zeta(1/2-iz)\), зануления во всех нетривиальных нулях и полной явной формулы, без RH. Тем же предельным переходом с гладкими cutoff-функциями равенство распространяется на сумму такого синтеза и элемента \(\mathcal N\): все глобальные шаблоны сверхэкспоненциально убывают. fileciteturn28file0L2-L2

Пусть \(f_c=\sum_n c(n)\psi_{n,L}\). Определим **единственные подъёмы** \(P_m^\circ,Z_m^\circ\in\mathcal N\), удовлетворяющие
\[
T_mP_m^\circ=f_{p_j},\qquad T_mZ_m^\circ=f_{z_j}.
\]
Например,
\[
Z_m^\circ=(G,G'')M_m^{-1}\mathbb B_m^*z_j;
\]
для \(P_m^\circ\) та же формула с \(p_j\). Определим ошибки
\[
\delta_p=f_{p_j}-P_m^\circ,\quad
\delta_z=f_{z_j}-Z_m^\circ,\quad
\delta_q=f_{q_j}-\frac{\sigma_mS_m}{\rho_m}.
\]
Последняя вычисляется из настоящего остатка:
\[
\boxed{
\delta_q=\frac{\sigma_m}{\rho_m}v_m,\qquad
v_m=T_mR_m+(T_m-I)S_m=f_{\mathbf a_m}-S_m.
}
\tag{D1}
\]
В этой записи нигде не требуется объявлять глобальную \(\mathcal E H_m\) допустимым аргументом формы: \(v_m\) — конечный синтез минус гладкий убывающий шаблон.

### 4.2. E удержан со знаками и сокращается точно

**[FINITE_CELL | PAPER]** Разность \(f_{\ell_j}-(\delta_q-\delta_p)\) лежит в \(\mathcal N\). Поэтому полная форма даёт
\[
\boxed{\ell_j^*K_j\ell_j=\mathcal W(\delta_q-\delta_p,\delta_q-\delta_p),}
\tag{D2}
\]
\[
\boxed{
E_j=\mathcal W(\delta_z,\delta_z)
+\mathcal W(\delta_p,\delta_p)
-2\operatorname{Re}\mathcal W(\delta_q,\delta_p).
}
\tag{D3}
\]
Подстановка в \(-\ell_j^*K_j\ell_j+E_j\) сокращает **ровно**
\(\mathcal W(\delta_p,\delta_p)\) и смешанный член. Получаем
\[
\boxed{
\tau_j=\mathcal W(\delta_z,\delta_z)-\mathcal W(\delta_q,\delta_q)
=\mathcal W(\delta_z,\delta_z)-\rho_m^{-2}\mathcal W(v_m,v_m).
}
\tag{D4}
\]

**Это причина не заменять \(E_j\) на \(\pm3\varepsilon_j\) до раскрытия.** Два его члена точно компенсируют соответствующие члены энергии утечки. При этом ни одна из оставшихся двух энергий не объявлена положительной.

## 5. Полный W02–WR–Prime ledger после сокращения

**[FINITE_CELL | PAPER]** Исходная матрица по-прежнему полная `ccmWeilTauN1`: отдельная диагональная ветвь, архимедова константа, интеграл и все \(2\le k\le m\) с весом \(\Lambda(k)/\sqrt{k}\). fileciteturn26file0L2-L2

Чтобы не повторить ошибку с отброшенными членами **в новом представлении**, положим
\[
Q_f(x)=\int_{\mathbb R}\overline{f(t)}f(t+x)\,dt
+\int_{\mathbb R}\overline{f(t)}f(t-x)\,dt,
\]
\[
\Omega_m(x)=Q_{v_m}(x)-\rho_m^2Q_{\delta_z}(x),\qquad
\mathfrak L_m=\mathcal W(v_m,v_m)-\rho_m^2\mathcal W(\delta_z,\delta_z).
\]
Тогда **полное**, не компонентное выражение имеет вид
\[
\boxed{
\begin{aligned}
\mathfrak L_m={}&\int_0^\infty 2\cosh(x/2)\,\Omega_m(x)\,dx\\
&-\frac{\gamma+\log(4\pi)}2\Omega_m(0)\\
&-\int_0^\infty
\frac{e^{x/2}\Omega_m(x)-\Omega_m(0)}{e^x-e^{-x}}\,dx\\
&-\sum_{k=2}^{\infty}\frac{\Lambda(k)}{\sqrt{k}}\Omega_m(\log k).
\end{aligned}
}
\tag{W1}
\]
Это применение полной формы Вейля к допустимым ошибкам, согласованное с CCM §§3–4 и источниковыми формулами; не условие её положительности. citeturn363458view0

Здесь особенно важны четыре проверки.

**Диагональ.** В отличие от старой разности форм двух единичных конечных векторов,
\[
\Omega_m(0)=2\bigl(\|v_m\|_2^2-\rho_m^2\|\delta_z\|_2^2\bigr)
\]
вообще не равна нулю. Поэтому **архимедова константа и вычитание \(\Omega_m(0)\) обязательны**. Нормировки ошибок нельзя наследовать от нормировок \(q_j,z_j\).

**Нижний край архимедова интеграла.** Ошибки имеют ровно те скачки на концах окна, которые вносит конечный синтез; вычитание гладкого глобального шаблона их не убирает. Отсюда
\[
\Omega_m'(0+)=-\frac2L\left(
\left|\sum_n\mathbf a_m(n)\right|^2
-\rho_m^2\left|\sum_n z_j(n)\right|^2\right).
\tag{W2}
\]
Таким образом, предел дроби в (W1) при \(x\downarrow0\) равен
\(\tfrac12\Omega_m'(0+)+\tfrac14\Omega_m(0)\); скрытой неинтегрируемой сингулярности нет.

**Prime powers и верхний край.** После вычитания глобальных шаблонов ошибки уже не компактно поддержаны: снаружи окна \(v_m=-S_m\), \(\delta_z=-Z_m^\circ\). Поэтому \(\Omega_m(L)\) не объявляется нулём, а prime powers \(k>m\) **возвращаются** в (W1). Они не являются новой частью матрицы: это члены точного изменения представления, оплаченные глобальным радикальным тождеством. Повторно усечь их на \(m\) нельзя.

**Абсолютная сходимость возвращённого хвоста.** При любом фиксированном \(m\) и \(A>1/2\) положим
\[
M_A=\|e^{A|t|}v_m\|_2^2+\rho_m^2\|e^{A|t|}\delta_z\|_2^2<\infty.
\]
Взвешенный Коши–Буняковский даёт
\[
|\Omega_m(x)|\le2M_Ae^{-A|x|},\qquad
\sum_{k>m}\frac{\Lambda(k)}{\sqrt{k}}|\Omega_m(\log k)|
\le2M_A\sum_{k>m}\frac{\log k}{k^{A+1/2}}<\infty.
\tag{W3}
\]
Эта оценка подтверждает допустимость всех операций. **Она не выдается за малую относительно \(\tau_j\) кофинальную ошибку**: \(M_A\) зависит от \(m\).

Таким образом, prime/archimedean cancellation использована только как **полное радикальное тождество**, а не как отдельное зануление W02, WR или Prime. В частности, физическая нулевая масса \(c_{m,0}=0\) не означает, что W02 конечной Fourier-проекции равен нулю.

## 6. Первый оставшийся знак — с уже раскрытым источником

**[COFINAL_FAMILY | PAPER]** После (F2), (F5), (Q6), (Q8) и совместного сокращения (D2)–(D3) остаётся
\[
\boxed{
\mathfrak L_{m_j}
=\mathcal W\bigl(T_mR_m+(T_m-I)S_m,\ T_mR_m+(T_m-I)S_m\bigr)
-\rho_m^2\mathcal W(\delta_z,\delta_z),\qquad
\tau_j=-\frac{\mathfrak L_{m_j}}{\rho_m^2}.
}
\tag{SIGN}
\]
Здесь \(R_m\) — **именно** остаток (Q3) выбранных Ferrers-мод; его вся конечная строка дана (Q6). Смешанные члены между \(T_mR_m\) и \((T_m-I)S_m\) остаются внутри первой формы и не расщепляются по модулю.

**Не доказано**, что \(\mathfrak L_{m_j}\ge0\) на неограниченной подпоследовательности. **Не доказано**, что \(\mathfrak L_{m_j}<0\) eventually с количественным верхним барьером. Поэтому ни один из двух знаковых исходов не следует.

Это уже не предложение оценить энергию произвольной малой утечки. Неизвестная величина привязана к конкретным сгруппированным Ferrers–Mellin-моментам, точному граничному члену и совместной энергии ошибок. Но **источниковой знаковой асимптотики этого остатка я не получил**.

### Сильнейшая атака на данный ход

Фраза «поправка \(1/m\) в плоскости, значит утечка \(O(m^{-2})\)» была бы необоснованной. Она требует контроля \(e_{n,m}\), переноса через \(\mathcal E\), нормировки и Fourier-проекции на всём растущем carrier. (Q7) показывает, почему локальное или фиксированно-частотное разложение этого не заменяет. Вторая опасность — перенести старое сокращение диагональной константы в (W1), где нормы уже разные. Ни один из этих переходов здесь не используется.

## 7. Один следующий проверяемый PAPER-тест

**`TEST_SELECTED_FERRERS_COUPLED_DEFECT_SIGN`**

Объект теста — \(\mathfrak L_m\) из (SIGN), вычисляемый по (F2), (F5), (Q6), а не по оценке \(3\varepsilon_m\). Требуется **одна равномерная знаковая оценка совместного остатка** на сетке
\[
m=J_P+j+2,\qquad s_n=\frac12-\frac{2\pi in}{\log m},\qquad -m\le n\le m.
\]

Конкретный сертификат теста:
\[
\boxed{
\mathfrak L_m=T(m)+\mathcal R(m),\qquad
\underline R(m)\le\mathcal R(m)\le\overline R(m),
}
\tag{TEST}
\]
где \(T,\underline R,\overline R\) получены **из сгруппированных моментов (F5)** и полного совместного ledger (W1). Остаточный бюджет должен сохранять смешанный член в (D1), оба края, диагональную константу и возвращённый бесконечный prime-хвост. Геометрический Ferrers-tail разрешено использовать как оценку оставшихся коэффициентов, но не как новую конечную модель источника.

Направления сертификата фиксированы заранее:

* \(T(m)+\underline R(m)>0\) на доказанно неограниченных выбранных индексах даёт \(\tau_j<0\) и **KILL_NULLPLANE** с тем же \(z_j\).
* \(T(m)+\overline R(m)<0\) на всём выбранном хвосте даёт **POSITIVE_NULLPLANE** и явную нижнюю функцию \(-[T(m)+\overline R(m)]/\rho_m^2\). Schur-блок этим не закрывается.
* Если интервал содержит ноль, тест не завершён. Точное равенство нулю требует отдельного тождества; сетка, округление или малый модуль его не доказывают.

Это один тест, с двумя допустимыми знаковыми исходами. **Следующее действие не состоит в доказательстве ещё одного norm-only wrapper или вычислении нескольких конечных спектров.**

### Два представления для этого же теста

| Представление | Что способно решить | Цена и риск |
|---|---|---|
| **Выбрано: Ferrers–Mellin-моменты + совместные ошибки (F5), (D1), (W1).** | Один кофинальный знаковый сертификат отвергает или подтверждает первый скалярный знак сразу на семье. | Одна равномерная оценка сгруппированного остатка и один полный знаковый бюджет. Главный риск — неравномерность на \(|n|\asymp m\). |
| **Альтернатива: явная формула на стороне комплексных нулей для тех же ошибок.** | Может обнаружить точное дополнительное зануление или знаковую структуру всей суммы. | Дороже: необходимо контролировать все сопряжённые/отражённые пары нулей без RH; нельзя заменить их вклады квадратами модулей на вещественной оси. |

Второй вариант не является второй директивой и не разрешает внешнюю нумерическую подмену. Выбран первый.

## 8. Closeout и граница результата

**[ABSTRACT | PAPER]** Проверка, объявленная до разбора явной поправки, различила ненулевую новую компоненту и попадание в прежнюю плоскость: получено второе, по (Q1)–(Q2). Знаковая ставка KILL/POSITIVE до этого не заявлялась; точность такой ставки задним числом не приписывается. Объявленная перед итоговой проверкой ledger ставка подтвердилась: после вычитания радикала возвращаются и диагональная константа, и prime powers за \(m\).

**Что стало конкретнее:** выбранная строка раскрыта через (F2), (F5); её остаток после точного in-plane-шаблона — через (Q6); \(p_j,\ell_j\) — через (Q8); полное \(E_j\) сокращено со знаками в (D2)–(D4).

**Что не закрыто:** первый знак (SIGN), eventual cellwise complement positivity и Schur-floor. Никакой новый положительный floor, предел \(a_j\) или residual ratio не поставлен.

**Что нельзя повторять:** выводить знак из нормовой малости; объявлять \(T_mG''=-\omega^2T_mG\) без граничного члена; превращать квазимодный шаблон в равномерную асимптотику выбранной строки; удалять новые диагональные и prime-хвостовые члены после смены представления.

```yaml
DOWNSTREAM_CONSUMER: first_scalar_gate_for_the_unchanged_cellwise_complement
ACTUAL_CONSUMER_REQUIREMENT: eventual_tau_positive_before_any_Schur_floor_claim
ORIGINAL_REQUESTED_OBJECT: signed_asymptotic_of_the_literal_selected_tau
ORIGINAL_OBJECT_IS: UNKNOWN
QUALIFICATION: tau_positive_is_necessary_but_this_asymptotic_representation_is_not_shown_necessary
KNOWN_WEAKER_INTERFACES:
  - unbounded_selected_tau_nonpositive_refutes_eventual_d_positive
  - a_signed_joint_defect_envelope_can_decide_tau_without_a_separate_leakage_floor
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
MINIMAL_MISSING_SIGN: signed_cofinal_envelope_for_mathfrak_L_in_SIGN
REOPEN_TRIGGER: full_source_one_sided_bound_separating_mathfrak_L_from_zero_or_exact_zero_identity
NOVELTY_AXIS: selected_Ferrers_moments_and_in_plane_quasimode_subtraction_and_joint_Weil_defect_cancellation
REQUESTED_SIGN_OR_FLOOR_THEOREM_SHAPE_KILLED: NONE
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
MEMORY_ENTRY:
  target: selected_nullplane_tau_sign
  status: OPEN
  invariant_learned: radical_subtraction_preserves_full_form_not_its_separate_components
  forbidden_future_move: discard_E_cancellations_or_reuse_unit_norm_diagonal_cancellation_for_errors
  next_decisive_test: TEST_SELECTED_FERRERS_COUPLED_DEFECT_SIGN
```

**Единственный итог: OPEN_SIGNED_LEAKAGE.** Это PAPER-раскрытие источника и сокращений, не сертификат знака. Lean, символьные/численные прогоны и проектный runtime не запускались; репозиторий и route-state не изменялись. Создан только Markdown-файл ответа.
