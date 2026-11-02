# STATUS: TRY_RADICAL_LEAKAGE_WITH_CONCENTRATION_SCOPE_GUARD
```yaml
OPERATIVE_CLASS: TRY_RADICAL_LEAKAGE_WITH_CONCENTRATION_SCOPE_GUARD
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_RADICAL_CONCENTRATION_AND_LOW_CLUSTER_REQUEST
SOURCE_REPOSITORY: Malaeu/chen_q3
SOURCE_BRANCH: rh_clean
SOURCE_COMMIT: 167dff63a632f170fed2d01d88af61268ad0af7f
SOURCE_RESULT_PATH: docs/routeB_bus/lowcluster_2026-11-02/ladder_limit/identify/RESULT.md
SOURCE_RESULT_GIT_BLOB: 51df067c78059b111acdcdb9407064c357056ac2
SOURCE_NOESCAPE_GIT_BLOB: 453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc
SOURCE_NOESCAPE_SHA256: fdfd384345b69d7565100b93ef57348eb6944bdbaf014a01c001df007129aded
SOURCE_CONFINE_GIT_BLOB: 1879347b72d1aa55cf506f5387de37059f929122
SOURCE_CONFINE_SHA256: 57088a914942b0dd1c3d1835edaca2f223a59831d78350c0a092356024852ddb
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: EXACT_SIGNED_LEAKAGE_IDENTITY_AND_SCOPED_CONCENTRATION_OBSTRUCTION
CARRIER: LITERAL_CCM_REAL_EVEN_N_EQUALS_M_L_EQUALS_LOG_M
SHARP_WINDOW_SIGNED_LEAKAGE_IDENTITY: EXACT_NO_REMAINDER
FINITE_FOURIER_RETURN: EXACT_MIXED_REMAINDER_WITH_EXPLICIT_BOUND
UNRESTRICTED_RADICAL_PROJECTS_ONTO: ENTIRE_FINITE_EVEN_CARRIER
UNRESTRICTED_RADICAL_L2_CONCENTRATION_SUPREMUM: ONE_NOT_ATTAINED
SIGNED_LEAKAGE_QUOTIENT: EXACTLY_ISOSPECTRAL_TO_FULL_A_M_NOT_ONLY_BOTTOM
REQUESTED_LIMITING_CLUSTER_IDENTIFICATION: NOT_PROVED
ACTUAL_LITERAL_CLUSTER_CONVERGENCE_REFUTED: false
SCOPED_REFUTATION: UNRESTRICTED_L2_CONCENTRATION_HAS_DISTINGUISHED_EXTREMIZERS
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: DENSITY_JENSEN_ZERO_COUNT_AND_EXACT_LIFT_THEOREM
FAILURE_TYPE: COUNTEREXAMPLE_AND_MISSING_SPECTRAL_COMPARISON
EPISTEMIC_STATUS: RESEARCH_DEBT_FOR_REGULARIZED_CLUSTER_THEOREM
VERIFIER: PAPER
PROGRESS_CLASS: FALSIFICATION_PROGRESS
ADDITIONAL_PROGRESS: EXACT_LEAKAGE_AND_FINITE_RETURN_BUDGET
COGNITIVE_OPERATOR: UNIT_AUDIT
EXACT_ALGEBRA_GROUPS_PASSED: 8
NEW_CCM_NUMERICAL_SCAN: false
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_ASSUMED: false
RH_PROVED: false
ROUTE_PROMOTION: false
```

## 0. Результат

Первая часть имеет точный смысл и доказывается: для допустимого глобального радикального профиля энергия его обрезки равна **полной знаковой Weil-энергии** удалённой части. Для жёсткой пространственной обрезки остаток равен нулю. Для буквального конечного CCM имеется дополнительная Fourier-утечка; её смешанный член и явный бюджет приведены ниже.

Вторая часть в заявленном неограниченном классе не становится теоремой концентрации. При естественной физической L²-нормировке супремум концентрации на любом фиксированном окне равен 1, но ни один ненулевой радикальный профиль его не достигает. Если вместо L²-утечки взять знаковую Weil-энергию и правильную внутреннюю метрику, получается точная копия **всей** матрицы A_m, а не независимый механизм выбора нижнего кластера.

Это не опровержение возможной предельной лестницы настоящего CCM. Опровергнута только попытка получить её как экстремали обычной концентрации на всём классе `H*g`, без ограничения g, без дополнительной нормы и без спектрального сравнения.

## 1. Источники, данные и область проверки

**[FINITE_CELL | PAPER; provenance, не сертификация чисел.]**

S1: `docs/routeB_bus/lowcluster_2026-11-02/ladder_limit/identify/RESULT.md`, прочитан целиком на SOURCE_COMMIT, blob указан в header. Файл помечен `DIAGNOSTIC_NEVER_A_PROOF`. Его число около 8.5e-14 — максимум **нормированных** величин `|Phi(gamma_k)|/max_t|Phi(t)|` при m=24, а не заявленная универсальная абсолютная оценка. Проверено десять нулей, восемь eigenprofiles и один least-ladder профиль. В самом отчёте зафиксированы ненулевые остатки, численные полюсы Phi/H и отсутствие доказанной предельной функции. Небольшие остатки не объявляются точными нулями.

S2: `docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md`, §1 и L1–L4 на том же pin. Локальные 64077 bytes / 1084 LF дают SHA-256 и Git blob из header, совпадающий с GitHub. Используются: полная форма, исходный carrier, fixed-jet residual, растущий near-zero count и сильная резольвентная сходимость к нулю. Нового независимого аудита этих поставщиков нет.

S3: `docs/routeB_bus/proshka/PROSHKA_VERDICT_CONFINE_2026-10-30.md`, §§1–2 на том же pin, явно цитируемый в S2 поставщик. Локальные 73080 bytes / 1266 LF совпадают с указанными SHA-256 и blob. Плотность всех чётных theta-производных и конечномерная сюръективность уже доказаны в S3 (2.1), (2.3): ниже они **наследуются, а не выдаются за новое открытие**.

E1: K. Kedlaya, *Notes on analytic number theory*, Chapter 9, Remark 9.7: безусловная формула счёта всех нетривиальных нулей с кратностями,
`N(T)=T/(2*pi)*log(T/(2*pi))-T/(2*pi)+O(log T)`.
https://kskedlaya.org/ant/chap-von-mangoldt.html
Используется только для запрета компактно поддержанного ненулевого Fourier-образа, делящегося на H. Никакая RH или новая область без нулей не импортируется. Остальной Jensen-аргумент доказан ниже.

Протокол получен через GitHub с rh_clean, включая конец. Управляющая задача — текущая прямая команда владельца. Новая математика здесь имеет уровень PAPER. Отдельный проверяющий не запускался.

## 2. Два разных проектора и допустимый радикал

**[ABSTRACT | PAPER; definitions.]** Работаем с вещественными чётными функциями. Пусть
\[
H(z)=4\xi(1/2-iz),\quad \widehat f(z)=\int f(x)e^{-izx}\,dx,
\quad b=L/2,\quad \chi_L=\mathbf1_{[-b,b]}.
\]
Пространственная проекция обозначается `chi_L`; конечная Fourier-проекция — `P_m`, всегда при `N=m,L=log m`. Они не отождествляются.

Обозначим через S_exp гладкие функции, все производные которых имеют любые фиксированные экспоненциально взвешенные L²-нормы. Безопасная область радикального тождества:
\[
\mathcal R_{\rm adm}=
\{r\in\mathcal S_{\exp}\cap L^2_E:
\widehat r=H g,\ g\text{ целая}\}.
\tag{2.1}
\]
Она содержит
\[
\mathcal R_{\rm pol}=\operatorname{span}_{\mathbb R}
\{h,h'',h^{(4)},\ldots\}.
\]
Условие «g целая» само по себе не задаёт область полной Weil-формы: нужны интегрируемость и допустимость её смешанных членов. Нельзя автоматически применить форму к произвольному целому множителю. Все отрицательные выводы о концентрации ниже верны уже на R_pol; запрет компактной поддержки верен и на более широком L²-классе с целым отношением.

Полная неизменённая форма на чётных функциях:
\[
\mathfrak k(u,v)=-c_*\langle u,v\rangle
+\int_0^\infty j(s)[2\langle u,v\rangle-Q_{u,v}(s)]ds
-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}Q_{u,v}(\log n)
+\langle p,u\rangle\langle p,v\rangle,
\tag{2.2}
\]
\[
j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad
c_*=\gamma+\log(8\pi)+\pi/2,\quad
p(x)=\sqrt2\cosh(x/2),
\]
\[
Q_{u,v}(s)=\int u(x)[v(x+s)+v(x-s)]dx.
\]
Нечётный полюс равен нулю по чётности, не вследствие удаления из источника. Все prime powers сохранены. Внешняя часть поддержана на двух неограниченных лучах, поэтому её prime-сумма **не обрывается при n=m**.

Для обоснования всех смешанных переходов положим
\[
\mathcal A[u]=\int_0^\infty j(s)\|u-T_su\|_2^2ds,
\quad T_1(u)=\|e^{|x|}u\|_2,
\quad \mathcal P(u)=\int p(x)|u(x)|dx.
\]
Тогда
\[
\boxed{|\mathfrak k(u,v)|\le
c_*\|u\|_2\|v\|_2+\sqrt{\mathcal A[u]\mathcal A[v]}
+32T_1(u)T_1(v)+\mathcal P(u)\mathcal P(v).}
\tag{2.3}
\]
Здесь `|Q_(u,v)(s)|<=2e^{-s}T1(u)T1(v)` и
`sum Lambda(n)n^(-3/2)<=16`, поскольку `Lambda<=log`, `log n<=4n^(1/4)` и `sum_(n>=2)n^(-5/4)<=4`. Архимедова строка контролируется Cauchy–Schwarz в пространстве сдвигов.

У r из (2.1) и его обрезок все величины (2.3) конечны. Граничные скачки допускаются логарифмической формой. Моллификация и отсечение дальнего хвоста сходятся в этой контролирующей норме. Явная формула S3 сначала даёт `k(r,v)=0` на гладких допустимых тестах, поскольку H зануляется во всех её нулях с кратностями, затем (2.3) продолжает равенство на используемые обрезки. Здесь не утверждается глобальная L²-непрерывность формы.

## 3. Точная энергия пространственной утечки

### Теорема 1. У жёсткой обрезки остаток равен нулю

**[ABSTRACT | PAPER; every L>0, every admissible pair.]** Пусть `r,s in R_adm` и
\[
t_r=(1-\chi_L)r,\qquad t_s=(1-\chi_L)s.
\]
Тогда
\[
\boxed{\mathfrak k_L(\chi_Lr,\chi_Ls)=\mathfrak k(t_r,t_s).}
\tag{3.1}
\]
В частности,
\[
\boxed{\mathfrak k_L[\chi_Lr]=\mathfrak k[(1-\chi_L)r].}
\tag{3.2}
\]

**Доказательство.** Разложить `chi r=r-t_r`, `chi s=s-t_s`. Три члена `k(r,s)`, `k(r,t_s)`, `k(t_r,s)` равны нулю по полной билинейной радикальности. Остаётся `k(t_r,t_s)`. Допустимость всех спариваний установлена (2.3). ∎

Правая часть — именно (2.2) на t: архимедова энергия, минус все простые степени, плюс чётный полюс, минус c*||t||². Это **не** `||(1-chi)r||²` и не сумма заведомо положительных граничных вкладов. Положительность полной Weil-формы не импортируется.

## 4. Буквальный N=m: Fourier-утечка и её явный остаток

### Теорема 2. Точное разложение конечной формы

**[FINITE_CELL | PAPER.]** При `L=log m`, положим
\[
u=P_mr,\quad q_m=\chi_Lr-P_mr,\quad t=(1-\chi_L)r.
\]
Тогда
\[
\boxed{\langle u,A_mu\rangle=\mathfrak k[t+q_m]
=\mathfrak k[t]+R_m(r),}
\tag{4.1}
\]
\[
\boxed{R_m(r)=2\mathfrak k(t,q_m)+\mathfrak k_L[q_m].}
\tag{4.2}
\]
Это также следует непосредственно из `r=u+(t+q_m)` и радикальности. Поляризация даёт соответствующее матричное тождество. Смешанный член не удаляется.

### Явный конечный budget

Пусть
\[
B_{r,L}=2|r'(b)|+\int_{-b}^{b}|r''(x)|dx,
\]
\[
e_0=\frac{B_{r,L}L^{3/2}}{\sqrt{24}\pi^2m^{3/2}},\quad
e_1=\frac{B_{r,L}\sqrt L}{\sqrt2\pi\sqrt m},\quad
e_\infty=\frac{B_{r,L}L}{2\pi^2m}.
\tag{4.3}
\]
Тогда
\[
\|q_m\|_2\le e_0,\qquad
\|q'_{m,\rm int}\|_2\le e_1,\qquad
\|q_m\|_\infty\le e_\infty.
\tag{4.4}
\]
**Доказательство.** Дважды интегрируем коэффициент исходного фазированного базиса по частям. Первый граничный член нулевой, так как r(b)=r(-b). Для n!=0:
\[
|\langle\psi_{n,L},\chi_Lr\rangle|
\le\frac{B_{r,L}}{\sqrt L(2\pi n/L)^2}.
\]
Применяем Parseval и `sum_(n>m)n^(-4)<=1/(3m³)`, `sum n^(-2)<=1/m`; для sup-нормы суммируем модули обоих знаков n. Периодическая H¹-сходимость на окне законна, поскольку значения r на его концах совпадают. Нулевое продолжение не объявляется глобально H¹. ∎

Положим
\[
H_q=18e_1^2+10e_\infty^2,\quad
H_t=36\|r'\mathbf1_{I_L^c}\|_2^2+40|r(b)|^2,
\]
\[
S_L=\sum_{\log n<L}\frac{\Lambda(n)}{\sqrt n},\qquad
P_L=\|p\mathbf1_{I_L}\|_2=\sqrt{L+2\sinh(L/2)}.
\]
Имеем `A[q_m]<=H_q`, `A[t]<=H_t`. Действительно,
\[
\|q_m-T_sq_m\|_2^2\le s^2e_1^2+2se_\infty^2
\]
сохраняется также при s>L. Для t распределительная производная состоит из `r' 1_out` и двух концевых скачков, откуда
\[
\|t-T_st\|_2^2\le2s^2\|r'\mathbf1_{out}\|_2^2+8s|r(b)|^2.
\]
Использованы строгие elementary bounds `int s j(s)ds<=5`, `int s²j(s)ds<=18`.

Следовательно,
\[
\boxed{\begin{aligned}
|R_m(r)|\le\mathcal E_m(r):={}&H_q+
(c_*+2S_L+P_L^2)e_0^2\\
&+2\sqrt{H_tH_q}\\
&+2\big[c_*\|t\|_2+32e^bT_1(t)+P_L\mathcal P(t)\big]e_0.
\end{aligned}}
\tag{4.5}
\]
Все величины RHS — явные нормы и интегралы данного r, конечная полная prime-сумма и числовые константы. Бесконечный внешний prime-tail включён в 32T1(t)T1(q); он не отброшен. Это абсолютный бюджет **ошибки возврата**, а не замена целевого знакового спаривания.

### Произвольно высокие фиксированные порядки

Для `p=2J>=2` положим, при k=2,4,...,p,
\[
C_k=\frac{L^{k-1/2}}{(2\pi)^k}
\left(2|r^{(k-1)}(b)|+\mathbf1_{k=p}\|r^{(p)}\|_{L^1(I_L)}\right).
\]
Повторное интегрирование по частям даёт `|c_n|<=sum C_k|n|^{-k}` и допустимые замены в (4.5):
\[
e_0=\sqrt2\sum_k\frac{C_k m^{1/2-k}}{\sqrt{2k-1}},\quad
e_1=\frac{2\pi\sqrt2}{L}\sum_k\frac{C_k m^{3/2-k}}{\sqrt{2k-3}},\quad
e_\infty=\frac2{\sqrt L}\sum_k\frac{C_k m^{1-k}}{k-1}.
\tag{4.6}
\]
**[COFINAL_FAMILY | PAPER; fixed profile only.]** Для каждого заранее фиксированного r из R_adm, выбирая p достаточно большим, получаем `E_m(r)=O_(r,B)(m^-B)` при любом фиксированном B. Граничные производные r убывают быстрее любой фиксированной экспоненты по b; `L=log m` сохранено. Константы зависят от профиля и p. Подстановка произвольного меняющегося r_m без новых norm-budgets недопустима.

Ни (4.5), ни superpolynomial absolute remainder не дают автоматически `error=o(cluster gap)`. Последний может быть намного меньше всякой фиксированной степени m^-1.

## 5. Почему знаковая энергия утечки не является обычной концентрацией

### Теорема 3. Буквальный радикальный контртест положительной коэрцитивности

**[ABSTRACT | PAPER; actual theta function and actual Weil form.]** Зафиксируем L и положим
\[
r_a(x)=\frac{h(x-a)+h(x+a)}{\|h(\cdot-a)+h(\cdot+a)\|_2},\qquad a\to\infty.
\]
Это чётные единичные допустимые радикальные профили:
\[
\widehat r_a(z)=H(z)\frac{2\cos(az)}{\|h(\cdot-a)+h(\cdot+a)\|_2}.
\]
Знаменатель стремится к `sqrt2 ||h||>0`. На фиксированном I_L функции r_a и их внутренние производные равномерно стремятся к нулю. Поэтому (2.2) и оконный arch-budget дают
\[
\boxed{\mathfrak k[(1-\chi_L)r_a]
=\mathfrak k_L[\chi_Lr_a]\longrightarrow0,
\qquad\|(1-\chi_L)r_a\|_2^2\longrightarrow1.}
\tag{5.1}
\]
Отсюда не существует `c(L)>0` с
`k[(1-chi_L)r]>=c(L)||(1-chi_L)r||²` для всех r этого класса. Отрицательный знак энергии не требуется: числитель стремится к нулю независимо от знака. Контроль не является eigenvector-контрпримером к настоящему нижнему кластеру.

Он также показывает: даже **точные** нули Fourier-образа на всех нулях H не гарантируют tightness профилей. Здесь quotient целый для каждого a, но нормированные r_a слабо уходят в ноль.

## 6. Неограниченная L²-задача концентрации вырождена

### Теорема 4. Супремум равен 1, ненулевых экстремалей нет

**[ABSTRACT | PAPER; the inherited physical L² metric.]** Рассмотрим
\[
\mathcal C_L(r)=\frac{\|\chi_Lr\|_2^2}{\|r\|_2^2},\qquad r\ne0.
\tag{6.1}
\]
На R_pol, R_adm и на всём L²-классе с целым quotient Hg:
\[
\boxed{\sup\mathcal C_L=1,\quad\text{но максимум не достигается}.}
\tag{6.2}
\]

**Супремум.** S3 (2.1) даёт плотность R_pol в чётном L². Приблизим ненулевой чётный компактный тест внутри окна в L² радикальными полиномами. Их концентрационные отношения стремятся к 1.

**Недостижение на R_pol.** Конечная комбинация theta-производных аналитична в физической полосе. Если она равна нулю вне окна, принцип единственности заставляет её быть нулевой всюду.

**Недостижение на полном классе с целым g.** Предположим, что ненулевое r поддержано в [-b,b]. Его F=hat r — целая функция и
\[
|F(z)|\le\sqrt L\|r\|_2e^{b|\Im z|}.
\tag{6.3}
\]
Выберем z0 с F(z0)!=0. Формула Jensen на окружности радиуса 2R вокруг z0 даёт
\[
n_F(D(z_0,R))\log2\le2bR+O_{r,z_0}(1).
\]
Следовательно, число нулей F в большом диске равно O(R). Но `F=Hg`, g целая, сохраняет **все** нули H с кратностями; их число имеет порядок R log R по E1. Противоречие. Никакое расположение нулей на критической линии не предполагалось. ∎

Для каждого фиксированного k также
\[
\sup_{\substack{S\subset\mathcal R_{\rm pol}\\\dim S=k}}
\inf_{0\ne r\in S}\mathcal C_L(r)=1.
\tag{6.4}
\]
Для доказательства одновременно приблизим k ортонормированных чётных компактных тестов; их Gram-матрицы сходятся к I, а внешние Gram-матрицы к 0. Ни одно ненулевое конечномерное подпространство не достигает (6.4).

Замыкание радикала в этой норме есть весь L²_even. На замыкании concentration operator становится обычным умножением на chi_L: собственное значение 1 имеет бесконечную кратность. Это не выделяет упорядоченную радикальную лестницу. Если нужна другая Hilbert-норма на g или ограничение его роста, их надо задать явно; здесь они не подменяются догадкой.

## 7. Ещё сильнее: каждый конечный вектор имеет сколь угодно концентрированный радикальный подъём

### Теорема 5. Exact-lift degeneracy

**[FINITE_CELL | PAPER.]** Для каждого отдельного исходного m:
\[
P_m\mathcal R_{\rm pol}=V_{m,E}.
\tag{7.1}
\]
Это унаследованное S3 (2.3), не новый результат. Его дополнительное следствие:
для любого `v in V_(m,E)`, v!=0,
\[
\boxed{\inf_{\substack{r\in\mathcal R_{\rm pol}\\P_mr=v}}
\|r-v\|_2=0,\qquad
\inf_{P_mr=v}\|r\|_2=\|v\|_2,}
\tag{7.2}
\]
и инфимумы не достигаются.

**Доказательство.** Из (7.1) выберем линейное сечение `S:V_(m,E)->R_pol`, `P_m S=I`. Так как область конечномерна, его L²-норма конечна при этом фиксированном m. По плотности выберем `a_j in R_pol`, `a_j->v` в L² и положим
\[
r_j=a_j+S(v-P_ma_j).
\]
Тогда `P_mr_j=v` точно и
`||r_j-v||<=(1+||S||)||a_j-v||->0`. Пифагор даёт
`||r_j||²=||v||²+||r_j-v||²`. Достижение инфимума означало бы `r=v`, то есть ненулевой компактный радикал, запрещённый Теоремой 4. ∎

Таким образом, каждый возбуждённый eigenvector, любая линейная комбинация и любое иное направление carrier имеют такие же произвольно хорошие концентрационные подъёмы, как bottom. При этом для каждого подъёма точно
\[
\boxed{\mathfrak k[r_j-v]=\mathfrak k_L[v],}
\tag{7.3}
\]
несмотря на `||r_j-v||₂->0`. Это не противоречие: глобальная форма не непрерывна в L²; нормы производных и веса этих меняющихся r_j не ограничены. Подставить их в fixed-profile estimate (4.6) с общей константой нельзя.

### Теорема 6. Точная знаковая quotient-задача совпадает со всей A_m

**[FINITE_CELL | PAPER.]** На
\[
\mathcal Q_m=\mathcal R_{\rm pol}/\ker(P_m|_{\mathcal R_{\rm pol}})
\]
зададим
\[
G_m(r,s)=\langle P_mr,P_ms\rangle,\qquad
E_m(r,s)=\mathfrak k((1-P_m)r,(1-P_m)s).
\]
Обе формы корректны на quotient, G_m положительно определена, и
\[
\boxed{E_m(r,s)=\mathfrak k(P_mr,P_ms).}
\tag{7.4}
\]
Отображение `[r]->P_mr` является изометрическим изоморфизмом на V_(m,E). Поэтому весь generalized spectrum `(E_m,G_m)` точно равен спектру A_m.

**Доказательство.** (7.4) — поляризация (4.1) с полным остатком `r-P_mr`. Если P_mr=0, строка (7.4) нулевая против любого s, что даёт спуск на quotient. Сюръективность — (7.1), инъективность — определение quotient. ∎

Это самый сильный безусловный ответ для **знакового** значения слова «энергия утечки»: не асимптотическое, а точное совпадение на каждом m. Но оно относится ко всем уровням и использует всю исходную форму; не поставляет нового lower-bound и не доказывает сходимости собственных функций.

## 8. Что нужно для настоящей теоремы о кластере

**[ABSTRACT | CONDITIONAL; supplier obligations, not established for CCM.]** На фиксированном конечном джете r_1,...,r_d разные задачи имеют разные матрицы:
\[
G^{all}_{ij}=\langle r_i,r_j\rangle,\quad
G^{in}_{ij}=\langle\chi_Lr_i,\chi_Lr_j\rangle,\quad
T^{out}=G^{all}-G^{in},
\]
\[
E^{out}_{ij}=\mathfrak k((1-\chi_L)r_i,(1-\chi_L)r_j).
\]
Обычная концентрация решает `G_in c=kappa G_all c`. Weil–Ritz-задача решает `(E_out+R_m)c=lambda G_m c`, где `G_m=(<P_mr_i,P_mr_j>)`. Между E_out и T_out нет доказанной положительной функциональной зависимости. Нужно оплатить и её, и различие метрик. Равенство (3.1) само этого не делает.

### Точный условный projector bridge

Пусть Q_m — изометрический frame выбранного d-мерного projected radical space,
\[
T_m=Q_m^*A_mQ_m,\qquad \mathcal R_m=A_mQ_m-Q_mT_m.
\]
Пусть E_m — спектральный проектор **нужного** кластера A_m ранга d, и
\[
\operatorname{dist}(\operatorname{spec}T_m,
\operatorname{spec}(A_m|_{E_m^\perp}))\ge g_m>0.
\]
Тогда
\[
\boxed{\|(1-E_m)Q_m\|_{HS}\le\|\mathcal R_m\|_{HS}/g_m.}
\tag{8.1}
\]
**Доказательство.** Проецируем residual на E_m^perp и диагонализируем T_m и A_m на этом дополнении. Каждый матричный элемент `(1-E)Q` равен соответствующему residual-элементу, делённому на `lambda_i-theta_j`; модуль знаменателя не меньше g_m. Суммируем квадраты. ∎

При равных рангах `||(1-E)Q||->0` даёт сближение подпространств. Сходимость отдельных eigenvectors требует ещё внутреннего разделения уровней либо согласованного выбора базиса в кратном пределе. Нулевой предельный оператор сам такой выбор не делает.

L1–L2 S2 дают малый residual на каждом фиксированном джете. Они не дают g_m, равенство rank(E_m)=d или отсутствие дополнительных низких направлений. L3 говорит, что в любом фиксированном полиномиальном окне около нуля число уровней растёт. L4 даёт сильную резольвентную сходимость к нулю, но не нормовую сходимость изолированных нижних spectral projectors. Подменить один тип сходимости другим нельзя.

Источник S1 не задаёт ни норму предельного g, ни uniform lifting budget, ни масштаб отделения кластера. Его десять Fourier-тестов не проверяют делимость на H во всех комплексных нулях с кратностями и не проверяют compactness/tightness растущей семьи.

## 9. Решение по маршруту и один следующий локальный target

| Представление | Что реально проверять | Сила / цена |
|---|---|---|
| Ограниченный радикальный класс: фиксированная Hilbert-норма на множителях либо оплачиваемый конечный jet | Существование концентрационных экстремалей, сравнение E_out с выбранной положительной concentration form, цена Fourier-return относительно gap | Высокая для выбора профиля / высокая аналитическая; конечные Gram-тесты дешевле |
| Знаковый quotient и projected Ritz frame | Полный residual и separation/completeness в (8.1), без претензии на положительную L²-утечку | Высокая для cluster identification / средняя конечная, высокая кофинальная |

Три проверенных стыка: (a) стандартная Hilbert-задача концентрации не переносится на незамкнутый R с данной нормой; (b) vanishing identity даёт точный signed leakage (3.1), не positivity; (c) объект, который действительно закрыл бы cluster convergence, — устойчивый нормированный lift/frame с residual/gap->0 и оплаченной полнотой кластера. Такой объект не построен.

**Единственная CODEX DIRECTIVE — AUDIT_RADICAL_LEAKAGE_AND_CONCENTRATION_SCOPE.** Проверить (3.1), (4.1)–(4.6), (6.2), (7.2), (7.4) на закреплённом источнике. Не выполнять новый eigenvalue scan до определения метрики concentration task. Затем вернуть один явно нормированный candidate class и конкретный недостающий comparison/gap budget из §8. Успех аудита не означает доказанный кластер или RH.

## 10. Consumer-first ledger и closeout

**[COFINAL_FAMILY | CONDITIONAL; requested limiting consumer.]**
DOWNSTREAM_CONSUMER: rigorous identification of the literal even low cluster, potentially supporting NOESCAPE/RH.
ACTUAL_CONSUMER_REQUIREMENT: source-specific compactness and spectral-projector control, not only divisibility or small residual.
ORIGINAL_REQUESTED_OBJECT: unrestricted entire-multiplier concentration and eigenvector convergence.
ORIGINAL_OBJECT_IS: UNKNOWN as a necessary route; natural L² extremizer formulation is false.
KNOWN_WEAKER_INTERFACES: a restricted-class projector theorem (8.1); direct NOESCAPE remains a separate possible route.
FAILURE_TYPE: COUNTEREXAMPLE for unrestricted L² extremizers; NO_DERIVATION for the repaired source spectral comparison.
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD only for the exact unrestricted L²-extremizer theorem shape; RESEARCH_DEBT for restricted-class/true low-cluster convergence.
KILL_SCOPE: THEOREM_SHAPE, not ROUTE_FAMILY.
KILL_EVIDENCE: Theorems 3–5; inherited density plus Jensen and unconditional zero count.
REOPEN_TRIGGER: specify a proper norm/growth-restricted class and prove the necessary source comparison and quantitative cluster separation.
DISCRIMINATOR: a proposed concentration selector must distinguish arbitrary exact radical lifts of high carrier directions from bottom lifts, and must not confuse the escaping translates in (5.1) with localization.
NOVELTY_AXIS: exact lifting degeneracy and complete Fourier-return remainder, not a new RH equivalence.

Перед исполнением алгебраических тестов зарегистрированы: (P1) leakage expansion требует mixed-term; (P2) radicality не делает projected form положительной; (P3) full signed quotient сохраняет весь спектр. Все три подтверждены соответствующими точными algebra controls; общие кванторы обеспечены доказательствами выше. Старые численные прогнозы источника не переоцениваются.

Что стало точнее: знак и метрика «энергии утечки», отличие sharp-window от finite Fourier projection, отсутствие экстремалей у указанного неограниченного L²-класса. Что не доказано: источник-зависимая асимптотическая идентификация нижнего кластера, NOESCAPE, RH. Повторять запрещено: превращать `P_m R=V_m` в утверждение только о дне; менять знаковую Weil-утечку на L²-норму; считать абсолютный остаток малым относительно неизвестного gap; принимать десять почти-нулей за entire divisibility.

Результат не основан на новом CCM-прогоне. Восемь exact-algebra groups выполнены; это не независимый аналитический аудит и не Lean/Arb-сертификат. Код ниже проверяет указанные конечные тождества; абстрактные матрицы явно не выдаются за CCM.

## Appendix. Reproducible exact algebra checks

Run after extracting this fence to `radical_concentration_checks.py`:
`uv run --with sympy radical_concentration_checks.py`.

```python
#!/usr/bin/env python3
"""Exact algebra checks for the radical-concentration audit.
These checks do not certify CCM spectra, analytic limits, or RH.
Run: uv run --with sympy checks.py
"""
import sympy as s

# Registered before execution: identities must retain the Fourier return,
# signed tails need not be positive, and equal compression spectra alone
# must not identify a limiting concentration profile.
I = s.eye(4)
r = s.Matrix([1, 0, 0, 1])
J = I - r*r.T/(r.dot(r))
A = J*s.diag(1, -2, 3, 4)*J
chi = s.diag(1, 1, 1, 0)
v = s.Matrix([1, 1, 0, 0])
Pi = v*v.T/v.dot(v)
t = (I-chi)*r
q = (chi-Pi)*r
u = Pi*r
assert A*r == s.zeros(4, 1)
assert (r.T*chi*A*chi*r)[0] == (t.T*A*t)[0]
print('PASS 1 sharp-window signed leakage identity')
assert (u.T*A*u)[0] == ((t+q).T*A*(t+q))[0]
assert s.expand((u.T*A*u)[0] - (t.T*A*t)[0] - 2*(t.T*A*q)[0] - (q.T*A*q)[0]) == 0
print('PASS 2 full Fourier correction including mixed term')

# A radical vector does not by itself make its projected energy positive.
A2 = s.diag(0, 2, -3, 5)
r2 = s.Matrix([1, 0, 0, 0])
v2 = s.Matrix([1, 1, 1, 0]); P2 = v2*v2.T/v2.dot(v2)
assert ((P2*r2).T*A2*(P2*r2))[0] == -s.Rational(1, 9)
assert (((I-P2)*r2).T*A2*((I-P2)*r2))[0] == -s.Rational(1, 9)
print('PASS 3 signed-tail control is not a positivity theorem (abstract model)')

l = s.symbols('l')
C = s.Matrix([[2, 1], [1, -3]])
Y = s.Matrix([[1, 2], [0, 1]])
G = Y.T*Y; B = Y.T*C*Y
assert s.expand((B-l*G).det() - Y.det()**2*(C-l*s.eye(2)).det()) == 0
print('PASS 4 quotient generalized spectrum is unchanged')

x,L = s.symbols('x L', positive=True)
c1 = s.Rational(1, 2)**-2 + s.integrate((2*x+s.Rational(1, 2))**-2, (x,0,s.oo))
c2 = 2*(s.Rational(1, 2)**-3 + s.integrate((2*x+s.Rational(1, 2))**-3, (x,0,s.oo)))
assert c1 == 5 and c2 == 18
print('PASS 5 archimedean moment upper constants 5 and 18')

M,m = s.symbols('M m', positive=True)
coef = M*L**s.Rational(3,2)/(4*s.pi**2)
e0sq = 2*coef**2/(3*m**3)
e1sq = 2*(2*s.pi/L)**2*coef**2/m
einf = 2*coef/(s.sqrt(L)*m)
assert s.simplify(e0sq-M**2*L**3/(24*s.pi**4*m**3)) == 0
assert s.simplify(e1sq-M**2*L/(2*s.pi**2*m)) == 0
assert s.simplify(einf-M*L/(2*s.pi**2*m)) == 0
print('PASS 6 all-mode Fourier-return factors')

# Frozen small-dimensional obstruction to eigenvector selection.
eps = s.symbols('eps', positive=True)
A3 = s.diag(eps, eps, -1)
Q = s.Matrix([[1,0],[0,1],[0,0]])
assert A3*Q == eps*Q and s.Matrix([0,0,1]).dot(A3*s.Matrix([0,0,1])) == -1
print('PASS 7 near-null trial space does not capture the bottom (abstract model)')

# Finite zero tests impose only finite constraints on a multiplier.
z = s.symbols('z')
prod = s.prod(z*z-j*j for j in range(1, 11))
assert all(prod.subs(z,j)==0 and prod.subs(z,-j)==0 for j in range(1,11))
assert prod.subs(z,11) != 0
print('PASS 8 finite zero annihilation does not give whole-zero divisibility')
print('ALL 8 EXACT GROUPS PASSED')

```
