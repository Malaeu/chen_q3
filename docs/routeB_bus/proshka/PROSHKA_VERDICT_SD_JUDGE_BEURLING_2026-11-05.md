# STATUS: TRY_SD_JUDGE_BEURLING_WITH_COFINAL_NEGATIVE_WITNESS

```yaml
STATUS: TRY_SD_JUDGE_BEURLING_WITH_COFINAL_NEGATIVE_WITNESS
OPERATIVE_CLASS: TRY_SD_JUDGE_BEURLING_WITH_COFINAL_NEGATIVE_WITNESS
REQUEST: Q_SD_JUDGE
DATE: 2026-11-05
AUTHORITY: DIRECT_OWNER_PINNED_REQUEST_IN_CHAT
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: rh_clean@34af3956b5bb33620695a579e871aed909eacbe8
INPUT_INBOX: proshka_inbox_2026-10-31@f96a9072071c13011cc0fb4a6408e2214ed64181
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_SD_JUDGE_BEURLING_2026-11-05.md
ROUTE: CHALLENGER_NOT_RH
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ANSWER_TO_1: A
RH_PROVED: false
ZETA_SD_PROVED: false
DMV_FINITE_PHASE_AND_HARDY_TRANSFER: true
DMV_SD_ON_ANY_COFINAL_SUBSEQUENCE: false
DMV_GRAPH_BOTTOM_TENDS_TO_MINUS_INFINITY: true
DMV_COMPLETED_WEIL_IDENTITY_ASSUMED: false
DMV_DENSE_RADICAL_ASSUMED: false
CURVE_CONTROL: PASS_SAME_TRANSLATED_RESPONSE_LAPLACE_JUDGE
STEP_B_EXECUTED: false
VERIFIER: PAPER
SCOPE: [ABSTRACT, FINITE_CELL, COFINAL_FAMILY]
NUMERICAL_TESTS: NOT_RUN
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
KILLS:
  - id: DMV_COFINAL_SD_WITH_FIXED_SOBOLEV_BUDGET
    scope: THEOREM_SHAPE
    range: EVERY_FIXED_INTEGER_r_GE_0_AND_EVERY_COFINAL_INTEGER_SUBSEQUENCE
    evidence: SECTIONS_2_3_AND_2_4_NEGATIVE_UPPER_ENVELOPE
    failure_type: COUNTEREXAMPLE
  - id: NEUMANN_PARTIAL_SUM_IN_RB_7_1_IS_A_LOWER_SONIN_PROJECTOR
    scope: THEOREM_SHAPE
    evidence: SECTION_5_3_EXACT_Q0_POWER_AND_SCALAR_ONE_QUARTER
    failure_type: COUNTEREXAMPLE
  - id: POSITIVE_FULL_DIFFERENCE_FOR_LITERAL_FINITE_PHASE
    scope: THEOREM_SHAPE
    evidence: SECTION_6_3_GAMMA_POLES_AND_DISTINCT_ANALYTIC_OBJECTS
    failure_type: INCOMPATIBILITY
DOES_NOT_KILL:
  - SD_FOR_THE_ACTUAL_RATIONAL_PRIMES
  - THE_ORIGINAL_SIGNED_THETA_BOUND_DAGGER
  - FINITE_PHASE_TRACE_IDENTITIES
  - GROWING_S_SONIN_CHANNEL_WITH_A_PAID_FIXED_NEGATIVE_BUDGET
  - CORRECTLY_REGULARIZED_TRACE_COMMUTATOR_METHODS
MINIMAL_MISSING_IDENTITY: "For actual rational primes, the existing SD bound remains open. Its necessary radical calibration is limsup_k T_mk,infinity[S_mk z_mk^00(h)] / ||h||_H1^2 < infinity with the SAME constant for all admissible radical h. No new mandatory supplier is imposed."
DISCRIMINATOR: "DMV: one compact even two-packet f with zero mean and pole moments has a source Rayleigh upper below -C; its literal returns give liminf_R E_m,R below -C for every sufficiently large m. Actual Q: a rigorous lower bound for the Sonin trace minus the full source upper, divided by graph energy; a sparse DIAG trend is not a cofinal refutation."
REOPEN_TRIGGER: "A specific failure in the Laplace-pole argument or fixed-test return reopens the DMV conclusion. A valid uniform radical trace bound, or a cofinal lower divergence, changes the status of the actual-Q Sonin channel."
K8A:
  DOWNSTREAM_CONSUMER: ORIGINAL_DAGGER_FOR_LITERAL_A_m_THEN_RH
  ACTUAL_CONSUMER_REQUIREMENT: ONE_FIXED_UPPER_GRAPH_BUDGET_ON_Kcal_ALONG_A_COFINAL_FAMILY
  ORIGINAL_REQUESTED_OBJECT: NEGATIVE_JUDGE_FOR_SD_BEFORE_STEP_B
  ORIGINAL_OBJECT_IS: UNKNOWN_AS_NECESSARY_FOR_RH
  KNOWN_WEAKER_INTERFACES: "A direct bound for dagger or for the full A_m avoids the selected Sonin channel."
  FAILURE_TYPE: COUNTEREXAMPLE_FOR_DMV_NO_DERIVATION_FOR_ACTUAL_Q
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_DMV_SD_ONLY_RESEARCH_DEBT_FOR_ACTUAL_Q
  NOVELTY_AXIS: SOURCE_TRANSLATED_RESPONSE_AND_LAPLACE_POLE_WITHOUT_BEURLING_COMPLETION
  REOPEN_TRIGGER: EXPLICIT_ERROR_OR_NEW_SOURCE_SPECIFIC_UNIFORM_BOUND
CLOSES:
  - Q_SD_JUDGE_FINITE_BEURLING_TRANSFER
  - Q_SD_JUDGE_DMV_NEGATIVE_CONTROL_ON_ALL_SUBSEQUENCES
  - Q_SD_JUDGE_NEUMANN_BOUND_ORIENTATION
  - Q_SD_JUDGE_OLD_NEW_PROJECTION_PAIR_DICTIONARY
OPENS: []
PROGRESS_CLASS: FALSIFICATION_PROGRESS
RH_SIGN_PROGRESS: NONE
ROUTE_SCORE: 4
ROUTE_STATE_CHANGED: false
DELIVERY_COMMIT: REPORTED_IN_THE_DELIVERY_RECEIPT_AFTER_WRITE
```

Ы. **Исход (а).** Конечная фазовая/Hardy-конструкция переносится на выбранную дискретную систему DMV. Но её (SD) ложна на любой неограниченной подпоследовательности окон. Более сильно: нижний край самой оконной формы после любой фиксированной соболевской нормировки уходит в минус бесконечность по всем поздним целым m. Поскольку положительный Сонин-след неотрицателен, это даёт отрицательный верхний свидетель для самого дефекта.

Для этого не требуется приписывать DMV функциональное уравнение ζ, отражённое entire completion или плотный радикал. Судья использует только действительную исходную атомную меру, компактные сдвинутые функции и полюс логарифмической производной. Кривая из запроса проходит тот же Laplace-судья. (SD) для настоящей ℚ здесь не доказана и не опровергнута.

## 0. Прочитанные источники и границы импорта

[FINITE_CELL | PAPER: сверка pinned raw-текстов, не независимый аудит всех прежних результатов.]

| Ref | Путь / commit / blob | Использованные места |
|---|---|---|
| R_B | `docs/routeB_bus/proshka/PROSHKA_PLAN_SIGNED_THETA_TRACE_DEFECT_2026-11-04.md`; `f96a9072071c13011cc0fb4a6408e2214ed64181`; `25e58f845f4767908db41478210c1ac28dedf847` | (3.1)–(3.4), §§4–6, (7.1), (8.1), §10 |
| R_A | `docs/routeB_bus/proshka/PROSHKA_VERDICT_FROBENIUS_GLUING_Q_2026-11-04.md`; `d558268a`; `7cf72ea5ae3f3370eee05b9cc688887e10c37852` | §§5–7, особенно (7.2)–(7.7) и контроль E/F3 |
| S1 | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SEMILOCAL_SONIN_SECOND_EXPRESSION_2026-09-06.md`; `3242ada9`; `7b4e6562c358902eb1c7204b1fcded7a2ee6b91d` | Lemmas 1–4, 6–9; (6)–(12), (20)–(21) |
| S2 | `docs/routeB_bus/NEAR_NULL_PROBE_OF_THE_SONIN_FLOOR_2026-09-08.md`; `3fa61c11`; `0c5bf5d2f413603514e7c34c2b9c2d616299eb6d` | полный небольшой отчёт; DIAG |
| S3 | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_KERNEL_2026-09-08.md`; `a97ad1bf`; `d171a2fb7b6b917a1780656952b1db5458cc9a34` | K25, K27–K34 и границы fixed-S |
| S4 | `docs/routeB_bus/SEMILOCAL_SIGN_TABLE_COMPARISON_2026-09-06.md`; база запроса; `3fdbb26af50fb846bbe0a95742453b1004a6afb7` | фактический источник плато и ошибок дискретизации; DIAG |

R_B также прочитан в смонтированной полной копии: её Git-blob точно совпал с pin. Отчёт S4 найден по конкретной фразе о плато; очереди и посторонние задания не выбирались. Файлы вне `docs/routeB_bus/` не открывались.

**T1 — THEOREM.** H. Diamond, H. Montgomery, U. Vorhauer, *Beurling primes with large oscillation*, Math. Ann. 334 (2006), 1–36, DOI `10.1007/s00208-005-0638-2`, Theorem 1, printed p.4; определения p.2 и logarithmic derivative pp.3–4. Фиксируем θ=3/4 и a=1, удовлетворяющие a>(4/e)(1−θ). Берём реализацию дискретной конструкции §7, где для больших k сетка v_k=√log k. Все последующие отрицательные выводы верны для любой системы с перечисленными свойствами Theorem 1; численная таблица обобщённых простых здесь не строится.

Используются ровно: ψ_B(x)=O(x); мероморфность ζ_B при Re s>θ с единственным полюсом, простым в s=1; бесконечные нули ρ=β+iγ с β=1−1/log γ→1. Не нужны симметрия относительно 1/2, continuation слева от θ и полный нулевой ряд.

**T2 — THEOREM, с явно доказанным здесь расширением параметра.** A. Connes, C. Consani, *Quasi-inner functions and local factors*, arXiv:2008.10974v1: §3, Lemmas 3.3–3.5; §4.2, Theorem 4.4, pp.17–18; Lemmas 4.6–4.7 и Theorem 4.8, pp.20–22; Definition 5.2. Печатное утверждение относится к местам ℚ. Ниже проверяется, что аналитическое доказательство компактности сохраняется для каждого конечного списка действительных q>1. Это не утверждение о существовании мест ℚ_q.

**T3 — THEOREM, ограниченный импорт.** N. Feldman, *The Berger–Shaw Theorem for Cyclic Subnormal Operators*, Indiana Univ. Math. J. 46 (1997), pp.741–742, Introduction/Main Theorem: указанные там условия hyponormality/cyclicity существенны. Их выполнение для нашего Toeplitz-блока не импортируется.

Helton–Howe / Carey–Pincus рассматриваются как **CONJECTURAL BRIDGE** к нашему конкретному дефекту, не как sign supplier. Для проверки знака и формы предлагаемого Toeplitz-коммутатора ниже дан самостоятельный расчёт на окружности; он не требует импорта общей теоремы.

Первичные адреса:
```text
T1 https://deepblue.lib.umich.edu/bitstream/handle/2027.42/46253/208_2005_Article_638.pdf
T2 https://alainconnes.org/wp-content/uploads/quasi-inner.pdf
T3 https://feldman.academic.wlu.edu/files/pdffiles/BergerShaw.pdf
HH https://mathweb.ucsd.edu/~helton/BILLSPAPERSscanned/HHo75.pdf
CP https://doi.org/10.1073/pnas.71.5.1952
```
T1/T3 прочитаны в PDF-тексте; web-screenshot соответствующих страниц вернул cache miss. T2, в частности pp.17 и 22, проверен также визуально. Повторное получение HH PDF вернуло timeout; никакая непроверенная специальная формула HH для u_m не объявляется импортом.

## 1. Конечный перенос на Beurling: проходит, включая компактность

[FINITE_CELL | PAPER; собственный вывод с T2 в указанной аналитической форме.]

Пусть q_1≤q_2≤…→∞, q_1>1, — обобщённые простые, с повторениями. Все суммы ниже учитывают их кратности. Положим
\[
 d\psi_B(x)=\sum_{q,k\ge1}\log q\,\delta_{q^k}(x).
\]
Вспомогательный полный источник на компактных гладких функциях определяется буквально:
\[
 W_B=H+P-B_B,\qquad
 B_B[f]=\sum_{q,k\ge1}\frac{\log q}{q^{k/2}}Q_f(k\log q).
\tag{1.1}
\]
Здесь H — тот же полный Γ-источник, P — ядро 2cosh((x−y)/2), а на чётном секторе P[f]=|⟨p,f⟩|², p=√2 cosh(x/2). Это **явно заданная оконная форма с ζ-архимедовой частью**, а не выдуманное естественное completion ζ_B. На каждом компактном носителе арифметическая сумма конечна.

Оставляем буквальные I_L, L=log m, N=m и косинусный синтез 𝒮_m. Определим
\[
 A_m^B=\mathcal S_m^*W_B\mathcal S_m,
 \quad G_m^{(r)}=(I+X_m)^r,
 \quad\mathcal K_m=\{z:z_0=0,\ p_m^*z=0\}.
\tag{1.2}
\]
Ни базис, ни физическая норма, ни Γ, ни полюс не меняются. Меняются только перечисленные реальные атомы.

### 1.1. Фаза и полный возврат

Для конечного мультимножества q<m:
\[
 u_m^B(t)=\rho_\infty(1/2+it)\prod_{q<m}
 \frac{1-q^{-(1/2-it)}}{1-q^{-(1/2+it)}},\qquad |u_m^B(t)|=1.
\]
Прямое дифференцирование даёт
\[
 \alpha_m^B(t)=-i\overline{u_m^B}(u_m^B)'
 =q_\infty(t)-2\sum_{q<m,k\ge1}
       \log q\,q^{-k/2}\cos(kt\log q).
\tag{1.3}
\]
При f=𝒮_mz обратное Fourier-равенство возвращает H−B_B. Для q^k≥m корреляция равна нулю точно, включая q^k=m. Поэтому
\[
 z^*A_m^Bz=|p_m^*z|^2+
 \frac1{2\pi}\int\alpha_m^B(t)|\widehat f(t)|^2dt.
\tag{1.4}
\]
Для этих равенств нужны только q>1 и конечность множества q<m. Целочисленность не использована.

### 1.2. Почему T2 переносится

Обозначим n число конечных факторов, с кратностями. В §4.2 T2 полюсы одного фактора стоят в 2πiℤ/log q; Gram-операторы §3 ограничены для любого log q>0. Контур R=(2j+1)π/log q, оценки ρ_q(−2j) и ненулевые знаменатели q^{2j}−1 не требуют q∈ℕ. Вклад общего полюса 0 имеет конечный ранг.

Для нескольких факторов Lemmas 4.6–4.7 делят Γ-отношение на n факторов посредством формулы умножения Гаусса. **Целое n здесь — количество факторов, не арифметическое свойство q.** Каждый Γ-фрагмент, умноженный на один ρ_q, имеет компактный off-diagonal: диагональная последовательность в residue-разложении убывает как O(|j|^{-1/(2n)}). Произведение конечного числа quasi-inner множителей остаётся quasi-inner. Совпадения q, рациональные зависимости log q и отсутствие локальных полей этому расчёту не мешают. Константы зависят от конечного списка; равномерности по m нет.

Следовательно c_m=P_-U_m^BP компактен. Сохраняются определения R_B:
\[
 D_m^B=(U_m^B)^*PU_m^B-P,\quad
 S_m^B=\operatorname{proj}\ker(P_-U_m^BP_-),\quad K_m^B=D_m^B-S_m^B.
\tag{1.5}
\]
Из dd*=I−cc* и блочных тождеств следует, как в R_B §4, что K_m^B компактен, самосопряжён, ||K_m^B||≤1. Это аналитический Hardy/Sonin-объект; адельный фактор по несуществующим ℚ_q не вводится.

### 1.3. Локализованный след

При a_R=χ_R f̂ всё доказательство R_B §5 сохраняется: u_m^B гладка на R, ядро D гладко на компактном квадрате после снятия диагональной особенности. Получаем обычные конечные следы
\[
 \frac1{2\pi}\int\chi_R^2\alpha_m^B|\widehat f|^2
 =T_{m,R}^B[f]+E_{m,R}^B[f],\qquad T_{m,R}^B[f]\ge0.
\tag{1.6}
\]
На 𝒦_m сумма стремится к z*A_m^Bz. В частности,
\[
 \boxed{\liminf_{R\to\infty}E_{m,R}^B[\mathcal S_mz]
 \le z^*A_m^Bz.}
\tag{1.7}
\]
Это правильное направление для отрицательного судьи. Никакая цикличность двух бесконечных несуммируемых слагаемых не использована.

## 2. Строгий отрицательный судья DMV без completion и без радикала

### Теорема 1

[COFINAL_FAMILY | PAPER; T1 плюс доказательство ниже.]

Для выбранной системы DMV и каждого фиксированного целого r≥0
\[
 \boxed{\lambda_m^B(r):=
 \inf_{0\ne z\in\mathcal K_m}
 \frac{z^*A_m^Bz}{z^*G_m^{(r)}z}\longrightarrow-\infty.}
\tag{2.1}
\]
Следовательно для каждого C<∞ существует M(C,r), такое, что **для каждого целого m≥M(C,r)** найдётся z∈𝒦_m с z*G_m^(r)z=1 и
\[
 \boxed{\liminf_R E_{m,R}^B[\mathcal S_mz]<-C.}
\tag{2.2}
\]
Поэтому SD при r=1, и его аналоги с любым фиксированным r, ложны на всех неограниченных подпоследовательностях. Конечный численный onset не установлен; cofinal-квантор доказан аналитически.

### 2.1. Один нуль и один компактный профиль

Из простого полюса ζ_B в 1 следует существование b_0∈(θ,1), такого, что ζ_B не имеет вещественных нулей на [b_0,1); справа от 1 их исключает Euler product. Выбираем один нуль ρ=β+iγ из T1 с β>b_0. Это возможно, поскольку β→1. Пусть ν — его полная кратность, u_0=ρ−1/2.

Выберем вещественную чётную η∈C_c∞ с интегралом 1 и достаточно узким носителем, чтобы F_η(u_0)≠0, где F_v(u)=∫v(x)e^{ux}dx. Это возможно: при сжатии η к нулю F_η(u_0)→1. Определим
\[
 g=\partial_x^2(\partial_x^2-1/4)\eta,
 \quad F_g(u)=u^2(u^2-1/4)F_\eta(u).
\tag{2.3}
\]
Тогда g реально-чётна, гладка, компактна и ненулевая;
\[
 F_g(0)=F_g(1/2)=F_g(-1/2)=0,\qquad F_g(u_0)\ne0.
\tag{2.4}
\]
Нули в (2.4) — точные условия на среднее и полюсные моменты. Они не используют нули ζ как положительную меру. Нуль ρ здесь — законный отрицательный свидетель в уже известном ложном мире.

### 2.2. Смешанный сдвиговый отклик и его Laplace-полюс

Пусть C_g(v)=∫g(x)g(x+v)dx, supp C_g⊂[−d,d], и T_tg(x)=g(x−t). Определим реальную непрерывную функцию
\[
 h_g(t)=W_B(g,T_tg),\quad t\ge0.
\tag{2.5}
\]
Все полюсные члены равны нулю. Арифметическая часть равна
\[
 -\sum_{q,k}\log q\,q^{-k/2}
 \{C_g(t-k\log q)+C_g(t+k\log q)\}.
\tag{2.6}
\]
При t>d архимедова часть точно равна
\[
 h_H(t)=-\int_0^\infty j(s)C_g(t-s)ds=O_g(e^{-t/2}),
 \quad j(s)=e^{-s/2}/(1-e^{-2s}).
\tag{2.7}
\]
На компактных t она непрерывна: в исходном смешанном интеграле разности сдвигов снимают особенность j у нуля. Из ψ_B(x)=O(x) следует h_g(t)=O_g(e^{t/2}).

Для λ=klog q>d
\[
 \int_0^\infty C_g(t-\lambda)e^{-ut}dt
 =e^{-u\lambda}F_g(u)F_g(-u)=e^{-u\lambda}F_g(u)^2.
\]
Второй сдвиг C_g(t+λ) тогда нулевой. Атомов с λ≤d конечное число; их отличие от этой формулы даёт целую функцию u. По (2.7) весь оставшийся архимедов вклад голоморфен при Re u>−1/2. Поэтому при Re u>1/2
\[
 \boxed{\int_0^\infty h_g(t)e^{-ut}dt
 =F_g(u)^2\frac{\zeta_B'}{\zeta_B}(1/2+u)+A_g(u),}
\tag{2.8}
\]
где A_g голоморфна при Re u>−1/2. Перестановка исходных сумм оправдана абсолютной сходимостью logarithmic Dirichlet series в Re(1/2+u)>1.

**Знак в (2.8) плюс:** в h стоит минус перед prime-суммой, а сама Dirichlet-сумма равна −ζ'_B/ζ_B. У u_0 правая часть имеет настоящий полюс с ненулевым вычетом
\[
 \nu F_g(u_0)^2\ne0.
\tag{2.9}
\]
У вещественного u=1/2 полюс ζ'_B/ζ_B снят множителем F_g(u)^2. Правая часть (2.8) голоморфна возле каждого вещественного u>b_0−1/2. Никакое отражение нулей или полная explicit formula DMV не понадобились.

### 2.3. Почему h_g не может быть ограничена снизу

Предположим h_g(t)≥−M. У неотрицательной функции h_g+M абсцисса Laplace-сходимости σ_c не больше 1/2. Полюс (2.9) заставляет
\[
 \sigma_c\ge\Re u_0=\beta-1/2>b_0-1/2>0:
\]
иначе Laplace-transform был бы голоморфен в u_0, вопреки мероморфной идентичности (2.8). Его продолжение отличается от правой части (2.8) только на M/u и потому голоморфно около вещественной σ_c.

Это невозможно для Laplace-transform неотрицательной функции. Короткое доказательство нужной леммы Ландау: если transform аналитичен через конечную σ_c, выбрать σ_1>σ_c столь близко, что его Taylor-диск достигает σ_1−v<σ_c. Коэффициенты ряда по положительному v равны неотрицательным интегралам t^n e^(−σ_1t)(h_g+M)/n!. Сходимость Taylor-ряда и монотонная сходимость дают конечность Laplace-интеграла при σ_1−v, противореча определению σ_c.

Следовательно
\[
 \boxed{\liminf_{t\to\infty}h_g(t)=-\infty.}
\tag{2.10}
\]
Переход от отсутствия глобальной нижней границы к t→∞ законен, поскольку h_g непрерывна на каждом компакте. Это аналитическая one-sided осцилляция, не DIAG.

Теперь берём чётные два пакета
\[
 f_t=T_{t/2}g+T_{-t/2}g.
\]
Они имеют нулевое среднее и оба нулевых полюсных момента. При t>d носители не пересекаются, и для каждого фиксированного r
\[
 \|f_t\|_{H^r}^2=2\|g\|_{H^r}^2,\qquad
 W_B[f_t]=2W_B[g]+2h_g(t).
\tag{2.11}
\]
Таким образом, на компактных допустимых чётных функциях отношение W_B[f]/||f||_Hr² не ограничено снизу.

### 2.4. Все поздние буквальные окна, затем сам дефект

Для любого требуемого D>0 сначала фиксируем t из (2.10), чтобы Rayleigh quotient (2.11) был меньше −2D. Только затем отправляем m→∞. После входа компактного носителя в I_L берём P_m^cos f_t и точно восстанавливаем ограничения:
\[
 v_m=\mathcal S_m^*f_t,
 \quad\widetilde v_m=v_m-v_{m,0}e_0,
 \quad z_m=\widetilde v_m-
        \frac{p_m^*\widetilde v_m}{p_{m,1}}e_1.
\tag{2.12}
\]
У компактного mean-zero f_t первая поправка фактически нулевая. Вторая сверхполиномиально мала: smooth Fourier-tail убывает быстрее любой степени m, а полюсная норма и 1/p_m,1 имеют лишь полиномиальный масштаб. Все внутренние производные фиксированного порядка сходятся.

Арифметическая норма оплачивается без целочисленных промежутков:
\[
 \|B_m^B\|\le2\int_{1^-}^{m}x^{-1/2}d\psi_B(x)=O_B(\sqrt m).
\tag{2.13}
\]
Γ и полюс те же, что раньше; их нормы на V_m полиномиальны. Граница нулевого продолжения оплачивается smooth Fourier-tail/endpoint estimate, а не объявляется глобально H¹-гладкой. Поэтому
\[
 z_m^*A_m^Bz_m\to W_B[f_t],\qquad
 z_m^*G_m^{(r)}z_m\to\|f_t\|_{H^r}^2>0.
\tag{2.14}
\]
Для всех достаточно больших m quotient меньше −D. Поскольку D произвольно, доказано (2.1). Нормирование z_m и (1.7) доказывают (2.2).

**Здесь нет перестановки кванторов:** D → один фиксированный t и f_t → все достаточно поздние m. Это и исключает каждую неограниченную подпоследовательность. Плотный радикал/return R2 для ζ_B не использовался; доказан только прямой compact-test return (2.12)–(2.14).

## 3. Где обязана войти арифметика ℚ; тот же положительный контроль

### 3.1. Что исправляется в R_B §10

[ABSTRACT / COFINAL_FAMILY | PAPER.]

Фраза R_B о том, что формальное Beurling-произведение не предоставляет T2, слишком груба: **Hardy-часть T2 переносится**, как доказано в §1. Но SD не следует из этой геометрии. Непроходимая строка для DMV — именно **равномерная нижняя оценка E_m,R в Шаге C**, уже до обращения к ζ-радикалу R2.

Точное необходимое следствие любой такой оценки:
\[
 (SD)_B\Longrightarrow W_B[f_t]\ge-C\|f_t\|_{H^1}^2
 \Longrightarrow h_g(t)\ge-C_g\quad\forall t.
\tag{3.1}
\]
DMV нарушает последнюю строку по (2.8)–(2.10). Это место поломки для самого дефекта, а не лишь для его последующего RH-export.

Нельзя назначить отличающим входом одну формальную μ*1=δ: инверсия Дирихле существует и на свободном моноиде обобщённых простых. Euler product, Λ как logarithmic derivative и конечная алгебра сдвигов также проходят. Несоизмеримость log p не участвовала ни в переносе, ни в отрицательном судье; одна её декларация не оплачивает (3.1).

Конкретный доступный ℚ-специфичный вход — **точная обычная целая решётка**, например N_Q(x)=⌊x⌋, а не N_B(x)=κx+O(x^θ). Она даёт
\[
 \zeta(s)=\frac{s}{s-1}-s\int_1^\infty\{x\}x^{-s-1}dx
 \quad(\Re s>0),
\tag{3.2}
\]
после продолжения исходного Stieltjes-интеграла. В выбранной конструкции §7 DMV атомы выбираются на нецелой сетке v_k=√log k, а не на обычных простых. Точная measure identity dN_Q=d⌊x⌋ ей не принадлежит. Если бы generalized integer multiset был ровно обычными целыми с кратностью один, последовательное восстановление его неразложимых элементов вернуло бы обычные простые. Это указание различающего входа, не его использование вместо недостающей оценки.

**Но (3.2) не объявляется supplier SD.** Требуется ещё вывести из специфической арифметики ограниченность подписанного отклика/следа. Доказано, где такой supplier обязан отличать миры; не доказано, что именно (3.2), а не иной эквивалентный арифметический вход, обязана использовать любая будущая теория.

### 3.2. E/F3 проходит этот же Laplace-судья

[ABSTRACT | PAPER; явный контроль J_E и source-нормировка из R_A §6.]

Пусть h=log3, J_E(z)=2cos(hz). Его нули
\[
 \gamma_n=(\pi/2+\pi n)/h,\quad n\in\mathbb Z,
\]
вещественны и просты. Используем **собственный** полный источник кривой из R_A, а не ζ-Γ-часть с придуманными curve-простыми. В его zero-side нормировке
\[
 W_E(f,g)=\sum_n\overline{\widehat f(\gamma_n)}\widehat g(\gamma_n).
\]
Для того же типа компактного smooth g с двумя нулевыми моментами
\[
 h_{E,g}(t)=W_E(g,T_tg)=
 2\sum_{\gamma_n>0}|\widehat g(\gamma_n)|^2\cos(\gamma_nt).
\tag{3.3}
\]
Сумма абсолютно сходится, h_E ограничена и
\[
 \int_0^\infty h_{E,g}(t)e^{-ut}dt
 =2\sum_{\gamma_n>0}|\widehat g(\gamma_n)|^2
                      \frac{u}{u^2+\gamma_n^2}
\tag{3.4}
\]
голоморфна в Re u>0. Полюсов, создающих противоречие §2.3, нет. Более того, W_E≥0 непосредственно; R_A реализует это через положительную Rosati-метрику. Также −J_E'/J_E=h tan(hz) имеет положительную мнимую часть в C_+.

**Это тот же пункт проверки:** bounded translated response / отсутствие правого Laplace-полюса. Не утверждается несуществующее тождество между curve-source и конечным ζ-произведением R_B. Поэтому положительный контроль не подменяет источник.

## 4. Что переносится с полки S1–S3 и что означает плато

### 4.1. Нулевой запас и постоянный бюджет — разные кванторы

[ABSTRACT / COFINAL_FAMILY | PAPER; S2/S4 — только DIAG.]

| Результат полки | Что сохраняется | Чего он не доказывает для SD |
|---|---|---|
| S1 Lemma 6 | Для fixed S локальная форма без глобального полюса бывает отрицательной | Это не отрицательная неограниченность graph-нормированного полного источника |
| S1 Lemmas 8–9; S3 K27–K30 | Ненулевой fixed Sonin-проектор не зануляет радикальный multiplier; compact-cutoff witness убивает глобальный zero-slack minorant | Отрицательная фиксированная константа поглощается C·G; нет uniform divergence при S=S_m |
| S3 K25 | Fixed nonzero closable global-L² канал не может занулять плотный радикал | SD не требует зануления и не даёт такого фиксированного предельного канала |
| S3 K31–K34 | Correction-square тоже не имеет нужного null-kernel; positive forms с точным занулением проходят через quotient | Это не знак остатка и не uniform trace-bound |
| S2 n₂(g_k)>0 | Диагностика согласована с аналитической injectivity-леммой | Ни числа, ни рост по k при S={∞,2} не дают роста по m при растущем S_m |

Таким образом, старые fixed-S контрпримеры надо сохранить, но нельзя ими объявить SD для ℚ ложной. Для этого требуется новое cofinal утверждение, например нарушение (8.1) R_B с правильным порядком пределов.

### 4.2. Это не две несвязанные пары проекций

[ABSTRACT / FINITE_CELL | PAPER; словарь S1 при λ=1.]

В общем Mellin/Fourier-представлении с Fourier-знаком exp(−itx) обозначим Jv(t)=v(−t). Тогда JPJ=P_- и полулокальная Fourier-инволюция имеет вид
\[
 F_S=U_S^*J.
\tag{4.1}
\]
Формула следует из архимедова Mellin-множителя и Euler-intertwiner S1 Lemma 1: его множитель равен ∏(1−p^(−1/2+it))^−1, а отношение значений при t и −t даёт именно u_S^*. Поэтому старый Fourier-cutoff проектор равен
\[
 Q_{old}=F_SPF_S=U_S^*P_-U_S=I-Q_{R_B}.
\]
Общие Sonin-проекторы совпадают, а старый angle-оператор
\[
 D_{old}=P+Q_{old}-I+S^{Son}=-K_{R_B}.
\tag{4.2}
\]
Это complement/sign dictionary, не случайная аналогия. При иных cutoffs нужны соответствующая дилатация и contact term; их нельзя молча положить нулём.

**Следствие для плато.** У одного фиксированного S собственные значения компактного K должны стремиться к нулю. Настоящее бесконечное плато около 0.4 противоречило бы компактности, и (4.2) его не спасает. Но S4 сообщает конечные DIAG-спектры и одновременно дефекты модели порядка 0.43 и 0.249, не доказанную сходимость в операторной норме. Конечное плато, медленный хвост или растущее число значений выше порога не доказывают бесконечного плато. Несуммируемость Σ|α_n|, даже Σ|α_n|², сама по себе совместима с α_n→0. При росте S_m компактность для каждого m также не даёт равномерной компактности семейства.

## 5. Радикальный судья (8.1): что можно получить дёшево

### 5.1. Необходимый бюджет и настоящий критерий опровержения

[COFINAL_FAMILY | CONDITIONAL для SD; PAPER для импликации.]

Для реальной ζ фиксируем
\[
 \widehat h(z)=z^2(z^2+1/4)\Xi(z)e^{-z^2},
\]
и прежний точный return f_m=𝒮_m z_m^00(h). Тогда A_m[f_m]→0, graph-energy→||h||_H1²>0. Из SD следовало бы
\[
 \limsup_k T_{m_k,\infty}[f_{m_k}]
 \le C\|h\|_{H^1}^2.
\tag{5.1}
\]
Требуемая C одна и та же для всех admissible h. Чтобы убить **все** subsequences, достаточно доказать рост T_m,∞/energy→∞ по всем поздним m хотя бы для одного fixed h. Неограниченный limsup или несколько растущих значений этого не доказывают.

### 5.2. HS даёт верхнюю границу, не отрицательный свидетель

[FINITE_CELL | PAPER.]

Из S≤D² и явного ядра R_B:
\[
 T_{m,R}[f]\le\|M_{a_R}D_m\|_{HS}^2
 =\frac1{4\pi^2}\int|a_R(t)|^2
       \int\frac{|u_m(s)-u_m(t)|^2}{(s-t)^2}\,ds\,dt.
\tag{5.2}
\]
При |s−t|≤1 числитель контролируется локальным sup|u_m'|²(s−t)²; при |s−t|>1 — числом 4. Поэтому внутренняя сумма не больше 2V_m(t)²+8, где V_m(t)=sup_{|v−t|≤1}|u_m'(v)|.

Из фазовой формулы
\[
 V_m(t)\le C_\Gamma(1+\log(3+|t|))+
 A_m^{loc},\quad
 A_m^{loc}=2\sum_{p<m}\frac{\log p}{\sqrt p-1}<\infty.
\tag{5.3}
\]
Для каждого fixed m и буквального f, f̂(t)=O_f((1+|t|)^−1). Следовательно (5.2) конечна даже с a=f̂. Это дополнительно оправдывает конечный T_m,∞ и сходимость T_m,R→T_m,∞; E_m,R имеет конечный предел A_m[f]−T_m,∞ на pole-null классе. **Глобальную trace-class принадлежность несрезанного D-sandwich из одной интегрируемой диагонали здесь не утверждаем.**

Константа (5.3) растёт с множеством простых. Получена finite-m корректность и upper bound, не равномерное (5.1). Большая верхняя граница не доказывает большого T.

### 5.3. В предлагаемой нижней Neumann-границе знак обратный

[ABSTRACT / FINITE_CELL | PAPER; точная алгебра.]

В блоках U=[[a,b],[c,d]] положим A=cc*, Q₀=b*b=I−d*d. Тогда A d=d Q₀. Для любого N≥0
\[
 S_N:=P_--d^*\sum_{j=0}^N A^j d=Q_0^{N+1}.
\tag{5.4}
\]
На ker d оператор Q₀ равен I; на её дополнении спектр лежит в [0,1). Поэтому
\[
 \boxed{S_N\succeq S^{Son},\qquad S_N\downarrow S^{Son}.}
\tag{5.5}
\]
**Это верхняя граница Сонин-проекции.** Она даёт нижнюю границу дефекта A−T, а не upper witness для его отрицательности. Контрпример к противоположному направлению уже скалярен на нижнем блоке: Q₀=1/4, ker d=0, S=0, но S_N=4^(−N−1)>0.

Возможны две честные нижние границы.

(i) Если отдельно сертифицировано η≥||Q₀|_(ker d)^perp|| и η<1, то при N≥1
\[
 \frac{Q_0^{N+1}-\eta^NQ_0}{1-\eta^N}\preceq S^{Son}.
\tag{5.6}
\]
Доказательство — скалярное неравенство на [0,η] и точное значение 1 в точке 1. После sandwich все следы конечны, поскольку Q₀≤D² как оператор на нижнем блоке. В отличие от ошибки εP_-, здесь не возникает бесконечного trace умножения на тождественный оператор. Сам η не предоставлен uniform по m.

(ii) Для конечного набора **точных** Sonin-векторов V=(v₁,…,v_n), H_V=V*V>0:
\[
 VH_V^{-1}V^*\preceq S^{Son},\qquad
 T_{m,R}\ge\operatorname{tr}
   \bigl(H_V^{-1}V^*M_{|a_R|^2}V\bigr).
\tag{5.7}
\]
Они могут строиться через source Euler-map из фиксированных архимедовых Sonin-векторов. Приближённое kernel-уравнение само по себе не доказывает включение ran V⊂ker d. Альтернатива — положительная Euler-Gram inverse из S1(11): там inverse входит с плюсом, и её Neumann partial sums действительно дают lower projection bounds. Это другая формула, не R_B(7.1).

### 5.4. Один ограниченный Codex-прогон, только при последующем запуске

[FINITE_CELL | CONDITIONAL; предрегистрация, НЕ выполненный эксперимент.]

ID: `SD_RADICAL_TRACE_BRACKET_NOT_CYCLIC_MATRIX_TRACE`.

Источник: неизменный u_m R_B, fixed h из §5.1, m=8,16,32,64, monotonically expanding cutoffs R=8,16,32. Все компоненты return сохраняются; raw radical без конечного return не подставляется вместо f_m.

Выход: для каждого m,R нижняя граница (5.7) или (5.6), верхняя HS-граница (5.2), источник A_m[f_m], graph-energy, полный ledger хвостов, Gram-ошибки и проекции. При отсутствии rigorously enclosed хвостов результат помечается DIAG; числа не повышаются до cofinal закона.

Предрегистрированные утверждения: P1 finite cyclic raw trace равен нулю при точном [U,w]=0; P2 S_N−S неотрицателен; P3 fixed-S Sonin trace на ненулевом радикальном multiplier положителен; P4 знак/рост actual-Q cofinal T НЕ предсказывается. P1–P3 уже имеют аналитические основания выше; будущий прогон проверяет прибор, не доказывает эти теоремы заново. Судьба прогона: NOT_RUN.

Нижняя оценка T вместе с верхней оценкой источника даёт **верхнюю** оценку E. Это единственный разрешённый отрицательный вывод. Конечное нарушение заданной C убивает только эту C/формулу, не существование другой постоянной. Для point 1 никакой Codex-прогон не нужен: Теорема 1 уже закрывает его аналитически.

## 6. Следовая аномалия и предложенные мосты

### 6.1. Конечномерный нуль точен; не вся цикличность запрещена

[ABSTRACT | PAPER.]

Для конечных матриц U unitary, [U,w]=0:
\[
 \operatorname{Tr}((U^*PU-P)w)
 =\operatorname{Tr}(P(UwU^*-w))=0.
\tag{6.1}
\]
Это алгебраическая теорема, не только n=9…14 DIAG. В бесконечном пространстве два слагаемых после разбиения не обязаны быть trace class. Локализованная **разность** имеет trace по R_B(5.2), но это не разрешает циклически переставлять её два несуммируемых слагаемых по отдельности.

Следовательно конечномерная модель, сохраняющая одновременно exact unitarity и [U,w]=0, не может сходиться в trace norm к ненулевой аномалии с нулевыми traces. Нужен явно оплаченный граничный дефект либо continuum diagonal formula. Цикличность для законных trace-class произведений остаётся разрешённой.

### 6.2. Helton–Howe / Carey–Pincus: возможен словарь, не знак

[ABSTRACT | PAPER для следующего расчёта; перенос к нашему полному K — CONDITIONAL.]

Предложенное тождество с одним [T_u,T_w] неверно уже на окружности: u(z)=z, w=1. Тогда [T_u,T_1]=0, а фазовая масса (2πi)^−1∮ūdu=1.

Для гладких символов на окружности правильная элементарная формула имеет вид
\[
 \operatorname{Tr}[T_f,T_g]
 =\sum_{n\in\mathbb Z}n f_{-n}g_n
 =\frac1{2\pi i}\oint f\,dg.
\tag{6.2}
\]
Её можно проверить на Laurent-мономах, затем перейти по абсолютно сходящимся Fourier-рядам с производными. В частности,
\[
 \operatorname{Tr}[T_{\bar u},T_{uw}]
 =\frac1{2\pi i}\oint w\bar u\,du
\tag{6.3}
\]
при |u|=1: добавочный интеграл dw равен нулю. Это объясняет тип trace cocycle, но **не** представляет Sonin-subtracted E как положительный объект. Для реальных u_m поведение в бесконечности, operator ideal и cutoff-limit требуют собственного обоснования. Формула smooth-circle не импортируется туда без этих условий. Ни теория principal function, ни название anomaly не дают uniform graph-sign.

### 6.3. D≥0 действительно проверяет inner, но это не пассивность R_A

[ABSTRACT / FINITE_CELL | PAPER.]

Для unit-modulus scalar multiplier U:
\[
 D=U^*PU-P\succeq0
 \iff U(H^2)\subset H^2
 \iff u\text{ — inner multiplier верхней полуплоскости}.
\tag{6.4}
\]
Первая эквивалентность — включение диапазонов ортопроекций. Вторая следует из multiplier property H²: операторная норма ≤1 ограничивает значения аналитического multiplier через reproducing kernels; граничный модуль равен 1.

Но u_m R_B не является completed Cayley-функцией 𝒮_Ξ из R_A(7.2). У каждого конечного u_m есть верхние t-полюсы Γ, например t=i(1/2+2j), j≥1, соответствующие s=−2j. Все конечные prime-ratios в этих точках конечны и ненулевые, полюс не снимается. Поэтому u_m не inner даже для настоящих простых. Эквивалентно c_m≠0, и на ran P
\[
 \langle v,D_mv\rangle=-\|c_mv\|^2<0
\]
для некоторого v. Это строго опровергает D_m≥0, но не положительность A_m на допустимых Fourier-squares. Дополнительный перенос к completed passivity R_A не доказан: там стоит другая функция, 𝒮_Ξ, а не u_m. Эквивалентность для одного и того же Cayley-объекта нельзя приписать этим разным объектам. Сам факт (6.4) верен; отрицание RH отсюда не следует.

### 6.4. Berger–Shaw пока не supplier

[ABSTRACT | PAPER algebra; применение T3 — CONDITIONAL.]

Для a=PUP на H²:
\[
 [a^*,a]=bb^*-c^*c.
\tag{6.5}
\]
Из компактности c не следует неотрицательность этого оператора: у конечномерного a=[[0,1],[0,0]] стандартная унитарная дилатация имеет компактный c, но [a*,a]=diag(−1,1). У Berger–Shaw требуются hyponormality и контроль рациональной циклической кратности; они здесь не доказаны. Даже их получение не отождествляет self-commutator с проектором ker d и не контролирует automatically локализованный T_m при росте m. Мост не запрещён вообще, но его текущая формулировка не поставляет (8.1) или SD.

## 7. Closeout и следующий разрешённый ход

[ABSTRACT / COFINAL_FAMILY | PAPER для итогов; actual-Q bounds — CONDITIONAL.]

**Что закрыто.** Выбран DMV-источник, конечный перенос проверен, SD опровергнута на всех подпоследовательностях строгим source/defect upper witness. Положительная кривая проходит тот же translated-response Laplace-судья. Уточнены полочная граница и знак Neumann-границ. Это результат о классе ложных источников, не положительная оценка для ζ.

**Что не повторять.** Не прятать DMV за отсутствующим функциональным уравнением: для этого судьи оно не нужно. Не выдавать μ-инверсию за отличие от обобщённых простых. Не выводить постоянный trace-bound из compactness/norm≤1. Не читать finite plateau как ненулевой essential spectrum. Не использовать нижнюю approximation inverse в вычитаемом выражении как нижнюю approximation проекции.

**Один следующий target.** Калибровать (8.1) именно на returned ζ-радикале с правильным lower Sonin bound и source upper; не начинать общий signed-angle Шаг B на основании одних bounded norms. Проверка может быть аналитической; §5.4 задаёт только ограниченный резервный DIAG-дизайн, не запущенную работу.

**Две сохраняемые репрезентации.** (i) Exact finite-S Euler-Gram projector: честные lower/upper trace brackets; сила отсечения высокая для данного канала, цена средняя и растёт с S. (ii) Shifted source response и его Laplace-полюсы: уже дал cofinal kill DMV без диагонализации; сила высокая/цена низкая для известных плохих zeros, но для настоящей ζ не поставляет отсутствие таких zeros. Ни одна не объявляется обязательным способом доказать RH.

**Предрегистрация и судьба.** Новых численных запусков не было. Главный pole-to-negative-response результат — аналитический вывод этой работы, не задним числом угаданная ставка. Старые numerical predictions S1–S2 не переоцениваются. P1–P4 в §5.4 относятся только к возможному последующему прибору; его статус NOT_RUN.

**Verification handoff.** Изменяется только этот новый Markdown. Никакие Lean-файлы, axioms, queue или route-state не меняются; Lean gate/axiom profile — NOT_APPLICABLE. Нужен независимый PAPER-аудит (2.8), Landau-шага, all-late-m возврата (2.12)–(2.14), и complement/sign dictionary (4.2). Коммит и remote blob после записи сообщаются отдельно; наличие коммита не является верификацией доказательства.
