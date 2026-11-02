# STATUS: TRY_EXACT_ZERO_TAIL_CORRECTED_INERTIA

```yaml
OPERATIVE_CLASS: TRY_EXACT_ZERO_TAIL_CORRECTED_INERTIA
DATE: 2026-11-02
TASK_MODE: OWNER_DIRECT_MATHEMATICAL_REQUEST
FORMAL_BUS_ADJUDICATION: NOT_PERFORMED
SOURCE_OPERATOR: LITERAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
SOURCE_RESIDUAL_COMMIT: 2176dab16bf77dd015f7efcb5a6f704587f732c8
SOURCE_RESIDUAL_BLOB: ebf7f8cab61a795118bda5dc7e65a0b3386247b7
SOURCE_RESIDUAL_SHA256: fb0176935d103209bea3feff8362605024da7635c568768dc5355f441e5ddd14
CAPACITY_DATA_PIN: rh_clean@bf89051
CAPACITY_RESULT_BLOB: a9f50694f8677e89fe80bc2db82387be6d15e7b3
CAPACITY_NORMALIZATION_BLOB: 54f37eef47dee0f59b6b95c31b5858dcdf900a5d
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
REQUESTED_LITERAL_FORMULA: NOT_PROVED_NOT_REFUTED_FOR_LITERAL_CCM
REQUESTED_STRIP_LEVEL_ATTRIBUTION: NOT_DEFINED_BY_THE_SUPPLIED_SOURCE
PROVED_EXACT_IDENTITIES:
  - LOW_ZERO_PAIRING_WITH_MULTIPLICITIES_AND_COMPLEX_NODES
  - EVENTUAL_LOW_FORM_INDEX_EQUALS_REDUCED_PAIR_INDEX
  - FULL_THRESHOLD_INDEX_EQUALS_SCHUR_INDEX
  - FULL_THRESHOLD_INDEX_EQUALS_TAIL_CORRECTED_ZERO_COORDINATE_INDEX
  - SHARP_RESIDUAL_TO_SCHUR_CORRECTION_BUDGET
  - NESTED_STRIP_SCHUR_INERTIA_WITH_SINGULAR_CORE_REPAIR
SCOPED_REFUTATIONS:
  - code: KILL_TAIL_FREE_PAIR_INDEX_ADDITIVITY
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    EVIDENCE: SECTION_6_1_EXACT_CONJUGATE_PAIR_AND_POSITIVE_RANK_ONE_TAIL
    CLAIM_DISCREPANCY_UPPER_ENVELOPE: -1
    EXCLUDES: LITERAL_CCM_COUNTEREXAMPLE_AND_ROUTE_FAMILY_DEATH
  - code: KILL_RAW_COMPLEMENT_COUNT_WITHOUT_COUPLING
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    EVIDENCE: SECTION_6_2_EXACT_POSITIVE_MATRIX
    CLAIM_DISCREPANCY_UPPER_ENVELOPE: -1
    EXCLUDES: LITERAL_CCM_COUNTEREXAMPLE_AND_ROUTE_FAMILY_DEATH
LITERAL_SOURCE_RESIDUE:
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  REOPEN_TRIGGER: SOURCE_SPECIFIC_RELATIVE_TAIL_INERTIA_AND_PRECISE_STRIP_LOCALIZATION
PROGRESS_CLASS: FALSIFICATION_PROGRESS
ADDITIONAL_PROGRESS: EXACT_SOURCE_PRESERVING_INERTIA_REPRESENTATION
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4
RH_ASSUMED: false
SIMPLE_ZEROS_ASSUMED: false
NONRESONANCE_ASSUMED: false
RH_PROVED: false
SPECTRAL_UPPER_COUNT_PROVED: false
VERIFIER: PAPER
INDEPENDENT_REVIEW: NOT_PERFORMED
EXACT_ALGEBRA_CONTROLS: EXECUTED
LITERAL_CCM_RECOMPUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
REPOSITORY_WRITTEN: false
ROUTE_STATE_CHANGED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **Заявленное равенство для исходной CCM-семьи здесь не доказано.** Из явной формулы и невязки следует точное равенство с **знаковой инерционной поправкой**, а не автоматически с неотрицательным числом уровней, приписанных полосе нулей.

Ниже доказана пригодная замена, включая фактические комплексные нули, все кратности, физическую метрику и полный бесконечный хвост. Общий переход, который удаляет поправку хвоста, опровергнут точной матрицей. Этот контрпример **не является другой дзета-функцией или literal CCM-матрицей**; он не опровергает возможную дополнительную source-specific теорему. Он запрещает выдавать такую теорему за следствие уже имеющихся предпосылок.

## 0. Главный результат

**[FINITE_CELL | PAPER]** Пусть на данной исходной ячейке

\[
J=J_m,\quad r=\dim J,\quad \|A_mQ\|\le\delta<\mu,
\qquad Q^*Q=I_r,\quad\operatorname{ran}Q=J.
\]

Выберем изометрию \(Z\) на \(J^\perp\), так что \([Q\ Z]\) унитарна, и определим

\[
B=Q^*A_mQ,\qquad C=Z^*A_mQ,\qquad D=Z^*A_mZ.
\tag{0.1}
\]

Тогда без предположений о простоте спектра и без исключения \(\mu\) из спектра:

\[
\boxed{
N_{A_m}(\mu)-r
=n_-\!\left(D-\mu I+C(\mu I-B)^{-1}C^*\right).
}
\tag{0.2}
\]

На достаточно поздних ячейках рассматриваемого moving-kappa семейства существует обратимая матрица фактических low-zero evaluation-координат \(F\), для которой

\[
\boxed{
N_{A_m}(\mu)-r=n_-\bigl(\mathcal J+\mathcal T_\mu\bigr),
}
\tag{0.3}
\]
\[
\boxed{
\mathcal T_\mu
=F^{-*}\left[R_\perp-\mu I+C(\mu I-B)^{-1}C^*\right]F^{-1}.
}
\tag{0.4}
\]

Здесь \(\mathcal J\) — корректно сокращённая попарная матрица нулей ниже \(T=\kappa_m\Omega_m\), \(R_\perp\) — сжатие **всего** нулевого хвоста \(\gamma\ge T\) на \(J^\perp\), а \(F\), \(\mathcal J\) и все нормировки определены ниже.

Следовательно, единственное безусловное аддитивное разложение с исходным попарным индексом, полученное здесь, имеет вид

\[
\boxed{
N_{A_m}(\mu)-r=n_-(\mathcal J)+\iota_m(\mu),\qquad
\iota_m(\mu):=n_-(\mathcal J+\mathcal T_\mu)-n_-(\mathcal J).
}
\tag{0.5}
\]

Поправка \(\iota_m(\mu)\) — целое **со знаком**. Она не объявляется новым неотрицательным счётчиком. Точная матрица в §6.1 имеет \(\iota=-1\), даже при \(R\succeq0\) и \(\|AQ\|=0\).

## 1. Source-lock и инвентарь

Прочитаны через GitHub connector: протокол на `rh_clean`; вердикт [S1] на полном SHA `2176dab16bf77dd015f7efcb5a6f704587f732c8`; `RESULT.md` и `NORMALIZATION.md` capacity-пакета на `bf89051`. Локальная копия [S1] совпадает с Git blob и SHA-256 из заголовка.

Это прямой математический запрос владельца, не новая транспортная adjudication по отсутствующему TXT. Очередь, route-state и сторонние OPEN-цели не выбирались. Репозиторий не изменялся.

**[COFINAL_FAMILY | PAPER, inherited S1]** Сохраняются

\[
L=\log m,\quad\Omega=2\pi m/L,\quad
\kappa_m=1+c(1+\log L)/L,\quad0<c<1,
\]

исходный чётный carrier \(V_m\), размерность \(d=m+1\), исходная физическая \(L^2\)-метрика, весь \(A_m\), все простые степени, полюсная компенсация и оконные границы. Нули в определении \(J_m\) — фактические комплексные нули, а не их проекции на прямую. Условия на производные в кратных нулях не добавляются.

В настоящей работе cofinal residual-оценка [S1] не доказывается заново. Все finite-cell инерционные утверждения действуют при явно указанной гипотезе \(\|AQ\|\le\delta<\mu\), независимо от того, как получено это неравенство. Ни один тест на малой матрице не объявлен тестом literal CCM.

### Ledger

| Claim | Scope | Verifier | Граница |
|---|---|---|---|
| L1, §2 | FINITE_CELL | PAPER | Точная низко-/высокочастотная явная формула; все комплексные пары |
| L2, §3 | COFINAL_FAMILY | PAPER | Полный строковый ранг после корректного удаления автоматических строк; индекс только усечённой формы |
| L3, §4 | FINITE_CELL | PAPER | Полный пороговый индекс через Schur; ties at mu сохранены |
| L4, §4.2 | ABSTRACT | PAPER | Точная наилучшая универсальная верхняя граница Schur-связи из полной residual-нормы |
| L5, §5 | FINITE_CELL | PAPER | Исправленная инерционная формула в zero-space координатах |
| K1–K4, §6 | ABSTRACT | PAPER | Контрпримеры общим сокращениям, не literal CCM |
| L6, §7 | FINITE_CELL | PAPER | Точное разбиение near-band и deep-index для эффективного дополнения |
| L7, §8 | ABSTRACT | PAPER | Нестированное полосовое разложение, включая singular core |
| O1 | COFINAL_FAMILY | CONDITIONAL | Отождествление corrected deep-index с n_-(Jcal) не установлено |
| O2 | COFINAL_FAMILY | CONDITIONAL | Приписывание всех near-band уровней геометрической полосе не установлено |

## 2. Что именно является попарной матрицей нулей

### 2.1. Кратности — веса, а не новые независимые значения

**L1 [FINITE_CELL | PAPER].** Для каждого **различного** верхнего нетривиального нуля

\[
\rho_j=\beta_j+i\gamma_j,\quad0<\gamma_j<T,
\qquad z_j=\gamma_j+i(1/2-\beta_j)
\]

обозначим его кратность через \(\nu_j\). Из чётности Fourier-образа это тот же evaluation-узел, что \(i(\rho_j-1/2)\), с противоположным знаком. Отражение \(\rho\mapsto1-\bar\rho\) индуцирует \(z_j\mapsto\bar z_j\); кратности в паре равны.

Положим

\[
(Ef)_j=\widehat f(z_j),\qquad
M=\operatorname{diag}(\nu_j),\qquad
(Pa)_j=a_{j^*},\quad z_{j^*}=\bar z_j,
\]
\[
\boxed{\mathcal J=2MP=2PM.}
\tag{2.1}
\]

Это эрмитова матрица. Фактор 2 учитывает верхние и нижние нули на **чётном** carrier; дополнительного \(2\pi\) или нового полюсного члена нет [S1, §4.1; S3].

Каждый критический нуль кратности \(\nu\) даёт блок \([2\nu]\). Каждая различная сопряжённая невещественная пара спектральных узлов даёт

\[
2\nu\begin{pmatrix}0&1\\1&0\end{pmatrix},
\tag{2.2}
\]

с одним положительным и одним отрицательным направлением. Поэтому **на пространстве различных evaluation-значений** отрицательный индекс — число таких пар, не сумма их кратностей. Все кратности при этом сохранены в весах.

Повторение строки \(\nu\) раз даёт эквивалентную квадратичную форму только после ограничения на образ повторяющего evaluation-отображения. Брать отрицательный индекс всей повторённой попарной матрицы без ограничения на этот образ нельзя; точный контроль — §6.3.

### 2.2. Полный оператор, а не положительная подмена

Из исходной явной формулы [S1, (4.1)] непосредственно:

\[
\boxed{A_m=H_T+R_T,\qquad H_T=E^*\mathcal J E,}
\tag{2.3}
\]
\[
\langle g,R_Tf\rangle
=\sum_{|\Im\rho|\ge T}
\overline{\widehat g(\overline{i(\rho-1/2)})}
\widehat f(i(\rho-1/2)).
\tag{2.4}
\]

При \(|\Im\rho|=T\) нуль относится к хвосту. Сумма при каждом фиксированном \(m\) абсолютно сходится: оконные transforms имеют \(O_m((1+|\Re z|)^{-1})\) в критической полосе, а нулевой счёт даёт суммируемость произведений. В конечной размерности это определяет эрмитову матрицу \(R_T\).

Формула (2.3) безусловна, но не утверждает \(R_T\succeq0\). В [S3] это различие специально оговорено. Полюсы и простые степени уже включены в \(A_m\) через полную явную формулу; не добавляются и не вычитаются ещё раз.

Имеем точно

\[
J_m=\ker E,\qquad H_TQ=0,\qquad A_mQ=R_TQ.
\tag{2.5}
\]

Последнее равенство показывает границу residual-результата: он контролирует столбцы \(R_TQ\), а не весь \(R_T\).

## 3. Какую инерцию низких нулей действительно можно перенести

**L2 [COFINAL_FAMILY | PAPER].** На достаточно поздних ячейках [S1], после удаления автоматических нулевых evaluation-строк, \(E\) сюръективно. Поэтому для \(F=EZ\):

\[
F\text{ обратима},\quad
H:=Z^*H_TZ=F^*\mathcal JF,\quad
\boxed{n_-(H)=n_-(\mathcal J).}
\tag{3.1}
\]

**Доказательство ранга.** Используем прежнюю точную конструкцию:

\[
\widehat f(z)=\frac{2\sin(zL/2)}{\sqrt L\,z}
\frac{P_f(z^2)}{\prod_{n=1}^{m}(z^2-\omega_n^2)},\qquad\deg P_f\le m.
\tag{3.2}
\]

Отображение \(f\mapsto P_f\) — изоморфизм пространств размерности \(m+1\). Инъективность следует из вычетов рациональных дробей в различных \(\omega_n^2\), а затем из постоянного члена.

Каждая неавтоматическая строка — ненулевой скаляр, умноженный на \(P_f(z_j^2)\). В модальных точках \(z_j=\omega_n\), \(n\le m\), берётся устранимый предел, и скаляр также ненулевой. Автоматическими являются вещественные внешние sinc-узлы \(z_j=2\pi k/L\), \(k>m\); такая строка тождественно нулевая. Её попарный блок положителен, поэтому его удаление не меняет отрицательного индекса \(\mathcal J\).

Для различных узлов с \(\Re z_j>0\) числа \(z_j^2\) различны. Значения полиномов степени не выше \(m\) в любом числе \(p\le m+1\) различных точек независимы: это обычная интерполяция Лагранжа. По [S1, §1] на достаточно поздних ячейках \(N(T)<m+1\); число различных активных строк \(p\) не больше \(N(T)\). Значит, все активные строки независимы, \(r=d-p\), и \(F=EZ\) — квадратная обратимая матрица. Равенство индексов в (3.1) следует из обратимой конгруэнции. ∎

**Это точная полезная часть предложенной связи.** Она относится к усечённому \(H_T\), а не автоматически к \(A_m\) или \(A_m-\mu I\).

На ранней ячейке без гарантии полного строкового ранга требуется ограничить \(\mathcal J\) на \(\operatorname{ran}E\). Если \(W\) — изометрия на этот образ, используются \(W^*\mathcal JW\) и обратимая матрица \(W^*EZ\). Сырой ambient index заменять ими молча нельзя.

## 4. Полная инерция: точная Schur-формула

### 4.1. Доказательство с правильным знаком

**L3 [FINITE_CELL | PAPER].** В разложении \(V_m=J\oplus J^\perp\):

\[
A_m-\mu I=
\begin{pmatrix}B-\mu I&C^*\\C&D-\mu I\end{pmatrix}.
\]

Так как \(\|B\|\le\delta<\mu\), блок \(B-\mu I\) отрицательно определён. Положим

\[
U_\mu=\begin{pmatrix}
I&(\mu I-B)^{-1}C^*\\0&I
\end{pmatrix}.
\]

Прямое умножение даёт

\[
\boxed{
U_\mu^*(A_m-\mu I)U_\mu
=\operatorname{diag}(B-\mu I,S_\mu),
\quad
S_\mu=D-\mu I+C(\mu I-B)^{-1}C^*.
}
\tag{4.1}
\]

Матрица \(U_\mu\) обратима, так что отрицательные индексы совпадают. Первый блок имеет ровно \(r\) отрицательных собственных значений. Это доказывает (0.2). Конгруэнция — стандартный механизм формулы инерции Хейнсворт [P1], но здесь она выписана и проверена непосредственно.

Знак перед связью **плюс**, поскольку исключаемый блок отрицателен. При собственном значении \(A_m\), равном \(\mu\), в \(S_\mu\) получается нулевое направление; оно правильно не входит в строгий счёт.

### 4.2. Более точный бюджет связи из полной невязки

**L4 [ABSTRACT | PAPER].** Из \(\|AQ\|\le\delta\) следует не только \(\|B\|,\|C\|\le\delta\), а

\[
B^2+C^*C\preceq\delta^2I.
\tag{4.2}
\]

Для \(\mu>\delta\) положим

\[
\tau(\delta,\mu)
=2\left(\mu-\sqrt{\mu^2-\delta^2}\right)
=\frac{2\delta^2}{\mu+\sqrt{\mu^2-\delta^2}}.
\]

Тогда

\[
\boxed{0\preceq C(\mu I-B)^{-1}C^*\preceq\tau(\delta,\mu)I.}
\tag{4.3}
\]

**Доказательство.** Пусть \(s=\mu-\sqrt{\mu^2-\delta^2}\), так что \(2\mu s-s^2=\delta^2\). Имеем точное неравенство функционального исчисления:

\[
2s(\mu I-B)-(\delta^2I-B^2)=(B-sI)^2\succeq0.
\]

Следовательно,

\[
(\mu I-B)^{-1/2}C^*C(\mu I-B)^{-1/2}
\preceq2sI.
\]

Ненулевые сингулярные значения произведения и его сопряжённого совпадают; отсюда (4.3). ∎

Граница наилучшая среди всех матриц с данной полной residual-нормой: при \(\mu=5,\delta=3,B=[1],C=[2\sqrt2]\) невязка равна 3, а связь равна \(8/(5-1)=2=\tau\). В частности, она **не расходится** при \(\mu\downarrow\delta\): \(\tau\le2\delta\). При \(\delta=o(\mu)\), \(\tau\sim\delta^2/\mu\).

Получаем конечные односторонние границы:

\[
\boxed{N_D(\mu-\tau)\le N_{A_m}(\mu)-r\le N_D(\mu).}
\tag{4.4}
\]

Они следуют из \(D-\mu I\preceq S_\mu\preceq D-(\mu-\tau)I\) и монотонности собственных значений. Если у \(D\) нет уровней в \([\mu-\tau,\mu)\), обе границы совпадают. Без такого разрешения границы порога одинаковое число не следует.

В (4.4) \(D\) — сжатие **полного** оператора. Никакого переноса индекса с усечённых нулей здесь ещё нет.

## 5. Возврат Schur-формулы к попарной матрице нулей

**L5 [FINITE_CELL | PAPER].** Используем (2.3), (2.5) и (3.1):

\[
B=Q^*R_TQ,\quad C=Z^*R_TQ,\quad
D=F^*\mathcal JF+R_\perp,
\quad R_\perp=Z^*R_TZ.
\tag{5.1}
\]

Поэтому

\[
S_\mu=F^*\mathcal JF+R_\perp-\mu I+C(\mu I-B)^{-1}C^*
=F^*(\mathcal J+\mathcal T_\mu)F.
\tag{5.2}
\]

Отсюда (0.3)–(0.5). В частности, физический порог в zero-space координатах имеет вид

\[
-\mu\,F^{-*}F^{-1},
\tag{5.3}
\]

а **не** \(-\mu I\). Это обязательная Gram/метрическая поправка. Знак \(\mathcal J\) не содержит информации о малых сингулярных значениях \(F\).

Разность индексов \(\iota\) можно интерпретировать как signed endpoint change вдоль эрмитова pencil \(\mathcal J+t\mathcal T_\mu\), \(0\le t\le1\). Для простых внутренних пересечений вниз она получает +1, вверх −1. Основное определение (0.5) остаётся корректным при кратных пересечениях и нулевых конечных собственных значениях; никакая transversal-гипотеза не нужна.

### Какой хвостовой бюджет действительно имеется

**[FINITE_CELL | PAPER, consequence of S1 §4].** Без зануления на \(J\) стандартная хвостовая Fourier-оценка даёт только

\[
\|R_T\|\le\Xi_m:=
8\frac{(1+v)^4}{(1-v)^4}
\frac{(2m+1)\sqrt m}{L}\mathcal Z(T),
\]
\[
v=(\kappa_m-\sqrt{\kappa_m^2-1})^2,\qquad
\mathcal Z(T)=\frac{\log T}{\pi T}+\frac{\log T+21/2}{T^2}.
\tag{5.4}
\]

Здесь отсутствует подавляющий множитель \(\theta^{k_m}\), потому что для вектора дополнения зануление ниже \(T\) не предполагается. В moving-kappa режиме эта имеющаяся верхняя граница не стремится к нулю. **Это не доказательство большого фактического хвоста**, а точная граница того, что оплачено нынешними оценками.

Кроме того, перевод в (0.4) может усилить её на \(\|F^{-1}\|^2\). Residual-оценка на \(J\) ни \(R_\perp\), ни этот inverse-evaluation фактор не оплачивает.

## 6. Точные проверки, которые убивают общий сокращённый вывод

### 6.1. Положительный хвост может удалить отрицательный pair-index

**K1 [ABSTRACT | PAPER; THEOREM_SHAPE ONLY].** Возьмём \(V=\mathbb C^3\) со стандартной метрикой, \(J=\operatorname{span}e_0\), и **сопряжённые** evaluation-строки

\[
E=\begin{pmatrix}
0&1/2&i/2\\
0&1/2&-i/2
\end{pmatrix},\qquad
\mathcal J=\begin{pmatrix}0&2\\2&0\end{pmatrix}.
\]

Здесь сохранены сопряжение строк реального базиса, фактор 2, один невещественный pair-блок, полный строковый ранг и точное ядро. Прямой расчёт:

\[
H=E^*\mathcal JE=\operatorname{diag}(0,1,-1).
\]

Добавим положительный rank-one хвост

\[
R=\operatorname{diag}(0,0,2)=2e_2e_2^*,\quad
A=H+R=\operatorname{diag}(0,1,1).
\tag{6.1}
\]

При \(\delta=0,\mu=1/2\):

\[
\|A|_J\|=0<\mu,\quad N_A(\mu)-\dim J=1-1=0,
\quad n_-(\mathcal J)=1.
\]

У полного дополнения оба уровня равны 1; ни одного в \([0,1/2)\) нет. Более того, **любой** неотрицательный дополнительный счёт дал бы правую часть не меньше 1. Поэтому предложенная общая формула нарушается со строгим discrepancy \(-1\).

Эта матрица опровергает только вывод из абстрактных предпосылок «попарная форма + точное evaluation-ядро + малая полная невязка». Она не объявляется literal CCM. Её можно расширять нулевым блоком произвольного растущего размера; невязка останется нулевой. Поэтому добавление лишь растущего ранга и сверхполиномиальной невязки не чинит этот общий вывод.

### 6.1b. Та же поломка при полном ранге всех evaluation-строк

**[ABSTRACT | PAPER].** Возражение «в предыдущем plant хвостовая строка зависима от низких» устраняется без изменения вывода. Сохраним тот же \(E\) и \(\mathcal J\), но возьмём

\[
w_\eta=(\eta,0,1),\quad R_\eta=2w_\eta^*w_\eta,\quad
A_\eta=\begin{pmatrix}
2\eta^2&0&2\eta\\0&1&0\\2\eta&0&1
\end{pmatrix},\qquad\eta>0.
\tag{6.2}
\]

Все три строки \(\left(\begin{smallmatrix}E\\w_\eta\end{smallmatrix}\right)\) теперь независимы: determinant равен \(-i\eta/2\). Сопряжение строк и положительный critical-type tail сохранены. При этом

\[
\|A_\eta e_0\|=2\eta\sqrt{1+\eta^2},\qquad D=I_2.
\]

При \(\eta=1/10\), \(\delta=\sqrt{101}/50<\mu=1/2\):

\[
S_\mu=\operatorname{diag}(1/2,7/12)\succ0,
\quad N_{A_\eta}(1/2)-1=0,
\quad n_-(\mathcal J)=1.
\]

У полного A остаётся одно отрицательное собственное значение, но оно стало near-zero и занимает один из уже оплаченных residual-кластером слотов. Оно не обязано быть **дополнительным** уровнем за пределами этих \(r\) слотов.

Можно взять \(\eta_m=e^{-m}\), \(\mu_m=m^{-B}\) для любого фиксированного \(B>0\), а также добавить нулевые координаты, увеличивающие \(r_m\). Тогда при всех достаточно больших m невязка положительна, сверхполиномиально мала и строго меньше \(\mu_m\), полный ранг трёх evaluation-строк сохранён, но excess count снова нулевой при pair-index 1. Этот plant всё ещё не заявлен literal CCM; он исключает объяснение ошибки только вырожденностью строк или нулевой residual-нормой.

### 6.2. Даже при положительных A и хвосте счёт сжатия может быть неверен

**K2 [ABSTRACT | PAPER; THEOREM_SHAPE ONLY].** Положим

\[
H=\operatorname{diag}(0,399/400),\qquad
R=\begin{pmatrix}1/100&1/10\\1/10&1\end{pmatrix}
=\begin{pmatrix}1/10\\1\end{pmatrix}
\begin{pmatrix}1/10&1\end{pmatrix},
\]
\[
A=H+R=\begin{pmatrix}1/100&1/10\\1/10&799/400\end{pmatrix},
\quad J=\operatorname{span}e_0,\quad\mu=2.
\]

Здесь \(A\succ0\), \(R\succeq0\), \(\delta=\sqrt{101}/100<\mu\). У сжатия \(D=[799/400]\) есть уровень ниже \(\mu\), но

\[
S_\mu=-1/400+1/199=201/79600>0.
\]

Поэтому \(N_A(2)-1=0\), а \(N_D(2)=1\). Простое использование спектра ортогонального сжатия вместо Schur-спектра неверно, даже в положительном примере.

### 6.3. Кратность не равна числу физических отрицательных направлений

**K3 [ABSTRACT | PAPER].** Повторим обе строки \(E\) из §6.1 дважды и возьмём \(\operatorname{diag}(\mathcal J,\mathcal J)\). Его ambient negative index равен 2. Но физическая форма равна \(2H\) и имеет negative index 1. Правильный distinct-node блок имеет вес кратности 2, а не две независимые физические пары.

### 6.4. Окно [-delta,mu) пересекает отрицательный спектр

**K4 [ABSTRACT | PAPER].** Даже при \(R=0\) нельзя автоматически складывать **весь** отрицательный индекс с числом уровней в \([-\delta,\mu)\). Возьмём

\[
A=\operatorname{diag}(0,-1/20,1),\quad
J=\operatorname{span}e_0,\quad\delta=1/10,\quad\mu=1/5.
\]

Невязка нулевая и не превосходит указанной \(\delta\). Слева \(N_A(\mu)-1=1\), а отрицательный индекс дополнения плюс его счёт в \([-\delta,\mu)\) равен \(1+1=2\). Малое отрицательное направление учтено дважды.

Таким образом, для окна с левой границей \(-\delta\) первый слагаемый индекс должен отвечать уровням **ниже −delta**, если не доказано их дополнительное разделение.

## 7. Формула с тем же интервалом, но без скрытого отождествления

**L6 [FINITE_CELL | PAPER].** Определим эффективное дополнение при фиксированном \(\mu\):

\[
\widetilde D_\mu:=D+C(\mu I-B)^{-1}C^*.
\]

Тогда точная версия разбиения пользователя такова:

\[
\boxed{
N_A(\mu)-r
=n_-(\widetilde D_\mu+\delta I)
+\#\bigl(\sigma(\widetilde D_\mu)\cap[-\delta,\mu)\bigr).
}
\tag{7.1}
\]

Уровни считаются с кратностями. Равенство — разбиение строгого счёта \(N_{\widetilde D_\mu}(\mu)\) на \(( -\infty,-\delta)\) и \([-\delta,\mu)\); оно сохраняет оба граничных соглашения.

Чтобы заменить первый член на \(n_-(\mathcal J)\), нужна отдельная source-теорема

\[
\boxed{n_-(\widetilde D_\mu+\delta I)=n_-(\mathcal J).}
\tag{7.2}
\]

Второй член (7.1) — спектральный счёт полного effective complement. Его принадлежность только полосе нулей \((\Omega,T)\) пока не установлена и не входит в определение \(J_m\).

Один достаточный, но не необходимый проверяемый бюджет для (7.2), при \(H=F^*\mathcal JF\), таков:

\[
\left\||H|^{-1/2}
\left[R_\perp+\delta I+C(\mu I-B)^{-1}C^*\right]
|H|^{-1/2}\right\|<1.
\tag{7.3}
\]

Действительно, после конгруэнции получается \(\operatorname{sgn}H+K\), \(\|K\|<1\); вдоль \(\operatorname{sgn}H+tK\) нуль не пересекается. (7.3) не принимается как новая обязательная гипотеза маршрута: это одна достаточная более сильная оценка с явно указанным потребителем. Для actual source она здесь не доказана.

## 8. Как строго определить «полосовое дополнение»

**L7 [ABSTRACT | PAPER, applied to literal nested constraints].** Положим

\[
J_\Omega=\ker E_{\gamma\le\Omega},\qquad J_T=J_m,
\quad U=J_\Omega^\perp,\quad W=J_\Omega\cap J_T^\perp.
\]

Нули ровно при \(\gamma=\Omega\) относятся к core; нули при \(\gamma=T\) остаются в хвосте. Тогда

\[
J_T^\perp=U\oplus W.
\tag{8.1}
\]

Это канонический кандидат на «направления, добавленные полосовыми условиями». Но он не обязан быть инвариантным для \(A\), \(D\) или \(S_\mu\).

В этих координатах запишем

\[
S_\mu=\begin{pmatrix}K&Y\\Y^*&Z_b\end{pmatrix}_{U\oplus W}.
\]

При обратимом \(K\) настоящая полосовая формула инерции есть

\[
\boxed{N_A(\mu)-r=n_-(K)+n_-(Z_b-Y^*K^{-1}Y).}
\tag{8.2}
\]

Здесь оба блока содержат полный хвост и coupling. Первый член не равен по определению \(n_-(\mathcal J)\), второй не является спектром отдельной суммы только полосовых нулей.

При вырожденном \(K\) можно сохранить точную формулу, не исключая границы. Пусть \(P_0\) — ортопроектор на \(\ker K\), \(K^\dagger\) — Moore–Penrose inverse, \(Y_0=P_0Y\), \(t=\operatorname{rank}Y_0\), и \(V_0\) — любой полноранговый базисный синтез \(\ker Y_0\subseteq W\). Тогда

\[
\boxed{
N_A(\mu)-r
=n_-(K)+t+
 n_-\!\left(V_0^*(Z_b-Y^*K^\dagger Y)V_0\right).
}
\tag{8.3}
\]

**Доказательство.** Сначала исключаем невырожденную часть \(K\), что даёт \(Z_b-Y^*K^\dagger Y\). В оставшейся части на \(\ker K\oplus W\) имеем блок \(\left(\begin{smallmatrix}0&Y_0\\Y_0^*&\cdot\end{smallmatrix}\right)\). Разложение по образу и ядру \(Y_0\) выделяет невырожденный \(2t\)-блок с инерцией \((t,t,0)\). Его inverse имеет нулевой нижний диагональный блок, поэтому последующее исключение не меняет сжатие на \(\ker Y_0\). Оставшиеся \(\dim\ker K-t\) направления нулевые. Это даёт (8.3). ∎

Формулы (8.2)–(8.3) — реальные точные альтернативы свободному приписыванию уровней нулям. Они также показывают дополнительный kernel-coupling index при singular core.

## 9. Что говорят capacity-данные и чего они не говорят

**[FINITE_CELL | CONDITIONAL, reported numerical evidence only].** [S2] сообщает \(\|A-2E^*E\|\approx0.10118\) при \(m=16\) и \(0.12764\) при \(m=24\), для таблицы нулей до 400; minimum same-index overlaps squared около 0.99780 и 0.99619. Это floating diagnostics, не интервальная инерция.

Эти данные не контролируют \(F^{-*}(R_\perp-\mu I+\cdots)F^{-1}\) при cutoff \(T=\kappa_m\Omega_m\) и не разрешают спектральную границу \(\mu\). Сам [S2] отмечает смешивание нескольких нулей в одной carrier-моде и почти коллинеарные высокочастотные строки. [S3] явно не утверждает безусловной положительности оставшегося хвоста.

Даже совпадение eigenvectors на 100% не сохраняет инерцию без границы на eigenvalues относительно порога: \(\operatorname{diag}(0,-\eta)\) и \(\operatorname{diag}(0,\eta)\) имеют один eigenbasis и разные отрицательные индексы. Это точная алгебра, не критика качества вычисленных данных.

## 10. Что проверено и что остаётся источниковой задачей

### DISCRIMINATOR

Для source upper-count потребителя минимальный объект:

\[
\boxed{S_{m,\mu}=D_m-\mu I+C_m(\mu I-B_m)^{-1}C_m^*.}
\]

Проверяемый критерий:

\[
N_{A_m}(\mu)\le r_m\quad\Longleftrightarrow\quad S_{m,\mu}\succeq0.
\tag{10.1}
\]

При \(\|AQ\|\le\delta<\mu\) уже имеется не меньше \(r_m\) уровней в \([-\delta,\delta]\), поэтому верхний счёт в (10.1) насыщен. Никакой source-нижней оценки \(S_{m,\mu}\) в этой работе не получено.

Для нулевого интервала вокруг порога нельзя фиксировать индекс по floating sign. Решающее свидетельство — certified one-sided bound для relevant Schur pivot / eigenvalue; при точном нуле — проверяемый kernel и учёт nullity. Для индекса (7.2) нужен также контроль у границы \(-\delta\). Нуль-совместимый determinant enclosure без этих данных не решает счёт.

### Две рабочие репрезентации до увеличения вычислений

| Представление | Что решает | Kill-power / cost | Главный риск |
|---|---|---|---|
| Физический \(S_{m,\mu}\) с sharp coupling budget (4.3) | Точный excess count; finite inertia и источник для upper count | 9/10 / 3–5/10 | Необходим сертифицированный source sign, а не overlap |
| Zero-space \(\mathcal J+\mathcal T_\mu\) и relative inertia | Проверяет именно замену tail correction на pair-index | 9/10 / 5–7/10 | Обратная evaluation-метрика может быть плохо обусловлена |

Альтернативный третий мост уже выписан: nested constraint spaces и полосовой Schur (8.3). Это не маршрут перебора отдельных собственных векторов.

### Consumer-first contract

```yaml
DOWNSTREAM_CONSUMER: NOESCAPE_L12_L13_SPECTRAL_SATURATION
ACTUAL_CONSUMER_REQUIREMENT: >-
  A genuine residual-bounded J_m, delta_m<mu_m, and cofinal
  N_A_m(mu_m)<=dim(J_m); delta_m tends to zero for L13.
ORIGINAL_REQUESTED_OBJECT: >-
  Pair-index below T plus a nonnegative count of complementary
  near-zero levels attributed only to the zero strip (Omega,T).
ORIGINAL_OBJECT_IS: NOT_NECESSARY
KNOWN_WEAKER_INTERFACES:
  - S_m_mu_positive_semidefinite_implies_saturated_upper_count
  - direct_cofinal_lower_floor_can_bypass_this_counting_interface
EXACT_Z_IMPLIES_Y: >-
  S_m_mu>=0 iff N_A_m(mu_m)<=dim(J_m), under delta_m<mu_m.
FAILURE_TYPE_FOR_LITERAL_FORMULA: NO_DERIVATION
EPISTEMIC_STATUS_FOR_LITERAL_FORMULA: RESEARCH_DEBT
NOVELTY_AXIS: >-
  Exact complex-zero pairing and metric-corrected Schur inertia;
  explicit signed tail defect, sharp coupling budget, and singular
  nested-strip correction replace an unsupported additive count.
REOPEN_TRIGGER: >-
  An actual-source theorem proves the relative deep-index transfer
  (7.2), with a precise strip spectral subspace; or a certified
  actual-source counterexample disproves that transfer.
FORBIDDEN_UPGRADE: >-
  The planted matrices do not prove a literal CCM failure or route death.
```

### CODEX DIRECTIVE — ровно одна задача

Выполнить bounded independent audit **источникового перехода (5.1)–(5.2)** на закреплённых [S1–S3], включая distinct-node/weighted multiplicity convention, строгие cutoff endpoints, physical metric и полный \(R_T\). Затем проверить, имеется ли в этих же suppliers что-либо, устанавливающее (7.2), а не только малость \(R_TQ\). Для проверки алгебры воспроизвести встроенный exact-control appendix. Возвращать `EXACT_CORRECTED_INERTIA_VERIFIED / RELATIVE_TAIL_INDEX_OPEN`, если истинны именно эти две части; при обнаружении дефекта дать первую неверную строку и exact plant. Не запускать расширение спектральных таблиц, не объявлять tail PSD, не менять route-state и не продвигать RH.

## 11. Closeout и fate predictions

До exact plant была зарегистрирована ставка: **pair-index сам по себе не определяет excess count; хвост способен изменить его при нулевой невязке на J**. Fate: **CONFIRMED**, §6.1, discrepancy ровно −1. Другие приведённые проверки — algebraic validation controls, не ретроактивно объявленные предсказания.

Что стало меньше: локализована единственная точная матрица переноса \(\mathcal T_\mu\), отделены inverse-evaluation metric, полный хвост и положительная Schur-связь. Последняя получила sharp universal budget, а не неуправляемый фактор \(1/(\mu-\delta)\).

Что убито: общий tail-free вывод и прямой счёт спектра ортогонального сжатия. Не убиты literal CCM, moving-kappa residual-теорема или маршрут к lower floor.

Что не повторять: не заменять \(A\) на \(E^*\mathcal JE\) без инерционного бюджета; не считать повторённые zero-координаты независимыми; не считать \([-\delta,\mu)\) непересекающимся со всеми отрицательными уровнями; не назначать уровню принадлежность полосе по спектральному сходству.

Текущая минимальная source-неизвестная для предложенной формулы: (7.2) плюс определённая спектральная локализация полосового счёта. Для прежнего saturation-потребителя — односторонний source sign (10.1). Это разные задачи, и более сильная первая не навязана второй.

```yaml
iteration:
  target: PROPOSED_EXACT_LOW_ZERO_PAIR_PLUS_STRIP_INERTIA
  status: OPEN_FOR_LITERAL_SOURCE
  failed_strategy: DELETE_ZERO_TAIL_INDEX_FROM_LOW_PAIRING
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: ACTUAL_RELATIVE_ZERO_TAIL_INERTIA_TRANSFER
  invariant_learned: >-
    Residual smallness fixes J columns, not complement inertia;
    threshold transport carries the inverse evaluation metric.
  forbidden_future_move: NONNEGATIVE_STRIP_COUNT_AS_UNPROVED_SIGNED_DEFECT
  next_decisive_test: SOURCE_AUDIT_OF_RELATIVE_INERTIA_SUPPLIER
```

## 12. Источники и граница верификации

[S1] `Malaeu/chen_q3`, commit `2176dab16bf77dd015f7efcb5a6f704587f732c8`, файл `docs/routeB_bus/proshka/PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md`, Git blob `ebf7f8cab61a795118bda5dc7e65a0b3386247b7`. Использованы определения (0.1)–(0.2), rank boundary §1 и полная явная формула/residual scope §4. Локальный SHA-256 `fb0176935d103209bea3feff8362605024da7635c568768dc5355f441e5ddd14` совпал с точным Git blob.

[S2] `Malaeu/chen_q3`, `bf89051`, `docs/routeB_bus/capacity_matrix_2026-11-02/RESULT.md`, blob `a9f50694f8677e89fe80bc2db82387be6d15e7b3`. Числа и caveats — сообщения отчёта, не новые вычисления настоящей работы.

[S3] Та же pin, `docs/routeB_bus/capacity_matrix_2026-11-02/NORMALIZATION.md`, blob `54f37eef47dee0f59b6b95c31b5858dcdf900a5d`. Проверены factor 2, multiplicity, indefinite off-critical pairing, full compensation и отсутствие безусловной tail positivity.

[P1] D. Nerantzis, C. S. Adjiman, *Tighter alpha BB relaxations through a refinement scheme for the scaled Gerschgorin theorem*, Journal of Global Optimization 73 (2019), 467–483, Theorem 3.2, DOI `10.1007/s10898-018-0718-y`. Первичная исследовательская статья, прочитана HTML-версия; в ней явно сформулирована используемая Schur/Haynsworth inertia formula. Само требуемое эрмитово тождество независимо доказано умножением в (4.1); никакой неоплаченной perturbation theorem из статьи не импортируется.

Программно выполнены exact SymPy controls из §13: conjugate-pair plant, positive-tail compression plant, repeated-row multiplicity, negative-window double count, 32 rational full Schur congruences/count sandwiches, 16 singular-core formulas, sharp-budget equality. Это проверки алгебры, не заменители изложенных доказательств и не интервальная сертификация literal data.

В этой сессии нет независимого математического аудита, Lean run, ARB_INTERVAL или repository write. Источник не повышен до LEAN_PROVED. Проверка произвольных схем не объявлена проверкой фактической CCM-ячейки.

## 13. Исполненный exact-control appendix

Сохранить следующий блок как `/tmp/proshka_inertia_controls.py` и выполнить:

```sh
uv run --with sympy python /tmp/proshka_inertia_controls.py
```

`/tmp/proshka_inertia_controls.py` — путь к файлу с блоком ниже. Никакие credentials, repository paths или численные источники не требуются. Все матрицы — явно помеченные algebraic controls.

<!-- BEGIN_EXECUTABLE_CONTROLS -->
```python
import hashlib
import json
import random
import sympy as s

# Exact Hermitian congruence elimination; no eigenvalue rounding.
def inertia(A):
    A=s.Matrix(A)
    assert A==A.conjugate().T
    pos=neg=zero=0
    while A.rows:
        n=A.rows
        i=next((i for i in range(n) if A[i,i]!=0), None)
        if i is not None:
            order=[i]+[j for j in range(n) if j!=i]
            A=A.extract(order,order)
            a=A[0,0]
            if a.is_positive: pos+=1
            elif a.is_negative: neg+=1
            else: raise AssertionError('Undecided exact pivot')
            v=A[1:,0:1]
            A=s.simplify(A[1:,1:]-v*v.conjugate().T/a)
        else:
            ij=next(((i,j) for i in range(n) for j in range(i+1,n) if A[i,j]!=0), None)
            if ij is None:
                zero+=n
                break
            i,j=ij
            order=[i,j]+[k for k in range(n) if k not in (i,j)]
            A=A.extract(order,order)
            H=A[:2,:2]; C=A[2:,:2]
            pos+=1; neg+=1
            A=s.simplify(A[2:,2:]-C*H.inv()*C.conjugate().T)
    return pos,neg,zero

# Distinct conjugate evaluations, correct factor two, multiplicity one.
E=s.Matrix([[0,s.Rational(1,2),s.I/2],[0,s.Rational(1,2),-s.I/2]])
J=s.Matrix([[0,2],[2,0]])
Q=s.Matrix([1,0,0]); Z=s.Matrix([[0,0],[1,0],[0,1]])
H=s.simplify(E.conjugate().T*J*E)
R=s.diag(0,0,2); A=H+R; mu=s.Rational(1,2)
assert E[1,:]==s.conjugate(E[0,:])
assert H==s.diag(0,1,-1) and A==s.diag(0,1,1)
assert A*Q==s.zeros(3,1) and inertia(R)[1]==0
assert inertia(A-mu*s.eye(3))[1]-1==0
assert inertia(J)[1]==1
F=E*Z
D=Z.T*A*Z
Tzero=s.simplify(F.conjugate().T.inv()*(Z.T*R*Z-mu*s.eye(2))*F.inv())
assert s.simplify(F.conjugate().T*(J+Tzero)*F-(D-mu*s.eye(2)))==s.zeros(2)
assert inertia(J+Tzero)[1]==0
print('P1: negative paired index erased by a positive rank-one tail: PASS')
print('MAIN: H=diag(0,1,-1); R=diag(0,0,2); A=diag(0,1,1); delta=0; mu=1/2; index defect=-1')

# Raw compression need not give the true excess count, even for A>=0, R>=0.
e=s.Rational(1,10)
H=s.diag(0,1-e**2/4)
v=s.Matrix([e,1]); R=v*v.T; A=H+R; mu=s.Integer(2)
b=A[0,0]; g=A[1,0]; d=A[1,1]
S=s.simplify(d-mu+g**2/(mu-b))
assert inertia(A)[1]==0 and inertia(R)[1]==0
assert S==s.Rational(201,79600)>0 and d<mu
assert inertia(A-mu*s.eye(2))[1]-1==0
assert g**2+b**2==s.Rational(101,10000)
print('Raw-compression control: PASS; S=201/79600, d=799/400<2')

# Repeating a pair is not a new physical direction.
E2=E.col_join(E)
J2=s.diag(J,J)
assert inertia(J2)[1]==2
assert inertia(s.simplify(E2.conjugate().T*J2*E2))[1]==1
print('Multiplicity/image-rank control: PASS')

# Small negative modes are double-counted by an unguarded [-delta,mu) addend.
A=s.diag(0,-s.Rational(1,20),1)
delta=s.Rational(1,10); mu=s.Rational(1,5)
assert inertia(A-mu*s.eye(3))[1]-1==1
assert inertia(s.diag(-s.Rational(1,20),1))[1]+1==2
print('Negative-window double-count control: PASS')

# Exact family check for the Schur sign and the count sandwich.
rng=random.Random(2176)
for trial in range(32):
    r,q=2,3
    B=s.zeros(r)
    C=s.Matrix(q,r,[s.Rational(rng.randint(-2,2),100) for _ in range(q*r)])
    X=s.Matrix(q,q,[s.Rational(rng.randint(-4,4),3) for _ in range(q*q)])
    D=X+X.T
    mu=s.Integer(1); delta=s.Rational(1,4)
    assert sum(abs(x)**2 for x in C)<=delta**2
    A=B.row_join(C.T).col_join(C.row_join(D))
    S=D-s.eye(q)+C*C.T
    P=s.eye(r).row_join(C.T).col_join(s.zeros(q,r).row_join(s.eye(q)))
    assert s.simplify(P.T*(A-s.eye(r+q))*P-s.diag(-s.eye(r),S))==s.zeros(r+q)
    excess=inertia(A-s.eye(r+q))[1]-r
    assert excess==inertia(S)[1]
    t=delta**2/(mu-delta)
    assert inertia(D-(mu-t)*s.eye(q))[1]<=excess<=inertia(D-mu*s.eye(q))[1]
print('32 rational Schur congruence and count-sandwich cases: PASS')
print('No literal CCM matrices, Lean or interval arithmetic were run.')
# Singular-core strip formula: the kernel-coupling rank is essential.
for trial in range(16):
    H=s.diag(s.Rational(1 if trial%2 else -1),0)
    C=s.Matrix(2,2,[s.Rational(rng.randint(-3,3),2) for _ in range(4)])
    D0=s.Matrix(2,2,[s.Rational(rng.randint(-3,3),2) for _ in range(4)])
    D=D0+D0.T
    Hp=s.diag(1/H[0,0],0)
    K=s.diag(0,1)*C
    basis=K.nullspace()
    V=s.Matrix.hstack(*basis) if basis else s.zeros(2,0)
    T=s.simplify(V.T*(D-C.T*Hp*C)*V)
    M=H.row_join(C).col_join(C.T.row_join(D))
    assert inertia(M)[1]==inertia(H)[1]+K.rank()+inertia(T)[1]
print('16 exact singular-core strip decompositions: PASS')
# Sharp full-residual coupling budget (not just separate B and C bounds).
mu=s.Integer(5); delta=s.Integer(3); b=s.Integer(1); g=2*s.sqrt(2)
t=2*(mu-s.sqrt(mu**2-delta**2))
assert b*b+g*g==delta**2
assert s.simplify(g*g/(mu-b)-t)==0 and t==2
print('Sharp residual-to-Schur correction budget: attained exactly at (mu,delta,b,g)=(5,3,1,2sqrt(2))')
# Robust plant: all retained and tail evaluation rows independent, residual >0.
E=s.Matrix([[0,s.Rational(1,2),s.I/2],[0,s.Rational(1,2),-s.I/2]])
J=s.Matrix([[0,2],[2,0]])
e=s.Rational(1,10); w=s.Matrix([[e,0,1]])
Eall=E.col_join(w)
H=s.simplify(E.conjugate().T*J*E)
R=2*w.T*w; A=H+R
mu=s.Rational(1,2); Q=s.Matrix([1,0,0]); Z=s.Matrix([[0,0],[1,0],[0,1]])
B=Q.T*A*Q; C=Z.T*A*Q; D=Z.T*A*Z
S=s.simplify(D-mu*s.eye(2)+C*(mu*s.eye(1)-B).inv()*C.T)
assert Eall.det()==-s.I/20 and Eall.rank()==3
assert inertia(R)[1]==0 and inertia(A)[1]==1
assert S==s.diag(s.Rational(1,2),s.Rational(7,12))
assert inertia(A-mu*s.eye(3))[1]-1==0
assert s.simplify((A*Q).dot(A*Q))==s.Rational(101,2500)
print('Full-row-rank positive-tail plant: PASS; det(Eall)=-i/20; residual^2=101/2500; Schur=diag(1/2,7/12); excess=0, pair index=1')
```
<!-- END_EXECUTABLE_CONTROLS -->

Фактический stdout:

```text
P1: negative paired index erased by a positive rank-one tail: PASS
MAIN: H=diag(0,1,-1); R=diag(0,0,2); A=diag(0,1,1); delta=0; mu=1/2; index defect=-1
Raw-compression control: PASS; S=201/79600, d=799/400<2
Multiplicity/image-rank control: PASS
Negative-window double-count control: PASS
32 rational Schur congruence and count-sandwich cases: PASS
No literal CCM matrices, Lean or interval arithmetic were run.
16 exact singular-core strip decompositions: PASS
Sharp residual-to-Schur correction budget: attained exactly at (mu,delta,b,g)=(5,3,1,2sqrt(2))
Full-row-rank positive-tail plant: PASS; det(Eall)=-i/20; residual^2=101/2500; Schur=diag(1/2,7/12); excess=0, pair index=1
```