# STATUS: TRY_QUIET_SPACE_THRESHOLD_INDEX

```yaml
OPERATIVE_CLASS: TRY_QUIET_SPACE_THRESHOLD_INDEX
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_FIXED_THRESHOLD_ZERO_PAIR_INDEX_REQUEST
TASK_MODE: MATHEMATICAL_RESPONSE_NOT_FORMAL_TXT_BUS_ADJUDICATION
SOURCE_OPERATOR: LITERAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
SOURCE_RESIDUAL_COMMIT: 2176dab16bf77dd015f7efcb5a6f704587f732c8
SOURCE_RESIDUAL_BLOB: ebf7f8cab61a795118bda5dc7e65a0b3386247b7
SOURCE_ADAPTIVE_COMMIT: 3bdd5f8ffa106036b74cfaa0794f60155156d563
SOURCE_ADAPTIVE_RESULT_BLOB: 38191320ba934eb36eb4b7e52095db5a32002268
SOURCE_ADAPTIVE_SCAN_BLOB: c6d6a4efa998b2163c4d0c4817fc300dfbd81e86
SOURCE_ZERO_NORMALIZATION_COMMIT: bf890512b36abf2330d8f61a95f120cae58d0e0a
SOURCE_ZERO_NORMALIZATION_BLOB: 54f37eef47dee0f59b6b95c31b5858dcdf900a5d
SOURCE_CONSTANT_FLOOR_COMMIT: d142486a735a11c48e2a1478dd4c632d89c8f6f4
SOURCE_CONSTANT_FLOOR_BLOB: 26eaa3ebe5f8fea7fadbdc6d1994654c4710b8c7
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: EXACT_THRESHOLD_SCHUR_INDEX_WITH_UNPAID_CORE_INERTIA
REQUESTED_RAW_PAIR_PLUS_NONNEGATIVE_BAND_FORMULA: NOT_PROVED
LITERAL_COFINAL_CLAIM_REFUTED: false
EXACT_ACTIVE_EVALUATION_RANK: PROVED_PAPER
UNSHIFTED_TRUNCATED_ZERO_INERTIA: PROVED_PAPER
FULL_THRESHOLD_INERTIA_WITH_ALL_TAILS: PROVED_PAPER
CONSTANT_RESIDUAL_SUFFICES_WITH_SATURATION: PROVED_USING_PINNED_FLOOR
FIXED_C_2_ON_FOUR_SELECTED_SAVED_SECTORS: FLOATING_DATA_CONSEQUENCE_NOT_CERTIFICATE
GENERAL_RAW_PAIR_INDEX_SHORTCUT: REFUTED_ONLY_AT_ABSTRACT_THEOREM_SHAPE_SCOPE
ZERO_LOCATION_ASSUMED: false
SIMPLE_ZEROS_ASSUMED: false
PRIME_POWERS_POLES_ARCHIMEDEAN_SOURCE: RETAINED_THROUGH_FULL_EXPLICIT_FORMULA
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ADDITIONAL_PROGRESS: EXACT_RANK_AND_SCOPED_ALGEBRAIC_FALSIFIERS
NEW_COFINAL_SOURCE_SIGN: NONE
EXACT_CONTROL_GROUPS: 8
REPORTED_DATA_SCALAR_CONTROL: 1
NEW_CCM_EIGENPROBLEMS: 0
INDEPENDENT_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
ROUTE_PROMOTION: false
```

## 0. Итог и граница

Константного нижнего пола действительно достаточно. Сверхмалая невязка не обязательна: достаточно одной конечной верхней границы невязки и точного насыщения ниже более высокого постоянного порога на неограниченной исходной семье.

Однако предложенная формула с **неизменённой матрицей попарного вклада нулей** и только неотрицательной полосовой добавкой не получена. Точный индекс содержит пороговую метрику, бесконечный нулевой хвост и поправку исключения тихого пространства. Ни один из этих членов не удаляется из явной формулы.

Ниже доказаны: точный ранг фактических value-условий с комплексными нулями; инерция конечной нулевой части при нулевом пороге; полный индекс при положительном C; точная формула изменения дефекта при расширении полосы; постоянный-floor потребитель. Контрпримеры к общему shortcut явно абстрактные, не другой CCM и не опровержение возможной кофинальной теоремы настоящего источника.

## 1. Что именно предоставляют закреплённые источники

**[FINITE_CELL | PAPER: проверка содержания источников, не сертификация чисел.]**

S1. `docs/routeB_bus/proshka/PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md`, pin 2176dab, определения (0.1)–(0.2), теорема (0.3)–(0.5), §4. Прочитаны эти разделы. Используется как унаследованный PAPER-поставщик, без нового независимого аудита его аналитического доказательства.

S2. `docs/routeB_bus/quiet_space_kappa_2026-11-02/adaptive_threshold/RESULT.md` и строки `scan.csv`, pin 3bdd5f8. Сохранены 84 точки на FOUR размерах m=16,24,32,40. Это не все целые от 16 до 40. Порог равен delta*(1+10^-6), не одному C. Насыщение есть в перечисленных секторах, не на всех kappa. В частности, при m=24,kappa=1: r=17, delta≈2.956529432, N_A(delta+)=20.

S3. `docs/routeB_bus/capacity_matrix_2026-11-02/NORMALIZATION.md`, pin bf89051. Удержанный вклад реальных положительных нулей равен 2E*E; off-critical вклад не является абсолютным квадратом. Остаток после конечного списка нулей не объявлен положительным. Нулевой индекс и физический carrier — разные пространства.

S4. `docs/routeB_bus/proshka/NOESCAPE_CONSTANT_FLOOR_REDUCTION_2026-10-31.md`, pin d142486. Унаследованный PAPER-вывод: при not-RH исходный lambda_min(A_m) стремится к -infinity; поэтому любой постоянный нижний пол на неограниченной исходной семье достаточен для RH. Не используется несуществующий по этому pin файл с другим именем `PROSHKA_VERDICT_SEMIBOUND...`.

Тонкость S1: сверхполиномиальная невязка доказана для выбранного расписания kappa=1+c(1+log log m)/log m при FIXED 0<c<1. Это НЕ равномерная оценка для всего закрытого интервала, включающего kappa=1. Там константы зависят от расстояния до 1. Далее точная индексная формула действует для любого kappa, когда выполнено указанное условие на тихий блок.

### Общий постоянный порог в сохранённых данных

Выбирая сектора (m,kappa)=(16,1),(24,1.02),(32,1),(40,1), получаем из опубликованных чисел:

|m|r|delta|lambda_r|общий C|
|---:|---:|---:|---:|---:|
|16|12|1.36271876|2.28564356|2|
|24|16|0.591690030|2.27276429|2|
|32|21|1.21381573|2.30665006|2|
|40|25|0.994272082|2.19035639|2|

На уровне этих floating-данных delta<2<lambda_r, так что N_A(2)=r. Это полезный finite discriminator, не интервальный и не кофинальный результат. При том же C=2, но m=24,kappa=1, данные дают N_A(2)-r=16-17=-1. Поэтому условие, что всё тихое пространство лежит ниже C, нельзя опускать даже при обсуждении этих таблиц.

## 2. Попарная нулевая форма без RH и без предположения простоты

**[FINITE_CELL | PAPER; все утверждения ниже о точных объектах.]**

Пусть d=m+1, L=log m, Omega=2*pi*m/L, T=kappa*Omega. Используем исходный вещественный чётный ортонормированный базис

    phi_j(x)=d_j*(-1)^j*cos(2*pi*j*x/L)/sqrt(L), |x|<=L/2,
    d_0=1, d_j=sqrt(2) (j>0),

с нулевым продолжением. Обозначим F_f(z)=hat f(z). Условие J_T — F_f(i(rho-1/2))=0 для ВСЕХ фактических нулей с 0<|Im rho|<T; в кратных нулях производные не добавляются.

Группируем симметричные нули в орбиты. Для критической пары ±gamma кратности nu её вклад на вещественном чётном f равен

    2 nu F_f(gamma)^2.

Для off-critical четвёрки с координатами ±(gamma+i beta), ±(gamma-i beta), beta!=0, кратности nu в каждой точке:

    4 nu Re(F_f(gamma+i beta)^2)
    =4 nu[(Re F_f(gamma+i beta))^2-(Im F_f(gamma+i beta))^2].       (2.1)

Следовательно, пусть E_T — вещественная матрица value-условий: одна строка на различную критическую пару; две строки Re/Im на различную off-critical четвёрку. Тогда

    A_<T = E_T^T Jcal_T E_T,
    Jcal_T = direct_sum [2 nu] and diag(4 nu,-4 nu),
    A_m = A_<T + R_T.                                           (2.2)

R_T — ПОЛНАЯ сумма всех оставшихся нулей с |Im rho|>=T. Полюс и prime powers не добавляются повторно: они уже входят в A_m и в полную явную формулу. В частности, (2.2) не заменяет R_T нулём или положительной матрицей.

Множитель кратности nu сохранён. Он не создаёт nu независимых value-условий. Повторение одинаковых строк допустимо, но перед вычислением их доступной инерции нужно факторизовать точные зависимости. Отдельная off-critical четвёрка кратности nu даёт ONE отрицательное направление в своих двух реальных value-координатах, а не nu независимых направлений.

Нулевая сумма для фиксированного m абсолютно сходится: в критической полосе Fourier-образы этих BV-функций равны O_m((1+|Re z|)^-1), и сумма |gamma|^-2 с кратностями конечна. Это тот же переход, который выписан в S1 §4.1.

## 3. Точный ранг и инерция УСЕЧЁННОЙ нулевой формы

**Теорема 1. [FINITE_CELL | PAPER.]** Удалим из E_T точно нулевые строки, агрегируем повторения. Пусть q_T — число оставшихся вещественных условий, то есть одна координата на реальную пару и две на комплексную четвёрку. Тогда

    rank E_T = min(q_T,m+1),
    dim J_T = max(m+1-q_T,0).                                  (3.1)

**Доказательство.** Положим p_j=(2*pi*j/L)^2 и D(t)=prod_(j=0)^m(t-p_j). Точная формула базисного преобразования:

    hat phi_j(z)=2 d_j z sin(zL/2)/(sqrt(L)(z^2-p_j)),
    F_f(z)=2 z sin(zL/2)/sqrt(L) * P_f(z^2)/D(z^2),
    P_f(t)=sum_(j=0)^m d_j a_j prod_(k!=j)(t-p_k).              (3.2)

Все модальные особенности устранимы. Отображение a->P_f изоморфно пространству вещественных полиномов степени <=m, поскольку P_f(p_j)=d_j a_j D'(p_j).

В немодальной точке с sin(zL/2)!=0 условие F_f(z)=0 равносильно P_f(z^2)=0. В модальной точке z=2*pi*j/L, |j|<=m, устранимый множитель ненулевой, так что условие снова P_f(p_j)=0. Единственные автоматические внешние строки: реальный z=2*pi*k/L с |k|>m; они равны нулю на ВСЁМ carrier и удаляются.

Оставшиеся квадратные узлы различны после группировки ±; невещественные узлы идут сопряжёнными парами. Полиномиальная интерполяция даёт независимость всех q_T условий, пока q_T<=m+1. При q_T>m любой полином степени <=m, зануляющийся в этих узлах, тождественно нулевой. Реальная размерность сопряжённой пары равна двум. Это доказывает (3.1). ∎

На всём диапазоне 1<=kappa<=1+c(1+log log m)/log m при FIXED 0<c<1 унаследованная оценка числа нулей S1 обеспечивает q_T<=N(T)<m+1 для больших m. Для ранга это равномерно, поскольку верхний конец диапазона даёт максимальное N(T). Для residual равномерности такой вывод не сделан.

**Следствие. [FINITE_CELL | PAPER.]** При q_T<=d:

    n_-(A_<T)=n_-(Jcal_T),
    n_0(A_<T)=dim J_T.                                        (3.3)

Действительно, дополним изометрический frame Q пространства J_T до [Q,U]. Матрица F=E_T U квадратна и обратима. В этом базисе A_<T=diag(0,F^T Jcal_T F). Невырожденная конгруэнция сохраняет инерцию.

Это строгий попарный индекс, но для УСЕЧЁННОЙ формы при пороге ZERO. Не для A_m-CI. Условие P_f(z^2)=0 не заменяется условиями на производные даже при кратности нуля zeta.

## 4. Точный индекс полного A_m при положительном C

**Теорема 2. [FINITE_CELL | PAPER.]** Пусть Q — изометрический frame J_T ранга r, U — изометрический frame J_T^perp. Введём

    D=Q^T A_m Q,  B=U^T A_m Q,  G=U^T A_m U.

Если C>lambda_max(D), то

    N_A_m(C)-r = n_-(S_m(C)),
    S_m(C)=G-CI+B(CI-D)^-1 B^T.                               (4.1)

Счёт N_A(C)=#{lambda<C} строгий. Нулевые собственные значения S не считаются отрицательными; поэтому равенство уровня C обработано точно.

**Доказательство.** В выбранном базисе A-CI имеет блоки H=D-CI, B^T, B, G-CI, причём H отрицательно определена. Конгруэнция матрицей

    [[I, -H^-1 B^T], [0,I]]

превращает её в diag(H,G-CI-B H^-1 B^T). Первый блок имеет ровно r отрицательных значений; второй равен S. Это и есть (4.1). ∎

Достаточно delta=||A_mQ||<C. Тогда ||D||,||B||<=delta и

    0 <= B(CI-D)^-1B^T <= delta^2/(C-delta) I.                 (4.2)

Знак поправки PLUS: исключается отрицательный, а не положительный блок A-CI. Из (4.2) следует строгая двусторонняя оценка

    N_G(C-delta^2/(C-delta))
      <= N_A(C)-r <= N_G(C).                                 (4.3)

Малая delta оплачивает только узкую неопределённость от coupling. Она не даёт знак G-CI. При delta=O(1), C>delta, формула остаётся точной; сверхмалая delta не нужна для её применения.

Если C<=lambda_max(D), формула с вычитанием r вообще не обязательна. При обратимом D-CI вместо r стоит n_-(D-CI). Если этот блок сингулярен, нельзя просто вставить псевдообратную без range-condition; можно считать при регулярных s<C и брать предел s↑C. Нулевые уровни на конечном пороге не удаляются.

## 5. Полная формула именно в координатах нулевых пар

**Теорема 3. [FINITE_CELL | PAPER; q_T=d-r.]** В обозначениях (2.2), (3.3):

    D=Q^T R_T Q,
    B=U^T R_T Q,
    G=F^T Jcal_T F + R_11,     R_11=U^T R_T U.

Поэтому определим

    Delta_m(C)=F^-T [ R_11-CI+B(CI-D)^-1B^T ] F^-1.            (5.1)

Тогда

    N_A_m(C)-dim J_T = n_-(Jcal_T+Delta_m(C)).                 (5.2)

**Доказательство:** подставить G в (4.1) и выполнить конгруэнцию F^-1. ∎

В Delta сохранены три разных объекта:

- пороговая метрика -C F^-T F^-1, НЕ ноль;
- полный высоконулевой хвост F^-T R_11 F^-1, НЕ только полоса (Omega,T);
- положительная поправка связи с тихим пространством.

S1 контролирует R_T Q, следовательно D и B. Он НЕ ограничивает R_11 тем же delta и НЕ даёт нижнюю границу sigma_min(F). Поэтому из даже сверхмалой невязки нельзя вывести малость Delta.

### Явный, но недостаточный, абсолютный бюджет хвоста

**[FINITE_CELL | PAPER; T>Omega, T>=e.]** Из (3.2), |Im z|<=1/2 и обратного неравенства треугольника:

    ||(hat phi_j(z))_j||^2
    <= 4(2m+1)sqrt(m)/L * (1+1/(4T^2))
       / (1-Omega^2/T^2)^2 * gamma^-2,     |Re z|=gamma>=T.

Используя унаследованную S1 (4.3),

    Z(T)=log(T)/(pi*T)+(log(T)+21/2)/T^2,

получаем со всеми знаками gamma и кратностями

    ||R_T|| <= E_m(T)
      := 8(2m+1)sqrt(m)/L * (1+1/(4T^2))
         * Z(T)/(1-Omega^2/T^2)^2.                           (5.3)

Здесь не использована RH и не положено beta=0. При T=Omega этот бюджет не применяется: нужно оставить конечный участок до любого T1>Omega точно, а (5.3) применить после T1.

При kappa=1+c(1+log L)/L выражение E_m(T) имеет грубый порядок O_c(sqrt(m)L^3/(1+log L)^2), а не o(1). Это НЕ утверждение о росте истинного знакового хвоста: только цена данного абсолютного upper. Нормированная поправка дополнительно требует

    ||Delta_m(C)|| <= sigma_min(F)^-2
      [E_m(T)+C+delta^2/(C-delta)].                          (5.4)

Бюджет (5.4) не оплачивает сохранение инерции Jcal. При этом никакие upper-count или zero-location предпосылки не были спрятаны в residual.

## 6. Полоса: что можно сосчитать точно, а что ещё требуется

**[FINITE_CELL | PAPER.]** Есть два разных точных способа отделить полосу.

### 6.1. Изменение числа условий при одном и том же A_m,C

Пусть J_Omega определено строгими условиями gamma<Omega, а J_T — gamma<T. Тогда новые активные условия лежат в [Omega,T), не всегда в открытом (Omega,T): нуль ровно на Omega нельзя исключать без предположения нерезонансности.

Пусть b=q_T-q_Omega. При q_T<=d:

    N_A(C)-dim J_T = [N_A(C)-dim J_Omega]+b.                  (6.1)

Это точное следствие (3.1); оператор A_m и C не меняются с kappa. b — число новых независимых условий, НЕ число независимо определённых физических eigenlevels полосы.

Запишем Jcal_T=Jcal_Omega direct_sum Jcal_band и b_+=n_+(Jcal_band). Тогда

    N_A(C)-dim J_T = n_-(Jcal_T)+b_+ + E_core(C),              (6.2)
    E_core(C)=N_A(C)-dim J_Omega-n_-(Jcal_Omega).

Таким образом, формула требуемого вида следует из E_core(C)=0, но это дополнительная исходниковая оценка. Она НЕ доказана расширением quiet space или малой невязкой J_T. E_core может иметь любой знак в общей модели. Объявить b_+ «числом уровней ниже C» без доказательства E_core=0 было бы кругом.

### 6.2. Полосовой Schur-блок с настоящими смешанными членами

Разделим M=Jcal_T+Delta из (5.2) на core/band блоки:

    M=[[M_00,M_01],[M_10,M_11]].

При обратимом M_00 точно

    N_A(C)-r = n_-(M_00)+n_-(M_11-M_10 M_00^-1 M_01).        (6.3)

Поэтому разность с n_-(Jcal_T) есть СУММА ДВУХ изменений инерции:

    [n_-(M_00)-n_-(Jcal_core)]
    +[n_-(M_11-M_10 M_00^-1 M_01)-n_-(Jcal_band)].            (6.4)

Они не обязаны быть неотрицательными. В частности, для комплексных нулей в band уже есть отрицательные направления; хвост может их сдвинуть через порог. При сингулярном M_00 применяется полный индекс (5.2), а не неоплаченная обратная матрица.

Достаточное, но не установленное условие E_core-like сохранения инерции — отсутствие нулевого пересечения вдоль соответствующего матричного пути. Например,

    || |Jcal|^-1/2 Delta |Jcal|^-1/2 || < 1

гарантирует n_-(Jcal+Delta)=n_-(Jcal). Здесь Jcal невырождена после удаления автоматических строк. Общая поправка есть ПОДПИСАННОЕ изменение инерции вдоль Jcal+t Delta, а не автоматически неотрицательный счёт полосы. При конечном пороге нулевые значения учитываются соглашением #{lambda<0}.

## 7. Точные отрицательные контроли неправильного перехода

**[ABSTRACT | PAPER; все следующие матрицы НЕ CCM.]**

1. Положительный префикс и пустая полоса. E=(0,1/2), Jcal=(2), R=0, A=diag(0,1/2), J=span(e_0), delta=0, C=1. Тогда N_A(1)-dim J=1, но n_-(Jcal)=0. Даже нулевой хвост не позволяет заменить положительный порог нулевым индексом.

2. Положительный хвост поднимает отрицательную пару. E имеет строки (0,1,0),(0,0,1), Jcal=diag(4,-4), R=diag(0,0,5). Тогда A=diag(0,4,1), delta=0, C=1/2. Слева 0, raw n_-(Jcal)=1. Неотрицательная band-поправка это не исправляет. Подобная матрица не выдается за действительный арифметический хвост.

3. Нельзя считать спектр одного несвязанного дополнения. A=[[0,1/2],[1/2,7/8]], C=1, J=span(e_0), delta=1/2<C. G=7/8<C, но S=7/8-1+1/4=1/8>0. В полном A ровно один eigenvalue ниже 1, так что N_A(1)-1=0, а простой count дополнения дал бы 1.

4. Положительные отдельные строки не имеют независимых eigenlevels. E=[[1,0],[1,1/10]], K=2EE^T. Обе диагональные строковые энергии больше 1, но det(K-I)<0: один eigenvalue ниже 1. Корреляции строк нельзя заменить их отдельными энергиями.

Эти контроли опровергают общую теорему «попарный индекс + полоса следует из residual и явной суммы». Они не опровергают дополнительную source-specific теорему, если она отдельно докажет отсутствующие инерционные сравнения.

## 8. Постоянный пол: точный потребитель и незакрытый знак

**Теорема 4. [FINITE_CELL | PAPER.]** Если ||AQ||<=delta<C и N_A(C)=r, то A>=-delta I.

**Доказательство.** Min–max для A^2 даёт хотя бы r уровней A с |lambda|<=delta. Все они строго ниже C. Условие N_A(C)=r исключает любые другие уровни ниже C, в частности ниже -delta. ∎

**[COFINAL_FAMILY | CONDITIONAL on the new source estimate; inherited PAPER consumer.]** Если на неограниченной исходной семье delta_m<C при одном фиксированном конечном C>0 и S_m(C)>=0, то (4.1) даёт N_A(C)=r, затем A_m>=-delta_m I>=-C I. S4 завершает вывод RH. Требовать delta_m->0 или равномерный положительный зазор C-delta_m для этого потребителя не нужно; зазор нужен лишь для устойчивости конкретной inverse-оценки (4.2).

Именно S_m(C)>=0 остаётся неоплаченным исходниковым неравенством. Формулы (4.1), (5.2), (6.2) не являются его доказательством. Ненулевой defect N_A(C)-r тоже не опровергает постоянный floor: дополнительные уровни могут быть положительными или ограниченно отрицательными.

## 9. Выбор дальнейшей проверки и реестр

| Представление | Дискриминатор | Сила / цена |
|---|---|---|
| Физический Schur-блок S_m(2) | Полная инерция с пороговыми equality-guards; сравнение с N_A(2)-r; нижний envelope S | Высокая для проверки saturation / умеренная конечная цена; кофинальный знак отдельный |
| Нулевые координаты Jcal+Delta и core/band Schur | Сохраняется ли core-инерция; можно ли ограничить подписанный остаток (6.4) | Высокая для проверки именно предлагаемого механизма / дороже из-за conditioning и бесконечного хвоста |

Проверены три стыка: interpolation дает точный ранг; Schur-конгруэнция даёт точный threshold index; constant-floor min–max даёт RH-consumer. Ни один стык не подменяет отсутствующий арифметический lower bound. Дискриминатор для zero-consistent результата — интервал минимального eigenvalue S_m(C) с оплаченной ошибкой всех блоков и строгим учетом C, а не малая невязка Q.

**Единственная CODEX DIRECTIVE: QUIET_THRESHOLD_SCHUR_SOURCE_AUDIT.** На закреплённых четырёх carrier проверить (2.1), (3.1), (4.1), (5.2) в правильной физической метрике; использовать C=2 и указанные выбранные kappa. Не добавлять высокие моды в eigenproblem и не ограничиваться сжатием Q^T A Q вместо полного AQ. Отдельно вернуть интервалы на D,B,G либо честные diagnostic-радиусы; вычислить S и воспроизвести N_A(2)-r. Для source theorem предъявить независимый нижний envelope S_m(C)>=0 на неограниченной семье либо сохранение core-инерции в (6.2)/(6.4), а не переименовать S в raw Jcal. Это задание, не заявленная выполненная независимая проверка.

Ledger: Theorem 1 and (3.3) — FINITE_CELL/PAPER; Theorem 2, (4.2)–(6.4) — FINITE_CELL/PAPER; tail (5.3) — FINITE_CELL/PAPER using S1 zero-count bound; controls §7 — ABSTRACT/PAPER; cofinal floor transfer §8 — COFINAL_FAMILY/CONDITIONAL on new S-bound; reported C=2 data — FINITE_CELL/diagnostic only.

DOWNSTREAM_CONSUMER: constant lower floor on literal CCM, hence RH using S4.
ACTUAL_CONSUMER_REQUIREMENT: one fixed lower floor, not the proposed detailed zero-level correspondence.
ORIGINAL_REQUESTED_OBJECT: raw pair inertia plus a nonnegative band-level count.
ORIGINAL_OBJECT_IS: NOT_NECESSARY as an interface to the constant-floor consumer.
KNOWN_WEAKER_INTERFACE: bounded delta<C and S_m(C)>=0 cofinally.
FAILURE_TYPE: NO_DERIVATION for literal cofinal sign; COUNTEREXAMPLE for the generic omission of threshold/tail/coupling.
EPISTEMIC_STATUS: RESEARCH_DEBT for literal claim; only the generic shortcut theorem shape is refuted.
KILL_SCOPE: THEOREM_SHAPE, never ROUTE_FAMILY.
REOPEN_TRIGGER: source-specific inertia stability or a direct lower envelope for S_m(C).
NOVELTY_AXIS: complete complex/multiplicity/rank crosswalk and threshold correction, not a new proof of RH.

Предсказания P1–P6 записаны до исполнения тестов: знак coupling положительный; raw-index shortcut может провалиться даже при delta=0; complement tail не контролируется quiet residual; band mixing существенен; кратность не даёт производных; четыре выбранных reported сектора допускают C=2. Все подтверждены соответствующими проверками. Первый запуск кода остановился на преобразовании SymPy BooleanTrue через int; исправлено на int(bool(...)). После этой технической правки прошли все 8 точных групп и 1 scalar diagnostic. Аналитическая теорема на эти конечные проверки не опирается.

Внешний поиск по классической формуле инерции не используется как новый supplier: её нужный случай полностью доказан конгруэнцией в §4. Новые численные eigenproblems, Lean, Arb и независимый аналитический аудит не запускались. Прежний PAPER-статус S1 не повышен.

## 10. Доставка

Один новый Markdown в `docs/routeB_bus/proshka/PROSHKA_VERDICT_QUIET_SPACE_INDEX_2026-11-02.md`, ветка `proshka_inbox_2026-10-31`; наблюдавшийся родитель перед доставкой 2176dab16bf77dd015f7efcb5a6f704587f732c8. Источники rh_clean, прежние вердикты, Lean и route-state не редактируются. SHA коммита и совпадение Git blob сообщаются только после успешной записи/чтения. Lean-команды и аксиомный профиль неприменимы: Lean-файлы не создаются. Git-доставка не является доказательством source-sign.

## Appendix: воспроизводимые локальные проверки

Извлечь Python fence в `checks.py` и выполнить `uv run --with sympy checks.py`. Проверки матриц абстрактные; последнее сравнение читает округлённые значения из S2 и НЕ сертифицирует их погрешность.

```python
#!/usr/bin/env python3
"""Exact algebra checks; reported-data scalar check is NOT an interval certificate.
Run: uv run --with sympy checks.py
No CCM eigensystem or zeta zero is numerically recomputed here.
"""
from decimal import Decimal
import sympy as s

# 1. Source parity/multiplicity factors.
a,b,nu=s.symbols('a b nu', real=True)
assert s.expand(2*nu*((a+s.I*b)**2+(a-s.I*b)**2)-4*nu*(a*a-b*b))==0
print('PASS 1 complex quartet = 4 nu (Re^2 - Im^2)')

# 2. Polynomial evaluation rank; conjugate nodes supply real+imaginary rows.
x=s.symbols('x',real=True)
z=2+s.I
E=s.Matrix([[s.re(z**k) for k in range(4)],
            [s.im(z**k) for k in range(4)],
            [s.Integer(4)**k for k in range(4)],
            [s.Rational(1,2)**k for k in range(4)]])
assert E.det()!=0
repeated=s.Matrix([[1,2,4],[1,2,4],[1,2,4]])
assert repeated.rank()==1
assert repeated.T*(2*s.eye(3))*repeated == 6*s.Matrix([1,2,4])*s.Matrix([[1,2,4]])
print('PASS 2 active evaluation rank and multiplicity without derivative constraints')

# 3. Congruence eliminates the quiet block with a PLUS correction.
D=s.Matrix([[s.Rational(1,8),s.Rational(1,16)],
            [s.Rational(1,16),-s.Rational(1,4)]])
B=s.Matrix([[s.Rational(1,6),-s.Rational(1,8)],
            [s.Rational(1,10),s.Rational(1,7)]])
G=s.Matrix([[s.Rational(3,2),s.Rational(1,5)],
            [s.Rational(1,5),s.Rational(1,3)]])
C=s.Integer(1); H=D-C*s.eye(2)
M=H.row_join(B.T).col_join(B.row_join(G-C*s.eye(2)))
T=s.eye(2).row_join(-H.inv()*B.T).col_join(s.zeros(2).row_join(s.eye(2)))
P=B*(C*s.eye(2)-D).inv()*B.T
S=G-C*s.eye(2)+P
assert s.simplify(T.T*M*T-s.diag(H,S))==s.zeros(4)
assert P[0,0]>0 and P.det()>0
print('PASS 3 exact Schur congruence and positive correction')

# 4. A positive prefix can lie below a positive threshold; no band, residual=0.
E=s.Matrix([[0,s.Rational(1,2)]]); J=s.Matrix([[2]])
A=E.T*J*E
assert A==s.diag(0,s.Rational(1,2))
assert sum(int(bool(v<1))*mult for v,mult in A.eigenvals().items())-1==1
assert sum(int(bool(v<0))*mult for v,mult in J.eigenvals().items())==0
print('PASS 4 raw zero-pair inertia is not a threshold count')

# 5. A PSD tail may lift a negative quartet direction; residual still zero.
E=s.Matrix([[0,1,0],[0,0,1]]); J=s.diag(4,-4)
R=s.diag(0,0,5); A=E.T*J*E+R
assert A==s.diag(0,4,1)
assert sum(int(bool(v<s.Rational(1,2)))*mult for v,mult in A.eigenvals().items())-1==0
assert sum(int(bool(v<0))*mult for v,mult in J.eigenvals().items())==1
print('PASS 5 complement tail cannot be inferred from quiet residual')

# 6. Removing the Schur correction overcounts a subthreshold direction.
A=s.Matrix([[0,s.Rational(1,2)],[s.Rational(1,2),s.Rational(7,8)]])
S=s.Rational(7,8)-1+s.Rational(1,4)
assert S==s.Rational(1,8)>0
assert (A-s.eye(2)).det()<0  # exactly one eigenvalue of A is below 1
assert s.Rational(7,8)<1
print('PASS 6 quiet/complement coupling changes the count')

# 7. Zero-row correlations prevent row-by-row spectral assignment.
E=s.Matrix([[1,0],[1,s.Rational(1,10)]])
K=2*E*E.T
assert K[0,0]>1 and K[1,1]>1
assert (K-s.eye(2)).det()<0
print('PASS 7 two positive row energies above C still have an eigenvalue below C')

# 8. Correct band Schur term retains mixed blocks.
M=s.Matrix([[2,3],[3,2]])
assert M.det()<0
assert 2-s.Rational(9,2)==-s.Rational(5,2)<0
print('PASS 8 band/core cross term is essential')

# 9. Scalar postprocessing of rounded source values only.
selected=[(16,'1.36271876','2.28564356'),
          (24,'0.591690030','2.27276429'),
          (32,'1.21381573','2.30665006'),
          (40,'0.994272082','2.19035639')]
C=Decimal(2)
assert all(Decimal(d)<C<Decimal(g) for _,d,g in selected)
print('DIAGNOSTIC 9 selected reported sectors admit common C=2; NOT interval-certified')
print('ALL 8 EXACT GROUPS PASSED; 1 REPORTED-DATA DIAGNOSTIC PASSED')
```
