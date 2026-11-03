# STATUS: TRY_PASSIVE_SECTION_P_WITH_FULL_HISTORY_BUDGET

```yaml
OPERATIVE_CLASS: TRY_PASSIVE_SECTION_P_WITH_FULL_HISTORY_BUDGET
DATE: 2026-11-03
AUTHORITY: DIRECT_OWNER_REQUEST_TO_PROVE_P
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: 01b3d757fb9faf16c425002c0090222115348aa1
HANDOFF: docs/routeB_bus/screw_line_2026-11-02/passivity_check/PROSHKA_HANDOFF.md
HANDOFF_BLOB: d9fc618e8b377aeb3d885d999ea0a05c0f944cfe
PREDECESSOR: bfd66b5aaf1756477f5cae2066c630cc8ba599b2
PREDECESSOR_BLOB: 074e32bee014784c1867fd78c2a3342b07c4250f
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE: CHALLENGER_NOT_RH
REQUESTED_P: NOT_PROVED
REQUESTED_P_REFUTED_FOR_ZETA: false
NEW_RESULT: ALL_FUTURE_NODE_BLOCK_LOCAL_EXTENSION_WITH_EXPLICIT_SOURCE_LOWER_ENVELOPE
NEW_RESULT_SCOPE: EVERY_FIXED_FINITE_POSITIVE_HISTORY_WITH_HISTORY_DEPENDENT_LENGTH
FIXED_ARITHMETIC_SECTION_LENGTH_COVERED_UNIFORMLY: false
FULL_HISTORY_RETAINED: true
EXPLICIT_SHORT_SOURCE_COERCIVITY: PROVED_PAPER
SHIFTED_PRIME_EVENTS_INSIDE_SECTIONS: PROVED_PAPER
EVENTUAL_ONE_ANCHOR_P_EQUIVALENT_TO_RH: PROVED_PAPER_USING_SUZUKI_TRANSFORM
RH_JUDGE: CONDITIONAL_PASS
W_JUDGE: LOCAL_THEOREM_PASSES_BUT_GLOBAL_P_FAILS
COARSE_LOWER_ENVELOPE_ON_SECTION_16: NEGATIVE_DIAGNOSTIC_NOT_A_COUNTEREXAMPLE_TO_P
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_BOUNDARY: LOCAL_ALL_NODE_QUANTIFIER_ONLY_NOT_GLOBAL_SIGN
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 4
VERIFIER: PAPER
INDEPENDENT_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
```

## 0. Ответ

Ы. Полное (P) для каждой заданной секции и каждого положительного прошлого в этой работе НЕ доказано. Для настоящего g_zeta контрпример также не получен.

Доказано более сильное локальное утверждение, чем прежняя одноточечная асимптотика: после ЛЮБОГО фиксированного конечного положительного прошлого существует исходниково контролируемый отрезок, на котором Schur-дополнение положительно для ЛЮБОГО количества новых узлов одновременно, без нижней границы расстояний между ними. Длина зависит от всей старой матрицы. Получен явный нижний envelope. Он не доказан неотрицательным на полной длине log((n+1)/n); его грубая версия уже не проходит один конечный контроль при n=16. Это провал оценки, не опровержение (P).

Ниже приведены точный полный источник, доказательство локального утверждения, местонахождение старой арифметики, точный барьер перехода к (P), оба судьи и проверка кванторов. Уравнения не используют глобальный положительный спектр как предпосылку.

## 1. Источники и фиксированные обозначения

[S1] Закрепленный handoff из header прочитан целиком. [S2] Предыдущий SCREW_LINE_PREDICTION_v1, commit bfd66b5, §§1–5: точный derivative-measure pullback и source-return для ступенчатых функций. [S3] passivity_check/RESULT.md на том же BASE: только прочитанные диагностические границы; ни один floating-знак не принят за универсальную теорему.

[P1] M. Suzuki, arXiv:2206.03682v4, (1.1)–(1.4), Theorems 1.1, 1.2, 1.7, §7.2. Первичный PDF прочитан; страницы 1 и 4 просмотрены скриншотами. Скриншот страницы 25 вернул cache miss; ее доказательство прочитано в извлеченном тексте. Положительность (P) из P1 не импортируется. Его полная арифметическая формула и Laplace identity — THEOREM; применение положительной нулевой меры — CONDITIONAL ON RH.

Пусть g=-Psi из [P1,(1.1)], g(0)=0, g четна, и

    K(s,t)=g(s-t)-g(s)-g(t).

Все старые узлы неотрицательны и предшествуют новой секции. Достаточно рассматривать вещественные коэффициенты: все матрицы вещественны симметричны, комплексный вариант следует разделением на действительную и мнимую части. Старый узел 0 или повторения невозможны при G_old>0. Новые узлы могут повторяться или совпадать со старым endpoint; соответствующие нулевые направления сохраняются.

Для вещественного компактного ступенчатого f с нулевым продолжением обозначим

    Q_f(u)=2 integral_R f(x)f(x+u) dx,
    j(u)=exp(-u/2)/(1-exp(-2u)),
    c_*=gamma_E+log(8*pi)+pi/2,
    A_+(f)=integral exp(x/2)f(x)dx,
    A_-(f)=integral exp(-x/2)f(x)dx.

Полная исходная форма:

    W[f]=integral_0^infinity j(u)||f-T_u f||_2^2 du
         -c_*||f||_2^2
         -sum_(q>=2) Lambda(q)/sqrt(q) Q_f(log q)
         +2 A_+(f)A_-(f).                                      (1)

Это [S2,(9)]. Поддержка делает арифметическую сумму конечной. В arch-интеграле сохранен весь хвост. Ступенчатая функция не обязана быть четной: оба полюса обязательны. W трансляционно инвариантна. Endpoint-массы распределительной производной не удаляются.

## 2. Точный Schur-объект всей новой секции

**[FINITE_CELL | PAPER; LA,A, источник E/F/I в (1).]** Сначала произвольные старые s_i и новые t_j. Пусть

    C=(K(s_i,s_j))>0, B=(K(s_i,t_j)), D=(K(t_i,t_j)),
    S=D-B^T C^-1 B.

Для каждого вектора z новых коэффициентов положим u=C^-1 Bz и

    f_z=sum_j z_j 1_(0,t_j) - sum_i u_i 1_(0,s_i).

Тогда точно

    z^T S z=W[f_z].                                           (2)

Распределительная производная f_z равна минус остаточной мере; общий знак не меняет квадрат. Таким образом, целевой знак (P) — знак полной (1) на оптимальных остатках (2), не на произвольном положительном квадрате.

Теперь обозначим максимальный старый узел через a=s_r>0 и t_j=a+h_j, 0<=h_j<=delta. Это не добавление нового старого узла. Если максимальный старый узел находится левее log n, фактическая delta равна max(t_j)-a, а не автоматически log((n+1)/n).

Вычтем из каждого нового вектора старый вектор с узлом a. Schur-дополнение не изменится. Определим

    F_ij=K(h_i,h_j),
    V_ij=K(s_i,a+h_j)-K(s_i,a).

Тогда

    S=F-V^T C^-1 V.                                          (3)

Это точное следствие стационарности приращений данного kernel и блочной конгруэнции. Не предполагается существование положительного стохастического процесса.

Для x>0 введем полный response прошлого

    eta_i(x)=g'(a+x-s_i)-g'(a+x),
    R_delta=integral_0^delta eta(x)eta(x)^T dx,
    rho_delta=lambda_max(C^-1/2 R_delta C^-1/2).                (4)

Производные понимаются почти всюду; все скачки сохраняются. У eta_r при x=0 логарифмическая особенность, интегрируемая в квадрате. Для p_z=sum_j z_j 1_(0,h_j):

    Vz=integral_0^delta eta(x)p_z(x)dx,
    z^T F z=W[p_z],
    ||p_z||_2^2=z^T M_h z,  (M_h)_ij=min(h_i,h_j).              (5)

Следовательно,

    z^T S z=W[p_z]-||C^-1/2 integral eta p_z||^2.              (6)

В (6) присутствуют ВСЕ старые узлы. Число новых узлов не ограничено.

## 3. Явный положительный бюджет свежего короткого отрезка

**Лемма 1. [ABSTRACT | PAPER; F,A,LA; E/I только для отсутствия атомов до log 2.]** Если 0<delta<log 2 и supp f имеет длину не больше delta, то

    W[f]>=beta(delta)||f||_2^2,
    beta(delta)=2[atanh(exp(-delta/2))+atan(exp(-delta/2))]
                -c_*-[2sinh(delta/2)-delta].                 (7)

В частности,

    0<delta<=1/16  ==>  beta(delta)>1/4.                      (8)

**Доказательство.** Для u>=delta корреляция равна нулю, поэтому

    H[f]>=2||f||^2 integral_delta^infinity j(u)du.

Замена r=exp(-u/2) дает integral_delta^infinity j=atanh(exp(-delta/2))+atan(exp(-delta/2)). Арифметических атомов на такой поддержке нет, не по отсечению источника, а потому что Q_f(log q)=0 при q>=2.

Перенесем поддержку в [-delta/2,delta/2]. Полюсный член равен |<p,f>|^2-|<q,f>|^2, где p=sqrt(2)cosh(x/2), q=sqrt(2)sinh(x/2). Отсюда его нижняя граница

    -||q||^2||f||^2=-[2sinh(delta/2)-delta]||f||^2.

Это доказывает (7). Нечетный отрицательный полюс не удален.

Для (8) beta убывает: beta'=-2j(delta)-cosh(delta/2)+1<0. Далее exp(-delta/2)>=1-delta/2 и atan липшицева с константой 1, поэтому

    beta(delta)>=log(4/delta-1)-gamma_E-log(8*pi)-delta
                  -[2sinh(delta/2)-delta].                   (9)

При delta=1/16 используем pi<22/7, gamma_E<3/5, log(5/2)>229/250 и 2sinh(1/32)-1/16<1/80000. Получаем

    beta(1/16)>229/250-3/5-1/16-1/80000>1/4.

Последняя оценка sinh следует из 2sinh(delta/2)-delta<=delta^3 exp(delta/2)/24. Все границы элементарные; десятичное вычисление beta не является доказательством. Фактическое значение beta(1/16) приблизительно 0.3263222785. ∎

## 4. Доказанная локальная лемма сразу для всех новых узлов

**Теорема 2. [ABSTRACT | PAPER; E/F/I/A/LA через полный источник.]** Для любого фиксированного конечного положительного прошлого C и любых новых узлов a+h_j, 0<=h_j<=delta<=1/16, верно

    S >= [beta(delta)-rho_delta] M_h.                         (10)

Поэтому если rho_delta<=beta(delta), то S>=0 для ЛЮБОГО количества новых узлов одновременно. При строгом неравенстве и различных положительных h_j матрица S строго положительна.

Кроме того, для каждого фиксированного такого прошлого существует delta_0>0, для которого условие выполняется при всех 0<delta<=delta_0.

**Доказательство.** Оператор L2(0,delta)->R^r, f |-> C^-1/2 integral eta f, имеет квадрат нормы ровно rho_delta. Совместить эту оценку с (6) и (7). Это доказывает (10), не ограничивая число или разделенность h_j.

Остается существование длины. Из полной формулы источника возле нуля

    g'(x)=1/2 log x +1/2[log(2*pi)+gamma_E]+O(x), x down to 0. (11)

Для каждого i<r аргументы a-s_i положительны, поэтому eta_i ограничена справа на достаточно малом отрезке, с возможными конечными скачками. Для i=r:

    eta_r(x)=1/2 log x+O_history(1).

Следовательно,

    tr R_delta=delta/4 [log(1/delta)]^2
               +O_history(delta log(1/delta)),
    rho_delta<=||C^-1|| tr R_delta=O_history(delta log^2(1/delta)).

При этом из (7)

    beta(delta)=log(1/delta)-gamma_E-log(2*pi)+O(delta).

Таким образом, rho_delta/beta(delta)->0. При необходимости уменьшить delta_0, чтобы beta-rho>0 на всем (0,delta_0]. ∎

Новые узлы h=0 и повторяющиеся h создают нулевые направления M_h, как и должны. Нулевая старая матрица здесь не инвертируется: исходный контракт требует C>0. Переход к бесконечному или вырожденному прошлому не сделан без контроля.

**Чего теорема НЕ утверждает.** delta_0 зависит от ВСЕЙ истории и ее обратной матрицы. Не доказано delta_0>=log((n+1)/n) для a=log n, равномерно по всем допустимым старым конфигурациям. Не доказано, что допустимые адаптивные длины имеют расходящуюся сумму. Из (10) нельзя заключить глобальное (P).

## 5. Где находится точная арифметика response и почему секция не гладкая

**[FINITE_CELL | PAPER; E,F,I,A.]** Пусть ell_k=2k+1/2. Дифференцируя именно [P1,(1.1)], получаем при u>0 вне атомов

    g'(u)=-4sinh(u/2)+c_*/2
           -sum_(k>=0) exp(-ell_k u)/ell_k
           +sum_(log q<=u) Lambda(q)/sqrt(q).                 (12)

Ряд равен atanh(exp(-u/2))+atan(exp(-u/2)); это обеспечивает устойчивое прямое вычисление. Таким образом, при u=a+x-s_i, v=a+x,

    eta_i(x)=4[sinh(v/2)-sinh(u/2)]
             -sum_(k>=0) [exp(-ell_k u)-exp(-ell_k v)]/ell_k
             -sum_(exp(u)<q<=exp(v)) Lambda(q)/sqrt(q).        (13)

Все старые prime powers остались в движущейся полосе (exp(u),exp(v)]. Знак Lambda не дает знака квадратичного отношения с C^-1.

Даже внутри (log n,log(n+1)) новый столбец K(s_i,t) имеет изломы в t=s_i+log q. Отсутствие нового целого q в exp(t) не устраняет эти перенесенные старые взаимодействия.

Для одной новой точки положим b(t)=(K(s_i,t)), alpha(t)=C^-1b(t),

    s(t)=-2g(t)-b(t)^T C^-1 b(t).

Определим c(v)=Lambda(q)/sqrt(q), если v=log q, и 0 иначе. Тогда точно

    jump s'(t)=-2c(t)[1-sum_i alpha_i(t)]
                -2sum_i c(t-s_i)alpha_i(t).                 (14)

На гладких промежутках

    s''(t)=-2g''(t)-2b'(t)^T C^-1b'(t)-2b''(t)^Talpha(t),
    g''(t)=j(t)-2cosh(t/2).                                 (15)

Отрицательный квадрат в (15) удержан. Ни гладкий поток, ни скачки не стали неотрицательными автоматически.

Есть actual-source отрицательный излом внутри секции: взять единственный старый узел s>0 малым и t=s+log 2 in (log 2,log 3). Тогда c(t)=0, c(t-s)=log 2/sqrt 2, а

    alpha(t)=[Psi(s)+Psi(log 2+s)-Psi(log 2)]/[2Psi(s)] ->1/2.

Поскольку Psi(s)~(s/2)log(1/s)>0 и Psi справа от log 2 имеет конечную производную, предел строгий. Поэтому для всех достаточно малых s

    jump s'(s+log 2)<0.                                    (16)

Это НЕ отрицательное s(t) и НЕ контрпример (P). Это опровержение монотонного-прироста как автоматического Euler-механизма. Полное состояние предиктора необходимо.

## 6. Точное место остановки попытки

Скалярная замена свежей формы W ее нижней коэрцитивностью beta теряет информацию. Она полезна для теоремы 2, но не доказана достаточной на полной секции.

Проверка настоящего источника на n=16, a=log16, delta=log(17/16), старые узлы (a/4,a/2,3a/4,a), дает при 40 dps:

    lambda_min(C) = 0.0363806384266045...
    beta(delta)   = 0.35772104768259835...
    rho_delta     = 0.95532489784161851...
    beta-rho      = -0.59760385015902016...

На трех новых узлах h=(delta/4,delta/2,delta) непосредственный минимум S равен +0.0186789231175902... . Все эти числа — DIAG, не interval certificate. Они показывают, что вычисленная достаточная оценка не доказывает даже этот случай, но НЕ дают отрицательного Schur-вектора.

Логическая потеря подтверждается точно без чисел источника: T=diag(1,100), V=(0,5), C=1. Тогда T-V^TC^-1V=diag(1,75)>0 и C-VT^-1V^T=3/4>0, но грубая нижняя цена beta-||V||^2=1-25=-24. Неуспех достаточного envelope не является неуспехом целевого знака.

Есть точная форма без этой потери. На замыкании ступенчатых профилей по положительной форме W_delta из §3 линейные функционалы f |-> integral eta_i f ограничены. Пусть v_i — их представители Рисса и M_ij=W_delta(v_i,v_j). Тогда

    (P) для всех новых узлов в (a,a+delta]
       iff M<=C.                                           (17)

Это следует из (6) и плотности линейных комбинаций индикаторов в ЭТОМ определенном замыкании. Формально M=V T_delta^-1 V^T; используется только реализация на указанном пространстве. Величина M<=beta^-1 R_delta, но обратное не верно.

(17) не объявляется доказанным положительным сравнением. Это точная та же whole-history задача, без скалярной потери. Из условия C>0 пока не выведено M<=C для настоящего g_zeta на каждой заданной секции.

## 7. Проверка силы квантора: уже один фиксированный старый узел достаточен

**Теорема 3. [COFINAL_FAMILY | PAPER; LA,A,F плюс THEOREM transform P1.]** Выберем s_0=1/64. По лемме 1, K(s_0,s_0)=W[1_(0,s_0)]>=beta(s_0)s_0>0. Рассмотрим лишь одноточечный вариант

    2Psi(t)-[Psi(s_0)+Psi(t)-Psi(t-s_0)]^2/[2Psi(s_0)]>=0
    для всех t>=log2.                                      (18)

Утверждения (18), полное (P) и RH эквивалентны для данного источника.

**Доказательство.** (P) влечет (18), поскольку любой t>=log2 находится в одной заданной секции и s_0 предшествует ей. Из (18) сразу следует Psi(t)>=0 при t>=log2. Достаточно уже eventual positivity, не всей старой истории.

Покажем это последнее следствие без скрытого импорта RH. Из [P1,(1.2)] при Re s>1/2:

    integral_0^infinity Psi(t)exp(-st)dt
       =xi'(1/2+s)/[s^2 xi(1/2+s)].                         (19)

Если Psi>=0 при t>=T, ее хвостовой Laplace-transform отличается от (19) целой функцией. Его абсцисса сходимости sigma_c не больше 1/2. Нуль xi с Re rho>1/2 принудил бы sigma_c>=Re rho-1/2>0, иначе аналитический transform имел бы внутренний полюс.

Для неотрицательной функции конечная абсцисса сходимости является особой точкой на вещественной оси. Короткое доказательство: если transform аналитичен через sigma_c, выбрать s_1>sigma_c и Taylor-диск, достигающий s_1-h<sigma_c. Производные равны интегралам (-t)^k f(t)e^(-s_1t). Taylor-сумма в s_1-h имеет неотрицательные интегральные слагаемые. По монотонной сходимости она равна integral f(t)e^(-(s_1-h)t), конечному вопреки определению sigma_c.

Но правая часть (19) аналитична возле каждой положительной вещественной s: xi(1/2+s) не имеет вещественных нулей; это следует из положительного чередующегося eta-ряда для положительных вещественных аргументов, Euler-области справа от 1 и устранимости completion при 1. Значит, положительная sigma_c невозможна. Отражение функциональным уравнением исключает все off-line нули. RH следует.

Обратно, под RH полная нулевая формула K — положительная Gram-сумма; обычная Schur-конгруэнция дает (P) при C>0 и, в частности, (18). ∎

Это проверка силы цели, а не доказательство (P) через эквивалентность. Не существует логического выигрыша от того, что старый блок в формулировке предположен положительным: уже один заранее положительный старый узел оставляет весь глобальный source-знак.

## 8. Два судьи

### RH-ветка

**[COFINAL_FAMILY | CONDITIONAL ON RH; A,LA.]** При RH K — исходная положительная нулевая Gram-сумма. Поэтому все Schur-блоки в (P) положительны. Для одной точки ее ошибка не больше 2Psi(t), а 2Psi(t)<=4 sum_gamma nu_gamma/gamma^2<infinity. Новый положительный lift с расходящейся суммой весов не вводится. §3ce4968 не обходится перемасштабированием неизвестного остатка.

### w-мир

**[COFINAL_FAMILY | PAPER for the defined control, conditional RH baseline; A,LA.]** Возьмем положительный baseline g_0 с bounded Psi_0 (например, ζ в RH-ветке) и

    g_w(t)=g_0(t)+4nu Re[(cos(wt)-1)/w^2],
    w=gamma+i eta, gamma=2pi/log2, 0<eta<1/2.

У perturbation тот же локальный тип: добавка к g' гладкая, O(t) возле 0. На поддержке длины delta абсолютная цена четверки не превосходит 4nu delta exp(eta delta)||f||^2. Поэтому beta_w>=beta-4nu delta exp(eta delta), а eta_i по-прежнему имеет тот же единственный logarithmic cusp. Теорема 2 о достаточно коротком продолжении ВСЕГО нового блока проходит в этом мире тоже.

Пусть S_0=sum_gamma nu_gamma/gamma^2 и a_w=Re(1/w^2)>0. На L_k=k log2:

    2Psi_w(L_k)<=4S_0-8nu a_w[cosh(eta L_k)-1]<0             (20)

для всех достаточно поздних k. Выберем один фиксированный достаточно малый положительный старый узел s_w с K_w(s_w,s_w)>0, что обеспечивает локальная коэрцитивность. Тогда одноточечное Schur-дополнение не превосходит 2Psi_w(L_k)<0. Это строгий отрицательный UPPER envelope, нарушающий (P) в этом контрольном мире.

Старые prime-изломы не меняются, но гладкая часть изменена: w-мир не назван вторым экземпляром точного g_zeta из (1.1). Он опровергает только вывод «локальное положительное продолжение для каждого конечного прошлого + правильный знак prime-изломов => (P)». Не доказано, что тот же сбой есть у ζ.

## 9. Классификация, проверки, closeout

| Утверждение | Scope | Verifier / зависимости | Граница |
|---|---|---|---|
| Точная оптимальная ступенчатая форма (2) | FINITE_CELL | PAPER; E/F/I/A/LA | Исходник полный |
| Перенос к свежим приращениям (3)–(6) | ABSTRACT | PAPER; LA/A | Все старые взаимодействия |
| Коэрцитивность beta>1/4 | ABSTRACT | PAPER; F/A/LA, локальная E/I | Поддержка <=1/16 |
| Нижний envelope (10), все новые узлы | ABSTRACT | PAPER; E/F/I/A/LA | Длина зависит от истории |
| Source-response и перенесенные изломы | FINITE_CELL | PAPER; E/F/I/A | Не знак Schur-значения |
| (18) iff (P) iff RH | COFINAL_FAMILY | PAPER; P1, A/F/LA | Теорема импликаций, RH не утверждается |
| Полная (P) для ζ | COFINAL_FAMILY | CONDITIONAL / unresolved | НЕ доказана |
| Отрицательный (20) в planted мире | COFINAL_FAMILY | PAPER for specified control | Не контрпример ζ |

Предрегистрация до тестов: P1 точная инвариантность Schur при переходе к приращениям; P2 beta>1/4; P3 перенесенные prime-события; P4 envelope положителен eventually при фиксированном прошлом; P5 локальное свойство проходит w, глобальное нет. P1–P4 подтверждены аналитически и контрольными расчетами; P5 доказан аналитически. После первых тестов и ДО отдельного теста секции16 зарегистрирована P6: грубый envelope может не пройти полную секцию без отрицательного S. Она подтверждена диагностикой §6; это не было выдано за первоначальную ставку.

Выполнены пять точных алгебраических controls: блочное тождество, вторая производная Schur, норма odd-pole, интеграл log^2, контроль потери scalar coercivity. При 50 dps проверены четыре source-derivative значения (расхождение <4.2e-33), перенесенный излом для s=log(5/4), t=log(5/2) (расхождение 2.61e-28), и два whole-block lower-envelope примера.

Для старых (log2/2,log2):

| delta | beta | tr(C^-1 R_delta), верх для rho | beta-tr |
|---:|---:|---:|---:|
| 0.001 | 4.49216256848 | 0.104840378584 | 4.38732218990 |
| 0.00001 | 9.09782773366 | 0.003327374921 | 9.09450035874 |

Для каждого проверен блок новых h=(delta/3,0.999delta,delta); матрица S-(beta-tr)M_h положительна при указанной арифметике. Это numerical normalization check, не Arb. На секции16 использовано 40 dps. Начальный quadrature harness получил nonfinite значения из-за a+x-a и atanh(exp(-x/2)) в предельно малых x; исправлены вычисление (a-a)+x и устойчивое log1p/expm1. Формулы, кванторы и пороги тестов не менялись. Новый большой CCM/DH eigensystem не считался.

### K8A и один объект продолжения

DOWNSTREAM_CONSUMER: положительность того же полного screw-kernel и его исходного derivative-measure pullback.
ACTUAL_CONSUMER_REQUIREMENT: (P) на всех заданных секциях и конфигурациях; достаточен даже one-anchor source-знак (18).
ORIGINAL_REQUESTED_OBJECT: исходниковая, не RH-условная, пассивность секции.
ORIGINAL_OBJECT_IS: RH-equivalent; не заменен локальной леммой.
FAILURE_TYPE: NO_DERIVATION of the required uniform joint comparison; coarse source estimate loses information.
EPISTEMIC_STATUS: RESEARCH_DEBT; literal (P) не объявлена mathematically dead.
MINIMAL_MISSING_IDENTITY: source-only domination M<=C in (17), or a genuinely independent eventual sign of the same Psi. Это две координаты того же знака, не новые принятые предпосылки.
REOPEN_TRIGGER: один из этих знаков доказан с полным источником и без положительной spectral/Hamiltonian предпосылки.
NOVELTY_AXIS: all-new-node local continuation and explicit history-response budget; not new global passivity.

Две допустимые репрезентации этого же объекта: (i) оставить полный short-source operator в M=V T_delta^-1 V^T вместо beta I — высокая точность дискриминатора, умеренная цена finite формулы, неизвестная цена универсального знака; (ii) one-anchor/Laplace представление (18)–(19) — минимум линейной алгебры, высокая арифметическая цена и прямой w-судья. Ни для одной не доказан положительный знак. Перебор более мелких сеток не объявляется доказательством.

DISCRIMINATOR: для фиксированного источника строгий lower-envelope S>=0 подтверждает только свой перечисленный scope; отрицательный upper на одном квадратичном векторе опровергает соответствующий finite P. Нуль-согласованный результат требует точного null/range анализа либо более тесного enclosure, не произвольного pseudoinverse threshold.

Единственная CODEX DIRECTIVE: независимо проверить формулы (3)–(17), особенно источник eta, сохранение обоих полюсов и all-node квантор. Не повышать статус P после проверки этих формул. Доставка этого Markdown не изменяет Route B, Lean, RH-экспорт или старые вердикты.

META CLOSEOUT: новый закрытый квантор — все новые узлы на достаточно коротком отрезке после каждого фиксированного положительного прошлого. Глобальный target не закрыт. Убит только автоматический вывод знака из локальных изломов/исторически неравномерного продолжения. Нельзя повторять: склеивать интервалы без общего бюджета; превращать отрицательный lower-envelope в отрицательный Schur-сертификат. Память стратегии: target=P; status=OPEN; failed_strategy=replace_full_fresh_source_by_scalar_coercivity; operator=REPRESENTATION_SHIFT; invariant=all_old_interactions_and_both_poles_retained; exact_remaining_object=M<=C; next_decisive_test=source-controlled_sign_of_the_same_full_history_response.

VERIFICATION HANDOFF: один новый Markdown в docs/routeB_bus/proshka/ на proshka_inbox_2026-10-31. Commit SHA сообщается после успешной записи и readback. Lean source не писался; Lean axiom profile неприменим. Самопроверки — не независимый аналитический аудит.

## 10. Короткое воспроизведение source-discriminator

Команда из каталога с извлеченным кодом: `uv run --with mpmath --with sympy check_passive_section.py`. Все параметры заданы в коде; замены путей и секретов нет. Скрипт проверяет частные source-числа, НЕ глобальный квантор (P).

```python
import mpmath as mp
import sympy as sy
mp.mp.dps = 50
c = mp.euler + mp.log(8*mp.pi) + mp.pi/2

def lam(n):
    f = sy.factorint(n)
    return mp.log(int(next(iter(f)))) if len(f) == 1 else mp.mpf(0)

def g(x):
    x = abs(mp.mpf(x))
    if not x:
        return mp.mpf(0)
    N = int(mp.floor(mp.exp(x)*(1+mp.mpf('1e-48'))))
    prime = mp.fsum(lam(n)/mp.sqrt(n)*(x-mp.log(n)) for n in range(2,N+1))
    tail = mp.exp(-x/2)*mp.lerchphi(mp.exp(-2*x),2,mp.mpf(1)/4)
    return prime - 4*(mp.exp(x/2)+mp.exp(-x/2)-2) + c*x/2 - (mp.pi**2+8*mp.catalan-tail)/4

def gp(x):
    x = mp.mpf(x)
    if x <= 0:
        raise ValueError('g prime requires a positive argument')
    r = mp.exp(-x/2)
    atanh_r = (mp.log1p(r)-mp.log(-mp.expm1(-x/2)))/2
    N = int(mp.floor(mp.exp(x)*(1+mp.mpf('1e-48'))))
    return -4*mp.sinh(x/2)+c/2-atanh_r-mp.atan(r)+mp.fsum(lam(n)/mp.sqrt(n) for n in range(2,N+1))

def K(s,t):
    return g(s-t)-g(s)-g(t)

def beta(d):
    r = mp.exp(-d/2)
    return 2*(mp.atanh(r)+mp.atan(r))-c-(2*mp.sinh(d/2)-d)

assert beta(mp.mpf(1)/16) > mp.mpf(1)/4
print('beta(1/16)', mp.nstr(beta(mp.mpf(1)/16),30))

# Shifted prime event, not a raw integer endpoint.
s = mp.log(mp.mpf(5)/4)
t = mp.log(mp.mpf(5)/2)
C = K(s,s)
assert C > 0
predicted = -2*mp.log(2)/mp.sqrt(2)*K(s,t)/C

def innovation(v):
    return K(v,v)-K(s,v)**2/C

h = mp.mpf('1e-14')
y = innovation(t)
left = (3*y-4*innovation(t-h)+innovation(t-2*h))/(2*h)
right = (-3*y+4*innovation(t+h)-innovation(t+2*h))/(2*h)
assert abs(right-left-predicted) < mp.mpf('1e-24')
print('shifted jump', mp.nstr(predicted,30))

# Full section 16: failure of sufficient envelope is NOT failure of P.
a = mp.log(16)
d = mp.log(mp.mpf(17)/16)
old = [a/4,a/2,3*a/4,a]
C = mp.matrix([[K(s,t) for t in old] for s in old])
assert mp.eigsy(C,eigvals_only=True)[0] > 0

def eta(i,x):
    return gp((a-old[i])+x)-gp(a+x)

R = mp.matrix([[mp.quad(lambda x: eta(i,x)*eta(j,x),[0,d/4,d]) for j in range(4)] for i in range(4)])
Li = mp.cholesky(C)**-1
vals = mp.eigsy(Li*R*Li.T,eigvals_only=True)
rho = vals[len(vals)-1]
new = [a+d/4,a+d/2,a+d]
B = mp.matrix([[K(s,t) for t in new] for s in old])
D = mp.matrix([[K(s,t) for t in new] for s in new])
S = D-B.T*(C**-1)*B
print('beta,rho,coarse gap', *[mp.nstr(x,25) for x in (beta(d),rho,beta(d)-rho)])
print('minimum sampled S', mp.nstr(mp.eigsy(S,eigvals_only=True)[0],25))
print('DIAGNOSTIC ONLY: NO RH, NO GLOBAL P, NO INTERVAL CERTIFICATE')
```

## References

- Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*, arXiv:2206.03682v4, primary PDF: https://arxiv.org/pdf/2206.03682v4 . Only the stated unconditional formulas and conditional directions are used.
- Repository handoff and previous exact source-return: precise commits, paths and blobs in header and §1. The requested sign is marked unpaid in the pinned handoff itself; it is not silently imported from its diagnostic packet.
