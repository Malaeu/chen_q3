# STATUS: TRY_BF_WEIL_SOURCE_MATCH_WITH_RANK_AND_BOUNDARY_GUARDS

```yaml
OPERATIVE_CLASS: TRY_BF_WEIL_SOURCE_MATCH_WITH_RANK_AND_BOUNDARY_GUARDS
DATE: 2026-11-03
AUTHORITY: DIRECT_OWNER_BRUINIER_FUNKE_WEIL_REQUEST
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
SOURCE_MOCK_COMMIT: cefe9d7b6123b9129f658ac73450b6fe095134e6
SOURCE_MOCK_BLOB: 148b5d9ddcd628fc15a62b455ab54af541e3146e
SOURCE_MOCK_SHA256: 99eede6696bdd20a347aad25980d678797100e487824c5adfc8bd519ec209164
SOURCE_LOG3_COMMIT: e4390b8f39143977b7118428f946b75033510c23
SOURCE_LOG3_BLOB: 2b5bbfd2c99e8fc1193188c941d509cbccf6d094
SOURCE_LOG3_SHA256: 4daedf962be48ffa858f00afba6977654843cfcc099569b2b0bcd4a454d8aa01
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE: CHALLENGER_NOT_RH
REQUESTED_GLOBAL_WEIL_EQUALS_BF_SHADOW_NORM: NOT_ESTABLISHED
FIXED_TYPE_LINEAR_POSITIVE_BF_FACTOR: REFUTED_ON_A_SINGLE_SHORT_WINDOW
KILL_SCOPE: THEOREM_SHAPE
KILL_TARGET: FIXED_FINITE_AUTOMORPHIC_TYPE_LINEAR_OR_ANTILINEAR_SHADOW_ISOMETRY
KILL_EVIDENCE: NONZERO_SHADOW_KERNEL_WITH_STRICTLY_NEGATIVE_NORM_MINUS_WEIL_UPPER
KILL_EXCLUDES_GROWING_TYPES_OR_INFINITE_DIRECT_INTEGRALS: false
FIXED_SHADOW_HOLOMORPHIC_ADDITION_VISIBLE_TO_BF: false
POSITIVE_HURWITZ_COEFFICIENTS_ENTER_STANDARD_INFINITY_PRINCIPAL_PART_PAIRING: false
THETA_IS_CUSPIDAL: false
THETA_WEIGHT_HALF_PETERSSON_NORM_DIVERGES: false
FINITE_DIMENSIONAL_LOG3_BF_REALIZATION: EXISTS_AFTER_USING_THE_POSITIVITY_CERTIFICATE
NEW_ARITHMETIC_POSITIVITY_FROM_THAT_REALIZATION: false
MAASS_SELBREG_FINITE_PART_AUTOMATICALLY_NONNEGATIVE: REFUTED_BY_EXACT_NEGATIVE_LIMIT
LOG3_CERTIFICATE_GENERATOR_REEXECUTED: true
LOG3_RATIONAL_CERTIFICATE_SHA256: 8b7fb1900093eb47e663ae352e0b52a2ad18043bd5d654e0f1a71aacec5ddcc0
LOG3_EXACT_LDL_RECONSTRUCTION_REEXECUTED: true
NEW_DIAGNOSTIC_DPS: [50,80]
NEW_FLOATING_RESULTS_ARE_INTERVAL_CERTIFICATES: false
NEW_COFINAL_POSITIVE_BOUND: NONE
INDEPENDENT_ANALYTIC_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_EXECUTED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
VERIFIER: PAPER
```

## 0. Ответ и область результата

Ы. Предложенное глобальное тождество Вейля с положительным спариванием Брюинье–Функе не выведено. Вместо переименования неизвестного знака выполнены три конкретные проверки: стандартное BF-спаривание, его согласование с полной положительной формой на log(3), и эйзенштейнова регуляризация.

Результаты:

1. В стандартном BF-спаривании голоморфная свобода при фиксированной тени по-прежнему исчезает. Положительные коэффициенты H(n) в разложении Загира при бесконечности не входят в главную часть, которую использует эта формула.
2. Для одной фиксированной группы, веса и конечномерного множителя линейное BF-нормовое представление всей оконной формы невозможно уже на одном коротком окне: тени с конечной обычной нормой образуют конечномерное пространство, а источник имеет бесконечный положительный ранг. Ни RH, ни посаженный мир для этого препятствия не нужны.
3. На любой заранее конечномерной положительной части окна BF-представление построить можно, но предъявленное ниже построение использует уже доказанную положительность. Оно не является новым источником знака.
4. В стандартной эйзенштейновой модели конкретная конечная часть Маасса–Сельберга отрицательна при малых ненулевых спектральных параметрах, хотя полная усеченная норма положительна. Поэтому знак нельзя перенести через вычитание регуляризующих членов автоматически.

Это не запрет всех автоморфных реализаций или всех theta-lifts. Указаны точные кванторы опровергнутого класса. Новое соответствие полного арифметического источника бесконечномерной положительной автоморфной норме не построено.

## 1. Источники и нормировки

R1. `PROSHKA_VERDICT_RAMANUJAN_MOCK_COMPLETION_2026-11-03.md`, pin в header. Полные локальные байты: 33212; SHA-256 и Git blob независимо пересчитаны и совпали с закрепленным connector-blob. Прочитаны §§2–5 и source-return (9)–(12).

R2. `PROSHKA_VERDICT_FIRST_STEP_LOG3_SOS_2026-11-03.md`, pin в header. Полные локальные байты: 29186; обе контрольные суммы совпали. Исходный исполняемый appendix извлечен без математических изменений и выполнен заново. Это воспроизведение собственного прежнего сертификата, НЕ независимый авторский аудит его полного аналитического доказательства.

P1. J. H. Bruinier, J. Funke, *On Two Geometric Theta Lifts*, arXiv:math/0212286v4: Proposition 3.2, definition of H_k^+ before Lemma 3.3, Proposition 3.5, the paragraph immediately following it, Theorems 3.6–3.7, Proposition 3.11. Проверено также по авторской окончательной версии. Импорт: THEOREM. Для scalar finite-index групп должны сохраняться все каспы и ширины; для vector-valued полной модульной группы — все компоненты Weil representation.

P2. P. Humphries, *Equidistribution in shrinking sets and L^4-norm bounds for automorphic forms*, Math. Ann. 371 (2018), Proposition 2.1, equation (2.2): полное четырехчленное соотношение Маасса–Сельберга. Импорт: THEOREM. Диагональный предел ниже выведен непосредственно из четырех членов; осциллирующие члены не отбрасываются.

P3. D. Zagier, *Eisenstein series and the Selberg trace formula I*, введение и §1: геометрический trace действительно содержит вычитание continuous-spectrum частей. Используется для классификации, не как поставщик положительности нашей формы.

P4. NIST DLMF 27.14.12, 27.14.17–19: eta-product, модульность нормированной Delta и tau-коэффициенты. В этом файле Delta означает eta^24, без множителя (2pi)^12 из одной из конвенций DLMF.

```text
https://arxiv.org/pdf/math/0212286
https://www.maths.dur.ac.uk/users/jens.funke/theta_revfinalfinal.pdf
https://link.springer.com/article/10.1007/s00208-018-1677-9
https://people.mpim-bonn.mpg.de/zagier/files/scanned/EisensteinSelberg/fulltext.pdf
https://dlmf.nist.gov/27.14
```

PDF BF доступен как извлеченный текст; повторные web-screenshot нужных страниц вернули cache/internal errors, и контейнерная загрузка также не удалась. Визуальное чтение этих страниц не заявляется. Страница введения Zagier просмотрена web-screenshot. Формулы P2 прочитаны в полном HTML первичной публикации.

Обозначения различаются строго: xi_R(s)=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2 — целая функция Римана; Lambda(s)=pi^(-s/2)Gamma(s/2)zeta(s) — мероморфное завершение; xi_k=2iy^k conjugate(partial_bar_tau) — антилинейный оператор BF. Эти три объекта нельзя отождествлять.

В R1 доказано theta -> Mellin xi_R -> logarithmic derivative -> g_zeta. Формально это НЕ утверждение, что zeta как функция s сама является harmonic Maass form с BF-тенью theta. В точной цепочке theta является тенью завершенной формы Загира.

## 2. Что действительно утверждает BF

**[ABSTRACT | PAPER; A/F/LA; импорт P1.]** В одной совместимой vector-valued нормировке, kappa=2-k,

    F in H_k^+,   h=xi_k F in S_kappa,
    {g,F}=(g,xi_k F)_Pet
         =sum_components sum_(n<=0) a_F^+(n)b_g(-n).             (1)

Для g=h это обычная сходящаяся положительная норма. В scalar-конгруэнц-группе правая часть включает вклады всех каспов с согласованными масштабированиями. Здесь не используется ошибочная однокаспная формула для Gamma_0(4).

Ключевой механизм — постоянный коэффициент произведения. При g=sum_(m>=0)b_g(m)q^m равенство n+m=0 допускает только n<=0. Для cusp g также b_g(0)=0. Поэтому положительные коэффициенты a_F^+(n), n>0, не входят напрямую в этот граничный вклад.

У исходного объекта Загира

    Hplus=-1/12+sum_(n>=1) H(n)q^n

при бесконечности нет отрицательной главной части. На этом каспе CT(Hplus*g)=-b_g(0)/12. Это не означает, что полный многокаспный pairing равен только этому числу: остальные каспы и допустимость роста нужно проверить отдельно. Но бесконечный положительный ряд H(n) нельзя объявить непосредственно выжившим в сумме (1).

### 2.1. Точная невидимость фиксированной тени сохраняется и в pairing

Если v in M_k^! — допустимая weakly holomorphic добавка, то xi_k v=0. Поэтому, в области теоремы,

    {g,F+v}-{g,F}=(g,xi_k v)_Pet=0.                         (2)

На стороне коэффициентов это дает точную сумму нуль по главным частям ВСЕХ каспов/компонент. Возможное изменение одной главной части компенсируется остальными условиями модульности. Это также прямо отмечено после Proposition 3.5 в P1.

Таким образом, переход от shadow map к BF-pairing не возвращает произвольную информацию, лежащую в kernel xi_k. Pairing факторизуется через quotient H_k^+/M_k^!.

### 2.2. Theta: не cusp, но это НЕ автоматическая расходимость нормы

В R1:

    xi_(3/2) Hhat=-theta/(16pi),   theta=1+2q+2q^4+... .      (3)

Theta не является cusp form. Поэтому Hhat не принадлежит стандартному H_(3/2)^+ из (1). Нельзя применять именно Proposition 3.5, не расширив ее гипотезы и не выписав нулевые Fourier-моды на каспах.

Однако ||theta||_(1/2) конечна: у каждого каспа после slash-преобразования theta ограничена, и вклад константы интегрируется как integral_Y^infinity y^(-3/2)dy. Некаспидальность при весе 1/2 НЕ требует вычитать бесконечную положительную норму. Соответствующая Stokes-версия должна учитывать все каспы; это иной boundary bookkeeping, не бесплатная новая арифметическая степень свободы.

Для тени alpha(f)*theta правая норма имеет вид const*|alpha(f)|^2. Если alpha линейна или антилинейна, это форма ранга не больше одного.

Чтобы H(n), n>0, вошли в постоянный коэффициент прямо на этом каспе, партнер должен иметь q^(-n)-член. Тогда он не голоморфен в каспе, а его обычная Petersson-норма имеет экспоненциально расходящийся положительный вклад. Замена ее регуляризованной величиной требует новой теоремы о знаке, а не обозначения ||.||^2.

## 3. Проверка на log(3): сертификат воспроизведен

**[FINITE_CELL/ABSTRACT | PAPER; E/F/I/A/LA; inherited source theorem with executable replay.]** R2 дает для I=[-log(3)/2,log(3)/2]

    W_zeta[f]>=2^-30 ||f||_2^2                              (4)

на ВСЕМ пространстве конечной форменной энергии с поддержкой в I, включая четный сектор. Это не только N=3 матрица.

Повторно выполнены исходные interval-enclosure + exact-integer Bareiss вычисления, 70 interval digits, Gauss 40, 80 panels, degrees 0..60. Получен тот же canonical JSON hash:

    8b7fb1900093eb47e663ae352e0b52a2ad18043bd5d654e0f1a71aacec5ddcc0.

Оба блока 31 и 30 имеют положительные точные Sylvester minors после сдвига 2^-29 I. Отдельное новое SymPy rational LDL вычисление проверило положительность всех диагоналей и точное L D L^T=R в обоих блоках. Полный возвращенный operator error <1.784e-18<2^-40. Повтор не является независимым аналитическим аудитом Binet/Bessel/Gauss доказательств R2; статус их предпосылок явно наследуется.

### 3.1. Двухмодовый тест против одной theta-тени

В физически ортонормированном четном базисе без endpoint sign flip

    f0=L^-1/2 1_I,
    f1=sqrt(2/L) cos(2pi*x/L)1_I,
    L=log(3),

прямая исходниковая проверка при 50 и 80 dps дает

    W_2 = [[ 0.1223286298250149594, -0.1861261148259935877],
           [-0.1861261148259935877,  0.2848044909169482112]],
    det W_2 = 0.00019681252166224302354... .                  (5)

Числа (5) — DIAG, не интервальное решение о знаке. Строгий знак уже следует из (4): W_2>=2^-30 I. Следовательно, факторизация W_2 через одну линейную theta-тень невозможна: ее determinant был бы нулем. Умножение второй basis-функции на -1 меняет лишь знаки двух смешанных элементов, не вывод.

В расчете использованы полные arch-поле terms и ровно атом 2; n=3 имеет нулевую корреляцию на границе. Постоянная мода независимо сверена через точную Lerch-сумму архимедова ряда.

## 4. Ранговое препятствие для всего стандартного BF-класса

### Теорема — фиксированный автоморфный тип не вмещает полную оконную форму

**[ABSTRACT | PAPER; LA/A, E/F/I только для исходной локальной коэрцитивности.]** Зафиксируем finite-index группу Gamma, вес k и конечномерный унитарный множитель/representation. Пусть F_f — линейное или антилинейное семейство harmonic weak Maass forms этого типа. Предположим, что h_f=xi_k F_f имеет конечную ОБЫЧНУЮ Petersson-норму и что

    W_zeta[f]=||h_f||_Pet^2                                (6)

для всех гладких четных f с поддержкой в I. Тогда получается противоречие.

**Доказательство.** h_f weakly holomorphic на верхней полуплоскости. Полюс любого порядка в каспе дал бы экспоненциальную расходимость обычной нормы. Поэтому h_f голоморфна во всех каспах (с допустимыми константами там, где вес позволяет L2). Это подпространство конечномерного M_(2-k)(Gamma,rho*). Конечномерность следует также из описания как пространства голоморфных сечений фиксированного векторного расслоения на компактной модульной кривой.

Пусть его размерность d. Возьмем d+1 независимых гладких четных оконных тестов. У линейной/антилинейной карты f->h_f имеется ненулевое ядро. Нормируем его элемент f до ||f||_2=1. Тогда

    ||h_f||_Pet^2-W_zeta[f] <= -2^-30 <0.                   (7)

Это строгий отрицательный UPPER для заявленного равенства, а не неуспех достаточной оценки. ∎

Глубина главной части F_f^+ может неограниченно расти; это не исправляет доказательство: BF-норма видит лишь конечномерный quotient по kernel xi_k.

### 4.1. Независимость препятствия от всего компьютерного log3-поставщика

Для проверки ранга достаточно меньшей поддержки delta=1/64, лежащей внутри I. На ней все prime correlations нулевые. Прямой полный source bound дает

    W[f]>=beta(delta)||f||^2,
    beta=2[atanh(e^-delta/2)+atan(e^-delta/2)]-c_*
          -[2sinh(delta/2)-delta].                         (8)

Здесь сохранены оба полюса. Неравенство следует из disjoint shifts u>=delta в arch-интеграле и lower pole bound -||sqrt(2)sinh(x/2)||^2.

Используя e^-delta/2>=1-delta/2 и Lipschitz-константу 1 для atan,

    beta(1/64)>=log(255/(8pi))-gamma_E-2sinh(1/128)
              >2-1-1/32=31/32.                           (9)

Для последнего шага: pi<22/7 дает 255/(8pi)>10; e<3 дает log10>2; gamma_E<1; sinh(x)<2x при 0<x<1/2. Поэтому (7) можно усилить до <-31/32 на бесконечномерном подклассе меньшей поддержки. Сам ранговый no-go не зависит от доверия к полной аналитической части R2.

### 4.2. Точная граница no-go

Не исключены: растущие веса/уровни/размерности representation; бесконечные прямые суммы/интегралы; негармонические автоморфные поля; иной signed pairing с оплаченным остатком.

Не предполагается, что всякая мыслимая нелинейная карта f->F_f обязана быть линейной. Теорема относится к linear/antilinear source lift или к представлению, сохраняющему ВСЕ смешанные спаривания. Последнее само обеспечивает линейность после факторизации нулевых направлений. Изолированное числовое назначение F_f=sqrt(W[f])*F0 заранее требует W[f]>=0 и не доказывает его.

Отрицательный контроль (7) убивает только фиксированный стандартный BF-изометрический класс, не автоморфный маршрут в целом и не RH.

## 5. Что действительно можно построить из сертификата: конечный F_f

**[FINITE_CELL | PAPER; LA/A, THEOREM BF surjectivity; positivity imported from R2.]** Пусть V — любое заранее конечномерное d-мерное подпространство окна log(3), A его точная Weil-матрица. Из (4) A>0; определим R^*R=A.

Выберем weight K=12d на SL2(Z). Формы

    Delta^j E4^(3(d-j)),   j=1,...,d,

— независимые cusp forms веса K: их первые степени q равны q^j. Ортонормируем их Petersson-метрику, получив g_1,...,g_d. По surjectivity xi_(2-K) выберем U_j с xi_(2-K)U_j=g_j.

Для f=sum c_i phi_i положим

    F_f=sum_j conjugate((Rc)_j) U_j.                       (10)

Антилинейность xi дает xi F_f=sum_j(Rc)_j g_j, поэтому

    ||xi F_f||_Pet^2=c^*Ac=W[f].                           (11)

BF principal-part identity теперь также верна. Это настоящее существование F_f на каждой конечной положительной части окна, с явно указанными весом и операциями.

Но (10) начинается с положительного квадратного корня УЖЕ сертифицированного A. Оно не выводит (4), не находит prime coefficients в независимой геометрии и не продолжается на неизвестные большие окна без нового знака. Это контроль того, что локальное представление после сертификата возможно, а не предлагаемое глобальное доказательство.

Вес 2-12d не равен прежнему 3/2; подмена не скрыта. Для всей бесконечномерной области один фиксированный такой вес не подходит по §4.

## 6. Путь через Эйзенштейна: нормировка и точная потеря положительности

**[ABSTRACT | PAPER; F/A/LA, E при logarithmic derivative.]** Для стандартного ряда E(z,s) на PSL2(Z) постоянный член равен

    y^s+phi(s)y^(1-s),
    phi(s)=Lambda(2s-1)/Lambda(2s)
          =[s/(s-1)] xi_R(2s-1)/xi_R(2s).                 (12)

Множитель s/(s-1) обязателен, если xi означает ЦЕЛУЮ функцию Римана нашей цепочки. Написание только xi_R(2s-1)/xi_R(2s) теряет полюсную нормировку. Для мероморфной Lambda этот множитель уже включен.

Пусть Lambda^Y E — стандартное усечение постоянного члена выше высоты Y>1. При s=1/2+it, t!=0, четырехчленная формула P2 дает

    N_Y(t):=||Lambda^Y E(.,s)||_2^2
     =2log Y-phi'(s)/phi(s)
       +[conjugate(phi(s))*Y^(2it)-phi(s)*Y^(-2it)]/(2it).
                                                               (13)

При этом |phi(s)|=1 и phi'(s)/phi(s) вещественно на этой прямой. Формула получается пределом s+conjugate(r)->1 в первых/последних членах P2 и сохранением двух остальных. Она также следует из Green identity. Последний осциллирующий boundary term не равен нулю.

Определим конкретную стандартную конечную часть, вычитая указанные неубывающие cusp terms:

    FP(t)=N_Y(t)-2log Y
          -[conjugate(phi(s))*Y^(2it)-phi(s)*Y^(-2it)]/(2it)
         =-phi'(s)/phi(s).                                 (14)

Это точная независимая от Y величина; ниже доказывается, что она не всегда положительна. Утверждение относится к данной нормировке конечной части, а не к любой иной схеме регуляризации с добавленными константами.

### 6.1. Строгий отрицательный конечный остаток

У мероморфного завершения

    Lambda(1+v)=1/v+A+O(v),
    A=(gamma_E-log(4pi))/2,
    Lambda(v)=-1/v+A+O(v).

Второе разложение следует из functional equation. Поэтому

    phi(1/2+epsilon)=-1+4A epsilon+O(epsilon^2),
    lim_(t->0,t!=0) FP(t)=4A=2[gamma_E-log(4pi)]<-2.         (15)

Последний strict upper следует из gamma_E<1, pi>3 и log12>2. По непрерывности FP(t)<-1 для всех достаточно малых ненулевых t. Никакой гипотезы о нулях не использовано. Точка t=0 сама является специальным вырожденным пределом и не подставляется в (13).

При 50/80 dps, t=0.01,Y=2:

    FP             = -3.9060176260259902395109761385...,
    oscillatory    = +2.5205225792704153866849395836...,
    2logY          = +1.3862943611198906188344642429...,
    N_Y            = +0.00079931436431576600842768793... .   (16)

Числа (16) — normalization DIAG. Строгий отрицательный результат доказывается пределом (15), а не decimal test.

Таким образом, положительная исходная усеченная норма НЕ дает положительной finite part. Запись ||.||_reg^2>=0 требует отдельной теоремы. Оставить истинную норму можно, но тогда boundary terms в (13) должны остаться и быть перенесены к нашему W без потерь.

### 6.2. Где находятся нули zeta в этой модели

Если xi_R(rho)=0, то стандартный scattering coefficient имеет полюс при s=rho/2. Числитель там не обнуляется: rho-1 лежит в -1<Re(s)<0, где у completed zeta нет нетривиальных нулей; полюса 0,1 также не совпадают с рассматриваемой невещественной точкой.

В физических координатах z_rho=i(rho-1/2):

    s_pole=1/4-i z_rho/2.                                  (17)

RH требует Re(s_pole)=1/4. Unitarity scattering дана на ДРУГОЙ прямой Re(s)=1/2. Реальность спектра self-adjoint Laplacian не утверждает, что все его resonance poles лежат на Re(s)=1/4.

Кроме того, обычный E(z,s) имеет eigenvalue s(1-s), не harmonic eigenvalue 0. Произвольный Eisenstein wavepacket не является одной harmonic Maass form из (1). Это изменение класса допустимо как новая попытка, но нельзя переносить BF-формулу без проверки.

## 7. Эйхлер–Сельберг: числа классов не делают trace положительным

**[FINITE_CELL | PAPER; I/A/LA.]** В нормировке Delta=q product_(n>=1)(1-q^n)^24=q-24q^2+... пространство S_12(SL2(Z)) одномерно. Для классического ненормированного Hecke T_2 имеем

    T_2 Delta=tau(2)Delta=-24Delta,
    Tr(T_2|S_12)=-24<0.                                    (18)

Коэффициент -24 следует прямо из eta-product; нормированность Delta и одномерность дают eigenvalue. Размерность также следует из valence bound ord_infinity(f)<=1 и отсутствия нулей Delta в H: f/Delta — голоморфная функция веса 0 на компактной модульной кривой.

Следовательно, trace-формула с class numbers не является суммой неотрицательных чисел только потому, что справа присутствуют числа классов. Trace(A^*A) был бы положительным, но тогда отдельно надо построить A из полного Weil-источника и вычислить все смешанные члены. (18) не убивает все возможные положительные trace-lifts.

## 8. RH-ветка и посаженный мир

**[COFINAL_FAMILY | CONDITIONAL ON RH.]** Под RH исходная полная форма равна положительной нулевой Gram-сумме. Ее можно реализовать в бесконечномерном l2 нулей с кратностями. Это не BF-конструкция из арифметики и не доказательство RH. Ранговое препятствие §4 сохраняется даже в этой положительной ветке: оно запрещает конечномерный образ полной локальной формы, а не положительность формы.

**[COFINAL_FAMILY | PAPER for the defined planted family.]** Пусть Xi_0 имеет реальные нули и положительную screw-форму с S0=sum nu_gamma/gamma^2<infinity. Посадим

    P(z)=[(z^2-w^2)(z^2-conjugate(w)^2)]^nu,
    w=2pi/log2+i eta, 0<eta<1/2,
    Xi_w=Xi_0 P.

На L_k=k log2 прежний exact upper сохраняется:

    W_w[L_k^-1/2 1_[-L_k/2,L_k/2]]
       <={4S0-8nu Re(w^-2)[cosh(eta L_k)-1]}/L_k <0         (19)

eventually. Поэтому source-matched ordinary positive BF-норма обязана сломаться в этом мире: либо источник не имеет нужного lift, либо за пределами обычного положительного класса появляется signed boundary/resonance contribution.

Но формальная unitarity scattering этого не замечает. Положим R(s)=P(i(s-1/2)); это вещественный polynomial с R(1-s)=R(s). Тогда

    phi_w(s)=phi_0(s) R(2s-1)/R(2s),
    |phi_w(1/2+it)|=1                                     (20)

всюду, где отношение определено. Действительно, R(1+2it)=R(-2it)=conjugate(R(2it)). Это точный planted-контроль против вывода RH из одной functional equation/граничной unitarity.

Не утверждается, что произвольная посаженная phi_w реализуется Eisenstein series настоящей модульной поверхности. Контроль (20) исключает лишь использование этих двух скалярных свойств как достаточных. Истинное automorphic source-matching могло бы дополнительно ограничивать допустимые функции; такого supplier здесь нет.

## 9. Что именно нужно сохранить в возможном ремонте

Самая слабая положительная версия, которая действительно была бы новым механизмом, требует source-defined, не извлеченный из неизвестного квадратного корня W, оператор T в БЕСКОНЕЧНОМЕРНОЕ положительное пространство и точный возврат

    W_zeta(f,h)=<Tf,Th>,

либо тот же возврат с полностью оплаченным signed остатком. Нужно сохранить физические endpoint masses, gamma/poles, все Lambda(p^k), смешанные спаривания и согласованность при изменении окна. Ни principal-part theorem, ни surjectivity xi сами этого не дают.

Две допустимые смены представления после указанного scoped kill:

| Representation | Exact contract and discriminator | Kill-power / cost |
|---|---|---|
| Infinite direct sum/direct integral of automorphic shadow types | Positive Plancherel measure; exact cross-Gram return to W, not individual fitted diagonal norms. Rank of finite restrictions must grow; w-negative witness must not map to a genuine positive norm | High / moderate for rank-source preflight; new source identity remains unproved |
| Full truncated Eisenstein/relative trace with ALL boundary terms | Retain (13), rational pole factor in (12), and locate zeta residues at (17); prove the resulting joint inequality rather than infer a sign from FP | High / low for the normalization falsifier already run; arithmetic boundary estimate remains unproved |

DISCRIMINATOR for a zero-consistent candidate: choose d+1 independent short-supported tests for a d-dimensional shadow target. The target Gram has a null vector; the source is >=2^-30 I (or >31/32 I on smaller support). This is a strict signed discrepancy, not a tiny-eigenvalue fit. For a regularized candidate, test the exact small-t limit (15) before any window scan.

## 10. Claim ledger, scores, and delivery boundary

| Claim | Scope | Verifier | E/F/Z/LA/A/I and limit |
|---|---|---|---|
| BF pairing and fixed-shadow invariance | ABSTRACT | PAPER | A/F/LA; imported theorem plus explicit coefficient calculation |
| Fixed-type ordinary-norm no-go | ABSTRACT | PAPER | LA/A; local source E/F/I, no Z or RH |
| Full log3 source certificate replay | ABSTRACT with finite certificate | PAPER | E/F/I/A/LA; executable replay, not independent analytic review |
| Local finite-dimensional F_f after certificate | FINITE_CELL | PAPER | LA/A; BF surjectivity; does not supply the sign used to construct R |
| Negative Maass-Selberg finite part | ABSTRACT | PAPER | F/A; exact strict upper via (15) |
| Positive Petersson/Eisenstein norm equals actual global W | COFINAL_FAMILY | CONDITIONAL | Not constructed or claimed |
| w scattering-unitarity and signed witness | COFINAL_FAMILY | PAPER | A/F/LA for explicitly altered source |

Predictions and their fate:
- Certificate expected hash was inherited before the replay; initial file-registration call failed to allocate a session. The replay is reported as reproduction of a known certificate, not a blind new prediction.
- P2, registered in a real local record before the new source/scattering runs: positive 2x2 source determinant versus zero one-shadow determinant — CONFIRMED; strict source sign is supplied by (4), not numerical output.
- P3: negative finite part at t=.01 and the limit (15) — CONFIRMED; exact limit supplies the mathematical sign.
- P4: full truncated norm with oscillatory boundary remains positive at the tested parameters — CONFIRMED; P2 Maass-Selberg supplies the identity.
- P5: planted FE-symmetric scattering ratio retains modulus one — CONFIRMED and proved by (20).
- Four exact algebraic controls: principal-part index selection, pole selection of positive H(n), rank-one determinant zero, Delta coefficient -24 — PASSED.

New calculations used mpmath 1.3.0, SymPy 1.14.0. New source/scattering numerical runs: 50/80 dps, diagnostic only. The older log3 generator was actually reexecuted at its specified 70-digit interval setup, with exact Bareiss signs; a separate exact SymPy LDL replay succeeded. No new global sign, independent author's audit, Lean, or Arb execution.

K8A:
DOWNSTREAM_CONSUMER: source-positive Weil form and then the inherited Route B positivity/floor consumers.
ACTUAL_CONSUMER_REQUIREMENT: a source-matched joint sign, not a generic norm identity in a different metric.
ORIGINAL_REQUESTED_OBJECT: harmonic Maass F_f with ordinary or demonstrably positive regularized shadow norm equal to W.
ORIGINAL_OBJECT_IS: NOT_NECESSARY as a particular proof mechanism; general positive realization is a sufficient interface.
FAILURE_TYPE: COUNTEREXAMPLE for the fixed-type linear isometry and automatic finite-part positivity; NO_DERIVATION for unrestricted growing-type source lifts.
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD only for the exactly named finite-type theorem shape; unrestricted automorphic route remains RESEARCH_DEBT.
KILL_SCOPE: THEOREM_SHAPE, not ROUTE_FAMILY.
KILL_EVIDENCE: (7), independently strengthened by (9); (15) for the regularization inference.
REOPEN_TRIGGER: an explicitly changed infinite-dimensional target and a new exact mixed source-return with all boundary terms.
NOVELTY_AXIS: precise local rank obstruction and explicit negative regularization control; no priority claim for abstract linear algebra or Maass-Selberg.
CLOSES: fixed-type BF norm identification; claim that the standard pairing restores arbitrary fixed-shadow information; automatic positive finite part.
OPENS: no new lemma is inserted as a mandatory supplier for Route B.

CODEX DIRECTIVE: audit this single candidate verdict. Check the local source-rank contradiction, actual BF growth/cusp hypotheses, the four-term Maass-Selberg diagonal limit, and the rational scattering prefactor. Do not promote the finite-dimensional construction (10) into an independent proof of its input positivity.

Verification handoff: extract the appendix to a writable directory as checks.py and run

    uv run --with mpmath==1.3.0 --with sympy==1.14.0 python checks.py

For the earlier full certificate, extract the unique python fence from the pinned R2 file and execute it; compare the exact JSON hash in §3. All steps run from their own writable working directory. No Lean source was added, so no axiom profile is claimed. Mathematical status changes only after a separate semantic audit, not on GitHub publication.

One new Markdown file is delivered under docs/routeB_bus/proshka/ on proshka_inbox_2026-10-31. Old verdicts and route-state files remain untouched. Commit and blob hashes are reported after remote readback.

## Appendix A. Executed local checks (new decimal outputs are DIAG)

The following program reproduces the new 2x2 source values, finite-part control, scattering normalization, and planted unit-modulus check. It does not rerun the larger source certificate; that separate exact replay is specified in §3.

```python
#!/usr/bin/env python3
"""BF-Weil candidate checks. New decimal values are diagnostic, not intervals."""
from pathlib import Path
import hashlib, json
import mpmath as mp
import sympy as sp
OUT=Path(__file__).resolve().parent

def source_checks(dps):
    mp.mp.dps=dps
    L=mp.log(3); a=mp.log(2); om=2*mp.pi/L
    c2=a/mp.sqrt(2); cs=mp.euler+mp.log(8*mp.pi)+mp.pi/2
    def j(u): return mp.exp(-u/2)/(-mp.expm1(-2*u))
    def C(i,k,u):
        if i==k==0: return 1-u/L
        if i!=k: return mp.sqrt(2)*mp.sin(om*u)/(L*om)
        return ((L-u)*mp.cos(om*u)-mp.sin(om*u)/om)/L
    tail=mp.atanh(mp.exp(-L/2))+mp.atan(mp.exp(-L/2))
    p=[4*mp.sqrt(2/L)*mp.sinh(L/4),-2*mp.sinh(L/4)/(mp.sqrt(L)*(mp.mpf(1)/4+om**2))]
    A=mp.matrix(2)
    for i in range(2):
        for k in range(2):
            delta=int(i==k)
            def integrand(u):
                if not u:
                    # exact one-sided value from C derivative at zero
                    cp=(-1/L if i==k==0 else (mp.sqrt(2)/L if i!=k else -2/L))
                    return -cp
                return 2*j(u)*(delta-C(i,k,u))
            H=mp.quad(integrand,[0,L/8,L/2,L])+2*delta*tail
            A[i,k]=H-cs*delta-2*c2*C(i,k,a)+p[i]*p[k]
    # independent scalar constant formula with exact positive-series resummation.
    ss=mp.pi**2/4+2*mp.catalan-mp.exp(-L/2)*mp.lerchphi(mp.exp(-2*L),2,mp.mpf(1)/4)/4
    W00=2*ss/L-cs-2*c2*(L-a)/L+32*mp.sinh(L/4)**2/L
    assert abs(W00-A[0,0])<mp.mpf(10)**(-(dps-8))
    assert mp.det(A)>0 and A[0,0]>0
    # Meromorphic completed zeta, distinguished from project entire xi.
    def Lam(s): return mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
    def xi(s): return s*(s-1)*Lam(s)/2
    def phi(s): return Lam(2*s-1)/Lam(2*s)
    def ldphi(s):
        def ldlam(z): return -mp.log(mp.pi)/2+mp.digamma(z/2)/2+mp.zeta(z,derivative=1)/mp.zeta(z)
        return 2*(ldlam(2*s-1)-ldlam(2*s))
    rows=[]
    gamma=2*mp.pi/mp.log(2);eta=mp.mpf(1)/4;w=gamma+1j*eta
    def R(z):
        u=1j*(z-mp.mpf(1)/2)
        return (u*u-w*w)*(u*u-mp.conj(w)**2)
    for t in [mp.mpf('0.1'),mp.mpf('0.01'),mp.mpf('0.001')]:
        s=mp.mpf(1)/2+1j*t;ph=phi(s);rr=-ldphi(s)
        Y=mp.mpf(2)
        osc=(mp.conj(ph)*Y**(2j*t)-ph*Y**(-2j*t))/(2j*t)
        norm=2*mp.log(Y)+rr+osc
        assert abs(mp.im(rr))<mp.mpf(10)**(-(dps-8))
        assert mp.re(rr)<0 and mp.re(norm)>0
        factor=s/(s-1)*xi(2*s-1)/xi(2*s)
        assert abs(factor-ph)<mp.mpf(10)**(-(dps-8))
        phw=ph*R(2*s-1)/R(2*s)
        assert abs(abs(phw)-1)<mp.mpf(10)**(-(dps-8))
        rows.append({'t':str(t),'finite_part':mp.nstr(mp.re(rr),40),'oscillatory_boundary':mp.nstr(mp.re(osc),40),'full_truncated_norm_Y2':mp.nstr(mp.re(norm),40),'planted_modulus_error':mp.nstr(abs(abs(phw)-1),6)})
    return {'dps':dps,'log3_even_source_2x2':[[mp.nstr(A[i,k],45) for k in range(2)] for i in range(2)],'determinant':mp.nstr(mp.det(A),45),'constant_formula_residual':mp.nstr(abs(W00-A[0,0]),6),'scattering':rows,'finite_part_limit':mp.nstr(2*(mp.euler-mp.log(4*mp.pi)),45)}

q=sp.symbols('q'); b0,b1,b2,h3,h4=sp.symbols('b0 b1 b2 h3 h4')
H=-sp.Rational(1,12)+h3*q**3+h4*q**4
g=b0+b1*q+b2*q**2
assert sp.expand(H*g).coeff(q,0)==-b0/12
# A pole would let positive-index class numbers enter.
assert sp.expand(H*q**-3).coeff(q,0)==h3
# Hecke trace sign at weight12: Delta=q-24q²+O(q³).
assert sp.expand(q*(1-q)**24).coeff(q,2)==-24
# Source-independent rank-one target has zero 2x2 determinant.
x,y,z=sp.symbols('x y z', real=True)
assert sp.det(sp.Matrix([[x*x,x*y],[x*y,y*y]]))==0
runs=[source_checks(d) for d in [50,80]]
res={'classification':'NEW_DIAGNOSTIC_PLUS_EXACT_ALGEBRA','symbolic_groups':4,'runs':runs}
(OUT/'checks.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(res,indent=2,ensure_ascii=False))

```
