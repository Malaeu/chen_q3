STATUS: TRY_MYTHOS_DOSSIER_RIGIDITY_WITHOUT_SIGN

OPERATIVE_CLASS: TRY_MYTHOS_DOSSIER_RIGIDITY_WITHOUT_SIGN
REQUEST: MYTHOS_H1_H12_2026_11_03
DATE: 2026-11-03
AUTHORITY: DIRECT_OWNER_REQUEST_IN_CHAT
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: rh_clean@cdb84497
INBOX_SOURCE: 75afd6a1f8e244f1da55e4c608233b22cc07c9f4
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE: CHALLENGER_NOT_RH
CARRIER: LITERAL_REAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
NEW_THEOREMS:
  - ALL_FEASIBLE_COUPLINGS_ARE_SUPERPOLYNOMIALLY_CLOSE_TO_ONE_POSSIBLY_EMPTY
  - COFINAL_COUPLING_FEASIBILITY_EQUIVALENT_TO_RH_WITH_INHERITED_SOURCE_RETURN
  - EVERY_FIXED_FINITE_PRIME_FAMILY_IS_UNIFORMLY_RIGID
  - FIXED_PRIME_FAMILY_HAS_A_POSITIVE_DUAL_ON_A_SPECTRAL_NEAR_ZERO_CLUSTER
  - DOUBLED_INTEGER_2_COUPLING_IS_EVENTUALLY_EMPTY_FOR_ALL_REAL_u
  - FULL_FINITE_CARRIER_HEAT_INERTIA_IS_NOT_AN_ORBITWISE_INVARIANT
SOURCE_SIGN_NEWLY_PROVED: false
FINITE_ACTIVE_PRIME_SET_IS_FIXED_BEFORE_m: true
ALL_GROWING_PRIME_HANDLES_p_LE_m_RIGIDITY_PROVED: false
INTERPOLATION_J_EQUALS_SPECTRAL_CLUSTER_ASSUMED: false
HYPOTHESIS_VERDICTS:
  H1: REDUCED
  H2: REDUCED
  H3: REFUTED
  H4: REDUCED
  H5: REDUCED
  H6: REDUCED
  H7: REDUCED
  H8: REDUCED
  H9: REFUTED
  H10: REFUTED
  H11: REDUCED
  H12: OPEN
REFUTATION_SCOPE:
  H3: ABSTRACT_ZERO_COMPRESSION_IMPLIES_COMPLEMENT_ONLY_RADIUS
  H9: UNIVERSAL_INERTIA_TRANSFER_FROM_QUARTET_TO_FINITE_CARRIER
  H10: ANNIHILATING_INTERPOLATION_J_ALONE_GIVES_UNIFORM_RADIUS
ACTUAL_ZETA_HEAT_INERTIA_REFUTED: false
NEW_SOURCE_EIGENSYSTEMS: 0
EXACT_CONTROL_GROUPS: 13
DIAGNOSTIC_PRECISIONS: [50, 80]
DIAGNOSTIC_OBJECT: EXPLICIT_FINITE_SPECTRAL_COUNTERMODEL_ON_LITERAL_m_2_CARRIER
NUMERICS_ARE_INTERVAL_CERTIFICATES: false
VERIFIER: PAPER
INDEPENDENT_ANALYTIC_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
PROGRESS_CLASS: PROOF_PROGRESS
ADDITIONAL_PROGRESS: SCOPED_FALSIFICATION_AND_SOURCE_RETURN
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
WRITE_BRANCH_REQUESTED: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_MYTHOS_HYPOTHESES_H1_H12_2026-11-03.md
REMOTE_PUBLICATION: NOT_PERFORMED_IN_THIS_SESSION
REMOTE_COMMIT_SHA: null

0. Ответ и главная развилка

Ы. Главный результат досье: арифметическую жёсткость удалось доказать отдельно от положительности. Для полного однопараметрического pencil любой допустимый коэффициент u сверхполиномиально близок к 1. Это безусловное утверждение допускает пустой интервал. На ложной RH-ветке интервал действительно должен стать пустым. Поэтому жёсткость сама по себе не поставляет знак.

Для любого заранее фиксированного конечного множества простых доказано аналогичное сжатие всей области весов, равномерное по направлениям. Для всех одновременно растущих ручек p<=m такой оценки нет. На спектральном околонулевом кластере фиксированный набор ручек имеет положительный двойственный баланс; он не является автоматически балансом на интерполяционном J.

Глубоко разобраны H1/H4, H3/H10 и H9. H2/H8 сведены к одному достаточному входу для уже закреплённого RH-потребителя. H5/H7 — к одному подписанному оператору кривизны. H6 сохраняет доказанный качественный горизонт, но не получает обещанный численный горизонт только из (gamma,a). H11 требует согласовать центр функционального уравнения; H12 не получает экспоненциальную скорость из сверхполиномиальной невязки.

Ни одно утверждение о настоящей ζ не опровергнуто абстрактной моделью без указания этой границы. Ни один конечный список критических нулей не использован для доказательства положительности.

1. Source lock и разделение входов

1.1. Прочитанные и унаследованные источники

Все пути ниже относительно github.com/Malaeu/chen_q3.

[R1] docs/routeB_bus/proshka/PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md, blob ebf7f8cab61a795118bda5dc7e65a0b3386247b7. Локальные байты независимо дают SHA256 fb0176935d103209bea3feff8362605024da7635c568768dc5355f441e5ddd14 и тот же Git blob. Используется только закреплённое расписание fixed 0<c<1, полный residual и нижний ранг.

[R2] docs/routeB_bus/proshka/SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_PAPER_AUDIT_2026-11-02.md на BASE, blob 4e6165039aaa6e5d52774413ca39de596be409bd. Прочитан полный независимый PAPER-аудит. Он не сертифицирует знак хвоста или конечный численный onset.

[R3] docs/routeB_bus/proshka/PROSHKA_VERDICT_CONFINE_2026-10-30.md на BASE, blob 1879347b72d1aa55cf506f5387de37059f929122, §§1–4, особенно (1.2)–(1.6), (3.1)–(3.9), (4.1)–(4.6). Это источник полной формы, theta-радикала, возврата КАЖДОГО ФИКСИРОВАННОГО jet в N=m и отрицательного компактного свидетеля. Не используется положительность формы как вход.

[R4] docs/routeB_bus/proshka/NOESCAPE_CONSTANT_FLOOR_REDUCTION_2026-10-31.md на BASE, blob 26eaa3ebe5f8fea7fadbdc6d1994654c4710b8c7. Прочитан целиком. Унаследованный PAPER-потребитель: любой постоянный полный нижний пол на неограниченной исходной семье исключает off-line нули. Он сильнее потребности в -o(1), но сам пол не поставляет.

[R5] docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_COMPLEMENT_2026-11-02.md на BASE, blob 1a20e653e46bbad3d0f5eb19e7c7d73f4fb5e82f. ВАЖНО: буквальный источник раскладывает относительно ОДНОГО theta-вектора, не относительно всего J. Ниже переход к общему J явно доказывается блочной оценкой, а не приписывается файлу.

[R6] docs/routeB_bus/proshka/PROSHKA_VERDICT_BALANCE_VERTEX_SOFTNESS_2026-11-03.md на inbox 75afd6a1, blob c150754c6c287545d3e893d60470c98998a98a45, SHA256 6059a9b59015189e6c63d5495b1eaf83f70052609a511fd50b03a5fa7b74bfb6. Проверены §§6–8 и локальные полные байты. Двойственная альтернатива, второпорядковый Schur и shifted-source Taylor сохраняются.

[R7] docs/routeB_bus/arithmetic_coupling_2026-11-03/RESULT.md на BASE, blob b0900f4c5533c4604aebfb418f13ced031c3d552. Все результаты файла остаются DIAG. В частности, его J имеет kappa=1; это НЕ J движущегося расписания [R1]. MP-отношения 9.7266,9.5769,9.8416 относятся к трём конечным окнам.

[R8] docs/routeB_bus/gaussian_height_2026-11-03/RESULT.md на BASE, blob 41d21ef1e22f9f3ef85b5a7254f6253ff8b09579. Полный источник не сертифицирован его конечным zero census. Текст прямо различает изолированную четверку и весь сжатый оператор; относительные совпадения 1.13%/0.323% — диагностика, не тождество инерции.

[R9] Унаследован из предоставленного досье и предыдущего контекста, без нового полного аудита: docs/routeB_bus/proshka/PROSHKA_VERDICT_QUIET_SPACE_INDEX_2026-11-02.md, blob 84b6d256ed...: принято точное попарное спаривание и пороговое дополнение Шура, без положительности высоких нулей. [R10] PROSHKA_VERDICT_FAKE_WORLD_EFZ_DH_BEURLING_2026-11-02.md, blob a391275...: унаследованный source-correct DH-контроль, не новый аудит.

docs/routeB_bus/stiffness_2026-11-03/RESULT.md не найден ни на указанном BASE, ни при отдельной проверке rh_clean. Данных параллельного опыта не выдумываю. Другие файлы этой папки не объявляются отсутствующими на основании этих двух 404.

1.2. Внешний контекст и его класс

Стандартные свойства дигамма-функции и её асимптотика сверяются с DLMF §§5.4,5.11; нормировка завершения и ζ — §§25.2,25.4,27.2. Это THEOREM/background. Основная новая математика ниже выведена из исходниковой формы и унаследованных возвратов, не импортирована из теорем, потребляющих искомый знак.

https://dlmf.nist.gov/5.4
https://dlmf.nist.gov/5.11
https://dlmf.nist.gov/25.2
https://dlmf.nist.gov/25.4
https://dlmf.nist.gov/27.2
https://arxiv.org/abs/2206.03682

1.3. Конвенции

Пусть W=C+B — полная чётная форма; B уже имеет отрицательный арифметический знак:

B[f]=-sum_(n>=2) Lambda(n)/sqrt(n) Q_f(log n),
Q_f(s)=2 Re integral conj(f(x)) f(x+s) dx.

На конечном окне длины L все n>exp(L) и крайний n=exp(L) дают нулевую корреляцию. Глобальные theta-тесты требуют бесконечной суммы, которая сходится абсолютно благодаря их хвостам.

C[f]=(1/(2pi)) integral a(t)|fhat(t)|^2 dt + |<p,f>|^2,
a(t)=Re psi(1/4+it/2)-log pi,
p(x)=sqrt(2)cosh(x/2),
c_*=EulerGamma+log(8pi)+pi/2.

В частности C>=-c_* I на каждом чётном окне. J — заданное value-пространство; K_m(mu) ниже — СПЕКТРАЛЬНЫЙ кластер |lambda|<=mu. Они нигде не отождествлены.

2. Таблица H1–H12: ровно один основной вердикт на пункт

Столбец p — исходная ставка Mythos, не изменённая после проверки. REFUTED всегда сопровождается областью контрпримера; REDUCED не означает, что гипотеза верна.

|H  |p  |Вердикт    |Что строго получено / точный остаток                                                                                                                                                                                                                                                        |Класс и scope                                                                                         |Reopen trigger                                                                                                                                                                                                                                     |
|---|--:|-----------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|H1 |.60|**REDUCED**|Новый THEOREM: всякий допустимый u удовлетворяет                                                                                                                                                                                                                                            |u-1                                                                                                   |<=eta_m, eta_m=o(m^-N) для каждого N; интервал может быть пуст. Непустота на неограниченной семье эквивалентна RH. Пропорция верхнего края lambda_q и универсальный коэффициент не доказаны; дан точный generalized-eigenvalue и coupling-критерий.|
|H2 |.15|**REDUCED**|u_+^perp>=2 — не обычная бесплатная потеря сита. Даже существование допустимого u_m>=1 на неограниченной семье уже влечёт RH, поскольку C>=-c_*I. Обратная импликация к числу 2 не доказана.                                                                                                |COFINAL_FAMILY/PAPER implication; source estimate CONJECTURE                                          |Строгий нижний envelope C_perp+2B_perp, либо иной допустимый u>=1 с полным хвостом.                                                                                                                                                                |
|H3 |.50|**REFUTED**|Нулевое Q*HQ не исключает выход при sqrt(lambda_q). Исправление: контролировать H Q и полный Schur complement; в спектральном разложении H Q=0 действительно переносит допуск на дополнение.                                                                                                |ABSTRACT/PAPER counterexample; не контрпример к вычисленной CCM-ячейке                                |Для конкретной ручки доказать invariant/block-diagonal action либо оплатить N и reduced gap.                                                                                                                                                       |
|H4 |.60|**REDUCED**|Новый THEOREM: все направления в ЛЮБОМ ФИКСИРОВАННОМ конечном наборе простых равномерно жёстки. Для такого набора существует dual Y>0 на спектральном околонулевом кластере. Растущие p<=m, метрика точного J и количественная кондиция Y не оплачены.                                      |COFINAL_FAMILY/PAPER fixed set; growing set CONJECTURE                                                |Uniform negative contrast kappa_m for all active directions with delta_m/kappa_m->0; injectivity и metric guards.                                                                                                                                  |
|H5 |.50|**REDUCED**|Нормированный боковой сдвиг имеет W_a=W_0-a²D/2+O(a⁴). Порог sqrt(2 lambda/D) условен на D>0 и контролируемый остаток. Ramanujan действительно нарушается у Euler-фактора, но строка, превращающая умеренность в знак, не найдена.                                                          |FINITE_CELL/PAPER Taylor; threshold CONDITIONAL                                                       |D_q>=d>0, quartic budget и eigenbranch-coupling bound; отдельный source sign из temperedness.                                                                                                                                                      |
|H6 |.45|**REDUCED**|Унаследован all-late-m отрицательный свидетель для каждого off-line нуля. Выписан вычислимый горизонт из отрицательного компактного теста и его норм. Uniform bound только по gamma,a не извлечён.                                                                                          |COFINAL_FAMILY/PAPER inherited; quantitative source-norm horizon THEOREM; coordinate-only horizon OPEN|Сертифицированные source-norm/normalization bounds для свидетелей по всей заявленной zero-region.                                                                                                                                                  |
|H7 |.20|**REDUCED**|i² задаёт знак Taylor-фактора, не знак D=sum(F#F)’’. В комплексных точках даже полностью занулённая четверка может дать D<0. Точный supplier — нижняя оценка полного derivative-Gram плюс tail.                                                                                             |ABSTRACT/PAPER obstruction; actual-zeta lower bound CONJECTURE                                        |Signed complete derivative compression with lower envelope; не positive finite zero head.                                                                                                                                                          |
|H8 |.10|**REDUCED**|Согласованная оценка -B_perp<=theta C_perp+epsilon I, 0<=theta<=1, sup epsilon<infinity даёт постоянный пол, значит RH. Exact factor2 — частный более сильный случай. Window inverse-kinks и point-Schur events нельзя смешивать.                                                           |COFINAL_FAMILY/PAPER implication; arithmetic supplier CONJECTURE                                      |Доказанная совместная inequality со всеми Γ/poles/prime powers.                                                                                                                                                                                    |
|H9 |.55|**REFUTED**|Построен точный countermodel на всём literal m=2 carrier: одна четверка плюс три реальные пары; A_0 имеет отрицательную линию, A_y>0 при явно конечном y. Изолированная четверка сохраняет индекс, overcomplete compression — нет. Для настоящей ζ на всех y инвариантность не опровергнута.|FINITE_CELL/PAPER model; actual-source universal claim OPEN                                           |Source-specific invariant of the heat image, not orbit determinant or finite census.                                                                                                                                                               |
|H10|.60|**REFUTED**|«Тень зануляется на J => uniform delta_0» ложно без контроля существующей связи. Даже HQ=0 при G>=1 может дать допуск O(delta_m²). Для spectral J + HQ=0 + uniform complementary gap верна исправленная версия.                                                                             |ABSTRACT/PAPER; actual mock shadow not specified                                                      |Явный source operator H и reduced-gap bound; голоморфная свобода с fixed shadow остаётся невидима.                                                                                                                                                 |
|H11|.75|**REDUCED**|Исправлена модель: xi(cs) центрирована в 1/(2c), а не 1/2. Полная форма — точная дилатация c W[U_cf]. Под RH допустимы все c>0; без RH имеется безусловный short-support feasible ray при c>=16L. Сдвиг одних пиков при старом Γ/полюсе — другая задача.                                    |ABSTRACT/PAPER exact source matching; local radius around1 OPEN unless RH                             |Явно зафиксировать изменяемые completion/center/weights; then source pencil derivatives and bounds.                                                                                                                                                |
|H12|.30|**OPEN**   |Из имеющегося residual не следует exp(-cm), относительная точность дна или точность ординат. H1 объясняет чувствительность через generalized spectrum, не через число верных цифр нулей.                                                                                                    |CONJECTURE for precise exp-rate; DIAG for three cells                                                 |Определить spectral object и доказать согласованные верхнюю/нижнюю оценки плюс root/eigenvector conditioning.                                                                                                                                      |

Оценка ставок: у H1 и H4 подтверждены указанные строгие подутверждения, не исходные составные заявления целиком. H3/H9/H10 опровергнуты в отмеченных универсальных формулировках. H2/H5/H6/H7/H8/H11/H12 не получили бинарного исхода для настоящей ζ; вероятности не «засчитываются» задним числом.

3. Главный новый результат: жёсткость связи без предположения знака

3.1. Pole-free radical jets плотны в нужной графовой метрике

Лемма 1 [ABSTRACT | PAPER; F/I/A и source identity E/F]. Из [R3] возьмём h с H(z)=hhat(z)=4xi(1/2-iz). Для любого вещественного полинома P функция

r_P=(d²/dx²-1/4) P(-d²/dx²) h

вещественна, чётна, имеет все экспоненциально взвешенные нормы производных и принадлежит глобальному радикалу W. Её Fourier-образ, с несущественным общим знаком,

R_P(t)=(t²+1/4)P(t²)H(t),

зануляет оба полюсных функционала при z=+/-i/2. В частности

W[r_P,g]=0,
C[r_P]=(1/(2pi)) integral a(t)|R_P(t)|² dt,
B[r_P]=-C[r_P].                                      (3.1)

Новый элемент: span{(t²+1/4)t^(2j)H(t)} плотен в чётном пространстве

L²(R,(1+|a(t)|)dt).                                 (3.2)

Доказательство. Обозначим Z(t)=(t²+1/4)H(t), w(t)=1+|a(t)|. У H есть экспоненциальное убывание на вещественной оси [R3,(2.2)], w=O(log(2+|t|)), Z не равен нулю почти всюду. Если U ортогональна всем t^(2j)Z в L²(wdt), то M(t)=conj(U(t))w(t)Z(t) интегрируема с некоторым экспоненциальным весом. Это следует из Cauchy–Schwarz. Все чётные моменты M равны нулю, нечётные — по чётности. Fourier-transform M аналитичен в полосе и имеет все производные нулевыми в начале; он тождественно нуль. Поэтому M=0, U=0. Это доказывает плотность. Реальные аппроксиманты получаются взятием действительных коэффициентов.

Здесь НЕ используется глобальная L²-непрерывность W. Плотность нужна только для отдельной arch-формы C после точного зануления полюсов. Невозможный перенос «радикал плотен => W=0 на всём L²» не выполняется.

Поскольку a(0)=-c_*<0 и a(t)=log(|t|/(2pi))+o(1)>0 при больших |t|, в (3.2) можно приблизить два ненулевых чётных теста, поддержанных в областях противоположного знака a. Квадратичная форма integral a|F|² непрерывна в метрике (3.2). Поэтому существуют ДВА ФИКСИРОВАННЫХ pole-free jets r_+,r_-, для которых

B[r_+]>0,       B[r_-]<0,       W[r_+]=W[r_-]=0.     (3.3)

Это существование доказано аналитически; конкретный полином минимальной степени и numerical onset не вычислены. Ни RH, ни конечная положительная zero-сумма не использованы.

3.2. Возврат обоих знаков на исходный N=m

Лемма 2 [COFINAL_FAMILY | PAPER; inherited [R3] плюс A]. Выбираем фиксированный cutoff chi из [R3] и

r_{±,m}=P_m[chi(x/b)r_±(x)],  b=log(m)/2.

Из [R3,(3.9)] для каждого N:

||r_{±,m}-r_±||₂ + ||A_m r_{±,m}||₂ = O_N(m^-N).    (3.4)

Дополнительно C[r_{±,m}]->C[r_±], а значит

B_m[r_{±,m}]->B[r_±].                               (3.5)

Обоснование (3.5) не теряет концы. Для projection error e внутри окна пусть epsilon_0=||e||₂, epsilon_1=||e’_int||₂ и j_e=|e(-b)|+|e(b)|. Его нулевое продолжение удовлетворяет при 0<s<=1

||e-T_s e||₂ <= s epsilon_1+sqrt(s) j_e.

Поэтому H[e]<=2 epsilon_1² integral_0^1 s²j(s)ds
+2j_e² integral_0^1 sj(s)ds
+4epsilon_0² integral_1^infinity j(s)ds ->0.

Это использует все endpoint-массы. Arch-форменное Cauchy–Schwarz переносит сходимость на смешанные члены. Полюсная ошибка ограничена ||p||_{I_m}epsilon_0=O(m^(1/4)epsilon_0)->0; cutoff-tail оплачивается weighted norms. Таким образом C сходится. Равенство B=W-C и (3.4) завершают (3.5).

В дальнейшем эти фиксированные r_± не объявляются точными элементами J_m. Они — действительные тесты в полном исходном carrier с доказанной полной невязкой.

3.3. Теорема о всём интервале связи

Теорема 3 [COFINAL_FAMILY | PAPER; E/F/I/A/LA]. Пусть

I_m={u in R:C_m+uB_m>=0}.

Существует неотрицательная последовательность eta_m, такая что для любого фиксированного N>0

eta_m=o(m^-N),
I_m subset [1-eta_m,1+eta_m]                         (3.6)

для всех достаточно больших m. Допускается I_m=empty.

Доказательство. Положим a_{±,m}=W[r_{±,m}], b_{±,m}=B_m[r_{±,m}]. Для поздних m b_{+,m}>b_+/2>0 и b_{-,m}<-|b_-|/2<0. Всякий допустимый u обязан удовлетворять одновременно

a_{+,m}+(u-1)b_{+,m}>=0,
a_{-,m}+(u-1)b_{-,m}>=0.

Следовательно

1-a_{+,m}/b_{+,m} <= u <= 1+a_{-,m}/|b_{-,m}|.

Можно взять eta_m=max(|a_+|/b_+, |a_-|/|b_-|) с конечными m-подстрочными величинами. Нормы r_{±,m} ограничены, поэтому (3.4) даёт сверхполиномиальность eta_m. Отрицательное a не исправляется по модулю для доказательства существования: модуль используется только для безопасного включения, которое допускает пустоту. Конец доказательства.

Не доказано этой теоремой: 1 in I_m, положительность A_m, экспоненциальная скорость exp(-cm), выбор нижнего eigenvector как единственного носителя выхода.

3.4. Непустота — ровно недостающий знак

Следствие 4 [COFINAL_FAMILY | PAPER, с inherited [R3]/[R4]]. Для настоящего источника эквивалентны:

RH;
I_m nonempty for an unbounded family of original m;
1 in I_m for every original m.                      (3.7)

Под RH W>=0 на всех исходных тестах, поэтому 1 in I_m. Для обратного направления из (3.6) и

||B_m|| <= 2 sum_(2<=n<=m) log(n)/sqrt(n)
         <=4 sqrt(m) log(m)

следует для любого допустимого u

A_m=(C_m+uB_m)+(1-u)B_m
    >=-4 eta_m sqrt(m)log(m) I = -o(1)I.            (3.8)

Отрицательный компактный off-line witness с all-late-m возвратом [R3,§4] противоречит (3.8) на неограниченной семье. Это доказательство импликации, не утверждение RH.

В частности, если RH ложна, I_m пуст для ВСЕХ достаточно больших m. Если RH верна, I_m действительно стягивается к {1} с включением (3.6). Гипотеза H1 о непустой игле содержит знак; одна только игольчатость его не содержит.

4. H1: точный верхний край и когда возникает коэффициент около 9.7

[FINITE_CELL | PAPER; LA.] При отдельно проверенном A=A_m>0 положим D=A^-1/2 B A^-1/2. Тогда

C+uB>=0 iff I+(u-1)D>=0,
u_+=1-1/lambda_min(D), if lambda_min(D)<0,           (4.1)
u_-=1-1/lambda_max(D), if lambda_max(D)>0.

Отсутствующий знак экстремального значения даёт бесконечный соответствующий конец. Если A не положительно определена, (4.1) нельзя применять молча; нужен другой строгий feasible anchor или прямые Rayleigh cuts.

Пусть q — единичный eigenvector A с eigenvalue lambda>0, и в его ортогональном разложении

A=diag(lambda,G), G>=g I>0,
B=[[ -beta, d* ],[ d, E ]], beta>0.

Для t=u-1>=0 точный scalar Schur:

lambda-beta t-t² d*(G+tE)^-1 d.                    (4.2)

Положим t0=lambda/beta. Если t0||E||<=g/2 и

theta=2lambda||d||²/(g beta²)<=1/2,

то

t0(1-theta)<=u_+-1<=t0.                            (4.3)

Верх — тест на q. Низ: complement>=g/2, а вычитаемый член <=2t²||d||²/g; в t0(1-theta) он не больше lambda theta. Конгруэнция даёт PSD. Поэтому коэффициент 1/beta возникает лишь при theta->0 и согласованном выборе q. В данных beta≈.103 объясняет ratios≈9.7; это не универсальная константа, не proof of asymptotics и не автоматически lambda_min(Q*AQ).

В тихом кластере соседний gap g может быть того же малого масштаба. Тогда (4.3) ничего не даёт, и нижний/верхний выход определяет вся generalized eigensystem, а не одна мода. [R7] именно фиксирует смешанный нижний носитель.

5. H4: строгая арифметическая жёсткость для любого фиксированного набора простых

5.1. Неотрицательное глобальное изменение арифметики невозможно

Лемма 5 [ABSTRACT | PAPER; E/I/A]. Зафиксируем конечное множество простых P0. Для t=(t_p) определим глобальную полную prime-group вариацию

H_t=sum_(p in P0) t_p B_p,
b_t(v)=-2 sum_(p in P0) t_p log(p)
                sum_(k>=1) p^(-k/2) cos(k log(p) v).  (5.1)

В каждом B_p сохранены ВСЕ степени. Ряд абсолютно и равномерно сходится; H_t — bounded L² multiplier. Если t!=0, b_t принимает оба знака.

Доказательство. Среднее b_t на [-R,R] стремится к нулю. Частоты k log p различны по уникальности факторизации. Поэтому среднее b_t² равно

2 sum_(p in P0) t_p² (log p)² sum_(k>=1) p^-k >0.    (5.2)

Пределы разрешены uniform convergence. Если b_t>=0, то b_t²<=||b_t||_infinity b_t и средний квадрат равен нулю — противоречие. Для b_t<=0 аналогично.

Это точное место использования обычной арифметики частот I и реальных prime-power weights E. Здесь умеренность нужна для абсолютной суммы по k; она сама не создаёт знак baseline W.

По плотности theta jets (достаточно обычной L²-плотности, поскольку H_t bounded) существуют фиксированные радикальные тесты с H_t[r_+]>0 и H_t[r_-]<0. Для каждого направления можно выбрать pole-free jets из §3.

5.2. Равномерная теорема по всем направлениям фиксированной размерности

Теорема 6 [COFINAL_FAMILY | PAPER; E/F/I/A/LA]. Для каждого фиксированного конечного P0 существует eta_{m,P0}=o(m^-N) для каждого N>0, такое что

W_m + sum_(p in P0)(w_p-1)B_{p,m} >=0
   ==> ||w-1||₂ <= eta_{m,P0}.                      (5.3)

Утверждение uniform over ALL directions in R^P0, не только для заранее выбранной прямой. Область может быть пустой.

Доказательство. Для каждого unit t лемма 5 даёт единичный фиксированный jet r_t с H_t[r_t]<0. По непрерывности линейного response по t тот же тест отрицателен в окрестности t. Компактность единичной сферы даёт конечное покрытие фиксированными r_1,…,r_N и единый kappa>0:

для каждого ||t||=1 существует j: H_t[r_j]<=-2kappa.

Возвращаем КОНЕЧНОЕ число фиксированных jets в carrier по [R3]. Их H_t responses сходятся uniform in ||t||=1, потому что P0 фиксировано и ||H_t|| равномерно ограничена. На поздних m один из них даёт H_t[r_{j,m}]<=-kappa, а |W_m[r_{j,m}]|<=epsilon_m=o(m^-N). Для w-1=R t допустимость требует 0<=epsilon_m-R kappa, откуда (5.3). Доказательство не фиксирует знак W_m и не удаляет активные baseline-атомы.

Оставшийся квантор H4: P0 нельзя заменить растущим P0(m)={p<=m} без равномерных оценок числа/порядка jets, их response margin и source-return constants. Именно там compactness по одной фиксированной сфере перестаёт оплачивать шаг.

5.3. Dual Y и его смысл

[ABSTRACT | PAPER; LA.] Для любого набора compressed prime matrices M_p на заданном конечном пространстве условие

{t: sum t_p M_p>=0}={0}

равносильно

injectivity of t->sum t_p M_p,
existence Y>0 with tr(YM_p)=0 for every p.          (5.4)

Доказательство — строгое разделение image subspace и компактного PSD trace-one сечения, как в [R6], но без ограничения sum t=0: Γ и полюс фиксированы. Поэтому справа теперь НУЛЕВЫЕ следы, не одинаковые ненулевые следы всех ручек.

На спектральном near-zero cluster K_m(mu_m), mu_m=m^-s, fixed s>0, (5.4) выполнено для каждого фиксированного P0 и всех достаточно больших m. Действительно, spectral projector Pi_m удовлетворяет

||(I-Pi_m)r_{j,m}|| <= ||A_m r_{j,m}||/mu_m=o(m^-N).

Все negative responses из доказательства теоремы 6 сохраняются после Pi_m. Следовательно никакой ненулевой t не имеет PSD compressed image; (5.4) даёт Y_m>0.

Это настоящее существование dual на указанном спектральном пространстве. Его кондиция/явные коэффициенты не получены. Если нужен вид меры, Y — положительная density matrix, то есть конечная положительная смесь rank-one states. Например, finite witness responses имеют 0 во внутренности своего convex hull; малое добавление epsilon I можно компенсировать положительными весами этих состояний. Таким образом Y можно представить как epsilon I+sum alpha_j v_j v_j*, alpha_j>=0, после решения конечной balancing system. Это не положительная мера по неизвестным нулям, принятой на веру.

На интерполяционном J низкие evaluation-строки зануляются: E_T Q=0. Поэтому любая конструкция

Q* E_T* D E_T Q

из одних низких значений ТОЧНО равна нулю и не может быть Y>0. Производные, высокие нули или source states могут участвовать, но их balance ещё надо доказать. Spectral cluster и J не заменяются друг другом без оценки угла/кондиции.

Для растущего набора удобен точный discriminator

kappa_m=min_(||t||₂=1) [-lambda_min(sum_p t_p M_p)].  (5.5)

Если kappa_m>0 и ||Q*A_mQ||<=delta_m, то всякая допустимая полная perturbation имеет ||w-1||<=delta_m/kappa_m. Существование Y без quantitative gap не даёт kappa_m/delta_m->infinity.

5.4. Строгий doubled-atom судья: eventual empty interval без RH

Теорема 7 [COFINAL_FAMILY | PAPER; E/F/I/A]. Для источника с удвоенным только целым атомом 2,

I_m^(2)={u:C_m+u(B_m+B_atom2,m)>=0},

интервал пуст для всех достаточно больших m.

Доказательство сохраняет Γ и полюс. На pole-free global radical C имеет symbol a(t), а добавленный атом имеет symbol h2(t)=-2c2 cos(t log2), c2=log2/sqrt2. В t=0:

a(0)=-c_* < h2(0)=-2c2 <0.

Плотность §3 даёт фиксированный jet r0 с C0<H0<0, где C0=C[r0], H0=B_atom2[r0]. На нём необходимое условие глобального coupling:

C0+u(-C0+H0)>=0 ==> u>= -C0/(-C0+H0)>1.

Выберем большой t1=2pi k/log2. Тогда a(t1)>0, h2(t1)=-2c2<0. Другой фиксированный jet r1 имеет C1>0,H1<0, поэтому

C1+u(-C1+H1)>=0 ==> u<= C1/(C1-H1)<1.

Два строгих порога несовместимы. Возврат обоих фиксированных jets сохраняет C,H и малость W; поэтому несовместимость сохраняется на ВСЕХ достаточно больших исходных m. Утверждение касается всего R по u, а не только окрестности 1. Никакой finite survey не экстраполирован.

Это аналитически объясняет eventual emptiness того контрольного pencil, который [R7] измерял. Не вычислены onset m0 и конкретные полиномы r0,r1. Нельзя подменять этим утверждением сертификацию каждой из 285 сохранённых ячеек.

6. H2 и H8: один вход, число 2 не принципиально

Теорема 8 [COFINAL_FAMILY | PAPER; LA, inherited E/F/A source]. Пусть G_m — compression A_m на J_m^perp, Cc и Bc — соответствующие части. Если на неограниченной семье существует u_m>=1 с

Cc+u_m Bc>=-E_m I,  0<=E_m<=E<infinity,

то RH следует на inherited PAPER-уровне.

Доказательство: при u>=1

G=(1/u)(Cc+uBc)+(1-1/u)Cc
  >=-[E/u+(1-1/u)c_*]I >=-(E+c_*)I.               (6.1)

В decomposition J+J^perp имеем A=[[D,K*],[K,G]], ||D||,||K||<=delta_m->0. Поэтому

lambda_min(A)>=min(lambda_min D,lambda_min G)-||K||
             >=-max(delta_m,E+c_*)-delta_m.       (6.2)

Это постоянный полный пол; [R4] завершает импликацию. RH здесь не утверждается.

Эквивалентная форма H8:

-Bc<=theta_m Cc+epsilon_m I,
0<=theta_m<=1, sup epsilon_m<infinity,             (6.3)

даёт G>=-(c_*+epsilon_m)I напрямую. Для theta=0 аргумент всё ещё действует. При theta>0 запись u=1/theta допустима. Убывание epsilon до нуля не требуется постоянному-floor потребителю.

H2 exact endpoint u=2 — частный более сильный supplier. Условие «sup feasible interval >=2» нужно читать вместе с nonempty interval; оно обеспечивает наличие какого-то feasible u>=1, а не обязательно разрешает подставить u=2 без проверки нижнего конца.

БЕЗ baseline guard или нижней оценки C endpoint-неравенство не даёт exact PSD при u=1. Контроль C=diag(-2,2), B=diag(1,-1) имеет единственный feasible u=2, но C+B=diag(-1,1). Это не контрпример постоянному-floor выводу (6.1).

Large sieve, Brun–Titchmarsh или Montgomery–Vaughan здесь не импортированы как поставщики (6.3). Абсолютная оценка ||B||<=4sqrt(m)log m не даёт bounded epsilon. Требуется signed comparison с actual C, не общая оценка нормы. «Паритетный барьер 2» пока HEURISTIC motivation, не доказательство.

Знак delta(S’)<=0 относится к указанному оконному rank-one birth при фиксированном carrier; у point-kernel есть shifted events и полная матрица событий. Положительный inverse-kink не является положительным вкладом энергии. Эти различия из [R6] не отменены.

7. H3 и H10: точные второпорядковые контроли и исправление

7.1. Нулевое сжатие не убирает тихий масштаб

[ABSTRACT | PAPER; LA; REFUTED H3 as stated]. Пусть

A_eta=diag(eta,1), eta>0,
J=span(e1), H=[[0,1],[1,0]].

Q*H Q=0, complement gap=1, но

det(A_eta+tH)=eta-t².

Точный двухсторонний допуск |t|<=sqrt(eta). Он зависит от quiet energy, а не только от дополнения. При eta=0 любой ненулевой t выходит из PSD-конуса. Это контрпример универсальной линейно-алгебраической импликации, не вычисление literal ζ.

7.2. Даже H Q=0 мало при несpectral J

[ABSTRACT | PAPER; LA; REFUTED uniform-radius clause of H10]. Возьмём

A_e=[[e²,e],[e,1+e²]], e>0,
J=span(e1), H=diag(0,-1).

A_e>0, ||A_eQ||=O(e), G=1+e²>=1, H Q=0. Тем не менее

det(A_e+tH)=e²(e²-t),

поэтому положительный допуск равен e². Причина — существующая связь: complement after eliminating J равен

G-KD^-1K*=e²,

а не G≈1.

7.3. Правильная теорема для ручки

[FINITE_CELL | PAPER; LA.] При A>0 и self-adjoint H точный симметричный радиус равен

delta_sym=1/||A^-1/2 H A^-1/2||,                    (7.1)

с infinity для H=0. Односторонние концы читаются из положительных/отрицательных generalized eigenvalues отдельно.

Если дополнительно ||QA Q||<=delta и ||QH Q||=h>0, то exact Rayleigh test даёт delta_sym<=delta/h. Поэтому первая часть H10 верна при delta/h->0, но одно слово «ненулевая тень» не обеспечивает этого отношения. Для одностороннего допуска нужно также выбрать правильный знак compression.

В decomposition J+J^perp, H=[[M,N*],[N,R]], exact Schur при G+tR>0:

D+tM-(K+tN)*(G+tR)^-1(K+tN)>=0.                    (7.2)

Если J — spectral invariant subspace, K=0, и H Q=0, то M=N=0; радиус ограничивается только G+tR. При G>=g>0 и ||R||<=R0 имеем |t|<=g/R0 независимо от тихой lambda. Если J не spectral, вместо G нужен положительный lower bound его reduced complement, как показал §7.2.

Для конкретной «мок-тени» H_m в запросе не определён. Ненулевое сжатие может быть положительным, тогда один знак delta не выводит из конуса вовсе. Обе стороны allowance требуют двух signed tests или (7.1). Голоморфная добавка с фиксированной BF-тенью не меняет исходную форму — это не новая непустая ручка.

8. H9: один квартет не доказывает инерцию всей тепловой матрицы

8.1. Правильное тождество

[ABSTRACT | PAPER; A/LA]. Если z_rho — фактические комплексные спектральные точки, то

W_y(f,g)=sum_rho e^(-y z_rho²) F_f#(z_rho)F_g(z_rho)
         = W_0(H_(y/2)f,H_(y/2)g),                 (8.1)

где H_s — физический heat operator с Fourier multiplier e^(-s z²). Для compact f его heat image не поддержан в исходном окне. Поэтому compression на V_m не получается конгруэнцией внутри V_m. В heat-source return арифметические n>m уже не исчезают по поддержке.

Один isolated quartet имеет вещественный блок

e^(-y(gamma²-a²)) [[cos(2y gamma a), sin(2y gamma a)],
                  [sin(2y gamma a),-cos(2y gamma a)]],

с determinant -e^(-2y(gamma²-a²)). Его индекс действительно сохраняется. Если evaluation coordinates независимы и исчерпывают carrier, Sylvester работает. При overcomplete zero rows их фиксированный image меняется относительно такой конгруэнции; индекс суммы не обязан сохраниться.

8.2. Полный точный countermodel на V_2

Теорема 9 [FINITE_CELL | PAPER; A/LA; не actual ζ spectrum]. Положим

m=2, L=log2, b=L/2, gamma=2pi/L, a=1/4,
w=gamma+ia,
r_j=gamma-j/64, j=1,2,3.

На literal even V_2, с той же physical L², зададим полную модель из ТРЁХ реальных пар и ОДНОЙ четверки, все multiplicities=1:

W_y[f]=2 sum_(j=1)^3 e^(-y r_j²) F_f(r_j)²
                 +4 Re[e^(-y w²)F_f(w)²].         (8.2)

Для вещественных чётных f формула задаёт real symmetric matrix; complex extension идёт поляризацией. Все перечисленные spectral nodes сохранены, никакого tail нет: это явно определённая конечная модель, не усечение, выданное за ζ.

При y=0 единичная постоянная phi0 имеет строго отрицательную энергию. Действительно,

F_phi0(z)=2sin(bz)/(sqrt(L)z),
F_phi0(w)=-2i sinh(L/8)/(sqrt(L)w).

Реальные пары дают не больше L/7168: используем r_j>7, sin(b j/64)<=b j/64 и sum j²=14. Отрицательная четверка имеет модуль

D=16sinh²(L/8)/L * (gamma²-1/16)/(gamma²+1/16)².

Из 8<gamma<10 и sinh(L/8)>=L/8 следует D>L/648. Поэтому

W_0[phi0] < L/7168-L/648 < -L/1024 <0.             (8.3)

В то же время A_y>0 для всех достаточно больших конечных y. Evaluation matrix E по r_1,r_2,r_3 обратима: исходная rational-polynomial interpolation на трёх различных немодальных squared nodes даёт ранг3. Пусть v — row at w, u=v E^-1, и

d=Re(w²)=gamma²-1/16,
Delta=d-r_1²=gamma/32-1/4096-1/16>0,
Y*=max(0,log(4||u||²)/Delta).

В real-node coordinates, после whitening положительной diagonal 2e^(-y r_j²), норма quartet perturbation не больше

2||u||² e^(-Delta y).

При y>Y* она <1/2, значит A_y>0. (8.3) и эта строгая нижняя оценка опровергают universal heat-inertia invariance всей конечной матрицы.

Детектор не обязан ломаться именно на каждом выборе planted frequency: в исходном w-контроле gamma≈9.06 расположена ниже первого критического ζ-тона, и heat не делает этот низкий квартет безвредным. Наш countermodel показывает, почему данные одного такого мира и determinant=-1 не доказывают общий закон.

8.3. Диагностический повтор, не часть доказательства знака

При 50 и 80 dps исходная full 3x3 model даёт W_0[phi0]=-0.00205119140573145… . Выбор y=62.737076… по более консервативной формуле с log(8||u||²) даёт положительную whitened matrix; подробности и код в приложении. Аналитические границы (8.3) и whitened error bound являются доказательством, а floating eigensystem проверяет нормировку.

Для A_y настоящей ζ на всех m,y результат остаётся неустановленным; под RH n_-=0 для всех y, но это условный судья. [R8] не содержит полного интервального source/tail сертификата, способного решить этот вопрос без RH.

9. H5/H7: одно signed curvature утверждение

[FINITE_CELL | PAPER; E/F/A; inherited [R6]]. Пусть F=fhat, F#(z)=conj(F(conj z)), H_f=F#F. Для нормированной формы произведения xi(s+a)xi(s-a):

W_a[f]=(1/2)sum_rho [H_f(z_rho+ia)+H_f(z_rho-ia)]
      =W_0[f]-(a²/2)D_f+E4,
D_f=sum_rho H_f''(z_rho),
|E4|<=a⁴ R_f/24,                                  (9.1)

с полным convergent fourth-derivative budget [R6,§8]. Нормировка 1/2 нужна, чтобы W_a при a=0 равнялась W_0, а не 2W_0.

На J низкие value-условия дают H_f’’=2F#‘F’. В реальных точках это 2|F’|², в комплексных — не absolute square. Все высокие нули остаются. Поэтому точный missing supplier H7 есть lower envelope для

Q* D_m Q,

где D_m — polarized complete (9.1). Ни его strictly positive minimum, ни tail domination в запросе не поставлены.

Алгебраический контроль: при w=gamma+ia,

F(z)=(z²-w²)(z²-conj(w)²)

зануляет всю четверку, но sum_quartet (F²)’’=-512gamma²a²(gamma²-a²)<0 при gamma>a. Это контроль аналитического знака, не Fourier-тест ζ. Чтобы получить genuine compact even Fourier-тест для той же конечной spectral model, умножить этот полином на Fourier-transform чётного C∞ bump, сжимаемого к delta_0. На четырёх фиксированных точках multiplier и его предел равны1; отрицательный знак сохраняется при достаточно малой поддержке. Полиномное умножение соответствует конечным производным bump. Таким образом, причина не в использовании полинома вне Fourier-класса.

Если для конкретного единичного q независимо известно W_0[q]=lambda>=0, D_q>=d>0, R_q<=r, то

W_a[q]<=lambda-(d/2)a²+(r/24)a⁴.

Достаточный строгий выход:

4lambda/d<a²<=min(a0²,6d/r).                       (9.2)

Для точной leading асимптотики фиксированного q требуется lambda r/d²->0; тогда a_q~sqrt(2lambda/D_q). Истинный eigenvalue exit может случиться раньше и требует контроля выбранной ветви/других направлений. Формула без sqrt2 зависит от определения A^(x²); её нужно нормировать, а не сравнивать коэффициенты на глаз.

При продольном spectral shift z->z+t Taylor-знак положителен, при z->z+ia отрицателен. Это верное i², но для полного источника на J оно умножает НЕИЗВЕСТНЫЙ signed D_f.

Где умеренность: Dirichlet-фактор ζ(s+a)ζ(s-a) имеет prime coefficient p^a+p^-a и logarithmic weights 2Lambda(n)cosh(a log n). При a!=0 нарушается Ramanujan bound O_epsilon(n^epsilon). Но completion также меняет gamma и pole data. В (9.1) и его sign-test нет строки, выводящей D_f>0 из Ramanujan. В source-return оценках умеренный рост контролирует нормы/сходимость; при любом фиксированном a эти оценки ремонтируются большей производной. Поэтому «неумеренность — единственная причина отрицательного знака» не доказана.

Для каждого fixed a!=0 произведение имеет off-line нули, например сдвиги существующих критических нулей. General explicit-formula witness construction даёт глобальную отрицательность и eventual finite detection с source-dependent constants. Это не uniform finite-m threshold a*(m).

10. H6: что уже является горизонтом, а чего не хватает для численной области

[COFINAL_FAMILY | PAPER; inherited A/F/E source]. [R3,§4] при заданном off-line нуле строит smooth even test phi с compact support [-R,R], ||phi||=1 и W[phi]=-nu<0. Для p>=2, L=log m, b=L/2>R положим

eps0=||phi^(p)||₂ (L/(2pi m))^p,
eps1=||phi^(p)||₂ (L/(2pi m))^(p-1),
Jerr=(2||phi^(p)||₂/sqrt L)(L/(2pi))^p
              sqrt(2/(2p-1)) m^(1/2-p),
Cphi=c_*+||phi''||₂ integral_0^1 s²j(s)ds
               +4 integral_1^infinity j(s)ds.

A sufficient all-test source-return error is

E_m(phi)=[(2+4L)sqrt(m)eps0+10eps1+10Jerr sqrt(3m/L)]
           +[Cphi+(2+4L)sqrt(m)]eps0.              (10.1)

Здесь ||P_m phi||<=1 уже использовано. При b>R и E_m(phi)<nu/2:

lambda_min(A_m)<=-nu/2.                            (10.2)

Это explicit test-dependent visibility criterion; все prime powers, arch и концы оплачены в [R3]. Чтобы получить horizon valid for every later m, берут монотонный majorant правой части (10.1), либо выбирают M с sup_{m>=M}E_m<nu/2. Для фиксированного p>=2 такого M достаточно и его можно вычислить из R,nu,||phi^(p)||,Cphi.

Не извлечён uniform M(gamma,a) только из координат четверки. В исходном isolating entire witness присутствуют multiplicity, значение quotient xi/P^nu в удалённом нуле и weighted derivative/cutoff norms. Они конечны для фиксированного источника, но их одинаковый бюджет по всей zero-region не выведен. Нельзя заменить это конечностью каждого нормировочного множителя по отдельности.

Сертификат A_m>=0 и (10.2) исключают только те off-line candidates/области, для которых соответствующий horizon уже оплачен. Сертификат на одном m не исключает неохваченную область. Это точный потребитель H6, а не «мы видим все нули потому, что дно мало».

11. H11: точное масштабирование меняет центр и весь источник

[ABSTRACT | PAPER; E/F/I/A]. У X_c(s)=xi(cs), c>0, центр FE равен s_c=1/(2c), полюс Dirichlet-фактора равен1/c, а spectral nodes z_rho/c. Поэтому source-correct form:

W_c[f]=sum_rho (F#F)(z_rho/c).

Пусть (U_cf)(x)=sqrt(c) f(cx); это унитарно в physical L² и

(U_cf)^hat(z)=c^-1/2 F(z/c).

Точно

W_c[f]=c W_1[U_cf].                                (11.1)

Входное окно L переходит в L/c, номер cosine-моды сохраняется. Это не замена original schedule без объявления: новая completed source сама требует такой дилатации.

В физическом источнике (11.1) даёт одновременно

W_c[f]= integral_0^infinity j(s/c)||f-T_s f||² ds
       -c c_*||f||²
       -c sum_n Lambda(n)/sqrt(n) Q_f(c log n)
       +|<sqrt2 cosh(x/(2c)),f>|²
       -|<sqrt2 sinh(x/(2c)),f>|².                 (11.2)

На чётных f последний член равен нулю. Арифметика здесь до n<=exp(L/c), не до m независимо от c. Γ-кernel, constant, poles и anchors меняются вместе с пиками. Формула получена substitution, не новой positivity assumption.

Под RH W_c>=0 для ВСЕХ c>0 и всех конечных окон. Поэтому true-world сверхмалый c-радиус не является RH-совместимым дискриминатором. Без RH уже короткая коэрцитивность на длине1/16 даёт

c>=16L ==> W_c[f]>=c(1/4)||f||²,                  (11.3)

для всех исходных f на длине L. Таким образом admissible c-set имеет безусловный поздний луч. Это не доказывает, что component вокруг c=1 соединена с ним без gap; exact local exit около1 остаётся отдельным вопросом до знания source sign.

Если сохранять старый Γ и pole, двигая лишь log n->c log n, получается другая deformation, НЕ ζ(cs). Для неё quantitative ultra-small allowance в данном досье не доказана.

12. H12: невязка, дно и точность нуля — разные величины

[COFINAL_FAMILY | PAPER for inherited upper; actual exponential law OPEN]. [R1]/[R2] дают

delta_m <= K_c sqrt(m)L³/(1+log L)²
   exp[-c² sqrt(m)(1+log L)²/(3072 L³)].             (12.1)

Это сверхполиномиально, но (12.1) НЕ даёт exp(-c0 m). Более сильная истинная скорость не опровергнута слабой оценкой. Кроме того ||A Q||<=delta_m говорит о малости всей заданной формы на J, не о знаке её eigenvalues и не о том, что весь bottom является quiet branch.

В отсутствие нижней спектральной оценки дно может уходить к -infinity вне J, оставаясь совместимым с (12.1). Это уже точно описано [R4]. Число верных цифр bottom в finite arithmetic не переводится в число верных цифр gamma без независимого inverse-condition bound для характеристического/интерполяционного отображения.

Например, точная новая CONJECTURE могла бы требовать для одного фиксированного cutoff schedule положительности lambda_min(QAQ) и двусторонних границ exp(-c2m)<=lambda_min(QAQ)<=exp(-c1m) с 0<c1<=c2 независимо от m. Ни одна из этих двух количественных границ в указанной форме здесь не доказана.

Для утверждения «~exp(-cm)» нужно назвать объект: lambda_min(A), lambda_min(Q*AQ), ||AQ||, ошибка projected theta test или ошибка восстановленного нуля — это не одна последовательность. Нужны sign, uniform upper/lower rates, separation/conditioning и согласованный cutoff. Таких данных три MP-точки [R7] не поставляют.

13. Карта зависимостей: что действительно ведёт к знаку

[COFINAL_FAMILY | PAPER/CONDITIONAL as marked].

Доказано без RH:
  две opposite-slope theta-формы
       -> every feasible I_m sits superpolynomially near 1
       -> finite-prime-family rigidity (отдельный theorem)
       НЕ -> existence of a feasible point.

С inherited source returns:
  I_m nonempty on an unbounded family  <=> RH
  complement >= -O(1) on an unbounded family <=> RH
  H8 bounded signed comparative estimate -> complement floor -> RH
  H2 feasible u>=1 on complement -> H8/floor -> RH.

H4:
  injective compressed map + positive dual Y
       <=> no nonzero PSD direction in that compression;
  quantitative kappa_m/delta_m -> infinity
       -> thin feasible region, POSSIBLY EMPTY.
  Ни одна из этих стрелок не создаёт допустимую точку.

H3 + H10:
  same Schur/coupling geometry;
  zero compression != zero coupling;
  spectral invariant J + HQ=0 + complement gap -> uniform safe radius.

H5 + H7:
  same complete derivative form D=sum(F#F)'';
  positive D + fourth-order budget -> sideways finite-window exit;
  это witness/detection, не positivity of zeta.

H6:
  off-line zero -> negative compact test -> explicit norm-based horizon;
  region-uniform horizon + finite PSD certificate -> regional exclusion.

H9:
  heat is pullback onto a DIFFERENT test subspace;
  orbitwise inertia does not fix compressed inertia.

H11:
  exact xi(cs) is dilation, not a new sign supplier.

H12:
  residual upper smallness != sign != numerical zero-location accuracy.

Общий минимальный positive supplier

На unchanged J^perp достаточно доказать ОДНО signed estimate

-B_m^perp <= theta_m C_m^perp + E I,
0<=theta_m<=1, E<infinity independent of m,

на одной неограниченной исходной семье. Это THEOREM как sufficient interface; её истинность для source — CONJECTURE/UNRESOLVED, не theorem. Theta=1 уже соответствует постоянному complement floor. Требовать theta=1/2, точный cluster count, fixed positive gap или всю growing-handle vertex theory не обязательно.

Cramer signal guard: сжатие/вычитание/heat не уничтожает off-line quartet автоматически. При heat его вклад остаётся signed и переносится в heat-image test space. При fixed-prime rigidity неизвестный знак остаётся в NONEMPTINESS, а не в ширине. При source correction он остаётся в discarded/counterterm. Нулевой либо малый residual сам по себе не является discriminator.

14. Отрицательные миры и граница каждого утверждения

|Механизм                         |ζ/RH-ветка                   |DH                                                       |Удвоенный атом2                                 |F_a                             |Посаженная четверка                              |
|---------------------------------|-----------------------------|---------------------------------------------------------|------------------------------------------------|--------------------------------|-------------------------------------------------|
|Rigidity без утверждения nonempty|Совместима                   |Может также выполняться; не sign test                    |Не спасает знак                                 |Не член finite-prime-only family|Может также выполняться                          |
|Новая H1+feasibility equivalence |Feasible при RH              |Generalized source return нужен отдельно; data не theorem|Теорема7: eventual empty for all real u         |Иная Γ/pole/weights family      |Off-line witness forces no global positive source|
|Source positive complement floor |Pass под RH                  |Должен fail у source-correct отрицательного witness      |Должен fail там, где источник строго отрицателен|Глобально fail для fixed a!=0   |Глобально fail                                   |
|Zero compression/HQ=0 alone      |Не гарантирует allowed radius|Та же algebra                                            |Та же algebra                                   |Та же algebra                   |Та же algebra                                    |
|Isolated quartet heat index      |Не нужен                     |Да, один quartet block                                   |Не применимо                                    |Да, при independent orbit coords|Да; full compression needs additional proof      |
|Exact xi(cs) dilation            |All c pass под RH            |Аналогичная корректная dilation сохраняет тип source     |Не делает altered source положительным          |Не равно горизонтальному shift  |Shifted zeros масштабируются, не исчезают        |

Доказательство «все положительные веса дают положительность» нигде не использовано. E/F недостаточны по отдельности, а список E/F/temperedness не заменяет source-specific estimate. В новой теореме5 E/I поставляют distinct frequencies и summability; F/полное completion поставляют theta-radical. Это делает rigidity точной, но не доказывает существование положительной исходной формы.

15. Predictions, мета-closeout и воспроизведение

15.1. Регистрация и исход

До новых символических/численных тестов записаны P1–P6; P7–P8 добавлены после первого source-audit, до выполнения тестов. Не выдаются за исходные ставки Mythos.

|Prediction                                              |Fate                                                                   |
|--------------------------------------------------------|-----------------------------------------------------------------------|
|P1: opposite-slope global radicals дают feasible squeeze|CONFIRMED аналитически §§3–4; numerical polynomial search не проводился|
|P2: zero compression допускает sqrt(quiet) exit         |CONFIRMED точным determinant, §7.1                                     |
|P3: isolated quartet invariant, full compression not    |CONFIRMED явной теоремой9 и 50/80-dps контролем                        |
|P4: xi(cs) требует source dilation/recentering          |CONFIRMED точной заменой переменной §11                                |
|P5: feasible complement u>=1 already implies floor/RH   |CONFIRMED (6.1)–(6.2)                                                  |
|P6: tiny residual не равен exponential law/positive sign|CONFIRMED логическим и source-scope audit                              |
|P7: fixed finite prime family has uniform stiffness     |CONFIRMED теоремами5–6; growing family НЕ проверена                    |
|P8: doubled integer2 has eventual all-real-u emptiness  |CONFIRMED теоремой7; onset НЕ вычислен                                 |

13 exact rational/symbolic control groups выполнены. Единственная initial harness error: структурное сравнение expanded polynomial с factored expression; заменено проверкой раскрытой разности. Математический тест и порог не менялись. Два small model eigensystems (50/80dps) — только DIAG. Ни одной новой ζ/DH eigenmatrix и ни одной finite-zero positivity promotion.

15.2. Три мостика и два surviving представления

BRIDGE 1 — convex duality: trace-balance Y, точная альтернатива (5.4); positive existence исходной формы не поставлена.
BRIDGE 2 — harmonic analysis of prime translations: symbol mean0 и positive mean square дают оба знака на global radical; этот мост закрыл fixed-prime rigidity целой семьи.
BRIDGE 3 — operator perturbation/Schur: точная цена связи, heat pullback и corrected shift threshold. Мост закрывает ложные универсальные inference, не arithmetic sign.
VANISHING IDENTITY: W(r_P,g)=0 используется только до confinement; finite remainder оплачен [R3].
COLLAPSE OBJECT: один source-defined positive lower envelope на J^perp; не новый kernel, полученный предположением RH.

Surviving re-representation R1: direct complete source comparative inequality (6.3). Kill-power 5/5, cost 4/5; слабейший интересный budget bounded, не necessarily o(1). Zero-consistent discriminator: rigorous Rayleigh upper for full A on a fixed source witness, including tails.
Surviving re-representation R2: full convex feasibility (3.7), with rigidity already paid. Kill-power 5/5, cost 5/5; искать primal feasible point/certified floor, а не ещё более узкий interval plot. Discriminator: nonempty-vs-empty with exact source envelopes, not thresholded nearzero eigenvalues.

15.3. Dependency epistemics и одно дальнейшее задание

DOWNSTREAM_CONSUMER: inherited constant-floor Route-B consumer on the unchanged N=m,L=log(m) family.
ACTUAL_CONSUMER_REQUIREMENT: bounded lower envelope on J^perp on one unbounded family, plus full quiet residual.
ORIGINAL_REQUESTED_OBJECT: adjudicate H1–H12, preferentially source sign/geometry.
ORIGINAL_OBJECT_IS: compound hypotheses corrected with explicit scope; several are stronger than necessary, several are not sign suppliers.
KNOWN_WEAKER_INTERFACES: (6.3) with bounded epsilon; any feasible u>=1 on complement; full coupling feasibility using theorem3 squeeze.
FAILURE_TYPE: NO_DERIVATION of positive source feasibility; COUNTEREXAMPLE only for scoped H3/H9/H10 inference.
EPISTEMIC_STATUS: positive source estimate RESEARCH_DEBT; exact refuted abstract theorem-shapes MATHEMATICALLY_DEAD only in stated scope.
NOVELTY_AXIS: author-level proof of feasible squeeze and fixed-prime-family rigidity; no historical priority claim.
REOPEN_TRIGGER: source-first primal feasible operator/lower bound, or a quantitative growing-prime contrast overcoming residual without claiming that thinness itself implies existence.

Один next directive: проверять именно bounded signed comparison (6.3) на полном дополнении, сохраняя C>=-c_*I и исходный prime sign. Допустимо использовать полный source variational method или доказанное representation identity. Недопустимо считать positivity of a finite critical-line zero prefix поставщиком. Успех — кофинальный lower envelope с независимым budget; failure — exact counter-witness или явно неоплаченный term. Новые massive spectrum scans не являются обязательным шагом этого вердикта.

Публикация: в этой сессии discovery GitHub по create_file вернул только read endpoints; поиск установленного GitHub plugin подтвердил тот же connector. Стандартная проверка прямого Git завершилась Could not resolve host: github.com. Поэтому remote commit/push не заявлены и SHA не выдуман. Полный исходный verdict выдан файлом; в нём один mathematical artifact и весь воспроизводимый код. Новые route-state/Lean файлы не создавались.

Appendix A. Reproduction

Save the Python block below as checks.py in an empty directory. It writes results.json. Dependencies: sympy, mpmath. It checks algebra and the explicit finite spectral model, NOT all analytic proofs, the full ζ source or any universal quantifier. No variable in the script is a repository path placeholder; its output directory is the script directory.

uv run --with sympy --with mpmath checks.py

Expected: 13 exact groups pass and two DIAG heat checks pass. A failure blocks reliance on the corresponding local normalization, not automatically the analytic source theorem. No Lean axiom profile is claimed.

"""Exact algebra controls; numerical heat checks are DIAG, not source certificates."""
import json
from pathlib import Path
import sympy as S
import mpmath as mp
out={'exact':[], 'diagnostic':{}}
def ok(name, condition):
    assert condition, name
    out['exact'].append(name)
e,t,b,g,n,r=S.symbols('e t b g n r', real=True)
A=S.diag(e,1); H=S.Matrix([[0,1],[1,0]])
ok('H3 det = quiet - t^2', S.expand((A+t*H).det())==e-t*t)
A2=S.Matrix([[e*e,e],[e,1+e*e]])
H2=S.diag(0,-1)
ok('H10 full annihilation of Q', H2*S.Matrix([1,0])==S.zeros(2,1))
ok('H10 det = e^2(e^2-t)', S.expand((A2+t*H2).det()-e*e*(e*e-t))==0)
C=S.diag(-2,2); B=S.diag(1,-1)
ok('H8 endpoint 2 without sign at 1', C+2*B==S.zeros(2) and (C+B).det()<0)
C0=S.Matrix([[2,1],[1,3]]); B0=S.Matrix([[1,2],[3,1]])
D0=S.Matrix([[5,1],[1,6]])
C1=S.Matrix([[1,0],[0,2]]); B1=S.Matrix([[2,1],[-1,3]])
D1=S.Matrix([[1,2],[2,-1]])
M0=C0.row_join(B0).col_join(B0.T.row_join(D0))
M1=C1.row_join(B1).col_join(B1.T.row_join(D1))
F0=C0.inv()*B0; T0=(-F0).col_join(S.eye(2)); Y0=B1-C1*F0
Su=D0+t*D1-(B0+t*B1).T*(C0+t*C1).inv()*(B0+t*B1)
S0=D0-B0.T*C0.inv()*B0
rhs=S0+t*T0.T*M1*T0-t*t*Y0.T*(C0+t*C1).inv()*Y0
ok('exact affine matrix Schur identity', all(S.cancel(x)==0 for x in Su-rhs))
u=S.symbols('u',real=True)
ok('constant-floor convex identity', S.expand((C+u*B)/u+(1-1/u)*C-(C+B))==S.zeros(2))
z,a=S.symbols('z a'); pol=(1+z+z*z)**2
avg=S.expand((pol.subs(z,z+S.I*a)+pol.subs(z,z-S.I*a))/2)
ok('H5 imaginary shift Taylor', S.expand(avg-pol+a*a*S.diff(pol,z,2)/2-a**4*S.diff(pol,z,4)/24)==0)
ga,eta=S.symbols('ga eta',real=True)
w=ga+S.I*eta; wb=ga-S.I*eta
Fp=(z*z-w*w)*(z*z-wb*wb)
Ds=sum(S.diff(Fp*Fp,z,2).subs(z,zz) for zz in [w,-w,wb,-wb])
ok('H7 quartet derivative sign', S.simplify(Ds+512*ga**2*eta**2*(ga**2-eta**2))==0)
phi=S.symbols('phi',real=True)
J=S.Matrix([[S.cos(phi),S.sin(phi)],[S.sin(phi),-S.cos(phi)]])
ok('single-quartet normalized determinant -1', S.trigsimp(J.det()+1)==0)
ok('heat constant-test upper rational gap', S.Rational(1,7168)-S.Rational(1,648)<-S.Rational(1,1024))
ok('heat exponent gap lower', S.Rational(8,32)-S.Rational(1,4096)-S.Rational(1,16)>S.Rational(3,16)-S.Rational(1,4096)-S.Rational(1,1000000))
ok('heat quartet rational amplitude lower', S.Rational(63,40804)>S.Rational(1,648))
ok('minimum of two roots counterexample', (S.Matrix([[0,1],[1,1]])).det()==-1)

for dps in (50,80):
    mp.mp.dps=dps
    L=mp.log(2); bb=L/2; om=2*mp.pi/L; ww=mp.mpc(om,mp.mpf(1)/4)
    nodes=[om-mp.mpf(j)/64 for j in (1,2,3)]
    def row(zz):
        return [2*(1 if j==0 else mp.sqrt(2))*zz*mp.sin(bb*zz)/(mp.sqrt(L)*(zz*zz-(j*om)**2)) for j in range(3)]
    E=mp.matrix([row(x) for x in nodes]); v=mp.matrix([row(ww)])
    base=2*E.T*E
    plant=mp.matrix(3)
    for j in range(3):
        for k in range(3):plant[j,k]=4*mp.re(v[0,j]*v[0,k])
    A0=base+plant
    U=v*E**-1
    uu=sum(abs(U[0,j])**2 for j in range(3))
    gap=mp.re(ww*ww)-nodes[0]**2
    yy=max(mp.mpf(0),mp.log(8*uu)/gap)+1
    N=mp.eye(3)
    for j in range(3):
        for k in range(3):
            N[j,k]+=2*mp.re(mp.exp(-yy*(ww*ww-(nodes[j]**2+nodes[k]**2)/2))*U[0,j]*U[0,k])
    eig0=mp.eigsy(A0,eigvals_only=True)
    eig1=mp.eigsy(N,eigvals_only=True)
    out['diagnostic'][str(dps)]={
      'm':2,'L':str(L),'gamma':str(om),'eta':'0.25','real_nodes':list(map(str,nodes)),
      'W0_constant':str(A0[0,0]),'negative_upper_target':str(-L/1024),
      'raw_eigenvalues_y0':list(map(str,eig0)),
      'y_positive':str(yy),'whitened_eigenvalues_at_y':list(map(str,eig1)),
      'analytic_whitened_error_bound':str(2*uu*mp.exp(-gap*yy)),
      'claim':'finite spectral model, NOT actual zeta/DH heat matrices'}
    assert A0[0,0] < -L/1024
    assert min(eig1)>mp.mpf('0.5')
    print('PASS DIAG heat dps',dps, 'constant',mp.nstr(A0[0,0],15),'y=',mp.nstr(yy,8))
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print('PASS',len(out['exact']),'exact control groups')

Appendix B. Executed output

{
  "exact": [
    "H3 det = quiet - t^2",
    "H10 full annihilation of Q",
    "H10 det = e^2(e^2-t)",
    "H8 endpoint 2 without sign at 1",
    "exact affine matrix Schur identity",
    "constant-floor convex identity",
    "H5 imaginary shift Taylor",
    "H7 quartet derivative sign",
    "single-quartet normalized determinant -1",
    "heat constant-test upper rational gap",
    "heat exponent gap lower",
    "heat quartet rational amplitude lower",
    "minimum of two roots counterexample"
  ],
  "diagnostic": {
    "50": {
      "m": 2,
      "L": "0.69314718055994530941723212145817656807550013436025",
      "gamma": "9.0647202836543876192553658914333336203437229354476",
      "eta": "0.25",
      "real_nodes": [
        "9.0490952836543876192553658914333336203437229354476",
        "9.0334702836543876192553658914333336203437229354476",
        "9.0178452836543876192553658914333336203437229354476"
      ],
      "W0_constant": "-0.0020511914057314489598006739250220176701610551807965",
      "negative_upper_target": "-0.00067690154351557159122776574361150055476123059996119",
      "raw_eigenvalues_y0": [
        "-0.0025445500927317556747256820021778235065653819633412",
        "0.0000013047239007384871704845048236205978617496769280111",
        "3.4622392181514665404207440531810990311014193287335"
      ],
      "y_positive": "62.737076401875930981770294050757468758584125980048",
      "whitened_eigenvalues_at_y": [
        "0.97971515688339207141842642692363954830370406073326",
        "1.0",
        "1.0000000000171285518541000376494481330318507262447"
      ],
      "analytic_whitened_error_bound": "0.20052372112983408000005034585119198593011496486042",
      "claim": "finite spectral model, NOT actual zeta/DH heat matrices"
    },
    "80": {
      "m": 2,
      "L": "0.69314718055994530941723212145817656807550013436025525412068000949339362196969472",
      "gamma": "9.0647202836543876192553658914333336203437229354475911683720330958812019074426102",
      "eta": "0.25",
      "real_nodes": [
        "9.0490952836543876192553658914333336203437229354475911683720330958812019074426102",
        "9.0334702836543876192553658914333336203437229354475911683720330958812019074426102",
        "9.0178452836543876192553658914333336203437229354475911683720330958812019074426102"
      ],
      "W0_constant": "-0.0020511914057314489598006739250220176701610551807965371688607301187510570853036591",
      "negative_upper_target": "-0.00067690154351557159122776574361150055476123059996118677160222657177089220895478",
      "raw_eigenvalues_y0": [
        "-0.0025445500927317556747256820021778235065653819633414387953265733633839372877428292",
        "0.0000013047239007384871704845048236205978617496769264953457482573616396123593668076045",
        "3.4622392181514665404207440531810990311014193287351795753131868103259640001225392"
      ],
      "y_positive": "62.737076401875930981770294050757468758584125980037011776762307047913471628498702",
      "whitened_eigenvalues_at_y": [
        "0.97971515688339207141842642692363954830370406073458196863278791319783953168184133",
        "1.0",
        "1.0000000000171285518541000376494481330318507262446711645033134171778453321083136"
      ],
      "analytic_whitened_error_bound": "0.20052372112983408000005034585119198593011496486041633562419754307770434893717353",
      "claim": "finite spectral model, NOT actual zeta/DH heat matrices"
    }
  }
}