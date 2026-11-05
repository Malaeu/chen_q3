# STATUS: TRY_ROUND4_DAMPING_TRANSPORT

```yaml
OPERATIVE_CLASS: TRY_ROUND4_DAMPING_TRANSPORT
DATE: 2026-11-05
ANSWER: B_FINITE_OPTIMAL_TRANSPORT_WITH_UNPAID_COFINAL_LOSS
REQUEST_COMMIT: 452a2bf0ebcf932e9fd146119f118fca0592095b
REQUEST_BLOB: 998b8e10544eb2a7a96e5d912449608857588c12
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
SPEC_FREEZE_COMMIT: 05e9008518f3a2d8adfb5d901725080e9962cf81
SPEC_FREEZE_BLOB: b3f0097b4aeea8ff62fd8e233c2803610c258c82
SPEC_BLOCK_SHA256: f592fe5e94766a6c7f32235cf7f4484d1d10bb3f5dbf04978d26db6640b0e2a6
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND4_DAMPING_TRANSPORT_2026-11-05.md
OBSERVED_INBOX_HEAD_BEFORE_FREEZE: 7a1d9a53e9972a0339369fe7b866d89e36cabe38
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
RH_PROVED: false
CORE_IS_RH_EQUIVALENT: true
PROVED_STEPS:
  - {id: LITERAL_ANALYTIC_DAMPING_PATH_AND_POSITIVE_TERMINAL, scope: FINITE_CELL, verifier: PAPER}
  - {id: EXACT_MINIMUM_UNITARY_TRANSPORT_LOSS_WITHOUT_GAPS, scope: ABSTRACT, verifier: PAPER}
  - {id: JOINT_POLE_PRIME_FLUX_AND_UNIFORM_NINE_OVER_TWENTY_FIVE_BUDGET, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: RH_IMPLIES_ACTION_AT_MOST_14_SIGMA_LOG_m_SQUARED, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: CURVE_CONTROL_ACTION_AT_MOST_TWO_LOG_m, scope: COFINAL_FAMILY, verifier: PAPER}
RH_GAP: "An unconditional polylogarithmic bound for the integrated maximal positive eigenvalue velocity of H_m(delta); only a growing absolute PNT bound is proved."
MINIMAL_MISSING_IDENTITY: "exists C,r,M: integral_0^(1/2) max(0,max_i lambda_mi'(delta)) ddelta <= C(1+log m)^r for every integer m>=M"
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: FINITE_OPTIMAL_TRANSPORT_AND_COUPLED_REMAINDER_NOT_GLOBAL_RH_SIGN
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: [FINITE_DAMPING_TRANSPORT_CONSTRUCTION, OPTIMAL_LOSS_FORMULA, NONARITHMETIC_FLUX_BUDGET]
OPENS: []
ROUTE_SCORE: 3
VERIFIER: PAPER
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
NUMERICAL_TESTS: NOT_RUN
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
ROUTE: CHALLENGER_NOT_RH
ROUTE_STATE_CHANGED: false
```

Ы. **Исход (b).** Построен точный квадратный перенос полного демпфированного источника и доказана его минимальная цена. Неполученный шаг — полилогарифмическая оценка этой цены для всех поздних окон. Положительный конец известен без RH; арифметическая отмена главной массы доказана; общий знаковый ресурс не оплачен. RH не объявляется.

<!-- FROZEN_SPEC_BEGIN -->
## 1. Спецификация S — фиксируется до построения

[FINITE_CELL / COFINAL_FAMILY | CONDITIONAL: существование со всеми свойствами не предполагается.]

Пусть m>=3, L=log m, V_m — буквальное чётное косинусное пространство с N=m, f=mathcal S_m z, нулевое продолжение за I_L=(-L/2,L/2). G_m=I+diag((2*pi*j/L)^2). Положим N_f=||f||_2^2, Q_f(u)=2 Re integral conjugate(f(x))f(x+u)dx; Q_f(u)=0 при u>=L. Сохраняются j(u)=exp(-u/2)/(1-exp(-2u)) и c_*=EulerGamma+log(8*pi)+pi/2.

Для 0<=delta<=1/2 определим ИЗ ПОЛНОГО ИСТОЧНИКА эрмитову A_m(delta):

    z* A_m(delta) z =
      integral_0^infinity j(u)[2 N_f-exp(-delta*u)Q_f(u)]du-c_* N_f
      + integral_0^L 2 cosh(u/2)exp(-delta*u)Q_f(u)du
      - sum_(2<=n<m) Lambda(n)n^(-1/2-delta)Q_f(log n).

Это демпфирование полной корреляции; Gamma, оба полюса и все простые степени сохраняются. При delta=0 получаем ровно A_m. В частности, это тот же A_m из полюсно-перенормированного тождества Round 3 (8d548cb18e312ae16a087542b1eedba6c00675ea, §3.1), а не другая матрица. Введём H_m(delta)=G_m^(-1/2) A_m(delta) G_m^(-1/2).

Искомый объект X состоит для каждого m из линейного T_m в некоторое положительное гильбертово пространство, абсолютно непрерывной унитарной матрицы V_m(delta), измеримой матрицы R_m(delta) и неотрицательной eta_m in L1([0,1/2]). Буква V_m(delta) здесь означает перенос, а V_m без аргумента выше — физическое пространство.

**S1 — положительный конец и нормировка.**

    H_m(1/2)=T_m* T_m,
    V_m(0)=I,  V_m(delta)*V_m(delta)=I.

T_m должен быть задан с доказанной положительной метрикой, а не корнем из неизвестно положительной H_m(0). Обозначим Omega_m=V_m' V_m*, так что Omega_m*=-Omega_m почти всюду.

**S2 — точное уравнение квадратного переноса.** Почти всюду по delta:

    H_m'(delta)+[H_m(delta),Omega_m(delta)]
         =eta_m(delta) I-R_m(delta)*R_m(delta).

R_m имеет интегрируемый квадрат нормы при каждом фиксированном m. Коммутатор [A,B]=AB-BA. Это равенство подписанных матриц, не положительность исходной H_m(delta).

**S3 — цена переноса.** Существуют одна C<infinity, одно целое r>=0 и M, такие, что

    integral_0^(1/2) eta_m(delta) ddelta <= C(1+log m)^r
       для каждого целого m>=M.

Одна C,r работает для всех поздних окон. Никакая равномерная оценка спектральных зазоров H_m(delta) не предполагается. В построении нельзя использовать RH, старые dagger/SD/Gaussian-бюджеты или знак H_m(0) как посылки.

**Достаточность.** Из S2 и V_m'=Omega_m V_m:

    H_m(0)=V_m(1/2)*T_m*T_m V_m(1/2)
       +integral_0^(1/2) (R_m V_m)*(R_m V_m) ddelta
       -(integral_0^(1/2) eta_m ddelta) I.

По S3 это даёт A_m>=-C(1+log m)^r G_m. Применение к фиксированному moving-Gaussian направлению из 62f782316d2ba4f83d27db82d0b64e1e8361cad2, blob 2b5e02a0aa816da34c204f2a56a9033e6ac6b542, §6, исключает положительный показатель Theta/2. Следовательно X с S => RH. Это доказательство импликации, не её предпосылки.

**Самостоятельность требований.** S2 задаёт квадратный перенос вдоль всего конкретного демпфированного источника, а S3 ограничивает накопленную потерю. Нижняя граница одной конечной матрицы не обеспечивает такой контроль движения между концами. Обратная импликация для настоящей zeta не предполагается и будет классифицирована отдельно. Проверка предъявленного X состоит из матричных тождеств, положительной терминальной метрики и интегрального бюджета.

**Границы прежних kills.** Нет положительного order-envelope для -K_m; нет глобального signed-current представления неперенормированной фазы; нет скалярного Euler-Mobius квадрата; нет утверждения о переносе равномерного бюджета на DMV; нет статической endpoint-склейки. Сентябрьские запреты положительных минорант не применяются без дополнительного аргумента: в точной формуле остаётся отрицательный скалярный ресурс, и терминальный квадрат унитарно переносится. Ни R>=0 для прежнего недемпфированного остатка, ни «бесплатное снятие демпфирования» не предполагаются.
<!-- FROZEN_SPEC_END -->

## 2. Предрегистрация

P1: исходная A_m(delta) должна быть вещественно-аналитической эрмитовой семьёй при каждом m; конечный перенос S1-S2 следует строить без предположения знака A_m(0).
P2: цена S3 НЕ предсказывается как малая; большой upper bound не будет назван опровержением малого бюджета.
P3: необходим отдельный контроль направления переноса: положительный квадрат в производной не разрешает автоматически двигаться от delta=1/2 к delta=0.
P4: численных экспериментов нет. При использовании pi-резонанса сначала исправляется и проверяется точное арифметическое условие, а не приближённое совпадение десятичных чисел.

Этот блок S не редактируется после начала построения. Итог дополнит файл доказательствами, источниками, цепочкой, false-world проверками и честным статусом оставшегося бюджета.

## 3. Источники, импорт и результат проверки счётчика

[ABSTRACT / FINITE_CELL | PAPER; наследование не означает нового независимого аудита.]

Бриф прочитан полностью по request pin из YAML; blob совпал. Протокол v3 получен через GitHub. Прочитаны также следующие конкретные материалы, а не задания из очереди.

| ID | Путь / pin / blob | Что используется |
|---|---|---|
| R3 | `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND3_POLE_RENORMALIZED_LIFT_2026-11-05.md`; `535d2c272bed0a0331359a9d6a7ade1362976168`; `8d548cb18e312ae16a087542b1eedba6c00675ea` | Полный источник, полюсная перенормировка, открытый бюджет Delta. |
| RG | `docs/routeB_bus/proshka/PROSHKA_VERDICT_PROVE_RH_2026-11-05.md`; `62f782316d2ba4f83d27db82d0b64e1e8361cad2`; `2b5e02a0aa816da34c204f2a56a9033e6ac6b542` | §6, Gaussian-return и показатель Theta/2; §8, собственные false-world источники. Это inherited PAPER, не новый zero theorem. |
| RP | `docs/Codex/REPORT_2026-09-17_SCATTERING_POISSON_FULL_FUNCTIONAL.md`; база запроса; `a6d21aa42faae590a2317587bfc142a076d2a6dc` | P1–P5: полная демпфированная форма и положительный конец; P7: остаток обоих знаков. Этот явно указанный брифом файл вне routeB прочитан, но не изменялся. |
| RA | `docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_ROUND3_ADDENDUM_SEPT_SIGN_2026-11-05.md`; `404f5710cc4186f94b41a58da173787c0b8b2270`; `d70d373e37b6183903a0ae321312ddf36ce61aaf` | Идеи и список исключённых классов; не sign supplier. |
| RI | `docs/routeB_bus/mythos/DIGEST_GOAL058_SEPT_2026/INDEX.md`; `c603afe90d04317ba1eff828b89b30c49566bd8a`; `5d4541dfe0863aef31aef5bb0355b5101aeba74d` | Границы сентябрьских запретов; digest, не замена доказательству. |
| RN | `docs/routeB_bus/NB_BD_LIFT_2026-11-05.md`; `a40be756`; `40ddadc20cfbd6f2d8104c9a16b1222882f1a6ad` | NB–BD вне старого скалярного квадрата; target capture и decay не доказаны. |
| RE | `docs/routeB_bus/proshka/ENTROPY_NOESCAPE_FIRST_PASS_2026-10-30.md`; база запроса; `a29cc023db1a1d79a5cbb774b5575661eff5d3dd` | Anchored entropy условно достаточна; source-bound отсутствует; sharp LSI позднее опровергнута. |

**THEOREM T1 (Rellich).** G. Barbarino–V. Noferini, arXiv:2211.15539v1, Theorem 1.1, p.1: вещественно-аналитическая эрмитова матрица на открытом вещественном интервале имеет аналитические вещественные eigenbranches и аналитическую унитарную диагонализацию. Теорема и страница проверены; разрывы спектрального зазора не исключаются.

**THEOREM T2 (PNT).** Johnston–Yang, arXiv:2204.01980v2, abstract: количественная безусловная оценка psi(x)-x. Используется только её слабое следствие: существует H>=1 с |psi(x)-x|<=H x/(1+log x)^4 для всех x>=1. H увеличивается на конечном начальном отрезке; численные оптимальные константы не нужны.

**THEOREM T3 (счётчик / Selberg).** M. A. Korolev, *On multiple zeros of the Riemann zeta function*, Izvestiya Math.70:3 (2006), pp.427,431–432: Definition 1, Definition 4, Lemma 4. Прочитаны формулы; screenshot этой PDF-страницы не получен из-за cache miss, визуальная проверка не заявляется.

**THEOREM T4 (Lagarias).** *On a positivity property of the Riemann xi-function*, Acta Arith.89 (1999), p.217, (1.4)–(1.5), Theorem 1.1: RH эквивалентна Re(xi'/xi)>0 на Re s>1/2. Прочитана также Correction, Acta Arith.116 (2005), pp.293–294: исправлены Lemma 3.1 и знак в (3.8). Повреждённая лемма здесь не используется. Обе первые страницы проверены визуально.

**THEOREM T5 (heat-flow scope).** Rodgers–Tao, arXiv:1801.05914v5, abstract: Newman constant >=0, тогда как RH требует <=0. Это не верхняя граница для нашей потери.

```text
T1 https://arxiv.org/pdf/2211.15539
T2 https://arxiv.org/abs/2204.01980v2
T3 https://www.mathnet.ru/php/getFT.phtml?jrnid=im&option_lang=rus&paperid=723&what=fullteng
T4 https://matwbn.icm.edu.pl/ksiazki/aa/aa89/aa8932.pdf
   https://www.impan.pl/shop/en/publication/transaction/download/product/81942
T5 https://arxiv.org/abs/1801.05914v5
```

### 3.1. F_m — не буквальный счётчик

Пусть theta(0)=0 — непрерывная Riemann–Siegel theta, так что theta'=q/2. Для t>0 вне ординат нулей точные равенства дают

    F_m(t)=theta(t)/pi+(C_L(t)-P_m(t))/pi,
    N(t)=theta(t)/pi+1+S(t),
    F_m(t)-(N(t)-1/2)=(C_L(t)-P_m(t))/pi-S(t)-1/2.       (3.1)

Здесь C_L=integral_0^L exp(u/2)sin(tu)/u du,
P_m=sum_(p<m,k>=1) p^(-k/2)sin(kt log p)/k. F_m гладка, N ступенчат. N считает все нетривиальные нули, не только критические; её монотонность не различает RH и not-RH. DIAG из брифа на t<=60 не ограничивает правую часть (3.1) на всей прямой.

T3 даёт безусловно S(t)=O(log t), а при RH — O(log t/log log t). Оба утверждения относятся к t, не к log m. Selberg-формула T3 использует сглаженные Lambda_z(n) до z^3 и сдвиг

    sigma_(z,t)=1/2+2 max(1/log z, |beta-1/2|),

где beta пробегает нули с |t-gamma|<=z^(3|beta-1/2|)/log z. При e^16<z<=t^2 остаток ограничен 15(sigma_(z,t)-1/2)(|sum Lambda_z(n)n^(-sigma_(z,t)-it)|+log|t|). Под RH сдвиг равен 1/2+2/log z; без RH это не разрешённая замена. И сдвиг, и taper отличаются от нашего жёсткого p<m и sigma=1/2. Неоплаченный переход между этими объектами не исчезает из-за совпадения Gamma. Поэтому T3 не доказывает бюджет Delta из Round 3.

### 3.2. Что значит двигать sigma

При delta=1/2 RP даёт настоящий положительный полный источник. Вне полуплоскости справа от всех нулей нельзя автоматически продолжать его Poisson-разложение как положительную плотность: при пересечении нулей появляются полюса и меняется допустимость Fourier-представления. T4 ровно фиксирует цену глобального переноса до 1/2.

Конечная A_m(delta), напротив, определена при всех delta и аналитична без zero-free предпосылки. Это позволяет исследовать физическую матрицу вместо предположения о положительной бесконечной плотности. Неравенство e^(-c)<=e^(-delta u)<=1 при delta=c/L само по себе не контролирует подписанную форму. RP P7 уже запрещает бесплатное снятие демпфирования.

## 4. Конечный объект: положительный конец и аналитичность

[FINITE_CELL | PAPER; RP supplies the positive source, T1 will supply the frame.]

Для каждого фиксированного m разность A_m(delta)-A_m(0) — целая по delta матрица: Q_f имеет носитель [0,L], а (e^(-delta u)-1)j(u) локально ограничено у нуля. Все производные положительного порядка содержат u^k j(u) и интегрируемы. Исходный Gamma-integral конечен, поскольку Q_f(u)=2N_f+O_f(u). Endpoint n=m в prime-сумме даёт нуль, не пропущенный атом. Для вещественного delta матрица эрмитова.

RP доказывает без RH

    P_1(t)=2 Re xi'(1+it)/xi(1+it)
          =2 sum_rho (1-beta)/((1-beta)^2+(t-gamma)^2)>0,
    A_m(1/2)[z]=(1/(2*pi)) integral P_1(t)|fhat(t)|^2 dt. (4.1)

Полюса 0,1, Gamma-константа и cusp e^(-|u|/2) здесь оплачены RP P4–P5. Это не positivity исходного A_m(0).

**Продолжение на буквальные косинусы.** Их нулевое продолжение имеет ограниченную вариацию; fhat=O_f((1+|t|)^(-1)). При a=1-beta in (0,1) прямое Poisson-интегрирование даёт

    integral [2a/((t-gamma)^2+a^2)]/(1+t^2) dt
          =2*pi*(1+a)/((1+a)^2+gamma^2)
          <=4*pi/(1+gamma^2).

Сумма последних весов конечна по обычной оценке числа нулей O(T log(T+2)). Поэтому (4.1) конечна. Mollification с равномерным BV-контролем возвращает конечную prime-сумму, полюса и сгруппированный Gamma-интеграл; у автокорреляции и её демпфированной версии вторая производная — конечная мера. Нулевое продолжение f не объявляется глобально H1.

Для y в graph-координатах определим

    (T_m y)(t)=sqrt(P_1(t)/(2*pi))
                  Fourier[mathcal S_m G_m^(-1/2)y](t).  (4.2)

Тогда T_m отображает в обычное положительное L2(dt) и H_m(1/2)=T_m*T_m. Это источник-определённый терминальный квадрат, не корень из неизвестно положительного A_m(0). S1 в части терминальной метрики построено.

## 5. Точная минимальная цена унитарного переноса

[ABSTRACT / FINITE_CELL | PAPER; THEOREM T1 is the only non-elementary finite-m input.]

### Теорема 1 — оптимальный квадратный перенос

Пусть H(delta) — любая аналитическая эрмитова n-by-n семья в окрестности [0,T]. Выберем её аналитические eigenbranches lambda_i(delta) по T1 и положим

    eta_*(delta)=max(0,max_i lambda_i'(delta)),
    L(H)=integral_0^T eta_*(delta) ddelta.              (5.1)

Тогда L(H) — точный минимум integral eta по всем AC-unitary V(0)=I, Omega=V'V*, eta>=0 и R с

    H'+[H,Omega]=eta I-R*R.                            (5.2)

Минимум достигается. Он не зависит от маркировки аналитических ветвей. Spectral gaps могут обращаться в нуль.

**Построение.** Пусть H=O Lambda O*, O аналитична и унитарна. Зададим

    Omega=O'O*, V(delta)=O(delta)O(0)*,
    R=O diag(sqrt(eta_*-lambda_i')) O*.                 (5.3)

Тогда Omega*=-Omega, V'=Omega V, V(0)=I и

    H'+[H,Omega]=O Lambda' O*=eta_* I-R*R.

Неотрицательность подкоренных чисел следует из определения eta_*, а не из знака H. Все функции непрерывны на компактном отрезке, R имеет конечный интеграл квадрата нормы. Таким образом S2 и оставшаяся часть S1 построены для каждого m.

**Минимальность.** Для любого собственного значения lambda матрицы H в данной точке обозначим его полный проектор P_lambda. Для всякой Omega

    P_lambda[H,Omega]P_lambda=0.

Из (5.2) следует eta>=lambda_max(P_lambda H' P_lambda). В Rellich-frame спектр этой компрессии состоит из lambda_i' для ветвей, сходящихся в lambda: компонента O*O' исчезает внутри равного eigenvalue-блока. Поэтому eta>=eta_* почти всюду. Интегрируем и сравниваем с (5.3). Это доказывает теорему, включая crossings. □

Для буквального пути пишем L_m=L(H_m) при T=1/2. Истинная минимальная цена не равна integral ||H_m'|| вообще; последняя лишь верхняя граница. Не требуется оценивать делители 1/(lambda_i-lambda_j). Формула на простом спектре Omega_ij=H'_ij/(lambda_j-lambda_i) только объясняет, какие смешанные члены удаляются; она не применяется в точках кратности.

### 5.1. Квадратная монотонность действительно существует — но за цену

Построенный объект даёт

    H_m(0)=V_T*H_m(T)V_T
       +integral_0^T (R_m V_m)*(R_m V_m) ddelta-L_m I,
    A_m >= -L_m G_m.                                  (5.4)

Функционал W_m(delta)=V_m*H_m(delta)V_m-(integral_0^delta eta_*)I имеет производную -(R_mV_m)*(R_mV_m)<=0. Здесь настоящее равенство с квадратом, но вычитаемый скаляр нельзя удалить. Такая монотонность строится для любой аналитической эрмитовой семьи; арифметический знак находится в оценке L_m.

**Контроль чрезмерности.** H(delta)=(1+M sin^2(2*pi*delta))I на [0,1/2] положительна на всём пути, оба конца равны I, но L(H)=M. Значит один положительный конец или даже positivity всего абстрактного пути не обеспечивает малую суммарную цену. Это не отрицательный пример для настоящей zeta; это точная граница общего метода.

## 6. Полная арифметическая производная и оплаченный остаток

[FINITE_CELL / COFINAL_FAMILY | PAPER; no RH used.]

Для f=mathcal S_m z, Q=Q_f, N=||f||^2, D=||f'_int||^2 дифференцирование полного источника даёт

    A_m'(delta)[z]=
      integral_0^L u e^(-delta*u)[j(u)-2cosh(u/2)]Q(u)du
      +sum_(n<m) Lambda(n)(log n)n^(-1/2-delta)Q(log n). (6.1)

Это НЕ дифференцирование одной prime-части. Положим

    psi(x)=sum_(n<=x) Lambda(n), E_psi(x)=psi(x)-x,
    D_psi(u)=e^(-u/2)E_psi(e^u).

Вес v(x)=(log x)x^(-1/2-delta)Q(log x) равен нулю и при x=1, и при x=m. Поэтому интегрирование по dpsi=dx+dE_psi не оставляет начальной или конечной платы. Континуум dx точно отменяет растущую половину полюса. В результате

    A_m'(delta)[z]=C_delta[f]+E_delta[f],               (6.2)

    C_delta[f]=integral_0^L
      u e^(-delta*u) e^(-5u/2)/(1-e^(-2u)) Q(u)du,

    E_delta[f]=-integral_0^L e^(-delta*u)D_psi(u)
       {[1-(1/2+delta)u]Q(u)+u Q'(u)}du.                (6.3)

Все простые степени остались в psi. Если m — prime power, Q(L)=0 учитывает endpoint точно. В Q' край не зануляется:

    Q'(u)=2 Re integral_(-L/2)^(L/2-u) conjugate(f(x))f'(x+u)dx
          -2 Re[conjugate(f(L/2-u))f(L/2)].             (6.4)

### Теорема 2 — равномерный неарифметический бюджет

Для любого m>=3, delta in [0,1/2], z:

    |C_delta[f]| <= (18/25)||f||^2,
    integral_0^(1/2)|C_delta[f]| ddelta <= (9/25)||f||^2. (6.5)

Действительно, |Q|<=2N и

    integral_0^infinity u e^(-5u/2)/(1-e^(-2u))du
       =sum_(r>=1)(2r+1/2)^(-2)
       <=1/(5/2)^2+integral_1^infinity(2x+1/2)^(-2)dx
       =4/25+1/5=9/25.

Это независимая от окна оценка целого совместного Gamma/pole/continuous-prime остатка. Она не утверждает знак C_delta и не оценивает E_delta. □

### 6.1. Реально полученная безусловная цена

Имеем ||f||_infinity^2<=N/L+2sqrt(ND), откуда |Q'|<=5(N+D) при L>=1. Поэтому модуль фигурной скобки в (6.3) не больше 7(1+u)(N+D).

По T2 с одной конечной H:

    ||H_m'(delta)|| <=18/25+
       7H integral_0^L e^((1/2-delta)u)/(1+u)^3 du.

Следовательно

    L_m <=9/25+
      7H integral_0^L (e^(u/2)-1)/[u(1+u)^3]du
      =O_H(sqrt(m)/(log m)^4).                         (6.6)

Интегранд у нуля продолжается значением 1/2. Интеграл асимптотически равен 2e^(L/2)/[L(1+L)^3]. Это верхняя оценка, не отрицательный свидетель и не полилогарифмическая граница. Она повторно выявляет предел абсолютной PNT-оплаты; улучшением RH-показателя она не является.

## 7. Точная логическая сила frozen S: обратная стрелка

[COFINAL_FAMILY | PAPER для импликации RH=>S; CONDITIONAL, а не безусловный bound.]

Необходимо прямо определить, не спрятана ли RH в новом ресурсе. Здесь можно доказать обратную импликацию: при RH цена L_m имеет полилогарифмический бюджет. Это только классификация, не посылка прямого доказательства.

Пусть RH верна, Sigma_0=sum_rho(1+gamma_rho^2)^(-1)<infinity с кратностями. Для k_f(u)=integral conjugate(f(x))f(x+u)dx полная явная формула и сохранённый cusp дают

    A_m(delta)[z]=sum_rho integral e^(-delta|u|)k_f(u)e^(i gamma_rho u)du,
    A_m'(delta)[z]=-sum_rho Fourier[r_delta](gamma_rho),
    r_delta(u)=|u|e^(-delta|u|)k_f(u).                   (7.1)

Выбор знака Fourier в последней строке несущественен после полной симметричной суммы. Нули здесь действительны ТОЛЬКО ПО ПРЕДПОСЫЛКЕ RH. Далее — явное обоснование дифференцирования и бюджета, включая края.

Положим E=N+D. Для L>=1 нулевое продолжение f имеет

    ||f||_1<=sqrt(L E),
    ||Df||_TV<=sqrt(LD)+2sqrt(2E)<4sqrt(L E).

Здесь Df — распределительная производная с двумя endpoint-атомами. Свёртка даёт

    ||k_f||_1<=LE, ||k_f'||_1<=4LE, ||k_f''||_TV<=16LE.

Для a_delta(u)=|u|e^(-delta|u|) на носителе k: |a_delta|<=L, |a_delta'|<=1, а a_delta''=2delta_0 плюс функция модуля <=1 при 0<=delta<=1/2. Следовательно

    ||r_delta||_1<=L^2 E,
    ||r_delta''||_TV<=16L^2E+9LE+2E<=27L^2E,
    |Fourier[r_delta](gamma)|<=28L^2E/(1+gamma^2).       (7.2)

Последняя оценка получается из L1 и двух распределительных интегрирований по частям. Она равномерна по delta и суммируется по нулям, поэтому (7.1) законна, в том числе в delta=0 как односторонняя производная. Сглаживание сохраняет те же BV-оценки; support и endpoint не теряются.

Из (7.2):

    RH => ||H_m'(delta)||<=28 Sigma_0 L^2
       => L_m<=14 Sigma_0 L^2.                         (7.3)

Таким образом для настоящей zeta

    RH <=> frozen S exists
       <=> exists C,r,M: L_m<=C(1+log m)^r for all m>=M. (7.4)

Да, ядро опять RH-эквивалентно. Ни (7.3), ни (7.4) не улучшают расположение нулей. Новые независимые результаты этой работы — оптимальность (5.1)–(5.3), точное source-coupled (6.2) и равномерный бюджет (6.5). Сама эквивалентность НЕ засчитывается как продвижение по знаку.

## 8. Цепочка вниз и точная остановка

[COFINAL_FAMILY | PAPER for arrows; CONDITIONAL for existence of the uniform budget.]

Для собственного источника каждого мира формулируем N2 с терминальным условием явно; у настоящей zeta оно уже THEOREM (4.1).

| Узел | Утверждение | Доказательство стрелки | Актив | Статус для Q | Отношение к RH |
|---|---|---|---|---|---|
| N1 | Объект X со всей frozen S существует | N1=>RH: точное интегрирование S2, затем Gaussian exponent | RP + RG, (5.4) | CONDITIONAL | Эквивалентно RH по §7 |
| N2 | H_m(1/2)>=0 для всех m и L_m<=C(1+log m)^r для всех поздних m | N2=>N1: (4.2), Rellich-построение (5.3); обратное по минимальности | THEOREM T1, новые §§4–5 | CONDITIONAL; terminal часть THEOREM | Эквивалентно RH для Q |

Нельзя дописать в таблицу «N3: PNT», будто (6.6)=>N2. Такой стрелки нет. Доказанные S1–S2 при каждом finite m не являются существованием объекта со ВСЕЙ S.

**Минимальная недоказанная строка:**

    exists C<infinity, integer r>=0, M:
      integral_0^(1/2) max(0,max_i lambda_(m,i)'(delta)) ddelta
                 <=C(1+log m)^r for every integer m>=M. (GAP)

Равносильный источник для производной дан в (6.2)–(6.4): нужна совместная односторонняя оценка остатка E_delta на движущихся собственных подпространствах, после точного удаления коммутаторной части. Ни положительный terminal, ни обычная PNT, ни Selberg-формула для другого cutoff, ни существование квадратов не дают GAP.

Это исход (b). Конструкция не объявлена невозможной: нет отрицательного верхнего свидетеля против GAP для настоящей zeta. При RH она действительно имеет бюджет (7.3). В то же время доказательство GAP из арифметики Q здесь отсутствует.

## 9. Каждый узел в ложных мирах и на кривой

[ABSTRACT / COFINAL_FAMILY | PAPER with inherited RG/RP inputs; no numerical test.]

**DMV.** Берётся полная оконная форма RJ/RG: generalized-prime atoms плюс явно указанные zeta-Gamma и pole, без придуманного functional equation. Путь полного корреляционного демпфирования существует. Если N2 верен, (5.4) даёт запрещённый полилогарифмический lower floor её Gaussian-направлениям; правый Laplace-полюс RG §8.1 даёт отрицательные степенные осцилляции. Поэтому N2, затем N1 ложны. Положительность terminal для DMV из одного расположения его нулей не импортируется: нет нужного completion/source dictionary. Точное исключающее условие — одновременное terminal positivity и малый action. Если terminal проходит, action обязан провалиться на отрицательной Gaussian-подпоследовательности.

**DH.** Используются все b_D(n), включая b_D(6), собственная odd-Gamma, conductor 5, отсутствие pole. Неправильный Euler product не вводится. N1/N2 уже исключаются Gaussian-response RG §8.2 и (5.4). Более точно, известный DH-нуль beta>1 также препятствует всем поздним положительным terminal-окнам при delta=1/2: Laplace-отклик демпфированного источника содержит F_g(u)^2 D'/D(1+u), поэтому имеет правый полюс u=rho-1 с ненулевым вычетом. Gamma и Gaussian correction аналитичны там; вещественных нулей D(s) при s>0 нет. Тот же Landau-аргумент и две разнесённые копии профиля дают отрицательный компактный тест terminal-формы, затем его буквальный возврат. Здесь изменён источник и line-shift, не знак доказательства. Следовательно N2 fails уже в terminal condition, N1 — в S1.

**Квартет a=1/3, gamma=7.** К полной форме прибавляется настоящий quartet kernel, и демпфируется также он. Нули completion остаются внутри 0<beta<1, поэтому собственный terminal positive; polynomial factor не удаляется. Но RG §8.3 даёт liminf q_m/m^b=-infinity для 0<=b<1/6. Из (5.4) L_m>=-q_m при graph-unit Gaussian vector. Поэтому action не имеет polylog budget; N2 и S3 в N1 ложны. Это отрицательный судья непосредственно цены, не только source mismatch.

**Кривая E/F3.** Пусть h=log 3, gamma_n=(pi/2+pi*n)/h, M_m=ceil(L/(2h))-1. Её собственная конечная damped-форма на том же физическом окне имеет вид

    A_m^E(delta)=2h I+2h sum_(k=1)^M_m (-1)^k e^(-2hk delta) R_(2hk),
    H_m^E=G_m^(-1/2)A_m^E G_m^(-1/2).                 (9.1)

Нулевые перекрытия при 2hk>=L точны. При delta>0 полная Fourier-серия — периодическое Poisson-сглаживание положительной spectral comb sum_n delta_(gamma_n), поэтому её terminal PSD. При delta=0 форма равна sum_n |fhat(gamma_n)|^2. Используется свой источник, не zeta-Gamma.

Так как ||R_s||<=2 и ||G_m^(-1/2)||<=1,

    integral_0^(1/2)||(H_m^E)'|| ddelta
       <=4h sum_(k=1)^M_m(1-e^(-hk))<=4hM_m<=2L.      (9.2)

Можно выбрать V=I, eta=||(H_m^E)'|| и R=(eta I-(H_m^E)')^(1/2); корень заведомо PSD по определению eta. Terminal T берётся из положительной Poisson-плотности. Значит N2[E] и N1[E] — THEOREM, с r=1 и C=2. Это тот же сертификат и то же направление переноса, не другая inner-модель вместо frozen S.

## 10. Границы каждого старого kill и доступной полки

[ABSTRACT | PAPER scope audit; no old kill is re-proved as a new result.]

**3d3ba2e6, positive operator envelope.** Здесь нет положительного оператора на вспомогательной частотной прямой с X+K>=0 и малой trace-ценой. S2 — динамика конечной физической матрицы; её квадрат и отрицательный scalar loss интегрируются вместе. Произвольные частотные masks для X не разрешаются, старый sqrt(m) witness не относится к этому объекту.

**e7be7f41, fixed-order current.** Не требуется представлять alpha_m как положительную меру плюс фиксированное число ограниченных частотных производных. Континуум полюса сохранён и в A_m, и в совместной отмене (6.2). Нелокальная матрица V(delta) не является таким током.

**8e584bb8, scalar-balanced Euler–Mobius square.** R_m из (5.3) не имеет вида Y^(1/2)(sqrt(t)Z-t^(-1/2)M*)S. Нет скалярного баланса t,d и нет обязанности старого остатка стать малым. Новая цена не выводится из обратимости Z.

**3f0d43a9, DMV-SD.** Мы не предполагаем одну цену для всех Euler products. §9 показывает нарушение полной спецификации у DMV. Его отрицательный контроль не является запретом той же цели для настоящих целых простых.

**d558268a, static gluing.** V(delta) — унитарный перенос матрицы в graph-координатах параметра delta. Это не boundary condition физического i*d/dx, не Floquet spectrum и не статическая склейка концов окна.

**NULLFIELD.** Нет утверждения о фиксированной положительной миноранте theta-формы на всём классе, сохраняющей массу на её радикале. В (5.4) остаётся оплачиваемая отрицательная константа; знак её цены не удаляется.

**RESOLVENTGRAM.** Не предполагается K_2=eta Gram+PSD для старого резольвентного ядра. Нормировка G — физическая reference-метрика, а не предполагаемо положительная Weil-Gram.

**POINCARECOMP.** Не импортируется M>=kappa D_X с универсальным положительным запасом. Теорема 1 вычисляет цену потери, а не производит coercivity из сравнения энергий.

**RAW_RESPONSE_FLOOR.** Терминальный квадрат — доказанный полный демпфированный функционал, не фиксированный квадрат сырого theta-отклика как миноранта недемпфированной формы. Его обратный перенос требует L_m.

**FINITE_PATH.** Простые не объявляются положительными ёмкостями. В (6.3) все их знаковые взаимодействия остаются в E_psi и Q,Q'; каждое слагаемое не получает отдельный благоприятный знак.

**SUPPORTSTABILITY absolute majorant.** Не строится абсолютная резольвентная страховка с бесконечной массой. Абсолютная оценка (6.6) дана лишь как недостаточный контроль; она не названа завершением sign-transfer.

**Энтропия / NOESCAPE.** RE уже показывает: anchored KL sufficient, но её uniform source-bound отсутствует; простые и Gamma в том jump-представлении имеют одинаковый dissipation sign. Никакой такой bound здесь не импортирован. Sharp LSI не воскрешена. Новая переменная delta не называется автоматически временем старого Markov flow.

**NB–BD.** RN честно оставляет target capture и decay. Эти L2-квадраты вне scalar-Mobius kill, но нового моста к GAP не предоставляют. Они не отброшены как невозможные и не подставлены как доказанный supplier.

**m-flow / heat flow.** Остаток 10/p старого one-prime increment контролирует другой Sonin-trace, оставляя signed first order. Без дополнительного сравнения это не bound для L_m. T5 доказывает Newman constant>=0, а не нужную <=0. Ни одно название потока не заменяет его оплаченный ресурс.

## 11. Pi-резонанс: исправление точного условия

[ABSTRACT | PAPER; элементарная арифметика.]

В прежнем разговорном self-prompt было неверное утверждение: exp(2*pi*i*j*log n/log m)=1 iff m divides n^j. Исправление:

    exp(2*pi*i*j*log n/log m)=1
        iff n^j=m^k для некоторого целого k>=0.         (11.1)

Для m>1, n>=1, j>=1 это следует из j log n/log m in Z и экспоненцирования. Делимость недостаточна: 12 divides 6^2, но 36 не равно 12^k ни при каком целом k. Для n=p prime условие (11.1) требует m=p^a и a divides j. Значит окно не имеет одновременного точного такого резонанса для p=2 и p=3.

2*pi здесь сокращается как период комплексной экспоненты. Калибровка log log m=pi не добавляет целочисленного равенства (11.1). Доказанной связи этого масштаба с GAP нет. Приближённые резонансы и точные мультипликативные связи не опровергнуты; но ни независимость фаз, ни их принудительная совместная отмена из (11.1) не следуют. Поэтому pi не используется как скрытая посылка текущего доказательства.

## 12. Сильнейшая атака, оставшиеся представления и closeout

[ABSTRACT / COFINAL_FAMILY | PAPER for the established statements, CONDITIONAL for GAP.]

Самая сильная претензия: Rellich-square всегда можно построить, так не была ли RH просто переименована? Ответ: существование конечного square-flow действительно общее и само по себе не доказывает RH. Поэтому результат не заканчивается этим равенством: доказана точная минимальность цены и source-specific отмена с бюджетом 9/25. Но эти результаты НЕ оплачивают GAP. Эквивалентность (7.4) и общий upper bound (6.6) не выдаются за новую арифметическую одностороннюю оценку.

Два оставшихся представления имеют разные издержки. Первое — pinched derivative из (5.1),(6.3): сохраняет собственные подпространства, но требует source-контроля движущихся направлений; аналитическая цена высокая, способность отсечь неправильный flow максимальна по теореме оптимальности. Второе — прямой совместный физический остаток без transport, либо прежний Delta с точной pole-ренормировкой: дешевле для алгебраической проверки, но uniform sign также не оплачен. Новый обязательный supplier сверх исходной цели не вводится.

**Дискриминатор цены:** для фиксированного кандидата C,r строгая нижняя граница L_m>C(1+log m)^r опровергнет именно его. Можно использовать положительный прирост одной аналитической eigenbranch на любом интервале: L_m>=lambda_i(b)-lambda_i(a). Конечное нарушение не опровергает существование других C,r. Все-m polylog существует iff RH для настоящего источника, поэтому независимый строгий cofinal kill означал бы гораздо больше, чем провал прибора. Численный прогон не назначен; сведения о цене здесь PAPER, не DIAG.

Предсказания: P1 подтверждено §§4–5. P2 не предсказывало малость; S3 остаётся OPEN, а не «опровергнута большой оценкой». P3 подтверждено точным знаком (5.4). P4 выполнено: вычислительных экспериментов нет; неверный divisibility-критерий исправлен без подгонки.

K8A:
- DOWNSTREAM_CONSUMER: исходный Gaussian exponent / RH для буквального A_m.
- ACTUAL_CONSUMER_REQUIREMENT: достаточен all-late subpolynomial graph-floor; polylog-action — данный способ его получить.
- ORIGINAL_REQUESTED_OBJECT: frozen X плюс source-correct chain; его полная S для Q RH-эквивалентна по §7.
- ORIGINAL_OBJECT_IS: PROVED_NECESSARY для RH в принятой PAPER-цепочке, а не в силу названия.
- KNOWN_WEAKER_INTERFACES: исходные dagger, SD при доказанном полном возврате или Gaussian one-sided bound; транспорт не обязателен как метод.
- FAILURE_TYPE: NO_DERIVATION — нет независимой source-оценки GAP.
- EPISTEMIC_STATUS: RESEARCH_DEBT, не MATHEMATICALLY_DEAD.
- NOVELTY_AXIS: finite-path optimality, exact coupled damping derivative and uniform nonarithmetic remainder; приоритет в литературе не заявляется.
- REOPEN_TRIGGER: source inequality paying GAP, либо конкретная ошибка в Rellich/pinching, cusp/BV bounds или Gaussian receiver.

```yaml
iteration:
  target: SOURCE_EXACT_DAMPING_DESCENT_FROM_POSITIVE_LINE
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: INTEGRATED_POSITIVE_EIGENVELOCITY_OF_LITERAL_DAMPED_PATH
  invariant_learned: ALL_PARTS_DAMPED_AND_ENDPOINTS_PRESERVED
  forbidden_future_move: CALL_GENERIC_SQUARE_FLOW_A_PROOF_OF_SMALL_LOSS
  next_decisive_test: SOURCE_BOUND_FOR_THE_SIGNED_PINCHED_ERROR_IN_6_3
  route_score: 3
```

## 13. Доставка и конечный вывод

Изменён только новый файл по WRITE_PATH; закрытые раунды и state-файлы не редактируются. Freeze commit 05e9008518f3a2d8adfb5d901725080e9962cf81, blob b3f0097b4aeea8ff62fd8e233c2803610c258c82. Блок S сохранён побайтово; SHA256 между маркерами: f592fe5e94766a6c7f32235cf7f4484d1d10bb3f5dbf04978d26db6640b0e2a6. Final commit и readback blob сообщаются в ответе после записи. Hash подтверждает доставку, не математическую правильность.

Уровень — PAPER. Нового независимого аудита, Lean и Arb нет; axiom profile NOT_APPLICABLE. Исход (b): конечный оптимальный перенос построен; граница полной цены не доказана.

**Итоговая теорема.** Для каждого буквального m минимальная потеря в frozen square-flow равна L_m=integral_0^(1/2) max(0,max_i lambda_(m,i)') ddelta, минимум достигается; A_m>=-L_m G_m. После точной совместной отмены полюса и continuous-prime main неарифметическая часть этой производной имеет интегральный бюджет не больше 9/25 в физических L2-единицах. Нужная оценка L_m<=C(1+log m)^r остаётся недоказанной. Если она установлена без RH, то все нетривиальные нули zeta лежат на Re s=1/2. В этой работе RH_PROVED=false.**
