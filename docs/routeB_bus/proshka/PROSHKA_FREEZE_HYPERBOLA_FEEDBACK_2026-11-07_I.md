# STATUS: TRY_HYPERBOLA_FEEDBACK_I

```yaml
STATUS: TRY_HYPERBOLA_FEEDBACK_I
OPERATIVE_CLASS: TRY_HYPERBOLA_FEEDBACK_I
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_FINAL_PROOF_CHECK_AND_TESTS
DATE: 2026-11-07
AUTHORITY: OWNER_OK_GO_AFTER_BACKWARD_BOOTSTRAP_DESIGN_H
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
INPUT_H_COMMIT: ba7a9b51624fde27858082a5662a24fe3f9bfbe2
INPUT_H_BLOB: 33732fd86c8439e8188cc8a1274d9c4b8af8d05a
INPUT_F_COMMIT: ed480327be4c37df57519cc5c06d4d7ecc3090e0
INPUT_F_BLOB: 642e3d6e6842a18ad04d7d11049404e356823413
OBSERVED_INBOX_HEAD: 621d382d2b315966cf8c59b6fdfe57863dff6d1e
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_HYPERBOLA_FEEDBACK_2026-11-07_I.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: SOURCE_DERIVED_JOINT_SIGNED_EXPONENT_GAIN
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: EXACT_HYPERBOLA_SPLIT_AND_MELLIN_FALSIFIER
ROUTE_SCORE: 3
```

Ы. Freeze после предварительного алгебраического анализа, до окончательной проверки доказательств и вычислений. Предварительный анализ уже предлагает разрез по sqrt(N) и возможное препятствие для диагональной энергии; его результаты ниже зарегистрированы как проверяемые ожидания, не как выполненные тесты. Этот файл не редактируется.

## Неизменная цель и источник

D(x)=psi(x)-x; B(X)=1+sup_(1<=x<=X)|D(x)|. N>=8, h=floor(N/2), H=N-h, W_N=psi(N)-psi(h)-H. Сохранить настоящую mu, все prime powers, все целые N, не только S. Вход H: W_N^2=V_N+Rjoint_N, 0<=V_N<=7N/2. Никакого переноса фазового среднего в фиксированное окно.

Пусть Y=ceil(sqrt N), b_(N,d)=mu(d)log(N/d), C_(N,Y)=sum_(d<=Y)b_(N,d)/d. Предлагаемый разрез:

    epsilon_N=sum_(2<=d<=Y)b_(N,d)*
       (floor(N/d)-floor(h/d)-H/d),
    U_(N,m)=sum_(max(Y,h/m)<d<=N/m)mu(d)log(N/d), 1<=m<=Y,
    T_N=H*(C_(N,Y)-1)+sum_(m<=Y)U_(N,m).

Сначала доказать W_N=T_N+epsilon_N с настоящими целыми границами. Затем оценить epsilon_N независимо и проверить цену перехода от W_N^2 к T_N^2. Не принимать T_N=O(sqrt N) как посылку.

## Проверяемая конструкция обратной связи

Предложенная, НЕ предполагаемая верной, положительная цена:

    gamma_N=H*(C_(N,Y)-1)/Y,
    Ediag_N=sum_(m=1)^Y |U_(N,m)+gamma_N|^2,
    |T_N|^2<=Y*Ediag_N.

Прежде чем пытаться оценивать Ediag, проверить, не слишком ли сильна достаточная цель

    for every eta>0, Ediag_N <= C_eta*
                  [N^eta*B(2N)+N^(1/2+eta)]

на всех достаточно больших N. Проверить также ОДИН фиксированный eta=1/8. Дискриминатор: последняя гиперболическая строка может быть нулевой, тогда Ediag контролирует настоящий dyadic Mobius band U_(N,1). Его Mellin-transform имеет множитель

    K(s)=integral_(1/2)^1 log(1/u)*u^(s-1)du
        =[1-2^(-s)(1+s log2)]/s^2.

Нужно проверить области сходимости, ненулевость K в хотя бы одном настоящем нуле zeta с Re rho>=1/2, перенос integer-N bound на real X и pole contradiction без простоты нулей. Это проверка способа оценки, не запрет настоящей совместной T_N.

## Предсказания до тестов

P1: точный короткий остаток удовлетворяет |epsilon_N|<=sqrt(N)log N для каждого N>=8.
P2: исходное c_N устраняется из сборки только тождественно; T_N хранит весь связанный длинный mu-кусок и короткое центрирование.
P3: на диагональном Cauchy-маршруте ожидается FATAL: U_(N,Y)=0 и первая строка несут Mellin-полюс, поэтому предложенная цена может быть чрезмерно сильной даже при сохранении настоящих mu и всех префиксов. Это не заранее доказанный kill.
P4: потеря при возвращении квадратов имеет допустимый тип sqrt(N)*log(N)*B(2N)+N*log^2(N), без фиксированной положительной потери степени.
P5: прямой bound для подписанного T_N может остаться открытым. Провал Ediag не опровергает T_N или RH.

Точные проверки: N=8,9,16,31,32,64,128; divisor counts, перестановка d*m, W=T+epsilon как рациональные векторы при log простых плюс рациональный constant; U_Y=0; нормировки Y и первого блока. Проверить символически Mellin K(s) и рациональные показатели гипотетического eta=1/8 шага. Большая численная сетка не нужна. Любые decimal-сравнения только DIAG. Нулевой log-вектор, а не small decimal, является алгебраическим судьёй.

## Pappus / K8A

DOWNSTREAM_CONSUMER: RH through the proved global exponent-bootstrap receiver G/H.
ACTUAL_CONSUMER_REQUIREMENT: genuine repeated improvement of the same global B, starting at theta=1, or another proved source receiver.
ORIGINAL_REQUESTED_OBJECT: independent one-sided bound for Rjoint, not another name for W^2.
ORIGINAL_OBJECT_IS: NOT_NECESSARY as a particular method.
KNOWN_WEAKER_INTERFACES: signed hyperbola energy with full cross terms; direct prime-only or NB receiver with its own quantifiers.
FAILURE_TYPE: UNRESOLVED_BEFORE_PROOF_CHECK.
EPISTEMIC_STATUS: RESEARCH_DEBT for the true source-bound.
NOVELTY_AXIS: exact small-divisor rounding cost matched to the nonlinear budget; test the proposed positive diagonal supplier before using it.
REOPEN_TRIGGER: an actual signed bound for T_N, or a defect in the claimed diagonal-energy obstruction.

Read before freeze: protocol, Pappus skill, H in full, constructor, and SELF_IMPROVEMENT_TEMPLATE_CHECK (eacc5128, blob 3d9b58e0a276dd1b07f05b698d4011dbcab5a09f). The short-Sobolev-window tautology is not repeated. A focused repository search for Rjoint returned no results; that is not an exhaustive absence claim. Existing G/H already settle the logical iteration, which is reused rather than sold as a new estimate.