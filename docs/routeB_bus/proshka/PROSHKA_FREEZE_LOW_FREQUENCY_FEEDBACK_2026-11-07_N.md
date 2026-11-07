# STATUS: TRY_LOW_FREQUENCY_FEEDBACK_N

```yaml
OPERATIVE_CLASS: TRY_LOW_FREQUENCY_FEEDBACK_N
ARTIFACT_STATE: FROZEN_BEFORE_COMPLETED_PROOFS_AND_TESTS
DATE: 2026-11-07
AUTHORITY: OWNER_PROVE_THE_EXACT_C_LONG_TARGET_FROM_M
INPUT_COMMIT: 45afff3806bd7671919f5330830b246b1229c75c
INPUT_BLOB: 27168a1a764b5254b53d87e5772673017b7f5d37
INPUT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_PAIRED_SCALE_DIVISOR_2026-11-07_M.md
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
OBSERVED_INBOX_HEAD: 45afff3806bd7671919f5330830b246b1229c75c
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_LOW_FREQUENCY_FEEDBACK_2026-11-07_N.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: TRUE_SOURCE_ONE_SIDED_TWO_SCALE_ESTIMATE
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: SOURCE_PRESERVING_SPECTRAL_COMPRESSION_AND_ROOT_ENERGY_FLUX
ROUTE_SCORE: 2
```

Ы. Предварительный алгебраический анализ уже предложил конечный Fourier-разрез и сравнение квадратных корней энергий. Это не слепые предсказания. Завершённых доказательств и вычислительных проверок новой попытки до данного freeze нет. Файл после коммита не изменяется.

## Цель и неизменный источник

Для каждого eta>0 доказать C_long(X)<=C_eta X^eta(sqrt(A(2X))+1) на всех достаточно больших dyadic X, с буквальными определениями M. Ни новая mu, ни другой carrier, ни фазовое среднее вместо нужного окна не допускаются. В M доказан возврат F(X)=A(X)-A(2X)/2=C_long(X)+R_X, |R_X|<=3(1+log(4X))^2/2+3(1+log X)^4/4. Он остаётся inherited PAPER, а не предполагаемая новая оценка C_long.

## Выбранная попытка

При X=2^j>=8 положить M=4X и конечный исходный вектор u_X(0)=0, u_X(n)=Lambda(n)-1 для 1<=n<M. Использовать DFT длины M с коэффициентами M^{-1}sum u_X(n)exp(-2pi i k n/M). Оба физических окна [X,2X) и [2X,4X) строить из ОДНОГО u_X. Никакого wrap-around в физических суммах нет.

Положить K=floor(sqrt X), оставить частоты |k|_M<=K, включая k=0, а высокую часть оценить через циклический дискретный примитив: v_n-v_(n-1)=u_high(n). Ожидаемая достаточная независимая цена: нормированные энергии высокой части O(log X) одновременно на обоих окнах. Проверить все коэффициенты, размер M и цену нижнего края floor(N/2).

Затем сравнить не разность квадратов по отдельным модулям, а корневой поток G(X)=sqrt(A(X))-sqrt(A(2X)/2). Исследовать точный возврат между искомым C_long-bound и односторонней субполиномиальной ценой соответствующего низкочастотного корневого потока. Само установление такого возврата не считается доказательством низкочастотного bound.

Попробовать оценить оставшиеся низкие частоты с настоящими коэффициентами Lambda-1, сохраняя всю отрицательную часть второго масштаба. Если независимого выигрыша нет, отделить доказанную высокочастотную цену от отсутствующей полной оценки.

## Предсказания до тестов

P1: конечная Parseval-оценка и multiplier (1-exp(-2pi i k/M))^{-1} дадут O(log X) для всей высокой части при K=floor(sqrt X), без нулей zeta и без фазового усреднения.

P2: переход к корневому потоку сохранит критический коэффициент 1/sqrt(2) с аддитивной O(sqrt(log X)) ошибкой; ненужная потеря epsilon*A(2X) не потребуется.

P3: новое низкочастотное пространство имеет 2K+1 частот, но его два окна при данном X обязаны использовать общую проекцию. Нельзя приравнивать второе окно проекции u_X первому окну проекции u_(2X).

P4: имеющихся общих норм и положительности недостаточно для независимого верхнего bound низкого корневого потока. Проверить конкретный согласованный искусственный источник u(n)=n^(beta-1), beta=3/4: он имеет линейный главный counting term и малую диагональную энергию, но должен сохранять положительный поток порядка X^(1/4). Это только судья универсального шага, не контрпример для Lambda.

P5: попытка получить source-specific верхнюю оценку остаётся открытой до расчёта; O(1) или subpolynomial gain не предполагается. Если такого bound нет, не выдавать compression или новую RH-эквивалентность за выигрыш показателя.

## Проверки

Сначала PAPER-вывод конечного inverse-difference bound и всех доменов. После freeze: X=8,16,32,64 для полного источника при 50 и 80 десятичных знаках; сверить прямые окна, DFT-реконструкцию, высокий примитив, обе энергии, изменение корневого потока и теоретические верхние константы. Decimal agreement — DIAG, не ARB_INTERVAL. Отдельные точные проверки над рациональными коэффициентами: telescoping матрицы окна, multiplicity floor(N/2), recurrence и домен без wrap-around. Никакой cofinal вывод из сетки.

DISCRIMINATOR: exact Fourier algebra for finite identities; strict analytic envelopes for claimed bounds; in the final source return a nonzero Mellin residue at an actual right zero. Near-zero DIAG is not a zero certificate.

## K8A

DOWNSTREAM_CONSUMER: requested C_long estimate, then the original energy-Mellin RH receiver.
ACTUAL_CONSUMER_REQUIREMENT: genuine one-sided improvement of the full source energy for all sufficiently late dyadic scales.
ORIGINAL_REQUESTED_OBJECT: exact C_long target from M.
ORIGINAL_OBJECT_IS: a sufficient interface, not a uniquely necessary proof method.
KNOWN_WEAKER_INTERFACES: source-correct signed root-energy increment or another complete RH receiver; each needs a quantitative return.
FAILURE_TYPE: UNRESOLVED_BEFORE_TESTS.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: uniformly paid frequency complement, not another entrywise divisor price.
REOPEN_TRIGGER: a source-specific estimate on the remaining low frequencies, or a defect in the frequency-return calculation.

Negative tails and signed cross terms remain in the complete paired energy. General spectral positivity alone must not be sold as the missing arithmetic information. Old closed verdicts, states and this freeze remain untouched.
