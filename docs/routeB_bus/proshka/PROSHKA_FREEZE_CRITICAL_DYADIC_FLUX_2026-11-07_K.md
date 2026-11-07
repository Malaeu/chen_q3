# STATUS: TRY_CRITICAL_DYADIC_FLUX_K

```yaml
OPERATIVE_CLASS: TRY_CRITICAL_DYADIC_FLUX_K
ARTIFACT_STATE: FROZEN_BEFORE_FINAL_PROOFS_AND_TESTS
DATE: 2026-11-07
AUTHORITY: OWNER_USE_LAST_RESULTS_AND_PROVE_CHAIN_TO_RH
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
INPUT_J_COMMIT: ef09e34ba5e74fa443b748339a27891baf15cc0d
INPUT_J_BLOB: 4c46ce316e795fc58eb5e66f96454cc94978b0eb
INPUT_I_COMMIT: 3934348594d25a8a4b9ec8102d75a22ff7ba3688
INPUT_I_BLOB: 8850b2e211917743c5b88cc7e256cb661fddf024
OBSERVED_INBOX_HEAD: ef09e34ba5e74fa443b748339a27891baf15cc0d
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CRITICAL_DYADIC_FLUX_2026-11-07_K.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: SOURCE_SPECIFIC_SIGNED_ENERGY_FLUX_BOUND
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: CRITICAL_SCALE_TELESCOPING_AND_INTEGER_CENTERED_PAIR_ENERGY
ROUTE_SCORE: 2
```

Ы. Freeze после предварительного алгебраического анализа, до окончательных доказательств и тестов. Старые файлы и этот freeze не редактируются. Проверена локальная копия J: 39855 bytes, Git blob совпадает. Новый source-bound не предполагается.

## Неизменный источник и попытка

D(x)=psi(x)-x; W(x)=psi(x)-psi(x/2)-x/2. Все prime powers сохранены. В I/J имеется исходный T_N с |W_N-T_N|<=sqrt(N) log N и энергия E_j=2^(-2j) sum_(2^j<=N<2^(j+1))T_N^2. Их неполученная рекурсия не является входом.

Проверить менее требовательный критический коэффициент 1/2 вместо фиксированного kappa<1/2: настоящая PNT должна дать E_j=o(2^j), что может оплатить граничный член при разворачивании рекурсии. PNT не заменяет самой рекурсии.

Для source-exact арифметической оценки ввести b_n=Lambda(n)-1 и S(x)=sum_(x/2<n<=x)b_n. Отличие S от W задаётся только целой частью. Рассмотреть A(X)=X^(-2) integral_X^(2X) S(x)^2 dx на dyadic X и точную разность A(X)-A(2X)/2. Полный квадрат раскрывается в конечный prime-pair Gram с точными концами, без усреднения по фазам. Требуется совместная верхняя оценка подписанной внедиагональной части, а не её отдельные модули.

## Предсказания и судьи

P1: PNT и точная цена I действительно разрешают критический коэффициент 1/2; из одного O(2^j) старта это не следовало. Проверить предел остатка и каждую перестановку сумм.
P2: floor-centering позволит заменить W-energy на A(X) с абсолютной O(1) ошибкой, без потери степени; определить явную константу и проверить атомные границы.
P3: критический kernel есть точная разность двух overlap-кernel, а его диагональ имеет O(log X) upper-budget. Оплата диагонали не оценивает off-diagonal.
P4: проверить самостоятельную арифметическую оценку off-diagonal. O(1), power saving и RH заранее НЕ предсказываются. Возврат к самой неизвестной A(X) не засчитывается как независимый bound.
P5: качественная PNT сама не может обеспечить нужный flux-bound; функция ошибки x^beta, 1/2<beta<1, служит аналитическим тестом логической достаточности, НЕ подменой настоящей zeta.

Тесты: dyadic X=8,16,32,64; точные rational-prime-log quadratic coefficient matrices для direct step integration против pair overlap и critical flux; независимые rational endpoint probes; при необходимости десятичная диагностика, но не ARB_INTERVAL. До этих тестов новых конечных результатов не заявляется. Численная сетка не заменяет cofinal-оценку. Дискриминатор алгебры — нулевая точная матрица коэффициентов; дискриминатор RH-supplier — строгая upper-envelope на всех достаточно больших dyadic X.

## K8A

DOWNSTREAM_CONSUMER: RH via source Mellin integral.
ACTUAL_CONSUMER_REQUIREMENT: subpolynomial energy on all sufficiently large dyadic scales, or an independently proved alternative receiver.
ORIGINAL_REQUESTED_OBJECT: a complete proof using the existing results.
PARTICULAR_FEEDBACK_INTERFACE_IS: NOT_NECESSARY as a method.
KNOWN_WEAKER_INTERFACES: pointwise psi bootstrap; original bounded-subsequence NB route with its own quantifiers.
FAILURE_TYPE: UNRESOLVED_BEFORE_TESTS.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: critical coefficient with PNT terminal decay, and an exact centered prime-pair flux whose diagonal is independently paid.
REOPEN_TRIGGER: a source-derived signed off-diagonal bound, or an error in the critical-limit/centering proof.
