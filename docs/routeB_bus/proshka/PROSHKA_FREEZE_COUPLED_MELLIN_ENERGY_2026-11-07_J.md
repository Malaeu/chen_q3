# STATUS: TRY_COUPLED_MELLIN_ENERGY_J

```yaml
STATUS: TRY_COUPLED_MELLIN_ENERGY_J
OPERATIVE_CLASS: TRY_COUPLED_MELLIN_ENERGY_J
ARTIFACT_STATE: FROZEN_BEFORE_FINAL_PROOFS_AND_TESTS
DATE: 2026-11-07
AUTHORITY: OWNER_USE_ALL_AND_PROVE_CHAIN_TO_RH
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
INPUT_I_COMMIT: 3934348594d25a8a4b9ec8102d75a22ff7ba3688
INPUT_I_BLOB: 8850b2e211917743c5b88cc7e256cb661fddf024
INPUT_H_COMMIT: ba7a9b51624fde27858082a5662a24fe3f9bfbe2
INPUT_H_BLOB: 33732fd86c8439e8188cc8a1274d9c4b8af8d05a
OBSERVED_INBOX_HEAD: 3934348594d25a8a4b9ec8102d75a22ff7ba3688
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_COUPLED_MELLIN_ENERGY_2026-11-07_J.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: INDEPENDENT_SIGNED_ENERGY_SELF_IMPROVEMENT
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: SIGNED_REASSEMBLY_BEFORE_SQUARING_AND_MELLIN_ENERGY
ROUTE_SCORE: 3
```

Ы. Предварительный анализ выполнен; следующие формулы являются кандидатами до окончательной проверки. Freeze после коммита не редактируется. Прочитаны актуальные bootstrap/Pappus, конструктор и вход I; полные локальные I/H совпадают с pins. Поиск COUPLED_MELLIN_ENERGY не дал результата, что не является исчерпывающим аудитом репозитория. Отдельные квадраты U_m из I не используются как поставщик.

## Объект и попытка

Сохраняются настоящие mu, Lambda со всеми prime powers, W_N=psi(N)-psi(floor(N/2))-(N-floor(N/2)), T_N и epsilon_N из I: W_N=T_N+epsilon_N, |epsilon_N|<=sqrt(N)log N. Все достаточно большие целые N, не подмена на S.

Репрезентация A: сначала совместно собрать все multiplicative rows. Для x>=1 определить U0(x)=sum_(x/2<n<=x)mu(n), U1(x)=sum_(x/2<n<=x)mu(n)log(x/n). Проверить точное суммирование sum_m[log(m)U0(x/m)+U1(x/m)] до взятия квадратов; low-end n=1 contribution учитывать отдельно. Рассчитать Mellin transform в общей области абсолютной сходимости Re s>1. Цель: определить, какие reciprocal-zeta полюса взаимно сокращаются и какие остаются у полного источника; не выводить bound из одного продолжения.

Репрезентация B: Tstep(x)=T_floor(x) для x>=8 и 0 ниже. Полная нормированная dyadic-энергия E_j=2^(-2j) int_(2^j)^(2^(j+1)) |Tstep(x)|^2 dx, j>=3. Это НЕ NB/Green Z_N. Построить собственный количественный Mellin receiver. Попробовать получить из source-exact перепаковки рекурсию E_j<=kappa E_(j+1)+C_eta 2^(eta*j)(sqrt(E_(j+1))+1), с фиксированным 0<=kappa<1/2. Такая рекурсия НЕ предполагается. Если она не выводится, написать точное отсутствующее неравенство, не ставить RH_PROVED=true.

## Предсказания до проверок

P1. В совместном Mellin-return reciprocal факторы должны сократиться до логарифмической производной zeta. Высокие порядки отдельных 1/zeta-полюсов не должны переноситься на полный источник. Ненулевой остаточный простой полюс вне линии при этом может сохраниться.
P2. Замена W_N на T_N имеет квадратнокорневой pointwise бюджет и лишь полилогарифмическую цену в нормированной длиннооконной энергии. Ошибка от floor(x) должна быть учтена явно.
P3. Субполиномиальный bound E_j для всех поздних j должен исключать каждый правый нуль по абсолютной сходимости Mellin integral; обратный pointwise-to-energy переход не требуется. Не заявлять нового zero-free bound до получения E_j.
P4. Рекурсия с kappa<1/2 должна запускаться из E_j=O(2^j); kappa=1/2 проверить на скалярной последовательности 2^j. Это тест класса логических контрактов, не контрпример для mu.
P5. Главная попытка — независимый source bound для связанной энергии. Ни точная сборка, ни аналитическое продолжение сами не считаются таким bound. Предположение о результате не делается.

Судьи после freeze: точная prime-log арифметика для N=8,9,16,31,32,64,128; символические Mellin-множители и локальные zero-orders 1,2,3; finite dyadic-energy comparisons j=3,...,7 при 50/80 знаках только DIAG, без extrapolation, без таблиц нулей. Zero-consistent алгебра проверяется рациональными коэффициентами, не малыми десятичными значениями.

K8A: DOWNSTREAM_CONSUMER=RH. ACTUAL_CONSUMER_REQUIREMENT=истинный source-specific bound с доказанным возвратом. PARTICULAR_ENERGY_IS=NOT_NECESSARY как метод. KNOWN_WEAKER_INTERFACES=прямой B-bootstrap, исходный NB bounded-subsequence receiver, prime-only Weil receiver. FAILURE_TYPE=UNRESOLVED_BEFORE_TESTS. EPISTEMIC_STATUS=RESEARCH_DEBT. NOVELTY_AXIS=совместное сокращение до квадрата и проверенный energy receiver, а не историческая новизна Mellin/Dirichlet convolution. REOPEN_TRIGGER=арифметическое улучшение с допустимой степенной ценой.
