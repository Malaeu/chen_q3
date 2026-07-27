# STATUS: PROOF_PROGRESS  (конспект-verbatim Mythos; оригинал у Прошки)

RIEMANN_SUM_BRIDGE_MATH: PROVED_ON_PAPER
DIRECT_LIPSCHITZ_LEAN_ASSEMBLY: ACTIVE — standalone project
BV_FIRST_PACKAGING: FROZEN FALLBACK
FULL MUNTZ CONTINUATION: OPEN DOWNSTREAM OF T2

Маршрут чистый: математической неопределённости в оценке правой суммы
Римана больше нет; остался библиотечный мост (Lean assembly).
⚠️ Две follow-up-декларации облачного working tree зависели от sorryAx —
их НЕЛЬЗЯ импортировать как доказанные; берём только точную постановку gap
и найденные API.

ROUTE MAP (standalone-цепочка):
finite cell estimate → finite aggregate right-Riemann estimate →
compact-support finite sum = tsum → zero mass убирает интеграл →
uniform bound Σh(nu) → |E_star| ≤ C√u → left-tail analyticity Re s > −1/2 →
regularized ζ·Mellin continuation → identity theorem.

FINAL PROPOSAL — два уровня:
Primary: прямая Lipschitz-сборка (cellwise Ku² на внутренних клетках,
terminal cell отдельно, конечная сумма → tsum → zero mass).
Fallback BV-first: ТОЛЬКО если прямая сборка два раза подряд не уменьшит
exact Lean-gap; BV-теорему строить на конечном Icc 0 (N·u), НЕ на Set.univ.
Kill-switch: два подряд NO_PROGRESS → REPRESENTATION_SHIFT → finite BV first.

STRONGEST ATTACK:
1) Ложная починка «extend by zero → global Lipschitz → generic bound» —
   неверна: midpoint representative допускает скачок в правой границе,
   terminal cell нельзя растворить в глобальной константе.
2) После T2 не возвращаться к сырому ζ(w)·M_h(w) в w=1: zero mass убирает
   principal part, но Mathlib-значение сырого произведения не становится
   removable value. Использовать только ZetaMellinReg(1) = M_h′(1).

CODEX DIRECTIVE (для standalone-проекта):
TARGET T2_RightEndpointRiemannAggregate · new standalone Mathlib-only ·
proof route: N покрывает [0,b] → ошибка = конечная сумма клеточных ошибок →
Ku² на внутренних → terminal-cell отдельно → суммирование бюджетов →
tsum=конечная сумма → hmass=0 → ∃C ∀u∈Ioo 0 1 ‖Σh(nu)‖≤C → ‖Estar‖≤C′√u.
FORBIDDEN: global Lipschitz zero-extension · импорт sorryAx-деклараций ·
raw ζ·M в w=1 · ослабление midpoint-семантики · sorry/admit/axiom/nd.
SUCCESS: T2_LIPSCHITZ_PROVED.
FAILURE: LIPSCHITZ_TERMINAL_CELL_API_GAP · LIPSCHITZ_FINITE_SUM_INTEGRAL_ASSEMBLY_GAP.

META: стена сжата до «finite cell estimates ⟶ aggregate integral
inequality»; убиты: сомнение в самой оценке, поиск нового механизма T2,
глобальный Lipschitz zero-extension, импорт sorryAx-черновиков.
Research не нужен — нужна Lean-сборка. Smallest gap:
T2_RightEndpointRiemannAggregate. Mainline Route B из-за standalone не
останавливать.
