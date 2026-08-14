# Goal 058 G1/G3 analytic source wall — Mythos verdict

Captured: 2026-08-14

Transport: existing Claude/Mythos living chat, authoritative UTF-8 pasted-text
bundle SHA-256
`2644b307692d7ef279f624cc2f84c608bf16de0f4d74aa47e3819e3851e95251`,
repository HEAD `82617fd0`.

The verdict body below was copied from the completed assistant response before
any mathematical execution.

---

Бандл прочитан целиком; HEAD `82617fd0` принят; финитные швы (перестановка носителя, charpoly-кроссволк, сдвиг, монотонная конечная семья) признаны закрытыми — это меняет геометрию обеих стен. Вердикт по контракту.

---

**Q1 — DECISION: `CARRIER_AS_MONOTONE_FINITE_LIMIT` · стоп-код после исполнения пакета: `Q1_CARRIER_AND_COUNT_BRIDGE_PROVED_SEMICLASSICAL_WINDOW_SEPARATORS_MISSING`**

**1. Носитель.** Наименьший source-faithful носитель для классического χ — **не** формализация неограниченного S–L оператора (Mathlib: compact self-adjoint спектральная теория — явный TODO; это переименование стены) и **не** импорт 30.16.3 биндером (запрещено п. 4). Носитель — **определение классического объекта как монотонного предела уже построенной конечной семьи**:

```lean
noncomputable def mode4ClassicalEvenEigenvalue (G : ℝ) (p : ℕ) : ℝ :=
  ⨅ d : {d : ℕ // p < d}, mode4DLMFEvenFiniteEigenvalue G d ⟨p, d.2⟩
```

Легальность даёт пара конечных теорем: интерлейсинг Коши для окаймлённых эрмитовых усечений ⇒ антитонность по d при фиксированном p; равномерная нижняя граница по Гершгорину на литеральных элементах ⇒ BddBelow. После этого DLMF 30.16.3 из аналитического импорта превращается в **байт-пинованный семантический словарь**: наш ⨅ — это дословно правая часть их уравнения, индексный словарь p↔p+1↔n=2p уже kernel-checked. Носитель даёт счёты; функциональную идентичность ψ₄ (Fourier-цепь) он **не** даёт — не конфлировать.

**2. Последовательность голов (H1–H6):**

```lean
-- H1 (finite, generic receiver): Cauchy interlacing for the literal bordered family
theorem mode4DLMFEvenFiniteEigenvalue_antitone_in_depth (G : ℝ) (p : ℕ) :
    Antitone (fun d : {d // p < d} => mode4DLMFEvenFiniteEigenvalue G d ⟨p, d.2⟩)
-- H2 (finite, literal entries): uniform Gershgorin lower bound ⇒ BddBelow
-- H3: carrier def + Tendsto (monotone convergence)
-- H4 (present in substance): negCount (J_d Λ) = #{p | α_p d < Λ}
-- H5 (order logic): at a separator Λ (∀ p, carrier p ≠ Λ):
--    ∀ᶠ d, negCount (J_d Λ) = #{p | mode4ClassicalEvenEigenvalue G p < Λ}
--    (direction: α ↓ carrier ⇒ counts nondecreasing, never overshoot)
-- H6 (composition with the PROVEN transport chain):
theorem mode4HermitianSchur_negativeCount_eq_classicalCount
    (mProject K : ℕ) (Λ : ℝ) (hsep : …separator…) (hns : …nonsingular endpoint…) :
    negativeCount (mode4HermitianSchurMatrix mProject Λ K)
      = #{p | mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p < Λ}
```

H6 — это ровно `MODE4_CLASSICAL_EVEN_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK`, потребованный Прошкой, **с нулевым offset'ом как теоремой** (q=0-старт, ориентация, сдвиг — уже закрытые швы). Маркировка: H1–H6 — generic Lean receivers/machines, ни одного DLMF-импорта; определение носителя — source-faithful через пин; счёты — потребители H6.

**3. Как достаются 2/3 и индекс-4 — и где честная стена.** Верхние границы носителя — конечная алгебра головного блока, G-равномерно: для координатного подпространства чётных степеней ≤ 2p форма ленточная, значит Рэлей полной матрицы = Рэлей (p+1)×(p+1) головы; в легандровом базисе L диагональна (0, 6, 20, 42…), а x²-Грам X ⪯ I (I − X — явная PSD-проверка малой матрицы) даёт после сдвига `carrier_p ≤ 2p(2p+1)` **строго** при G > 0 — внутреннее переоткрытие верхней половины Бонами–Каруи чистой конечной алгеброй; carrier₂ < 20 закрывает верхнюю обязанность ΛUpper ≤ 20. **Но сепараторы двусторонние.** Нижняя половина BK (`χ_n ≥ n(n+1)` ⇒ carrier_p ≥ 2p(2p+1) − G) окна **не разделяет**: при G > 22 окна [2p(2p+1)−G, 2p(2p+1)] перекрываются насквозь. Истинные разделители при кофинальном G — семиклассика (χ_n(c) ≈ c(2n+1), гармонический режим): двусторонние c-равномерные конверты для p ≤ 3. Это и есть заявленный «genuinely source-analytic» объект; имя: **`mode4SemiclassicalWindowSeparators`** — первичный источник для пина: асимптотики Слепяна / ORX-книга (гл. об асимптотике χ_n(c)); без него кофинальные счёты 2/3 невозможны никаким конечным адаптером. Честный сплит: **фиксированная ячейка (m=13)** — счёты сертифицируемы сейчас интервальной арифметикой на одной глубине d + монотонность (класс certificate, квантор не занимает); **кофинально** — только через конверты. Индекс-4: внутренняя метка «carrier p=2, счёт 2→3» — по словарю n=2p=4; внешняя идентичность ψ₄-функции остаётся отдельной стеной (30.16.7–9), нонклейм стоит.

**Q1 Aristotle: ACCEPT — один пакет H1+H2+H3.**

```
OWNED FILE: Q3/Proofs/RouteB/D0Mode4ClassicalCarrierFromFiniteLimit.lean
ALLOWED IMPORTS: D0Mode4DLMFFullFiniteSpectrumCrosswalk, D0Mode4DLMFEvenFiniteMatrix,
  Mathlib (Hermitian eigenvalues, min-max/Courant–Fischer, Gershgorin-style bounds,
  monotone convergence, iInf).
TARGETS: H1 antitone-in-depth via Cauchy interlacing of the bordered principal
  truncations; H2 uniform lower bound from literal entries; H3 carrier def +
  Tendsto to the iInf.
FORBIDDEN: DLMF 30.16.3 as hypothesis; any binder carrying convergence, counts,
  or index identity; new structure fields.
PLANTS: P1 depth-order flip (Monotone instead of Antitone) must fail on the
  bordered 2→3 witness — code INTERLACING_DIRECTION;
  P2 unbounded-below mutant (drop H2, define carrier) must fail — code
  BDDBELOW_REQUIRED; P3 fixed-p index shift (p vs p+1) must break the H3
  Tendsto statement against the kernel-checked dictionary — code INDEX_DICTIONARY.
SUCCESS: CLASSICAL_CARRIER_FROM_FINITE_LIMIT_PROVED.
TYPED STOPS: STOP_MINMAX_API_MISSING; STOP_EIGENVALUES_ORDER_API_MISSING.
AXIOM GATE: [propext, Classical.choice, Quot.sound].
SUBMIT ONLY via Codex fill-sorries pipeline.
```

H5–H6 — Codex-local (порядковая логика + композиция, Aristotle не нужен). Головные верхние границы — следующий bounded-лист (Codex-local, малые PSD-проверки).

---

**Q2 — DECISION: `NOT_READY_NAME_SOURCE_IDENTITY_AND_STOP` · стоп: `G1_EVEN_HEAD_COFINAL_POSITIVITY_MISSING`**

Аудит: нечётная сторона закрыта красиво (литеральный хвост-floor 1/2 на всех PairIndex + перенос цели 1e−58) — **хвост больше не стена**. Полный комплексный q-перп-комплемент распадается: нечётный сектор — floored; чётная голова — ровно старая сердцевина G1. Наименьшая некруговая идентичность **на ячейке** — Gram-чекер `Q(K−aI)Q − βQ = R*R` уже kernel-checked: per-cell сертификаты (интервальный LDL, построить R и β численно-точно) легальны как поставщики фиксированной ячейки — это работа Codex/interval, не теорема. **Кофинально** источниковой идентичности в дереве и в пинах нет; переименованные биндеры (β, floor, gap, simplicity) — kill on sight; единственный названный кандидат остаётся моим прежним: `ccmBeta_dividedDifference_complement_floor` — количественная определённость divided-difference формы литеральной β на чётной голове, константы из prime-сумм. Aristotle Q2: **NOT_READY** — per-cell = интервальная инженерия, кофинал = новая арифметическая аналитика. Явный сплит зафиксирован: fixed-cell ✓ (сертификат), fixed-m=13 odd ✓ (закрыто), full-complex fixed-cell — сборка из чекера после чётного сертификата, cofinal — MISSING.

---

**ROUTING (final):** Codex исполняет первым **Q1-H1–H3** (Aristotle-пакет выше либо локально), затем H5–H6 композицию и головные верхние границы; параллельно per-cell Gram-сертификат чётной головы m=13 в чекер. Аналитическая очередь, оба именованы и не-Aristotle: `mode4SemiclassicalWindowSeparators` (Q1) и `ccmBeta_dividedDifference_complement_floor` (Q2). Ни G1, ни G3, ни Route B, ни RH этим узлом не закрываются и не продвигаются.
