# BRIEFING: где мы сейчас в Q3/RH и как связан разбор другого Claude с актуальным кодом

**Кому:** следующая сессия Claude / Louise / Pro chat / любой агент работающий с `rh_lean_01_2026`
**От:** session 2026-06-10, синтез после прошерки master docs + Q3_OBSTRUCTION_ATLAS + PSD_STEP33_MONITOR + step33-bootstrap skill
**Status:** synthesis, не theorem statement

---

## ⚠️ READ §−1 FIRST.

`prime_term_le_at_t_critical_axiom` — **доказано ЛОЖНОЕ** контрпримером из собственного `verify_variant_b.py` репо. **Это единственная non-standard axiom в активной Fourier RKHS chain Step33** — подтверждено через `#print axioms` (2026-06-10, see §−1 GROUND TRUTH block).

Codex закрывает receivers в этой цепи (lake build, q3_check, hole scan — всё pass), но **каждое закрытие conditional на эту ложную axiom**. Зелёный билд = технически валиден, math = отравлен. Atlas не флагает ложь, потому что statement-level inspection не проверяет numerical consistency.

`Q3.Clean.MainClean` (legacy январский snapshot) — отдельная декларация, не собирается из-за A1_density issue. Эта неработоспособность legacy chain **не защищает** активный путь.

Связь с Connes-Consani (см. `connes_consani_sonin_research_node.md` Phase 2): их mechanism **не использует** cap-style утверждение типа `prime ≤ arch`. Их `W_∞(g*g) ≥ Tr(ϑ(g) S ϑ(g)*) − c|g̃(0)|²` (c ∈ 13..17) — alternative decomposition через Sonin reservoir + compact perturbation. Q3 пытается доказать через axiom которая ложна, в то время как опубликованный путь Connes-Consani 2021 показывает что задача (для archimedean) решается **без** этой axiom.

## TL;DR

1. **Главное расхождение картинок.** Файл `Downloads/Проверка доказательства гипотезы Римана.md` (диалог с другим Claude через Claudify) описывает состояние **до января 2026**: 5 axioms в `Q3.Main`, `prime_term_le_at_t_critical_axiom` главная, Step 33 в работе. Это **legacy картина**. Реальность 2026-01-13 и вчерашняя (10.06):
   - `Q3.Clean.RH_proven_clean` зависит от Tier-1: `[propext, sorryAx, Classical.choice, Quot.sound, Q3.Clean.Weil_criterion]`. ⚠️ **`sorryAx` в списке означает что теорема формально НЕ доказана** — она условна на 4 открытых sorry. Имя `RH_proven_clean` — мина самообмана, см. §0 ниже.
   - 6 из 8 bridges fully closed (0 sorry)
   - 7 из 9 Tier-2 theorems FULLY PROVEN
   - 4 sorry осталось: 2 в `Q_nonneg_on_atoms`, 2 в `A1_density_WK_axiom`
   - Step33A.1 — фронт-линия (`RawOmegaATaylorModelCertificate` + 2392-cell payload, route C)

2. **Разбор Gate ⟺ RH остаётся валидным, но Gate РАСПЫЛЁН на 5 локусов** (revealed 2026-06-10 после Fourier path audit). Все эквивалентны через Теорему 4:
   - `prime_term_le_at_t_critical_axiom` (4-я incarnation ρ_cap, K-pointwise, в Fourier upstream)
   - `A3_bridge_axiom K hK` (K-dependent Tier-1)
   - `Q_nonneg_on_BaseAtomCone_axiom` (τ=0 corollary)
   - `Q_nonneg_on_atoms_uniform` (K-uniform = RH-equivalent, alternative path)
   - `MainClean.lean:59` sorry (K → ∞ exhaustion = Step 34)

   Это **честная открытая архитектура**, но сложность **не одна**, она расщеплена на синонимы. Atlas не позволил спрятать её, но и не закрыл. См. §0.2.

3. **Sign crisis (centeredA − P = −101.66) закрыт правильно, но post-mortem отсутствует.** Canonical convention зафиксирована как **`step22PositiveAxisOmegaAProfile`** (raw positive-axis Ω) — explicit-formula-derived, не выбор по знаку. Centered-конвенция деактивирована, но **не объяснена**. Нужен абзац «что это было» в INSIGHTS.md — бесплатный consistency check. См. §0 пункт 4.

4. **Дисциплина против self-deception встроена в `Q3_OBSTRUCTION_ATLAS.md`** — 7 walls + Acceptance Checks. Prime-side wall прямо запрещает scalar mirror, Matrix-identification wall совпадает с критикой другого Claude.

## §−1. CRITICAL FINDING 2026-06-10 — `prime_term_le_at_t_critical_axiom` ДОКАЗАНО ЛОЖНОЕ

**Это не «RH-весовая axiom», это ложное утверждение в Lean.** Контрпример **встроен** в собственный verify скрипт репо.

### Дословный statement (`Q3/Proofs/Q_nonneg_t_critical.lean:328-331`)

```lean
axiom prime_term_le_at_t_critical_axiom (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ)
```

Claim: для **любых** (K, B, τ) с условием |τ|+B≤K, prime_term ≤ arch_term на сдвинутом Fejér×heat атоме при t_critical.

### Контрпример (репо знает)

`Q3/Proofs/Q_nonneg_t_critical.lean:538-540` (комментарий перед `Q_nonneg_on_base_atoms_at_t_critical`):

```
Numerical verification (Python verify_variant_b.py):
  For all B ∈ [0.5, 4.9], τ=0: min Q = 1.03 > 0  ✓
  For τ > 0: Q can be < 0 (e.g. Q = -911 at τ = 1.69)  ✗
```

`verify_variant_b.py:572` (комментарий теста на AtomCone):

```python
WARNING: This test FAILS for τ > 0! Use BaseAtomCone (τ=0) instead.
```

`verify_variant_b.py:596`: `"test": "Q on AtomCone (FAILS for τ>0)"`. `Line 681`: `Test C: Q on AtomCone with τ > 0 (info only)... EXPECTED TO FAIL`.

Поскольку `Q (phi_shift_critical B τ) := arch_term − prime_term`, factное Q < 0 ⟺ prime_term > arch_term. Это **прямой контрпример** axiom-у, и **выбор τ удовлетворяет условиям axiom** (например K=4, B=2.3, τ=1.69 → |τ|+B = 3.99 ≤ 4).

### Архитектурное несоответствие

Авторы **сами знают** что AtomCone (произвольный τ) не работает. Theorem `Q_nonneg_on_base_atoms_at_t_critical` (line 542) **сам себя ограничивает** до `BaseAtomCone_critical` (τ=0 only). Но `prime_term_le_at_t_critical_axiom` **по τ свободна**, и используется upstream в `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` для **полного** `AtomCone_K_fixed`. Это разрыв между знанием в verify скрипте и axiom statement в Lean.

### Build status — независимо не собирается (защита от accidental "доказали RH")

```
$ lake build Q3.Clean.MainClean
error: Q3/Clean/TheoremsTier2.lean:130:14: Unknown constant `Q3.Clean.Theorems.A1_density`
error: Lean exited with code 1
```

`RH_proven_clean` **не компилируется** в current state репо. `#print axioms` недоступен. PROJECT_STATUS.md от 2026-01-13 описывает **прошлый snapshot**, не настоящее. Это случайно спасло от accidental publication отравленного результата — Codex/Lean чек не пускает цепь дальше.

### Следствие для §0 и §0.2

«Распылённый Gate на 5 локусов / все эквивалентны через Теорему 4» — **неправильная классификация**. Один из локусов **не RH-equivalent**, а ложен. Теорема 4 (Gate ⟺ RH) применима только к **корректным** формулировкам типа `Q_nonneg_on_atoms_uniform`. K-pointwise cap с фиксированными константами сильнее RH (и потому ложен), а не "synonim".

Текущая честная теорема проекта **не** «RH ⇐ Gate». Она:

```
RH ⇐ (Weil_criterion ∧ A3_bridge ∧ prime_cap[FALSE] ∧ BaseAtomCone ∧ exhaustion)
```

— конъюнкция, где **одно утверждение опровержимо**, три синонимичны (через Теорему 4 — только uniform-формулировки), exhaustion условен на остальные.

### Action items приоритетом

1. **Срочно: документировать ложность axiom** в `q3.lean.aristotle/docs/INSIGHTS.md` явным красным блоком. Это критический факт о состоянии проекта.
2. **Замена axiom**: либо доказать **слабее** утверждение (ограниченное BaseAtomCone, τ=0), либо признать что Fourier path не работает без τ-restriction и явно его restrict.
3. **Коллапсировать архитектуру** к единой именованной гипотезе — естественный кандидат `Q_nonneg_on_atoms_uniform` (как Opus 5 review предложил). Все остальные локусы либо доказать леммой из неё, либо убить контрпримером.
4. **F2 audit численно проверяет axiom** — встроить в скрипт: для серии (K, B, τ) с |τ|+B≤K, вычислить prime - arch и flag negative samples. Если найдёт ещё counter-examples, ещё одно подтверждение.

---

## §0. AUDIT СОХРАНЕНИЯ СЛОЖНОСТИ (must-fix перед канонизацией брифинга)

**Принцип:** в любой цепи, ведущей к RH, ровно один элемент обязан нести RH-вес. Если кажется что ни один не несёт — ошибка спряталась. Сложность не исчезает, она переезжает.

Прогон брифинга через этот аудит обнажил 4 точки которые надо ужесточить:

### 1. `RH_proven_clean` с `sorryAx` — naming mine

Имя `RH_proven_clean` для теоремы, чьи зависимости содержат `sorryAx` — это ровно тот класс самообмана, который запрещает Atlas. Через полгода кто-то прочитает имя и поверит ему.

**Fix:** переименовать в `RH_conditional_clean`, либо повесить в docstring жирное:

```
/-- ⚠️ Depends on `sorryAx` until `Q_nonneg_on_atoms` (2 sorry) and
    `A1_density_WK_axiom` (2 sorry) are closed. NOT a complete proof of RH. -/
theorem RH_proven_clean : ...
```

**Owner:** следующая сессия, до любого audit'a квантора.

### 2. `Q_nonneg_on_atoms` — квантор установлен (RESOLVED 2026-06-10)

**Lean type signature** (`Q3/Atoms_Positive.lean:45`):

```lean
theorem Q_nonneg_on_atoms (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ AtomCone_K_fixed K Q3.t0_critical, Q g ≥ 0 := by
  ...
  exact Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS K hK hA3 hRKHS
```

Квантор: **`∀ g ∈ AtomCone_K`** = «на всём atom cone», не на каждом атоме отдельно. Это **Variant B** из исходной дилеммы. Но дилемма оказалась **ложной** — реальная картина trichotomy:

#### Уровень 1: K-fixed theorem (на одном `t0_critical`)
`Q_nonneg_on_atoms` использует `_of_A3_Fourier_RKHS K hK hA3 hRKHS`. 2 sorry здесь — **финитная инженерия на одном K**, не Gate. Закрывается через A3 bridge + RKHS contraction. По Bonus Предл. 2 при ограниченном носителе prime-сумма конечна и финитная позитивность доказуема.

#### Уровень 2: K-dependent uniform axiom (DEPRECATED)
`Q3/Axioms.lean:692` — `Q_nonneg_on_atoms_of_A3_RKHS_axiom`:
```lean
axiom Q_nonneg_on_atoms_of_A3_RKHS_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  A3_bridge_data K → RKHS_contraction_data K →
  ∀ g ∈ AtomCone_K K, Q g ≥ 0
```
Помечена `DEPRECATED`. Это формулировка которую видел другой Claude осенью 2025.

#### Уровень 3: PRIMARY uniform axiom — RH-эквивалент (вот это Gate)
`Q3/Axioms.lean:704` — `Q_nonneg_on_atoms_uniform`:
```lean
axiom Q_nonneg_on_atoms_uniform :
  A3_bridge_data_uniform → RKHS_contraction_data_uniform →
  ∀ K ≥ 1, ∀ g ∈ AtomCone_K K, Q g ≥ 0
```
**Помечено как:** "core result, December 2025 primary formulation".

`∀ K ≥ 1` **перед** конусом-квантором = **равномерная позитивность по K** = `m(K) ≥ m₀ > 0 ∀K` из Теоремы 4 = **Gate ⟺ RH**.

#### Это правильная архитектура

Ылша **уже изолировал RH-вес** как открытую Tier-1 axiom `Q_nonneg_on_atoms_uniform`. Это **не самообман**, это **честная декомпозиция**:
- Финитная позитивность на одном K — инженерия (2 sorry в K-fixed theorem)
- Равномерная позитивность ∀K — открытая axiom с понятным паспортом RH

Это **в точности** структура «Honest deliverable» из разбора другого Claude:
- Часть I-III (безусловно) = K-fixed + finite certificates
- Часть IV (открыто, красная табличка) = `Q_nonneg_on_atoms_uniform`

#### RESOLVED: Fourier path = Исход 3 (третий путь) + распылённый Gate

Проверка `rg` (2026-06-10) показала: Fourier path **не вызывает** `Q_nonneg_on_atoms_uniform`. Имеет **свой набор axioms** — и среди них **жив `prime_term_le_at_t_critical_axiom`** (`Q3/Proofs/Q_nonneg_t_critical.lean`). Это **четвёртая incarnation ρ_cap**, никогда не уходила, просто переименована/перенесена в upstream chain. Atlas не дал её спрятать как scalar mirror, но и не **закрыл** её.

**Распределение RH-веса (распылённый Gate):**

| Locus | Где | Class |
|---|---|---|
| `prime_term_le_at_t_critical_axiom` | `Q_nonneg_t_critical.lean` | **K-pointwise cap (4-я incarnation ρ_cap)** |
| `A3_bridge_axiom K hK` | `A3_bridge.lean` | K-dependent Tier-1 (часть transfer chain) |
| `Q_nonneg_on_BaseAtomCone_axiom` | `Q_nonneg_base_atoms.lean` | τ=0 corollary axiom |
| `Q_nonneg_on_atoms_uniform` | `Axioms.lean:704` | **K-uniform statement** = RH-equivalent (alternative formulation) |
| `MainClean.lean:59` sorry | clean main chain | **K → ∞ exhaustion** (Step 34 место) |

**Все пять локусов эквивалентны через Теорему 4.** Это не нелегальная склейка — это **несколько синонимичных формулировок** одной гипотезы. Архитектурно **честно открыто**, но **сложность не одна** — она **расщеплена**.

`A1_density` **не несёт RH-веса** — у него стандартная uniform continuity для finite K, без uniform-по-K bound. Это инженерия (2 sorry в `_integrated.lean`).

**Что это значит для action items:**

1. **Naming hygiene (§0.1) становится острее.** Имя `RH_proven_clean` для теоремы, чьи зависимости включают `prime_term_le_at_t_critical_axiom` + sorryAx — это удвоенный самообман. Должно быть `RH_conditional_on_Gate_clean` или explicit docstring с **именами всех пяти локусов**.

2. **F2 margin(K) audit становится приоритетом #2** — нужно увидеть какая из 5 формулировок «легче атакуется» эмпирически. Margin curve работает с K-pointwise данными и автоматически индексирует pointwise vs uniform gap.

3. **Connes–Consani–Sonin attack (см. §1.5 ниже) становится приоритетом #3.** Если она работает за пределами prime-free зоны (до √2 dilation), то её механизм **должен ломаться** где-то на одном из 5 локусов — и какой именно покажет где live frontier за пределами текущей Q3 architecture.

### 3. `Q3.Clean.Weil_criterion` — нужен паспорт нормализации

Аксиоматизация классической теоремы (Weil 1952 explicit formula) в Tier-1 — легально и стандартно. Но:
- В Mathlib **её нет** — формализация явной формулы Вейля = отдельный большой проект
- Нужна **точная ссылка** на источник: Weil 1952 («Sur les "formules explicites" de la théorie des nombres premiers») и/или Bombieri 2000 («The Riemann Hypothesis», CMI millennium problem statement) — какая нормализация используется
- Нужна **проверка** что формализованная *формулировка* в Lean совпадает с литературной (signs, normalizations of measures, sum over all zeros vs nontrivial zeros, etc.)
- Ошибка в нормализации аксиомы **обесценит всю цепь**, а её никто не проверяет потому что «это же классика»

**Задача:** ревью Lean-statement `Q3.Clean.Weil_criterion` с приведённым источником + side-by-side сравнение с published formulation. Один параграф в `Q_STAR_DEFINITIONS.md` или отдельный `WEIL_CRITERION_PASSPORT.md`.

### 4. Sign crisis −101.66 — нужен post-mortem (бесплатный consistency-тест)

Centered-route деактивирована (правильно), canonical = `step22PositiveAxisOmegaAProfile` (правильно). Но **что такое centered convention математически?** Чем был −101.66?
- Ошибка знака Ω при centering?
- Другая квадратичная форма, для которой негативность *ожидаема* (например другой Toeplitz после shift)?
- Численный артефакт (round-off от больших cancellations)?

**Это бесплатный тест.** Если расхождение двух конвенций **нельзя объяснить выводимым преобразованием** (raw → centered = explicit unitary / scaling / shift), значит где-то в ассемблере живой баг, который Step22-деривация могла унаследовать. И тогда canonical convention ловит ту же ошибку другой стороной.

**Задача:** один абзац «Post-mortem: centered-positive-A route» в `q3.lean.aristotle/docs/INSIGHTS.md`:
1. Что такое centered convention формально (operator/formula)
2. Какое преобразование переводит raw → centered (если есть)
3. Если есть — почему −101.66 vs canonical +X согласовано (или нет)
4. Если нет — записать как открытый вопрос + workaround «not used in main chain»

### Классификация всех открытых элементов

| Элемент | Класс | Действие |
|---|---|---|
| 2 sorry в `A1_density_WK_axiom` | инженерия/анализ, безусловно доказуемо (но не бесплатно) | стандартный grinding по протоколу sorry resolution |
| 2 sorry в K-fixed `Q_nonneg_on_atoms` | финитная инженерия (квантор = на конусе, но один K) — доказуемо | стандартный grinding через A3 bridge + RKHS contraction |
| `Q_nonneg_on_atoms_uniform` axiom | **RH-эквивалент** (= Gate Теоремы 4) — Tier-1 open | красная табличка в Часть IV honest paper, F2 audit margin(K) |
| `Weil_criterion` axiom | классика, формализуемо, нужен паспорт нормализации | §0.3 source + side-by-side |
| Step 34 exhaustion | RH-вес живёт здесь и/или в Q_nonneg (Вариант B) | F2 audit margin(K) до инвестиции в Step34 |
| `RH_proven_clean` naming | оксюморон с `sorryAx` | §0.1 rename / docstring warning |

**Если после §0.2 окажется что ни один элемент не выглядит RH-весовым** — это не победа, а **сигнал тревоги**. Сложность не исчезает. Значит дыра замаскировалась, и искать её надо в:
- Формулировке `Weil_criterion` axiom (тихая ошибка нормализации)
- Или в тихом усилении density theorem (`A1_density_WK_axiom` теорема может скрытно зависеть от RH через test class)
- Или в самом квантор-переходе «atoms ⇒ full cone»

### Применить §0 ДО распространения брифинга как канона

Эти 4 пункта — не «улучшения», а **must-fix** перед тем как briefing цитируется в репо как STRATEGIC_CONTEXT. Без них он сам становится источником self-deception ровно того типа, который Atlas запрещает.

---

## Что говорит разбор другого Claude (компактно)

### Доказанные результаты (безусловно)

- **Лемма 1**: `S(X) = Σ Λ(n)/√n ≥ 1.8√X − C` (Чебышёв, партиальное суммирование)
- **Предложение 2**: uniform cap `T_P ⪯ ρ·T_A` с ρ<1 равномерно по K **не существует**. Плато-тест φ_K даёт `P(φ_K) ≥ 3(K−4)e^{K/2}` vs `A(φ_K) ≤ CK` ⇒ `sup P/A → ∞`. Контрпример — элемент собственного словаря (треугольник Фейера, плато-автокорреляция).
- **Предложение 3**: расщепление `dψ(x) = dx + d(ψ(x)−x)` показывает что вся опасность сидит в `R(φ) := 2 ∫_2^∞ x^{−½} g(log x) d(ψ(x)−x)`. Boundary-null убивает главный член правильно.
- **Теорема 4** (закон сохранения сложности): **Gate ⟺ RH**. Доказать равномерный `m(K) ≥ m₀ > 0` = доказать RH. Любой синтез из имеющихся блоков **содержит дыру** (Предл. 2 — теорема).

### Что НЕ доказуемо сегодня

Безусловная Gate. Никем. Размеры расходятся как `e^{K/2}/K`, спасает только компенсация знаков в `ψ(x)−x`, а это и есть распределение нулей. Круг замкнут.

### Honest deliverable (REVISED 2026-06-10 — Opus 5 ruling)

**КРИТИЧНО:** «τ=0 case + extension assumption» **не годится**. Атомы с τ=0 не плотны ни в каком разумном тестовом классе (плотность A1 требует сдвигов τ). «Extension» = безымянная переадресация RH-веса. Заголовочная гипотеза статьи должна быть **`Q_nonneg_on_atoms_uniform`** — одна именованная река, не τ=0 + extension.

**Архитектурный direction:** Вариант A (статья) и Вариант B (semi-local Sonin reservoir research) **не альтернативы**. Делаются параллельно. Paper — A; CC pivot — B как research thread.

**Структура paper (одна река):**

```
Гипотеза статьи:       единственная — Q_nonneg_on_atoms_uniform
                       (∀ K ≥ 1, ∀ g ∈ AtomCone_K K, Q g ≥ 0)
                       Остальные локусы либо leмmas, либо вне цепи.

Карантин:              prime_term_le_at_t_critical_axiom помечена
                       numerically falsified, restricted к BaseAtomCone (τ=0),
                       исключена из main chain.

Часть I  (безусловно): framework + Предл. 2 (falsification) + Предл. 3 (структура)
Часть II (безусловно): finite certificates machine-checked + margin(K) + spectrum tail
Часть III (условно):   Q_nonneg_on_atoms_uniform ⇒ RH — полная строгая цепь
Часть IV (открыто):    Q_nonneg_on_atoms_uniform — красная табличка
Directions (1 абзац):  semi-local Sonin reservoir = research target
                       (Connes-Consani-Moscovici 2023, forthcoming Jacobi paper).
                       Если построится — следующая статья.
```

Это **публикуемо**, аналог «модулярность ⇒ Ферма» Уайлса. **Paper-структура не зависит ни от F2, ни от судьбы pivot'а** — только от коллапса 5 синонимов в одну реку.

### Lean strategy (REVISED 2026-06-10 — Opus 5 ruling)

**Полная формализация CC-математики НЕРЕАЛИСТИЧНА и НЕ НУЖНА.**

В Mathlib: Hilbert spaces, compact self-adjoint operators + spectral theorem, Fourier/Plancherel. **НЕТ**: trace-class в нужной общности (Schatten фрагментарны), prolate spheroidal functions (Slepian) — многолетний проект.

**Двухуровневая схема:**

- **CC-математика** живёт в **прозе** (paper Часть I/IV) — proof в литературе, цитата.
- **Lean** оформляет CC-вход как **одну новую axiom-гипотезу** (replacement для ложной prime axiom):

```lean
/-- Connes-Consani-motivated structural replacement.
    Open Tier-1 hypothesis. Status: open, CC-motivated.
    Replaces falsified prime_term_le_at_t_critical_axiom.
    See arXiv:2006.13771 + arXiv:2310.18423. -/
axiom semi_local_reservoir_dominates : ...
```

Скелет «гипотеза ⇒ RH» Lean уже умеет — текущая архитектура с **одной** рекой вместо пяти и **без** ложной axiom. Формализация самой CC-математики — опциональный side project, **в критический путь не ставить**.

### Итог одной строкой (Opus 5 verdict 2026-06-10)

> **Paper — по варианту A с единственной гипотезой `Q_nonneg_on_atoms_uniform` (НЕ τ=0); F2 — добавить cross-check с repo-генератором (БЛОКЕР) и deflation `m_codim(K)` (главный сигнал); Lean — CC входит как одна axiom-гипотеза, не как формализация.**

---

## Как это связано с актуальным кодом

### Gate в текущих координатах

**ВНИМАНИЕ:** эта секция была переписана после §0.2 + §−1 + `#print axioms` ground truth. Если читаешь briefing впервые — читай §0.2 и §−1 как авторитет, эту секцию как historical context.

Картина по результатам ground truth (`#print axioms Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS`):

- Active Fourier RKHS chain зависит от **единственной** non-standard axiom: `prime_term_le_at_t_critical_axiom` (плюс propext, Classical.choice, Quot.sound).
- Эта axiom **ЛОЖНА** по `verify_variant_b.py` (counterexample τ=1.69, Q=−911). См. §−1.
- K-fixed `Q_nonneg_on_atoms` theorem — финитная инженерия, **НЕ Gate**. Quantifier на конусе, но для одного фиксированного `t0_critical`.
- `Q_nonneg_on_atoms_uniform` (Axioms.lean:704, `∀ K ≥ 1, ∀ g ∈ AtomCone_K K, Q g ≥ 0`) — **uniform** по K, в точности RH-эквивалентное утверждение Теоремы 4. **Это Gate.**
- `A1_density_WK_axiom` — 2 sorry в `_integrated.lean`, инженерия для finite K density, **не несёт RH-веса**.
- `MainClean.lean:59` sorry (legacy Q3.Clean) — K → ∞ exhaustion, **не собирается** independent of A1_density issue.

`Q_nonneg_on_atoms` (K-fixed theorem) и `Q_nonneg_on_atoms_uniform` (open axiom) — **разные утверждения**, нельзя путать. K-fixed закрыт через Fourier path (= conditional на ложную prime axiom), uniform остаётся открытой Tier-1 axiom.

**Gate = `Q_nonneg_on_atoms_uniform`.** Финитная позитивность через Fourier path **формально** валидна, но **conditional на ложь** → отравлена.

### Step33 contract (из q3-psdpd-step33-bootstrap skill)

3 gates:
- **33A**: construct `ActiveCenteredCoeffEntryHboxCert` ← текущая работа
- **33B**: derive finite analytic Weil positivity from certified centered coeff blocks
- **33C**: package singleton `DirectedCertFamily` handoff

Step33A.1-A фронт-линия — raw-Omega A finite/tail bounds certs. Live artifacts:
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorPayloadImport.lean`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkIntegralBoundsImport.lean`
- `Q3/Proofs/PSD_CenteredCoeffAnalyticABoundsBackend.lean`

Open generated layer: 2392-cell payload через `RawOmegaATaylorModelCertificate.Valid` instances.

### Связь Step33 ↔ Gate

Step33 закрывает **finite block** (Atlas: Finite-to-global wall). Это **не** глобальный Weil positivity. Step34 — это перенос (continuity + exhaustion). Step35 — global RH theorem.

Step33A — это **конкретные cells** в конкретных payloads. Каждый cell certified Taylor model — это маленький кирпичик. Когда все certified — `ActiveCenteredCoeffEntryHboxCert` builds, далее по contract.

**Где здесь Gate:** на финитном блоке Gate тривиально выполняется (Предл. 2 Bonus: при `supp g ⊂ (−log 2, log 2)` prime-сумма пуста, W ≥ 0 безусловно). Конечные сертификаты на малых K проходят при любой судьбе RH. Step33 даёт **инфраструктуру** но **не доказывает Gate** напрямую — Gate появится при exhaustion на Step34.

То есть: **Step33 = инфраструктура для условной теоремы "Gate ⇒ RH"**. Сам Gate — Step34, и его честный путь — F2 audit (margin curve) сначала, чтобы понять плато/распад.

### Sign crisis закрыт правильно

```text
canonical finite Weil convention: C_rawOmega = A_rawOmega - P
canonical A source: step22PositiveAxisOmegaAProfile
```

Другой Claude писал: "правильную A надо вывести из формулы Вейля, а не выбрать ту, что проходит". Ровно это и сделано — A зафиксирована через Step22 derivation (`step22PositiveAxisOmegaAProfile`), не через позитивность. Centered positive-A wrappers остаются как inactive compiled support — для свободы маневра.

---

## F2 margin(K) audit (диагностический Python код)

Параллельно с Step33A работой — стоит запустить F2 диагностику. Это **не доказательство**, а numerical curve чтобы понять плато/распад margin(K). Если плато — Gate жив и Step34 имеет смысл. Если распад к нулю — Gate мёртв в текущей формулировке.

### Setup

```bash
# Если на Linux (nala):
sudo nala install python3-venv
python3 -m venv ~/.venvs/f2 && source ~/.venvs/f2/bin/activate
pip install numpy scipy mpmath sympy tqdm matplotlib pandas primesieve gmpy2

# Если на macOS Apple Silicon:
uv venv ~/.venvs/f2 && source ~/.venvs/f2/bin/activate
uv pip install numpy scipy mpmath sympy tqdm matplotlib pandas primesieve gmpy2
```

### Critical parameter (НЕ перепутать)

```
K_max = (1/2) · (log(MAX_PRIME) − (k+1)·ℓ)
```

| k | ℓ | W = (k+1)ℓ | K_max @ MAX_PRIME=1e8 |
|---|---|---|---|
| 11 | 1.0 | 12 | **3.2** ← смерть пилота |
| 11 | 0.5 | 6 | 6.2 |
| 11 | 0.25 | 3 | 7.7 |
| 9 | 0.25 | 2.5 | 7.9 |

**Дефолт: `ℓ = 0.25`** (НЕ 1.0). При ℓ=0.25 honest exact range K=2..7 при sympy, K=2..10.5 при primesieve (MAX_PRIME до 1e12).

### Reuse from repo

```text
КОНТЕКСТ РЕПО: ~/Documents/GitHub/rh_lean_01_2026/ доступен.
Прочесть:
- q3.lean.aristotle/docs/INSIGHTS.md — конвенции ℓ, узлы u_j, степень k, cutoff
- Генераторы payload/CSV для A, P, P0, Q в scripts/ — переиспользовать их конвенции
- step22PositiveAxisOmegaAProfile — canonical A source, использовать её формулировку Ω(t) = Re ψ(¼ + it/2) − log π
- Существующий refined generator: scripts/q3_psdpd_step33_a_refined_subchunk_candidate_overlay.py
  — паттерн чтения от него
Standalone модель — fallback если эти файлы не читаются.
```

### Модель

- Базис: `ψ_j(u) = ℓ^{−½} η_k((u−u_j)/ℓ)`, η_k — кардинальный B-spline степени k (k=11 primary, k=9 control), узлы u_j равномерно на [−K,K] с шагом ℓ/4
- `r_k(x)` = автокорреляция η_k (B-spline степени 2k+1, sympy/scipy точно)
- Gram: `G_ij = r_k((u_j − u_i)/ℓ)`
- Prime: `P_ij = Σ_{p,r: r log p ≤ 2K + 2ℓ} (log p / p^{r/2}) · [r_k((u_j − u_i − r log p)/ℓ) + r_k((u_j − u_i + r log p)/ℓ)]`
- **Exact mode: primesieve streaming, НЕ sympy.primerange** (sympy мёртв на 1e8+)
- Arch: `A_ij = (ℓ/2π) ∫ Ω(t) |Ê_k(ℓt)|² e^{it(u_j−u_i)} dt` с Ê_k = sinc^{k+1}, Ω(t) = Re ψ(¼+it/2) − log π через mpmath.digamma. **Считать в ДВУХ конвенциях** (raw positive-axis и centered) для consistency check с canonical в репо
- Boundary: `Q = 2×n`, `Q_{+,j} = e^{u_j/2}`, `Q_{−,j} = e^{−u_j/2}`

### Вычисление m(K)

1. ker Q через SVD: матрица N (n × (n−2))
2. `C' = Nᵀ(A−P)N`, `G' = NᵀGN`
3. `m(K) = scipy.linalg.eigh(C', G')` — минимальное обобщённое eigenvalue
4. Опционально: `R_κ = A − κP0`, `D_θ = C − θR_κ` если P0 доступна

### Sanity checks (must pass или fail with error)

- `K < log(2)/2` → P пустая → m(K) = чистый arch floor, должен быть > 0
- Симметрия A, P, G до 1e−12; G ≻ 0
- `Im(A) < 1e−10`
- Spot-check P_ij на одной паре с прямой mpmath суммой (mp.dps=50)

### Compact support guard (КРИТИЧНО при K>10)

Для каждой пары (i,j) суммировать только `p^r` с `|u_j − u_i ± r log p| ≤ (2k+2)ℓ` (компактный носитель r_k). Иначе K=20 нереально по памяти.

### Approx mode (K=10..20)

Через интегрирование по частям: P-вклад = аналитический главный член (quad) + флуктуация против ψ(x)−x. Флуктуацию по явной формуле с первыми N нулями Римана (таблицы Одлыжко). CSV маркировка: `prime_mode=zeros_truncated_N`. **Не смешивать с exact** в вердикте.

### Выход

`margin_audit.csv` колонки: K, n, dim_kerQ, lambda_min_C_raw, lambda_min_C_centered, lambda_min_R, lambda_min_D, cond_projected, tail_error_budget, net_margin, prime_mode, runtime_s

`margin_vs_K.png`: обе кривые (raw/centered) + y=0 горизонталь, symlog по |m|

Вердикт в конце: **PLATEAU / DECAY / NEGATIVE** для каждой конвенции

### Финальные команды

```bash
python f2_margin_audit.py --k 11 --ell 0.25 --K-min 2 --K-max 10 --prime-mode exact
python f2_margin_audit.py --k 9  --ell 0.25 --K-min 2 --K-max 10 --prime-mode exact
```

### Что смотреть на выходе

1. **Какая конвенция A когерентна** — той, что выведена из явной формулы (step22PositiveAxisOmegaAProfile), обязана совпасть с одной из raw/centered. Empirical sign crisis closure.
2. **Форма кривой margin(K)**:
   - PLATEAU = структура Connes-Consani расширяется на semi-local (есть стабильное compact perturbation с одним λ > 1); Step34 имеет смысл, искать равномерную лемму
   - DECAY = добавление prime contributions ломает single-dangerous-eigenvalue structure; нужно либо больше conditions, либо другая декомпозиция
3. **cond_projected** — если взрывается с K, margin может быть артефактом координат, нужна перенормировка узлов.

### ⚠️ MUST-FIX BEFORE LAUNCH (Opus 5 critique 2026-06-10) — F2 BLOCKER

Atlas Matrix-Identification Wall **применима к самому F2**. Standalone-модель F2 строит A, P, G по собственным формулам. Если её конвенции расходятся с repo-payload (`step22PositiveAxisOmegaAProfile`, нормировка `ℓ^{−1/2}`, шаг `ℓ/4`), вся кривая `margin(K)` будет про **другой объект**, чем Lean-цепь — и любой вердикт PLATEAU/DECAY будет недействителен для проекта.

**MANDATORY первый прогон перед любой margin серией:**

```python
def cross_check_with_repo(K_test=4, B_test=2.5):
    """Per-element comparison F2 vs repo-generator on overlapping block.
    
    Reads repo-side payload (e.g. via step22PositiveAxisOmegaAProfile output CSV),
    computes F2-side same block, compares to 1e-10.
    FAIL = abort F2 — нет смысла гонять кривую если объект другой.
    """
    A_f2 = compute_arch_matrix(K_test, B_test, mode='step22')
    P_f2 = compute_prime_matrix(K_test, B_test)
    A_repo = load_repo_arch_payload(K_test, B_test)
    P_repo = load_repo_prime_payload(K_test, B_test)
    assert np.max(np.abs(A_f2 - A_repo)) < 1e-10, "A mismatch — F2 не про тот объект"
    assert np.max(np.abs(P_f2 - P_repo)) < 1e-10, "P mismatch — F2 не про тот объект"
```

Если repo-payload недоступен в нужной форме — вывести один элемент A[i,i] и P[i,i] в Lean через `#eval` и сравнить. Cross-check блокирует всё остальное.

### Третий эксперимент — DEFLATION (most informative signal)

Opus 5 указал что эксперименты A (полный хвост) и B (Q2 vs Q3) **не дают напрямую** ключевой сигнал. Самый информативный — **m_codim(K) после удаления плохих направлений**:

```python
def deflation_audit(C_prime, G_prime, K, n_remove=3):
    """λ_min after orthogonal projection out of bottom-n eigenvectors.
    
    If m(K) decays but m_codim(K) plateaus — strongest possible signal that
    positivity holds modulo finite codimension. This is Step34 in passable form.
    """
    eigvals, eigvecs = scipy.linalg.eigh(C_prime, G_prime)
    bad_vecs = eigvecs[:, :n_remove]
    # Orthogonal complement w.r.t. G-inner product
    n = C_prime.shape[0]
    P_bad = G_prime @ bad_vecs @ bad_vecs.T @ G_prime
    P_good = np.eye(n) - bad_vecs @ bad_vecs.T @ G_prime
    C_codim = P_good.T @ C_prime @ P_good
    G_codim = P_good.T @ G_prime @ P_good
    # Eigenvalue on the codim subspace
    eigvals_codim = scipy.linalg.eigh(C_codim, G_codim, eigvals_only=True)
    return {'m_K': eigvals[0], 'm_codim_K': eigvals_codim[n_remove],
            'n_remove': n_remove}
```

**Самый сильный возможный исход:** `m(K)` распадается, **но** `m_codim(K)` — плато при `n_remove = O(1)`. Это «позитивность по модулю конечной коразмерности» — точно проходимая форма Step 34. Эксперименты A/B этот сигнал **напрямую не видят**.

Цена: три строки numpy поверх уже посчитанного спектра.

### Микро-добавка к B — Rayleigh integral row projection (секунды)

Прежде чем гонять полный 3-row, посчитать `Rayleigh = vᵀCv / vᵀGv` где `v` = projection of integral row `q0` onto ker Q. Если плохое направление **и есть** CC-направление, это видно за секунды из уже готовых матриц:

```python
v_integral_in_kerQ = N @ N.T @ q0_row.T
rayleigh_integral = (v_integral_in_kerQ.T @ C_prime @ v_integral_in_kerQ) / \
                    (v_integral_in_kerQ.T @ G_prime @ v_integral_in_kerQ)
# Сравнить с λ_min(C', G'). Если близко — CC-инсайт работает.
```

### Connes-Consani lens (REVISED 2026-06-10 после Opus 5 критики)

**ВАЖНО:** первая версия mapping табл инвертировала роли Sonin space (= **инструмент** в CC) и Arch floor (≠ инструмент). Поправленная картина в `connes_consani_sonin_research_node.md` Phase 2. Что F2 должен **дополнительно** сообщить:

**A. Полный нижний хвост спектра (не только λ_min):**

```python
spectrum_audit(C', G', K) → {
    n_negative,           # количество eigvals < 0
    n_small_positive,     # количество 0 < eigvals < 1e-2
    n_bad_for_CC,         # количество eigvals < 1 — "опасные" в смысле CC
    bad_localizations,    # узловые индексы u_j на которых сидят bad eigvecs
}
```

CC-сигнатура: `n_bad_for_CC` **стабильно O(1)** при росте K + локализация устойчива у края prime-окна.

**B. Q из 2 строк vs Q из 3 строк (воспроизведение CC-эффекта):**

```
2 rows:  Q_{+,j} = e^{u_j/2}, Q_{-,j} = e^{-u_j/2}
3 rows:  + Q_{0,j} = ∫ ψ_j  (для B-spline ≈ const row up to normalization)
                          (это analog условия ĝ(0) = 0 у CC)
```

Прогнать F2 **дважды**, side-by-side margin curves. Если `margin_3row[K]` качественно > `margin_2row[K]` при росте K — воспроизвели CC-эффект в packet basis. **Первый эмпирический мост** Q3 ↔ CC.

**C. Numerical falsifier для prime axiom (отдельный CSV):** см. блок ниже про `axiom_check_loop`. Если найдено ≥1 failure — axiom dead unconditionally, CC pivot обязателен.

### Выводы которые F2 НЕ дарит (правка к ранней формулировке)

- **PLATEAU + O(1) bad directions устойчиво** = **консистентно** с переносом CC-структуры, но **не доказательство**. Доказательство — только построенный semi-local Sonin резервуар.
- «margin падает → проблема не в P, а в спектре» — это **одно и то же сказанное дважды** (P и есть деформатор спектра). Не отдельные явления.

### Numerical falsification of `prime_term_le_at_t_critical_axiom` (added 2026-06-10)

§−1 brief показал: axiom утверждает `prime_term ≤ arch_term` для всех (K, B, τ) с |τ|+B ≤ K, **но репо знает что для τ > 0 axiom ложна** (verify_variant_b.py:572). F2 должен встроить explicit numerical test:

```python
def axiom_check_loop(K_range, B_range, tau_range):
    """Flag counterexamples to prime_term_le_at_t_critical_axiom."""
    failures = []
    for K, B, tau in product(K_range, B_range, tau_range):
        if abs(tau) + B > K: continue        # outside axiom domain
        prime = compute_prime_term(B, tau, t=T_CRITICAL)
        arch  = compute_arch_term(B, tau, t=T_CRITICAL)
        if prime > arch:
            failures.append({'K':K, 'B':B, 'tau':tau,
                             'prime':prime, 'arch':arch, 'margin':arch-prime})
    return failures
```

Запускается **до** margin curve. Если найдётся ≥1 failure — axiom dead, Connes-Consani-style pivot **обязателен**, не optional. CSV output: `axiom_falsifier.csv` отдельно от margin_audit.

---

## Что НЕ делать (Atlas walls + commitments)

- ❌ Не доказывать PSD в raw coordinates если route требует Gram correction (Coordinate wall)
- ❌ Не использовать positive numerical table как proof of imported prime form (Prime-side wall)
- ❌ Не сводить boundary-null к informal endpoint argument (Boundary leakage wall)
- ❌ Не fill P0 hbox fields weakening theorem statement (P0 enclosure wall)
- ❌ Не добавлять fake axioms / trusted payload shortcuts (Finite-certificate wall)
- ❌ Не утверждать что Step32 закрывает global RH (Finite-to-global wall)
- ❌ Не sweeping entries one by one в Step33A.1 (Scalar replay swamp wall) — compress первый: packet center delta + compact-support live prime-shift filter
- ❌ Не выдавать F2 margin curve за доказательство Step 34 — это диагностика
- ❌ Не coммитить в `Q3.Main` до Step35 (skill workflow rule #5)
- ❌ Не использовать `sorry`, `admit`, `exact?` в new code (skill guardrails)
- ❌ Не объявлять PLATEAU без понимания **какая структура его держит**

## PRO_REVIEW_REQUEST pattern

Если непонятна route choice или generated payload shape: append в `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/report.md` блок:

```text
PRO_REVIEW_REQUEST:
  date: <today>
  topic: <one line>
  context: <3-5 lines>
  decision needed: <specific question with options>
  blocking: <theorem name>
```

Это уходит к Louise/Pro chat (claude.ai Opus). Backend decisions от 2026-06-05 пришли таким путём (route C).

---

## Файлы для синхронизации

Перед стартом сессии прочесть в порядке:

1. `~/Documents/GitHub/rh_lean_01_2026/AGENTS.md`
2. `~/Documents/GitHub/rh_lean_01_2026/Q3_OBSTRUCTION_ATLAS.md` (7 walls + acceptance)
3. `~/Documents/GitHub/rh_lean_01_2026/SESSION_ENTRY.md`
4. `~/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md`
5. `~/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md`
6. `~/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/INSIGHTS.md` (Step33 entries)
7. `~/Documents/GitHub/rh_lean_01_2026/.agents/skills/q3-psdpd-step33-bootstrap/SKILL.md`

И этот файл — он не заменяет, а **синтезирует и связывает** Gate-разбор с актуальным состоянием.

---

## Source documents

- **Original Claude conversation** (340 lines): `~/Documents/GitHub/prowka-bot/Projects/q3-rh-gate-analysis/docs/source_chat_with_other_claude.md`
- **Genesis** (как родился этот проект): `~/Documents/GitHub/prowka-bot/Projects/q3-rh-gate-analysis/docs/GENESIS.md`
- **Project CLAUDE.md**: `~/Documents/GitHub/prowka-bot/Projects/q3-rh-gate-analysis/CLAUDE.md`
- **Memory**: `~/.claude/projects/-Users-emalam/memory/project_q3_rh_gate_analysis.md`

---

## Краткий итог одной фразой

**Step33 строит инфраструктуру для условной теоремы "Gate ⇒ RH" — это публикуемо. Сам Gate (= безусловная RH) останется открытой гипотезой, F2 margin(K) curve покажет насколько серьёзно её атаковать стоит, и аудит квантора `Q_nonneg_on_atoms` — первый пункт следующей сессии.**
