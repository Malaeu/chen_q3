# LINUX PREFLIGHT REPORT — GOAL058_SELECTED_FERRERS_H2A_FINAL_CONSUMER_PREFLIGHT

```yaml
REPORT_KIND: READ_ONLY_PREFLIGHT
TASK_ID: GOAL058_SELECTED_FERRERS_H2A_FINAL_CONSUMER_PREFLIGHT
PARENT_VERDICT: REQ-2026-08-26-L (commit 9f72b51a)
BASE_HEAD: 28df2481869eab257cc55420450ab192bec8f7e1
MODE: PAPER_AND_SOURCE_READ_ONLY
LEAN_EDIT_PERFORMED: false
NUMERICAL_PROBE_PERFORMED: false
RESULT_CODE: SELECTED_FERRERS_H2A_OR_THEOREM510_SINGLE_NEXT_NODE_LOCKED
DISCRIMINATOR_RESOLVED: BRANCH_A_WITH_ONE_PREDICATE_DEFINITION
THEOREM510_BRIDGE_IS_ASSEMBLY_ONLY: true
NEW_ANALYTIC_INPUT_REQUIRED: none
H2A_ITSELF_REMAINS_OPEN: true
```

## 1. Точный H2a-предикат отобранного шелла (RETURN 1)

Консюмер зафиксирован в скелете:

    Theorem510RealZeroBridge C H2aAt :=
      ∀ i, H2aAt i → Differentiable ℂ (C.Pstar.family i) →
        ZerosRealOn Set.univ (C.Pstar.family i)
    (CanonicalRHRouteSkeleton.lean:112-116)

Для отобранного шелла `C = D.canonicalApproximation`, `Index = ℕ`,
`parent = extract = id`, `C.Pstar.family k = D.centeredPstar k`
(G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:617-628).

ТОЧНЫЙ H2aAt, который нужен и достаточен:

    SelectedFerrersSimpleEvenGroundAt P k : Prop :=
      ∃ (ε : ℝ) (ξ : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ)
        (c : ℂ) (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
        (b : Module.Basis ι ℝ …квоциент по ker сдвинутой формы…),
        c ≠ 0 ∧
        1 ≤ ((selectedFerrersCofinalSourceData P).index k).N ∧
        Matrix.mulVec (ccmWeilMatFinite (…index k).m (…index k).N) ξ = ε • ξ ∧
        ccmEtaFinite (…index k).N ⬝ᵥ ξ = 1 ∧
        (∀ x, ε * (x ⬝ᵥ x) ≤ x ⬝ᵥ Matrix.mulVec (ccmWeilMatFinite …) x) ∧
        Module.finrank ℝ ((ccmWeilOpFinite … ).eigenspace ε) = 1 ∧
        (∀ n ∈ modeSet ((selectedFerrersCofinalSourceData P).index k),
          c_n … n = c * proposition59CCMCoefficient (…N) ξ n)

Читается так: в индексе `k` отобранная строка пробной функции с точностью до
ненулевого скаляра совпадает с ВЕЩЕСТВЕННЫМ нормированным простым
bottom-собственным вектором конечной матрицы Вейля. Это ровно slot H2a
(«simple even ground»), выраженный на литеральных объектах шелла; чётность
получается теоремой, а не постулируется.

## 2. Точные конечные объекты после реиндексации (RETURN 2)

| объект | точное имя | статус |
|---|---|---|
| носитель мод | `CCMModeFinite N`, `ccmModeFinite`, `ccmModeFiniteEquivIcc` | есть |
| матрица | `ccmWeilMatFinite mProject N`, оператор `ccmWeilOpFinite` | есть |
| сдвинутая форма | `ccmShiftedWeilMatFinite mProject N ε` | есть |
| нормировка | `ccmEtaFinite N ⬝ᵥ ξ = 1` | есть |
| отражение/чётность | `ccmReflectionEndFinite`, `ccmEigenvector_even_of_simple_eigenspace_and_normalized` | есть, ДОКАЗАНА |
| отобранная строка | `selectedFerrersFiniteCCMRow P k` (комплексная, `c_n` пробной функции) | есть |
| унитарность строки | `selectedFerrersFiniteCCMRow_unit` (`q* ⬝ q = 1`) | есть |
| кроссволк строки | `sourceOrderedCCMRawTransform_selectedFerrersFiniteCCMRow_eq_rawFplus` | есть |
| длина окна | `logLength i = Real.log i.m`, `ccmL m = Real.log m` — совпадают при `m = i.m` | есть |

КЛЮЧЕВОЙ ШОВ: отобранная строка КОМПЛЕКСНАЯ и принадлежит ПРОБНОЙ функции;
мост требует ВЕЩЕСТВЕННЫЙ bottom-собственный вектор. Вердикт запрещает
подставлять пробную строку вместо грунтовой без точного H2a-предиката —
именно поэтому предикат из §1 содержит связь `row = c · P59CCMcoefficient ξ`
как обязательное поле, а не выводится.

## 3. Существующая цепь G2/P59 до вещественности нулей (RETURN 3)

    H2a-данные (ε, ξ, bottom, simple, normalized, базис b)
      → ccmEigenvector_even_of_simple_eigenspace_and_normalized   [чётность]
      → ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
      → Proposition59GroundLagrangeZeroSetBridge
      ⟹ ZerosRealOn Set.univ (proposition59CCMTransform (ccmL m) N ξ)

Далее уже существующие переносы:

    rawFplus_eq_smul_ccmTransform_of_row  (D0RawTransformRowScaling.lean:62)
      rawFplus D i z = c · proposition59CCMTransform (logLength i) N ξ (−z)
    zerosRealOn_smul / zerosRealOn_congr / zerosRealOn_of_eq_smul
      (D0ZerosRealOnScalarTransfer.lean:34-55)

Отражение `z ↦ −z` сохраняет вещественность нулей тривиально
(`(−z).im = 0 ↔ z.im = 0`), центрирование `centeredPstar = (Ξ(0)/raw(0))·raw`
— ненулевой скаляр, гасится `zerosRealOn_smul`; знаменатель ненулевой по полю
`rawZeroNonzero` шелла.

## 4. Вердикт по дискриминатору и одна следующая теорема (RETURN 4)

ВЕТКА A подтверждается с одной оговоркой: **мост Theorem510 собирается без
новых аналитических входов**, но требует, чтобы H2a-предикат был ОПРЕДЕЛЁН
как в §1. Ни одного недостающего аналитического поставщика в цепи §3 нет;
все звенья kernel-green и публичны.

Единственная следующая публичная теорема:

    theorem selectedFerrersCofinalTheorem510RealZeroBridge_of_simpleEvenGround
        (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData) :
        Theorem510RealZeroBridge
          ((selectedFerrersCofinalSourceData P).canonicalApproximation)
          (SelectedFerrersSimpleEvenGroundAt P)

плюс определение `SelectedFerrersSimpleEvenGroundAt` в том же файле.
Доказательство — чистая сборка: распаковать предикат, получить
`ZerosRealOn` грунтовой трансформы через §3, перенести на `rawFplus`
крoссволком строки, отразить аргумент, домножить на центрирующий скаляр.

Файл: `q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTheorem510Bridge.lean`

## 5. Импорты (RETURN 5)

    Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMSourceRow
    Q3.Proofs.RouteB.Proposition59GroundLagrangeZeroSetBridge
    Q3.Proofs.RouteB.D0RawTransformRowScaling
    Q3.Proofs.RouteB.D0ZerosRealOnScalarTransfer
    Q3.Proofs.RouteB.CanonicalRHRouteSkeleton

Все имена внешних лемм проверены `rg` по исходникам с указанием файла и
строки (см. §2–§3). UNVERIFIED_EXTERNAL_NAME: нет.

## 6. CLOSES / OPENS (RETURN 6)

CLOSES при исполнении: `THEOREM510_REAL_ZERO_BRIDGE` (условно, на
предикате H2a отобранного шелла).
OPENS: ничего нового. `SLOT_H2A_SIMPLE_EVEN_GROUND` остаётся ОТКРЫТЫМ и
после этого узла — он становится ЕДИНСТВЕННОЙ аналитической стеной крыши;
предикат §1 фиксирует ровно то, что должен поставить будущий узел H2a.

Для справки: абстрактный движок H2a уже существует и kernel-green —
`H2a_SimpleEvenGround_FromPenaltyCoercivity` (H2aPenaltyCoercivity.lean:395),
он даёт простоту, зазор и J-чётность нижнего обобщённого собственного
значения из penalty-сертификата `K − βG + τ(Gq)(Gq)* ⪰ 0` при `a < β`.
Недостающее для H2a — не движок, а конструкция конкретной четвёрки
`(G_k, K_k, J_k, q_k)` и проверенный сертификат на отобранном расписании.
Это следующий фронт после моста, и он НЕ входит в предлагаемую транзакцию.

## 7. Код (RETURN 7)

SUCCESS_CODE: SELECTED_FERRERS_H2A_OR_THEOREM510_SINGLE_NEXT_NODE_LOCKED
