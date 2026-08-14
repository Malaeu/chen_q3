# Goal 058 G3 post-inertia source crosswalk — Mythos verdict

Source: visible completed response in the existing Mythos/Claude phase chat on
2026-08-14.  The text below is line-normalized from the browser response; it is
not represented as a byte-exact downloaded artifact.

Прочитано с живого дерева (146 строк, пин `496c907c`, carrier
`c461959f`). Дельта впечатляет: моя Штурм-голова доказана, и поверх неё уже
стоит инерционная лестница Шура — строгий порядок по Λ, одномерные ядра, метка
«Λ-порядок ⟺ порядок `negativeCount`». Отвечаю по шести пунктам.

## 1. PRIMARY

`C_SOURCE_ENDPOINT_COUNTS_ON_LITERAL_SCHUR` — концевые счёты на обоих краях
пинованного окна Бонами–Каруи.

Не A и не B, и вот решающий довод: инерционная метка превращает всю задачу
«существование + порядок + идентификация» в два числа — `negativeCount` на
нижнем крае окна и на верхнем. Якорь `negCount = 0` внизу плюс
`negCount = 3` вверху плюс уже доказанные «переход через корень поднимает
индекс» дают разом: существование ровно трёх чётных корней в окне, их порядок
и внутренние метки 0, 1, 2 — третий корень идентифицирован механически.

Конструктор A для маркировки становится не нужен (он останется нужен позже для
самих объектов ψ, питающих `ProlatePair` — другая задача); кроссволк B без
якоря вообще не умеет метить. Причём равенство `= 3` сверху, а не `≥ 3`,
закрывает и дыру вырожденных переходов: сумма скачков зажата сверху общим
счётом, три корня при скачках `≥ 1` и тотале 3 форсируют скачки ровно по
единице — компаньон-лемма о точности скачка не нужна.

## 2. Предложенные головы

Обе задуманы как производители: счёт доказывается, не биндится.

```lean
theorem d0Mode4Schur_negativeCount_eq_zero_at_windowBottom
    (K : ℝ) (hK : K ∈ sourceKWindow) :
    negativeCount (d0Mode4SchurMatrix K (windowBottomΛ K)) = 0

theorem d0Mode4Schur_negativeCount_eq_three_at_windowTop
    (K : ℝ) (hK : K ∈ sourceKWindow) :
    negativeCount (d0Mode4SchurMatrix K (windowTopΛ K)) = 3
```

`windowBottomΛ` / `windowTopΛ` — явные константы из pin-пакета (верх —
`20 + ε` в dimensionless-Λ, из eq. (8) Бонами–Каруи при `n = 4`, физическая
страница 5). Механизмы: низ — диагональная доминантность/Гершгорин на
литеральных элементах (формулы на диске); верх — три явных чётных
вектора-свидетеля отрицательности плюс позитивность на дополнении. Биндер
`K ∈ sourceKWindow` обязателен — счёты нужны на всём source-окне, не в одной
точке.

## 3. Как потребляется инерционная метка

НЕТ, трёх упорядоченных корней недостаточно; стартовый концевой счёт остаётся
несущим. Метка даёт только относительный порядок `negativeCount`-ов; без
якоря «внизу ноль» три корня могут нести метки 5, 6, 7 — если ниже окна
прячутся непойманные корни. Absolute labeling = якорь + скачки; якорь и есть
опция C. Больше того: с двумя концевыми счётами конструкция корней перестаёт
быть входом — она становится выводом.

## 4. Разделение

Это действие поставляет только ODE/index-сторону — существование и внутреннюю
маркировку третьего чётного Schur-корня (метка `negCount = 2`). Restricted
finite-Fourier eigenrelation — вклад ноль, пакет отдельный (Osipov Thm 3 /
Slepian, фаза `i^n`).

Честная оговорка к имени стопа: внешняя идентификация «это есть `ψ₄`
классиков» требует ещё crosswalk-а Schur-корень ↔ классический спектр.
Предложенные головы говорят о Schur-объектах и метках — nonclaim
`NO_INDEX4_IDENTIFICATION_YET` снимается только до уровня «внутренний индекс
2», внешнее имя ждёт crosswalk-а. Это первая само-атака.

## 5. Aristotle

ДА — но только на нижний якорь. Он bounded: конечная матричная алгебра,
Гершгорин, всё на диске. Верхний счёт требует выбора свидетелей — творческий
шаг, Aristotle там утонет; это Codex-local leaf следом.

```text
OWNED FILE: Q3/Proofs/RouteB/D0Mode4SchurWindowBottomAnchor.lean
ALLOWED IMPORTS: D0Mode4Schur* family files, Mathlib matrix/quadratic-form API.
TARGET: d0Mode4Schur_negativeCount_eq_zero_at_windowBottom,
  via diagonal dominance => PosDef => negativeCount = 0.
PLANTS:
  P1 windowTop mutant must FAIL — ANCHOR_NOT_AT_TOP;
  P2 K outside sourceKWindow with broken dominance must fail — K_WINDOW_REQUIRED;
  P3 sign-flipped offdiagonal mutant must break dominance — DOMINANCE_PLANT.
AXIOM GATE: [propext, Classical.choice, Quot.sound].
SUCCESS: SCHUR_WINDOW_BOTTOM_ANCHOR_PROVED.
TYPED STOPS: STOP_ENTRY_FORMULAS_MISSING; STOP_NEGCOUNT_API_MISSING.
SUBMIT ONLY via Codex fill-sorries pipeline.
```

## 6. Само-атаки

1. Категорная: метки Schur-корней не равны именам `ψ_n` без crosswalk-а —
   принято, героев не называем, nonclaim стоит.
2. Объектная: окно Бонами–Каруи сформулировано для истинных `χ_n(c)`;
   использовать `20` как верх окна для Schur-счётов легально только как выбор
   диапазона вычисления, не как спектральный факт. Предложенные головы это
   соблюдают: окно входит константой, не гипотезой о спектре.
3. Доменная: если верхний счёт при каком-то `K` из окна окажется 4, а не 3 —
   это не провал, а находка (лишний корень в окне); прекоммит:
   `WINDOW_COUNT_SURPRISE` с обязательной публикацией числа, без подгонки ε.

## Наименьшее исполнимое действие

`[→CODEX]` Materialize `windowBottomΛ` / `windowTopΛ` / `sourceKWindow` as
explicit constants from the pin packet, then prove the lower anchor Codex-local
first (diagonal dominance is hours, not days); the Aristotle task above is an
authorized-shaped fallback if the `negativeCount` API resists; the upper-count
witness leaf follows as the next Codex-local step. Both endpoint theorems land
before any constructor work.

Nonclaims preserved: G1/G3 open; no Route B promotion; no PX/RH claim.

## Executor note before judge dispatch

The names `sourceKWindow`, `windowBottomΛ`, `windowTopΛ`, and
`d0Mode4SchurMatrix` in the proposed heads are architectural placeholders, not
verified current declaration names.  The current literal family is
`mode4HermitianSchurMatrix mProject Λ K`, where `mProject` is the source scale
and `K : ℕ` is the finite Schur dimension.  Proshka is asked to judge this
object/arity mismatch before any Aristotle submission or implementation.
