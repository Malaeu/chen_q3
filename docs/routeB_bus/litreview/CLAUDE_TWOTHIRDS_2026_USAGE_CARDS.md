# Claude / Anthropic, «More than two thirds of the zeros … lie on the critical line» + формализация

bib `CLAUDE-TWOTHIRDS-2026` · Zotero `ZMK5VP9N` · PDF `litreview/pdfs/` ·
сопутствующие: `ANTHROPIC-TWOTHIRDS-NOTE-2026`, `CLAUDE-TWOTHIRDS-EXPLANATION-2026`,
`CLAUDE-TWOTHIRDS-TRANSCRIPTS-2026`

Формализация: `https://github.com/anthropics/zeta-23-lean`, склонирована владельцем в
`/mnt/hdd01/Soft/GitHub/zeta-23-lean` (вне нашего репозитория).

---

## Карточка 1 — результат и при каком условии

**Что ДОСЛОВНО сказано** (абстракт):

> We prove unconditionally that `lim inf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2/3`, that at least
> `(2/3 − o(1))N(T,2T)` of the zeros are simple and on the critical line, and that at least
> `(5/6 − o(1))N(T,2T)` are distinct; with an optimised test family the three constants
> become `0.6725, 0.6725, 0.83625…`

> The Riemann hypothesis, classically needed to read the zero side as a positive sum over
> real ordinates, is replaced by **linear algebra applied to a finite compression of Weil's
> Hermitian form**: Sylvester's law of inertia (an off-line pair `{ρ, 1−ρ̄}` contributes a
> block of signature `(1,1)`) and a rank–trace inequality for Hermitian matrices, proved via
> von Neumann's trace inequality.

Аналитические входы: `[BGSTB24]`, `[GS25]`, `[GS26]`. Новое — линейно-алгебраическое
прочтение их суммы парной корреляции.

**Что даёт НАМ.** Прецедент: **конечная компрессия формы Вейля** используется как рабочий
объект, из которого извлекается безусловное утверждение о нулях. Наш `K_odd` — компрессия
той же формы в другом базисе.

**Чего НЕ даёт.** Их вопрос — сигнатура (сколько положительных/отрицательных направлений),
наш — пол (насколько положительна, с явной константой). Прямого переноса результата нет.

---

## Карточка 2 — устройство доказательства (§4, «zero side»)

**Что ДОСЛОВНО сказано** (§1.3):

> Rather than test for positivity on the whole space, we restrict `W` to a finite-dimensional
> family `V` of `d ≈ λN` test functions — modulated copies `ϕ(u)e^{iτ_k u}` of a fixed
> compactly supported window, with centre frequencies `τ_k` equispaced through `[T, 2T]` at
> the critical sampling density — and let `G̃` be the `d × d` real symmetric matrix of `W|V`.

> **(Z) Zero side.** … `G̃ = P + Q` where, by the functional equation, each distinct point on
> the critical line contributes to `P` a real rank-one nonnegative form and each off-line pair
> `{ρ, 1−ρ̄}` contributes to `Q` a form of signature `(1,1)`. Thus `P ⪰ 0` has rank at most
> `s`, the number of distinct on-line points; by Sylvester's law of inertia … `Q` has at most
> `p` positive eigenvalues, `p` the number of distinct off-line pairs; and
> `tr P ≤ N_on` and `N ≥ N_on + 2p`.

> **(P) Prime side.** By the explicit formula, `tr G̃` and `‖G̃‖²_F` are integrals …

> That the negative index of truncations of Weil's form counts off-line zeros is due to
> **Bombieri [Bom00]**; we use rank and positive index.

**Что даёт НАМ.** Явная схема: положительная часть ↔ нули на прямой, отрицательная ↔ нули
вне её, а связывает их след и норма Фробениуса, вычисляемые через явную формулу.

**Ограничение метода, названное ими самими** (§7.5): `rank P, n_θ⁺(G̃) ≤ d = λ⁻¹N(1+o(1))`,
поэтому при полосе `λ ≤ 1` потолок любого такого рассуждения — 100% при `λ = 1` и ничего
при `λ ≤ 1/2`.

---

## Карточка 3 — формализация: что в ней проверено

**Что ДОСЛОВНО сказано** (`AUDIT.md` репозитория):

> Declarations of new axioms (`axiom ...`) anywhere in the repository, counted on the sources
> with comments and docstrings stripped: **0**.

> Occurrences of the `sorry` token outside comments: **27**, all in the trusted challenge
> statement files … none under `Zeta23/` and none in any `Solution` file.

> Axiom audit: every line printed by the `#print axioms` commands below is exactly
> `[propext, Classical.choice, Quot.sound]` … in particular no `sorryAx` and no
> project-specific axiom.

Тулчейн: Lean `v4.33.0-rc2`, Mathlib pinned на `51e6992e`. Объём: 329 файлов, 103 067 строк.

**Что даёт НАМ — два приёма, которых у нас нет:**

1. **`comparator`.** Утверждения записаны в отдельных файлах-заявках с доказательством-заглушкой
   и сверяются внешним инструментом (`github.com/leanprover/comparator`). Это отвечает на
   вопрос «доказано ли именно то, что заявлено», который у нас никак не закрыт.
2. **`AUDIT.md` как воспроизводимая запись:** команды сборки, число задач, счётчики `sorry` и
   аксиом — всё, что читатель может перепроверить сам.

Аксиомная тройка `[propext, Classical.choice, Quot.sound]` — та же, которую наш проект
держит требованием.

---

## Карточка 4 — `Zeta23/ZeroSide.lean`: ζ-free линейная алгебра, переносимая на наш объект

**Что ДОСЛОВНО сказано** (шапка файла):

> Design: this file is **ζ-free**. Section 1 is generic Hermitian-matrix lemmas missing from
> Mathlib/RHLinalg. Section 2 proves `prop:block` for an ABSTRACT finite zero configuration
> `ZeroBlockData` (distinct points `z` with explicit multiplicities `m z ≥ 1`, the involution
> `σ = (ρ ↦ 1 − conj ρ)` with `m ∘ σ = m`, and evaluation vectors `v z = (φ̂(γ_z − τ_k))_k`
> with `v (σ z) = conj ∘ v z`). Section 3 instantiates from `Defs.lean`'s `ZeroConfig`.

Структура (строка 161):

```lean
structure ZeroBlockData (ι d : Type*) where
  m : ι → ℕ
  one_le_m : ∀ z, 1 ≤ m z
  v : ι → d → ℂ                  -- вектор оценки
  σ : ι → ι                      -- инволюция ρ ↦ 1 − ρ̄
  σ_invol : Function.Involutive σ
  m_σ : ∀ z, m (σ z) = m z
  v_σ : ∀ z, v (σ z) = star (v z)
```

Секция 1 доказывает то, чего нет в Mathlib:

```lean
rank_add_le                        (A + B).rank ≤ A.rank + B.rank
rank_sum_le                        для конечных сумм
rank_smul_vecMulVec_le
posIndex_le_rank                   posIndex hA ≤ A.rank
posIndex_eq_zero_of_hermForm_nonpos
posIndex_neg_eq_zero_of_posSemidef
posIndex_sub_le_rank               P, N PosSemidef → …
posIndex_smul_pos
rank_smul_of_ne_zero
card_eq_onLine_add                 card ι = #onLine + 2·p
```

**Что даёт НАМ — и это главное в карточке.** Файл **не зависит от дзета-функции**: это
абстрактная теория сигнатуры и ранга для конфигурации с инволюцией и условием сопряжения
на векторах оценки.

У нас такая структура **есть**: отражение `J` с `J² = I`, коммутация `JK = KJ`, разложение
на чётный и нечётный блоки — всё проверено в Phase 0 (точный ноль на четырёх парах). Значит
леммы секции 1 применимы к нашей матрице напрямую, без переноса дзета-специфики.

Отдельно: у них `posIndex` уже определён в `Zeta23.LinAlg` (namespace `RHLinalg`) вместе с
`posIndex_add_le` (субаддитивность) и подпространственной характеризацией Сильвестра. Это
готовый слой под `Birman–Schwinger inertia`, которую наш судья держит в резерве как
`Re-representation 2`.

**Чего НЕ даёт.** Лицензия Apache 2.0 — заимствование возможно, но требует указания. И их
`ZeroBlockData` инстанцируется от конфигурации **нулей дзеты**, а наша матрица приходит от
`w02 − wr − prime` на centered-окне: сама структура переносится, инстанциация — нет.

---

## Что не прочитано

Прочитаны: абстракт и §1.3 статьи, §7.5 (пределы метода), `AUDIT.md` целиком, шапка и
секция 1 `ZeroSide.lean`, объявление `ZeroBlockData`.

**Не читались:** §2–§6 и §8 статьи (явная формула, леммы линейной алгебры, prime side,
доказательства теорем A/B/C, численные иллюстрации); 328 остальных файлов формализации,
включая `LinAlg.lean`, где живёт сам `posIndex`; `note`, `explanation` и `transcripts`
целиком — из них прочитаны только оглавления.

`transcripts` — 116 страниц лога рабочих сессий; там может быть описан процесс, полезный
для нашей организации работы, но математически он вторичен.
