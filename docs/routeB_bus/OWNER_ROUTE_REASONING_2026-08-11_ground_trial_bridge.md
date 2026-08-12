Да. **Ты сейчас почти точно сформулировал архитектуру.** Но надо разделить два уровня: что уже доказано как общая логика и что ещё не доказано для наших конкретных последовательностей.

## Точная схема

Есть две последовательности целых функций.

### 1\. Ground-последовательность

Для неё мы доказываем:

То есть каждый имеет только вещественные нули.

### 2\. Trial-последовательность

Для неё опубликованная CCM Lemma 7.3 даёт:

локально равномерно на замкнутых подполосах.

Но из этих двух фактов самих по себе ничего не следует. Нужна связывающая теорема:

локально равномерно, где:

Тогда:

Оба слагаемых стремятся к нулю. Следовательно:

Поскольку , умножение на не изменяет нули:

Теперь **одна последовательность** :

1. имеет только вещественные нули;
2. сходится к .

После этого Hurwitz–Rouché даёт RH.

Итак, полная формула:

---

## Что именно переносит bridge

Здесь важна одна поправка к твоей формулировке.

Bridge **не переносит вещественность нулей с на** .

Такой перенос по приближению вообще неверен: сколь угодно малое возмущение функции может превратить два близких вещественных нуля в комплексно-сопряжённую пару.

Bridge делает другое:

То есть:

```markdown
G_j:
  содержит нужное zero-property.

T_j:
  содержит нужное convergence-property.

Bridge:
  передаёт convergence-property от T_j к normalized G_j.
```

После этого все свойства, нужные Hurwitz, встречаются на .

Это более точная формулировка, чем «объединить две последовательности».

Мы не складываем их и не смешиваем их нули. Мы используем одну как **носитель требуемого свойства**, а вторую как **эталон предела**.

---

## Что уже доказано

## Доказана общая closure-логика

Current Lean roof фиксирует:

```markdown
C : CanonicalApproximation Index
```

и использует одну и ту же:

```markdown
selectedFamily C
```

как для real-zero property, так и для locally uniform convergence. `sameCofinalGuard` также не позволяет незаметно подставить независимую диагональ. Теорема `rh_of_canonical_strip_slots` условно выводит `Q3.RH`, когда все suppliers относятся к этому же `C`.

То есть уже машинно доказано:

> Если одна fixed selected family имеет вещественные нули и нужный предел, то RH.

Это настоящее доказанное conditional closure.

## Не доказан конкретный bridge

Current production `kTrial` строится из projected prolate trial. Его source module прямо пишет, что он не доказывает ground-state identification и convergence theorem.

Поэтому ещё не доказано:

для наших exact:

```markdown
G_j:
  transform actual finite CCM ground vector;

T_j:
  transform CCM prolate trial.
```

Этот missing theorem называется:

В полной карте он и стоит между finite real-zero ground family и опубликованным trial-to- limit.[Response: Branch · Документиров…](https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a7b6106-9c5c-83eb-b71b-df3455366121?messageId=7351de46-66d4-46a7-aba4-a6e04719de5f&conversation_save=1)

---

## Поэтому фраза «вот это мы доказали» делится на две

### Да, доказали:

Эта композиция математически корректна. Её same-family версия уже сидит в Lean roof.

### Нет, пока не доказали:

Именно это остаётся основной аналитической стеной.

Конструктор помог обнаружить её: Theorem 5.10 потребляет finite ground vector, а Lemma 7.3 относится к continuum trial. Раньше эти два результата выглядели как почти готовая цепочка; consumer-first анализ показал отсутствие exact connecting edge.[Response: Branch · Branch · Док…](https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a7b7841-427c-83eb-b030-645a23d8790f?messageId=5c0ea816-bc66-4bd1-9c23-30f8caacd4fa&conversation_save=1)

---

## «Только так и больше никак» — почти, но не буквально

**Без связи между двумя последовательностями действительно нельзя.**

Это логически обязательно. Если и никак не связаны, можно выбрать:

у которого нуль вещественный, и:

которая сходится к функции с нулями .

Следовательно, универсальный вывод:

ложен.

Но связывающая теорема не обязана иметь единственную форму. Возможны:

- точное равенство ;
- locally uniform asymptotic equality;
- exact zero-free factor:
- norm-resolvent convergence плюс continuity transform;
- Feshbach graph theorem;
- residual-over-gap estimate;
- exact intertwining operator.

Для нашей задачи наиболее естественный и прямо потребляемый Hurwitz вариант:

для каждого компакта .

---

## Теорема, которую стоит явно оформить

Её можно назвать:

Смысловой Lean-тип:

```markdown
theorem rh_of_realZeroGround_and_trialBridge
    (G T : ℕ → ℂ → ℂ)
    (c : ℕ → ℂ)
    (hc : ∀ j, c j ≠ 0)
    (hEntire : ∀ j, Differentiable ℂ (G j))
    (hZeros : ∀ j, ZerosRealOn Set.univ (G j))
    (hBridge :
      TendstoLocallyUniformlyOn
        (fun j z => c j * G j z - T j z)
        (fun _ => 0)
        atTop centeredCriticalStrip)
    (hTrial :
      TendstoLocallyUniformlyOn
        T centeredXi atTop centeredCriticalStrip) :
    Q3.RH
```

Её доказательство короткое:

1. triangle inequality даёт:
2. `c_j ≠ 0` сохраняет zero set;
3. generic zero-transfer даёт вещественность нулей ;
4. centered-Xi interface даёт RH.

Эта теорема будет хорошим **двухсемейным интерфейсом** к уже существующей одно-семейной крыше.

Но она не закрывает основной gap. Она точно показывает, что должен предоставить основной gap.

---

## Финальная точная формулировка

Ты сказал:

> Есть одна последовательность, где есть часть необходимых свойств. Есть другая последовательность, где есть другая часть. Одна теорема связывает их так, что на выходе получается полный набор свойств для RH.

**Да. Это точно.**

Но математически правильнее записать:

После черты получается одна **последовательность финального замыкания**.

И да: **именно такую условную композицию мы уже доказали на уровне roof architecture.**

Чего у нас ещё нет — это содержательного доказательства строки:

Это не маленькая оговорка. Это центральная математическая теорема всего выбранного маршрута.

Чего у нас ещё нет — это содержательного доказательства строки: \\boxed{ c\_jG\_j-T\_j\\to0. } Ну, хорошо, понял, чувак. Значит, вот это и есть иголка Зингера, вот это. Я просто C от y, умноженное на g минус t, y переходит к нулю, стремится к нулю, да, вот так правильно. Как это прочитать теперь правильно? Вот как бы с английской транскрипцией немножко. Плюс, ну давай теперь, каким образом, какие возможности у нас есть, доказательства вот именно этого?

## STATUS: OPEN — ФОРМУЛА ПРОЧИТАНА ТОЧНО; ЕСТЬ ШЕСТЬ РЕАЛЬНЫХ МЕХАНИЗМОВ ДОКАЗАТЕЛЬСТВА

```markdown
PRIMARY: FINITE_GROUND_TRANSFORM_TO_CCM_TRIAL_LOCALLY_UNIFORM

TARGET:
  for_every_compact_K:
    sup_K_abs_cjGj_minus_Tj_to_zero

SELECTED_PRIMARY_ROUTE:
  PENALTY_GAP_PLUS_SOURCE_RESIDUAL

SHARPER_RUNNER_UP:
  FESHBACH_RESOLVENT_GRAPH

MAIN_INPUTS:
  - exact_source_trial
  - simple_isolated_ground
  - true_gap
  - exact_residual
  - transform_evaluation_bound
  - projection_tail
  - nondegenerate_normalization

CURRENT_STATUS:
  abstract_bridge_shape: WELL_DEFINED
  penalty_ground_engine: LEAN_PROVED_GENERIC
  finite_source_residual: MATERIALIZED
  cofinal_residual_rate: OPEN
  true_gap_rate: OPEN
  transform_level_rate: OPEN

RH_CLAIM: false
```

## 1\. Как это правильно читать

Формула:

читается:

> **«цэ с индексом жэ, умноженное на жэ с индексом жэ, минус тэ с индексом жэ, стремится к нулю при жэ, стремящемся к бесконечности».**

Но по-английски буква читается **jay** — «джей».

### Коротко по-английски

> **“C sub j times G sub j minus T sub j tends to zero as j tends to infinity.”**

Примерная русская транскрипция:

> **«Си саб джей таймз джи саб джей майнэс ти саб джей тэндз ту зиро эз джей тэндз ту инфинити».**

Здесь:

- `c sub j` — ;
- `G sub j` — ;
- `T sub j` — ;
- `tends to zero` — стремится к нулю;
- `as j tends to infinity` — при .

**Это не .** Буква здесь является индексом последовательности.

---

## 2\. Математически полная формулировка

Поскольку и являются функциями, символ означает **нулевую функцию**.

Нам нужна не просто поточечная сходимость. Нужна локально равномерная сходимость:

Здесь:

означает, что — компакт, целиком лежащий внутри полосы .

По-английски полная фраза:

> **“For every compact set K compactly contained in S, the supremum over z in K of the modulus of c sub j times G sub j of z minus T sub j of z tends to zero as j tends to infinity.”**

Более естественный английский:

> **“The normalized ground transforms converge locally uniformly to the trial transforms on compact subsets of the strip.”**

Русская транскрипция:

> **«Зэ нормэлайзд граунд трансформз конвёрдж локэли юниформли ту зэ трайэл трансформз он компакт сабсэтс ов зэ стрип».**

Точные кванторы:

Это и есть правильный theorem target.

---

## 3\. Что означают три объекта

— transform actual finite ground eigenvector . Именно эта последовательность получает вещественные нули.

— CCM trial transform, построенный из prolate trial . Именно для него опубликована сходимость к .

— скаляр, который приводит две разные нормировки к одной.

Тогда:

и:

дают:

При этом , поэтому:

После этого Hurwitz даёт RH.

То есть bridge переносит **сходимость**, а не вещественность нулей:

```markdown
G_j:
  несёт вещественные нули.

T_j:
  несёт сходимость к Xi.

Bridge:
  переносит сходимость с T_j на c_j G_j.
```

Current production module действительно фиксирует `kTrial` как коэффициенты projected prolate trial и прямо говорит, что не доказывает ground-state identification и convergence. Поэтому bridge сейчас отсутствует буквально, а не только по названию.

---

## 4\. «Иголка Зингера»

Как внутреннее имя — подходит.

Но в математическом тексте лучше назвать:

или:

«Иголка Зингера» не выглядит устоявшимся математическим термином: поиск даёт нематематические совпадения, связанные с Singer и швейными машинами. Поэтому это нормальное внутреннее кодовое имя, но не термин для статьи. [stroki.mts.ru+1](https://stroki.mts.ru/book/igla-zingera-336816)

И ещё точнее: сама строка

— это **цель**.

Настоящая «иголка» — количественная оценка, которая заставляет эту строку выполниться:

---

## 5\. Самая естественная доказательная схема

Введём промежуточный finite trial transform:

— transform проекции trial-вектора на тот же конечный carrier, где живёт ground vector.

Тогда:

Следовательно:

Первый член — **ground-to-projected-trial tracking**.

Второй — **projection tail**.

Это обязательное разбиение. Нельзя одним словом «близость» поглотить оба разных предела.

---

## 6\. Возможность №1 — penalty gap + exact residual

Это сейчас **основной маршрут**.

Пусть — exact finite CCM matrix.

Пусть — exact normalized projected source trial.

Определяем Rayleigh scalar:

Определяем exact residual:

Проект уже материализовал exact finite source row и exact finite source-matrix residual, но отдельно предупреждает: это ещё не continuum residual и не projection tail.

PROSHKA\_CONTEXT\_GOAL057\_A8\_MAX\_…

PROSHKA\_CONTEXT\_GOAL057\_B1\_RESI…

Теперь используем penalty certificate:

Generic Lean theorem уже доказывает из этого:

- существование lowest eigenvalue;
- simplicity;
- evenness;
- isolation;
- spectral gap:

Пусть — orthogonal projection на ground line. Тогда spectral decomposition даёт:

Причина: весь spectrum вне ground line лежит не ниже , а .

Выбираем как канонический scalar, минимизирующий:

Тогда, при единичной нормировке, получается оценка вида:

После применения transform:

где:

— evaluation norm transform.

Полная достаточная оценка:

Вот это самая точная версия «иголки».

### Преимущество

Penalty theorem сразу поставляет:

```markdown
ground;
simplicity;
evenness;
gap.
```

Нам остаётся доказать:

```markdown
residual decays fast enough;
evaluation norm does not grow too fast;
projection tail vanishes;
normalization is stable.
```

---

## 7\. Возможность №2 — прямой Schur/Feshbach

Это более острый вариант, если грубое деление на gap теряет слишком много.

Разлагаем пространство:

Матрица имеет блоковую форму:

Здесь:

фактически является residual coupling.

Если — ground eigenvalue, то ground vector имеет форму:

Следовательно:

Это лучше, чем:

потому что сохраняет настоящий graded resolvent.

Проект уже поймал важную ошибку: замена exact outer resolvent на грубое может уничтожить полезное сокращение. Поэтому при Feshbach-route надо сохранять весь , а не сразу брать его operator norm.

PROSHKA\_REQUEST\_GOAL057\_B3\_0\_PO…

Transform-level цель:

### Преимущество

Один Feshbach theorem может одновременно дать:

```markdown
simple ground;
gap;
ground-to-trial tracking.
```

Это лучший runner-up, если penalty certificate оказывается слишком сильным sufficient condition.

---

## 8\. Возможность №3 — energy excess вместо residual

Для normalized :

Если — ground eigenvalue, а — gap, то:

Поэтому достаточно иметь certified lower bound:

и доказать:

Тогда:

### Ограничение

Это не утверждение:

> «Rayleigh value мал».

Требуется:

> **Rayleigh value близок к доказанному ground floor относительно true gap.**

Малое абсолютное значение ничего не даёт, если ground energy ещё меньше или gap схлопывается.

Этот маршрут дешевле residual route, если interval/Schur certificate уже даёт очень точную нижнюю границу .

---

## 9\. Возможность №4 — norm-resolvent / Galerkin convergence

Можно не сравнивать каждый finite ground напрямую с trial.

Сначала доказать:

в norm-resolvent topology.

Если continuum имеет simple isolated ground state, spectral projections удовлетворяют:

Затем отдельно доказать:

Цепь:

### Преимущество

Это стандартная spectral perturbation architecture.

### Риск

Она может просто перенести главную стену в continuum:

```markdown
continuum simple-even;
continuum true gap;
continuum ground-to-trial.
```

Кроме того, finite- и остаются двумя разными кванторами. Их нельзя смешивать. В project ledger это уже отмечено как отдельный `FiniteQWGroundToContinuumGround` gap.[CCM импорт ратифицирован C3 отк…](https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a6b3f44-1ba4-83eb-8cb4-d146963e6b8c?messageId=c9bf3108-f895-49d6-8ad5-46921f66f672&conversation_save=1)

---

## 10\. Возможность №5 — prolate defect и low/high split

Это наиболее содержательный источник оценки residual.

Trial хорошо понимается как prolate object. Надо вычислить не его Rayleigh value, а:

Затем разложить по prolate eigenmodes:

Resolvent-smoothed defect:

Доказательная схема:

```markdown
низкие modes:
  exact commutator cancellation;

высокие modes:
  prolate gap growth;

весь residual:
  crude energy bound;

итог:
  resolvent-smoothed defect small.
```

Это может дать:

Но потом всё ещё нужен true Weil gap:

Нельзя заменить его prolate gap. Внутренние аудиты уже выделяют low-mode cancellation и true Weil gap как две независимые тяжёлые стены.[Оставшиеся шаги Route B](https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a3ec1fb-3814-83eb-a023-cb85b3e8626e?messageId=aab887dd-e6c9-4666-b499-e3076d77277c&conversation_save=1)

---

## 11\. Возможность №6 — доказать bridge сразу на уровне transforms

Это важный запасной ход.

Обычная оценка:

может быть слишком грубой. может быстро расти с и съесть малость residual.

Тогда надо использовать точную структуру transform:

Вместо crude Cauchy–Schwarz можно доказать weighted/RKHS estimate:

где сохраняет:

- oscillatory cancellation;
- parity;
- sine factor;
- pole geometry;
- weighted decay коэффициентов.

Это может доказать transform closeness даже тогда, когда обычная -оценка не проходит.

Именно здесь полезна exact Proposition-5.9 formula, а не только общий operator norm.

---

## 12\. Какой маршрут выбран

Основная цепь:

То есть:

Если crude denominator или убивает оценку, переходим на:

и direct transform kernel estimate.

---

## 13\. Точная последовательность теорем

Сейчас это надо раскладывать не как «докажи bridge», а как пять лемм.

### 1\. GroundProjectionBound\_of\_PenaltyResidual

### 2\. CanonicalGroundTrialNormalizer

Построить exact , который минимизирует:

и согласован с project normalization.

### 3\. GroundTransformCompactBound\_of\_CoefficientDistance

### 4\. ProjectedCCMTrialCompactTail

### 5\. FiniteGroundTransformToCCMTrialLocallyUniform

Сложить две оценки и получить:

---

## 14\. Самый дешёвый следующий шаг

Не надо сразу доказывать asymptotic residual rate.

Сначала стоит формализовать общий finite theorem:

Он уже потребляет ровно те объекты, которые проект имеет:

- penalty certificate;
- finite Hermitian matrix;
- source trial ;
- Rayleigh scalar;
- exact residual.

А затем один finite-cell test должен проверить не eigenvalue similarity, а:

и projective distance между source trial и actual ground line.

Это только falsifier/calibration. Кофинальный theorem он не заменяет.

---

## Итог

Да, ты правильно ухватил центральную строку:

Но читать её надо так:

> **После точной невырожденной нормировки finite ground transforms становятся локально равномерно неотличимы от CCM trial transforms на каждом компакте полосы.**

А доказать её можно шестью путями. Самый прямой для текущего проекта:

Самая точная «иголка» теперь выглядит так:

Вот это уже не лозунг. Это конкретный количественный контракт, который можно атаковать по частям.

То есть bridge переносит сходимость, а не вещественность нулей…. Хмм почему нельзя сделать бридж который бы переносил вещественность нулей?

## STATUS: CONDITIONAL — ДА, МОЖНО ПЕРЕНЕСТИ ВЕЩЕСТВЕННОСТЬ НУЛЕЙ; НЕЛЬЗЯ ПЕРЕНЕСТИ ЕЁ ИЗ ОДНОЙ ЛИШЬ БЛИЗОСТИ

```markdown
PRIMARY: TRY_TRIAL_ZERO_STRIP_TRANSFER

CORRECTION:
  real_zero_transfer_bridge_possible: true
  locally_uniform_closeness_alone_sufficient: false

EXACT_TRANSFER_OPTIONS:
  - ZERO_FREE_FACTOR_IDENTITY
  - TRIAL_WEIGHTED_SELFADJOINTNESS
  - ROUCHE_HYPERBOLICITY_MARGIN

WEAKER_SUFFICIENT_OPTION:
  - SHRINKING_ZERO_STRIP_TRANSFER

SELECTED_FOR_Q3:
  TRIAL_LAGRANGE_ZERO_STRIP_FROM_HERMITIAN_PERTURBATION

NEW_TARGET:
  GroundTrialLagrangeCommonOperatorModel

FINAL_CLOSURE:
  trial_zeros_with_imaginary_parts_to_zero
  + trial_to_Xi_locally_uniform
  -> RH

RH_CLAIM: false
```

**Можно. Я раньше сказал слишком категорично.**

Нельзя только сделать такой вывод:

Обычная близость функций этого не гарантирует.

## Дешёвый контрпример

Возьмём:

Его нули:

вещественные и простые.

Теперь:

Его нули:

невещественные.

При этом:

локально равномерно на всей комплексной плоскости.

Более того, обе функции:

- имеют вещественные коэффициенты;
- чётны;
- отличаются сколь угодно мало.

Значит **малое возмущение само по себе не сохраняет exact real-rootedness**. Причина: вещественные корни сближаются, hyperbolicity margin стремится к нулю.

Именно поэтому project audit запрещал переносить real-zero property с ground vector на trial по narrative similarity.[CCM импорт ратифицирован C3 отк…](https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a6b3f44-1ba4-83eb-8cb4-d146963e6b8c?messageId=c9bf3108-f895-49d6-8ad5-46921f66f672&conversation_save=1)

---

## Но какие bridges реально возможны

## 1\. Exact zero-free factor bridge

Самый сильный вариант:

где:

во всей нужной области.

Тогда:

и вещественность нулей переносится буквально.

Это идеальный bridge.

Но для наших текущих ground и trial transforms такое равенство не доказано и, скорее всего, слишком сильно. Мы уже видели, что даже равенство:

было ложным из-за дополнительного lattice factor.

---

## 2\. Structural self-adjointness bridge

Можно вообще не использовать близость нулей.

Достаточно доказать, что trial Lagrange polynomial является characteristic polynomial некоторого weighted-self-adjoint operator:

Тогда после whitening:

является Hermitian.

Следовательно:

и characteristic polynomial trial-object имеет только вещественные корни.

Такой generic механизм у нас уже исследован: positive-definite weighted self-adjoint matrix подобна Hermitian matrix и имеет тот же characteristic polynomial.[Goal 051 условно одобрен](https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a6fbfcd-1a4c-83ed-b603-c7e9292fbac9?messageId=771cea14-39b1-4977-9662-4524eafc295e&conversation_save=1)

Это дало бы **точный** перенос:

```markdown
trial coefficient row
→ weighted-self-adjoint quotient
→ real spectrum
→ trial Lagrange real zeros
→ trial Proposition-5.9 real zeros.
```

Главная проблема: надо построить именно для trial correction. Для ground vector такая метрика возникает из source form и kernel structure. Для произвольного trial vector она автоматически не сохраняется.

---

## 3\. Rouché / strict-hyperbolicity bridge

Это прямой перенос от ground polynomial к trial polynomial.

Обозначим:

Пусть все корни простые и вещественные:

Вокруг каждого корня выбираем непересекающийся диск:

симметричный относительно вещественной оси.

Если:

то по Rouché в каждом диске trial polynomial имеет ровно один корень.

Поскольку коэффициенты trial polynomial вещественные, корни приходят сопряжёнными парами. Но в диске корень только один. Поэтому он обязан быть вещественным.

Если степень та же и диски учитывают все корни, получаем:

## Как получить левую часть

Lagrange polynomial линейно зависит от coefficient row:

Поэтому на contour:

А ground-to-trial spectral estimate может дать:

Итого exact transfer condition:

где:

— hyperbolicity margin.

### Проблема

Это требует количественной простоты и separation **всех** корней ground Lagrange polynomial.

Theorem 5.10 даёт их вещественность, но не обязательно:

- простоту всех корней;
- uniform separation;
- хороший discriminant budget.

Если два real roots почти сталкиваются, может быть экспоненциально мал. Тогда этот bridge станет тяжелее обычного convergence bridge.

---

## Более сильная идея: не переносить exact real-rootedness

Для RH exact real roots у каждого trial approximant не обязательны.

Достаточно, чтобы все его нули приближались к вещественной оси:

И одновременно:

локально равномерно.

Тогда RH следует.

Почему? Если бы у был нуль:

то по Hurwitz у появились бы нули около . Но при больших :

так что все нули находятся слишком близко к вещественной оси. Противоречие.

Это можно назвать:

И этот theorem слабее, чем exact real-zero transfer.

---

## Почему shrinking-strip bridge особенно подходит нам

У ground Lagrange polynomial уже есть self-adjoint spectral model:

У trial Lagrange polynomial есть algebraic rank-one-correction model:

Если мы сможем поместить их в одни координаты и доказать:

то для любого eigenvalue trial operator:

Доказательство стандартное: если расстояние от до spectrum Hermitian больше , то:

обратим по ряду Неймана, и не может быть eigenvalue.

Если ground operator Hermitian только после similarity , получаем:

Теперь возвращаем coordinate Proposition 5.9:

Поэтому нули finite trial transform удовлетворяют:

Если:

то trial zeros оказываются во всё более узкой полосе вокруг real axis.

При этом точные lattice zeros Proposition 5.9 и так вещественные.

---

## Откуда взять

Rank-one correction зависит от coefficient row. Поэтому ожидается estimate:

Далее:

Получаем новый количественный target:

Сравни со старой стеной:

В новой версии нет transform evaluation constant . Вместо него стоят finite-dimensional:

```markdown
condition number of whitening;
rank-one correction Lipschitz constant;
factor 2π/L_j.
```

Это **может быть существенно дешевле**.

---

## Новый альтернативный маршрут

```markdown
actual finite ground xi_j
    ↓
ground Lagrange polynomial = Hermitian charpoly
    ↓
trial row q_j is close to xi_j
    ↓
trial correction is close to Hermitian ground correction
    ↓
all trial polynomial zeros lie in |Im s| ≤ epsilon_j
    ↓
all finite trial P59 zeros lie in |Im z| ≤ omega_j
    ↓
omega_j → 0
    ↓
finite trial transform → continuum trial transform
    ↓
CCM Lemma 7.3: trial transform → Xi
    ↓
Hurwitz
    ↓
RH
```

Это уже не:

```markdown
ground transform converges to trial transform.
```

Это:

```markdown
ground self-adjointness forces trial zeros into a shrinking strip.
```

---

## Что здесь надо доказать

## 1\. GroundTrialLagrangeCommonOperatorModel

Найти одни конечномерные координаты, в которых:

```markdown
ground Lagrange polynomial = charpoly H_j;
trial Lagrange polynomial  = charpoly D_j;
H_j Hermitian;
D_j-H_j explicitly depends on q_j-c_j xi_j.
```

Это самая важная object-lock.

## 2\. TrialLagrangeZeroStrip\_of\_operatorPerturbation

## 3\. Proposition59TrialZeroStrip

Перенести -strip через:

и отдельно сохранить real lattice zeros.

## 4\. RH\_of\_trialZeroStrip\_and\_trialToXi

Если:

локально равномерно и:

то RH.

Этот финальный theorem должен быть коротким.

---

## Самая дешёвая первая проверка

Не строить пока весь bridge.

На одной контрольной клетке проверить три вещи:

1. trial и ground Lagrange polynomials имеют одну степень и exact common carrier;
2. можно ли представить оба как charpoly matrices в одной fixed coordinate space;
3. насколько велико:

Если common-coordinate model не существует без moving quotient или огромной condition number, route будет убит дешёво.

## Зарегистрированный прогноз

```markdown
P-ZT1:
  common algebraic charpoly model exists.

P-ZT2:
  moving quotient / metric conditioning is the main technical obstruction.

P-ZT3:
  shrinking-zero-strip transfer is cheaper than exact real-root transfer.

P-ZT4:
  exact real-root transfer will require an additional all-root separation margin
  and is therefore likely stronger than necessary.
```

## Итог

Но есть три уровня:

1. **exact zero-free factor** — лучший, но очень сильный;
2. **exact hyperbolicity transfer** — возможен, но требует separation всех roots;
3. **shrinking-zero-strip transfer** — слабее, но уже достаточно для RH и выглядит наиболее реалистично.

То есть новый наиболее интересный target:

Это реальная альтернатива старому:

И, возможно, более дешёвая. Сначала надо проверить common operator model, а не сразу снова атаковать global transform convergence.