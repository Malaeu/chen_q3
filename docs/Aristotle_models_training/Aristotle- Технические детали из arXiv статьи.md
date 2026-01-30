# Aristotle: Технические детали из arXiv статьи

**Источник:** arXiv:2510.01346v1 [cs.AI] 01 Oct 2025
**Авторы:** The Harmonic Team
**Контакт:** aristotle-report@harmonic.fun

## Обзор системы

Aristotle — это AI-система, которая комбинирует формальную верификацию с неформальным рассуждением. Система достигла золотой медали на IMO 2025, решив 5 из 6 задач с формальными доказательствами.

## Три основных подсистемы

### 1. Lean Proof Search Algorithm (Алгоритм поиска доказательств)

Основной компонент системы, построенный на **Monte Carlo Tree Search (MCTS)** с обученной функцией ценности в духе Expert Iteration и AlphaZero.

**Ключевые характеристики:**
- Использует **highly parallel Monte Carlo Graph Search (MCGS)**
- Большой трансформер служит как policy и value function
- Policy предсказывает Lean тактики условно на:
  - Lean proof state
  - Proof history
  - Неформальное доказательство (если доступно)
- Получает блок Lean кода и пытается заменить все `sorry` statements доказательствами

**Похожие системы:** HyperTree Proof Search, ABEL, DeepSeek-Prover-V1.5, AlphaProof

### 2. Lemma-based Informal Reasoning System

Генерирует неформальные доказательства математических утверждений, разбивает их на леммы, формализует каждую лемму в Lean, и итерирует процесс на основе формальной обратной связи.

### 3. Geometry Solver

Решает задачи планиметрии вне Lean, используя подход на основе AlphaGeometry.

## Детали архитектуры поиска

### 2.1.1 States and Actions

- Алгоритм может быть инициирован из любой коллекции **Lean states**
- States разбиваются по целям до метапеременных
- **Action** — текстовая строка, интерпретируемая как фрагмент Lean кода (одна тактика или последовательность)
- Может включать неформальные комментарии

### 2.1.2 Equivalences and Graph Search

- Lean states считаются эквивалентными если равны goal expressions, local context expressions, local variable names
- Поиск превращается в **Monte Carlo Graph Search** вместо tree search
- Работает на графах с O(D) на деревьях до O(V)

### 2.1.3 Search Strategy

- Используется вариант **PUCT (Predictor Upper Confidence bound applied to Trees)**
- Exploration bonus взвешен prior policy
- Prior policy аппроксимируется через sequence logprobs из генеративной модели
- AND/OR структура для minimax problem

### 2.1.4 Interleaving Informal Reasoning

Модель производит два вида неформального вывода:
1. **Informal comments** в дополнение к Lean тактикам
2. **Hidden chain of thought** с динамически устанавливаемым thinking budget

Все три вида вывода (hidden chain of thought, informal comments, formal Lean code) **co-evolved during training**.

### 2.1.5 Postprocessing

После поиска применяются:
- Linter suggestions
- Skipping sequences of actions
- Offline computation для конденсации и упрощения доказательств

### 2.1.6 Reinforcement Learning

**Тренировка:**
- Используется **единая модель** для value function и action generation
- Тренируется через **reinforcement learning в стиле expert iteration**
- Большой датасет математических утверждений из open-source коллекций и in-house данных
- **Statement autoformalization system:**
  - Initial autoformalization
  - Judging using signals from Lean REPL
  - Correction

**Обучение policy:**
- На доказательствах найденных через search
- Фильтрация по measures of nontriviality
- Value function на proven states и nearby states (disproven или unproven после significant effort)
- Judge для предсказания faithfulness к informal proof
- **Hindsight Experience Replay** — render proofs of non-root states как if they were root states

### 2.1.7 Test-Time Training (TTT)

При развёртывании на больших масштабах используется **test-time training**:
1. Делается несколько попыток решить основную задачу + леммы из outer reasoning loop
2. Если задача не решена — **retrain модель на search traces** из этих попыток

TTT улучшает:
- Эффективность и специализацию на конкретной задаче
- Cross-pollination между леммами из разных proof sketches
- Работу с новыми Lean abstractions

## Ключевые инсайты для тренировки

1. **Данные:** Большой датасет математических утверждений (open-source + in-house)
2. **Autoformalization:** Система для автоматической формализации утверждений
3. **Expert Iteration:** RL в стиле expert iteration с MCTS
4. **Co-evolution:** Три типа вывода развиваются совместно
5. **Test-Time Training:** Дообучение на конкретной задаче во время inference
6. **Hidden Chain of Thought:** Динамический thinking budget


## 2.2 Lemma-based Reasoning (Детали)

### 2.2.1 Lemma Generation Pipeline

Алгоритм поиска может быть инициализирован с любым существующим Lean code block, который может содержать уже доказанные background results или леммы, специфичные для целевой теоремы.

**Pipeline обработки через natural language queries:**

1. **Запрос неформального доказательства** теоремы
2. **Реструктуризация** доказательства как последовательности лемм (каждая с коротким доказательством)
3. **Формализация** утверждений лемм в Lean
4. **Error correction** — отправка формализаций в Lean REPL, получение ошибок, запрос исправлений

Каждый шаг включает multiple subqueries для рефлексии и редактирования.

### 2.2.2 Iteration with Formal Feedback

Итеративный framework при неудаче:
1. Запрос revision списка лемм (сохраняя доказанные, дополняя новыми)
2. Формализация новых лемм
3. Error correction

### 2.3 Geometry Solver

Основан на **Yuclid** — очень быстрый C++ DD/AR (deductive database and algebraic reasoning) engine.
- Опубликован под Apache 2.0 на GitHub
- До **500x быстрее** чем AlphaGeometry-1
- Решает 17 из 30 задач в AG-30 set за ~0.4s на single 3.1GHz core

**Оптимизации Yuclid:**
- Numerical rule matcher
- Deduplicating statements
- AR optimizations (Gaussian elimination)
- Memory management с C++ STL и Boost containers

## 3. Results

### Масштабирование системы

Для максимальной производительности на IMO требовалось масштабирование в трёх направлениях:
1. **Модель с >200B параметров** для search algorithm
2. **Параллельные instances** lemma-based reasoning pipeline
3. **Итерации** formal feedback loop для error correction

### Test-Time Training

Использовался для максимизации returns масштабирования.

### Дополнительные результаты

Во время тренировки Aristotle:
- Доказал теоремы отсутствующие в Mathlib (Niven's theorem, Gauss-Lucas theorem)
- Внёс вклад в Polynomial Freiman Ruzsa formalization project
- Внёс леммы в Generalized Quantum Stein's Lemma project
- Валидировал части учебника Terence Tao по real analysis в Lean
- Нашёл 4 ложных упражнения с explicit counterexamples

## 4. Related Work

### Конкуренты:
- **ByteDance Seed-Prover** — также достиг gold medal на IMO 2025 с formal solutions
- **OpenAI** — gold-medal level с natural language solutions
- **Google DeepMind** — gold-medal level с natural language solutions
- **AlphaProof + AlphaGeometry-2** — silver-medal на IMO 2024

## Ключевые параметры модели

- **Размер модели:** >200B параметров (для search algorithm)
- **Архитектура:** Large transformer
- **Тренировка:** Expert Iteration + Reinforcement Learning
- **Test-Time Training:** Дообучение на search traces конкретной задачи


## Информация от основателей (Sequoia Podcast)

**Источник:** https://sequoiacap.com/podcast/training-data-harmonic/
**Основатели:** Vlad Tenev (CEO Robinhood) и Tudor Achim (co-founder Helm.ai)

### Ключевые принципы тренировки

**1. Math is Reasoning**
- Математика — основа рассуждения во всех областях науки и инженерии
- Если система хорошо понимает математику, она будет хорошо рассуждать в других областях

**2. Recursive Self-Improvement**
- Lean используется как formal verification tool для объективной оценки математических доказательств
- Это позволяет быстрые циклы reinforcement learning и self-play
- Нет верхней границы математических знаний — рекурсивное улучшение может продолжаться бесконечно

**3. Synthetic Data Generation**
- Ключевое преимущество: генерация огромных объёмов синтетических математических данных
- Создание training examples возрастающей сложности
- Имитация того, как люди учат математику — от простого к сложному
- "Synthetic data is the fuel for the model"
- Оригинальные данные (человеческие доказательства) не очень применимы, поэтому почти все данные — синтетические

### Технический подход

- Использование **Lean** как formal verification tool
- **Reinforcement learning + self-play** для быстрого улучшения
- Объективная reward function через верификацию в Lean
- Генерация синтетических данных возрастающей сложности


## Детальная архитектура (Emergent Mind Summary)

**Источник:** https://www.emergentmind.com/topics/aristotle-imo-level-automated-theorem-proving

### 1. System Architecture and Integration

Aristotle состоит из трёх тесно связанных компонентов:

**1.1 Lean Proof Search System**
- Ядро использует Lean proof search algorithm, работающий на Lean "sketches" — частично написанных code blocks с gaps, помеченными `sorry`
- Поиск организован как **Monte Carlo Graph Search (MCGS)** — обобщение MCTS
- Lean states — вершины в directed graph (с equivalence classes)
- Actions соответствуют Lean tactics (например, `intro`, `cases`)
- **Large transformer model (>200B параметров)** служит unified policy и value function
- Выбирает promising tactics и оценивает likelihood of future proof success

**1.2 Lemma-Based Informal Reasoning**
- Natural language module декомпозирует сложные задачи в списки informally reasoned lemmas
- Elicits high-level proof sketches и supporting claims
- Autoformalizes их в Lean для formal proving
- **Iterative error feedback:** Lean verification errors парсятся и возвращаются для revision
- Создаёт creative auxiliary definitions (не указанные в оригинальной задаче)

**1.3 Dedicated Geometry Solver (Yuclid)**
- High-performance solver на C++
- Использует deductive databases и algebraic reasoning (Gaussian elimination, numerical rule matching)
- Preprocesses diagrams и генерирует structural relationships
- Оптимизирован для скорости (deduplication, fast memory management)

### 2. Lean Proof Search и Reinforcement Learning

**MCGS Framework:**
- Proof states как nodes в directed graph
- Edges соответствуют tactic applications
- Equivalence relations на states помогают избежать redundant exploration
- PUCT-based variants для prioritization actions

**Transformer Model:**
- Policy и value functions unified в large transformer
- Тренируется через **reinforcement learning expert iteration**
- Successful search paths (partial или complete) replayed для refinement
- Actions "successful" только если все resulting subgoals resolved

**Parallelization и Test-Time Training:**
- Multiple instances proof search run in parallel
- Каждый explores different lemma decompositions или proof tactics
- **Test-time training** — learning from own inference-time search traces
- Adapts tactic selection к structure каждой задачи

### 3. Lemma Discovery и Informal–Formal Bridging

**Proof Narrative Elicitation:**
- Генерирует narrative of intended proof
- Decomposed в supporting lemmas
- Mirrors expert human problem solving

**Auxiliary и Novel Definitions:**
- Производит creative auxiliary definitions
- Пример: `def S (f : N+ → N+) : Set N+ := {p | Nat.Prime(p) ∧ f(p) > 1}`

**Autoformalization Pipeline:**
- Natural language lemmas конвертируются iteratively в Lean statements
- Errors fed back к informal layer для correction
- Robust и adaptive даже на challenging inputs

### 4. Geometry Module: Yuclid

**Diagram Preprocessing:**
- Scans diagrams для standard configurations (midpoints, bisectors, similar triangles)
- Identified через numeric rule matching

**Algebraic Reasoning:**
- Configurations encoded в equations и inequalities
- Gaussian elimination и algebraic rule tables
- Generic relationships формализуются как Lean auxiliary facts

**Deductive Database:**
- Extensive rule tables
- Rapid deduction
- Tens of geometry problems solved within milliseconds on single core

### 5. Performance и Scaling

- **IMO 2025:** 5 из 6 задач решены (failed только на самой сложной)
- **Transformer backbone:** >200B параметров
- **MiniF2F benchmark:** 90% (state-of-the-art на момент публикации)
- Parallelized lemma generation и tactic search


---

## Инсайдерская информация от сотрудника Harmonic (Hacker News)

**Источник:** https://news.ycombinator.com/item?id=46561569

Сотрудник Harmonic (maxwells-daemon) прояснил несколько ключевых моментов:

### Ключевые факты

1. **Aristotle uses modern AI techniques heavily, including language modeling**
   - Подтверждает использование LLM как основы

2. **Aristotle can be guided by an informal (English) proof**
   - Если proof correct, Aristotle has a good chance at translating it into Lean
   - Это "strong vote of confidence" что English proof is solid

3. **Core of approach:**
   - Once a proof is formalized into Lean (assuming correct formalization), there is **no doubt that the proof is correct**
   - You can do a lot of AI-driven search
   - Once you find the answer, you are certain it's correct **no matter how complex the solution is**

### Верификация через Lean

- Lean validates that steps in machine-readable proof are valid
- Implies result from accepted axioms
- This is **not AI** — tiny, well-reviewed kernel that only accepts correct formal logic arguments
- Nigh infallible checker that won't accept incorrect hallucinations

### Значение для создания Skill

Ключевой инсайт: Aristotle использует **AI-driven search** для генерации доказательств, но **Lean compiler** служит как infallible verifier. Это позволяет:
- Генерировать много кандидатов
- Автоматически отсеивать неверные
- Быть уверенным в корректности финального результата
