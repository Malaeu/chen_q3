# Конкуренты Aristotle в области автоматического доказательства теорем

## 1. DeepSeek-Prover-V2 (DeepSeek AI)

**Источник:** https://arxiv.org/abs/2504.21801

### Основные характеристики

DeepSeek-Prover-V2 — open-source large language model для formal theorem proving в Lean 4.

**Архитектура и тренировка:**
- Initialization data через recursive theorem proving pipeline powered by DeepSeek-V3
- Cold-start training: DeepSeek-V3 decompose complex problems в series of subgoals
- Proofs of resolved subgoals synthesized в chain-of-thought process
- Combined с DeepSeek-V3's step-by-step reasoning для initial cold start для RL
- Integrates informal и formal mathematical reasoning в unified model

**Результаты:**
- **DeepSeek-Prover-V2-671B** — state-of-the-art performance
- **88.9%** pass ratio на MiniF2F-test
- **49 из 658** problems из PutnamBench
- **6 из 15** AIME problems (2024-25)

**Размер модели:** 671B параметров

---

## 2. ByteDance Seed-Prover 1.5

**Источник:** https://seed.bytedance.com/en/blog/seed-prover-1-5-advanced-mathematical-reasoning-through-a-novel-agentic-architecture

### Основные характеристики

Seed Prover 1.5 — specialized model для formal mathematical reasoning с Agentic Reinforcement Learning.

**Архитектура:**
- **Agentic Prover** — новая парадигма, балансирующая step-prover и whole-prover
- Lean как foundational tool с autonomous tool invocation
- **Mathlib Search Tool** — поиск в математической библиотеке Mathlib
- **Python Code Execution** — запуск Python скриптов для верификации
- **Incremental Lemma Verification** — декомпозиция в независимые леммы

**Тренировка:**
- Large-scale Agentic RL training
- Lean compiler provides objective "correct/incorrect" feedback
- RL training: success rate от 50% до ~90%

**Hierarchical Multi-Agent System:**
1. **Natural Language Prover** — high-level mathematical intuition
2. **Sketch Model** — converts natural language proofs в Lean sketches
3. **Agentic Prover** — formal proofs для каждой lemma in parallel

**Sketch Model Training:**
- RL с hybrid reward signals:
  - Signal 1: Lean compiler verifies structural correctness
  - Signal 2: Natural Language Prover checks each lemma
  - Signal 3: Rubric scoring model (Long-CoT) для semantic quality

**Результаты:**
- **IMO 2025:** 5 из 6 problems (35/42 points) — gold-medal level
- **Putnam 2025:** 11 из 12 problems
- **PutnamBench:** 88% (undergraduate level)
- **Fate-H:** 80% (graduate level)
- **Fate-X:** 33% (PhD level)

---

## 3. AlphaProof (Google DeepMind)

**Источник:** https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/

### Основные характеристики

AlphaProof — система для доказательства математических утверждений в Lean.

**Архитектура:**
- Pre-trained language model + AlphaZero reinforcement learning algorithm
- Self-training для prove mathematical statements
- Formal language: Lean

**Результаты:**
- **IMO 2024:** Silver-medal level (3 из 5 non-geometry problems)
- Публикация в Nature (November 2025)

---

## 4. AlphaGeometry-2 (Google DeepMind)

Специализированная система для геометрических задач, работает в паре с AlphaProof.

---

## Сравнительная таблица

| Система | Компания | Размер модели | MiniF2F | IMO 2025 | Особенности |
|---------|----------|---------------|---------|----------|-------------|
| Aristotle | Harmonic | >200B | 90% | 5/6 (Gold) | MCGS + Lemma reasoning + Yuclid geometry |
| DeepSeek-Prover-V2 | DeepSeek | 671B | 88.9% | N/A | Subgoal decomposition + RL |
| Seed-Prover 1.5 | ByteDance | N/A | N/A | 5/6 (Gold) | Agentic RL + Multi-agent system |
| AlphaProof | DeepMind | N/A | N/A | Silver 2024 | AlphaZero-style RL |

---

## Ключевые отличия Aristotle

1. **Три интегрированных компонента:** Lean proof search + Informal reasoning + Geometry solver (Yuclid)
2. **Monte Carlo Graph Search (MCGS)** вместо стандартного MCTS
3. **Test-Time Training** — дообучение на конкретной задаче
4. **Yuclid** — специализированный C++ geometry solver (до 500x быстрее AlphaGeometry-1)
5. **Hidden Chain of Thought** с динамическим thinking budget
6. **Co-evolution** трёх типов вывода (hidden CoT, informal comments, formal Lean code)
