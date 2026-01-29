# mgrep + websearch Discovery

**Date:** 2026-01-18

## Что обнаружили

### 1. mgrep — semantic search по проекту

Установили и настроили [mgrep](https://github.com/mixedbread-ai/mgrep) от Mixedbread.

**Store:** `565025c1-db39-4b93-87ea-08e72a7bd051`
- 643 файла проиндексированы
- 1.6M tokens
- Все леммы, доки, insights Q3 проекта

**Benchmark (643 files):**
| Метрика | mgrep | grep |
|---------|-------|------|
| Время | 1.57s | 1.60s |
| Качество | 98% match на нужное | Exact string only |

**Multilingual:** Понимает русский → находит английские файлы!
```bash
q3search "почему RKHS оператор меньше четверти от floor bound" -c
# → A3_bridge_v4_real_TP.md (91.96% match)
```

### 2. websearch — AI web search

`mgrep --web --answer` ищет по облачному индексу Mixedbread (не Google/Bing).

**Полезные находки для Q3:**

| Запрос | Match | Источник |
|--------|-------|----------|
| Toeplitz/Szegő eigenvalues | 71% | [arxiv:2411.19298](https://arxiv.org/html/2411.19298v2) |
| Weil/Li criterion | **99%** | [arxiv:2301.05779](https://arxiv.org/abs/2301.05779) |
| Fejér approximation | 96% | UNM wavelets paper |

**Особенно ценное:**
- [MathOverflow: lowest eigenvalue of Toeplitz](https://mathoverflow.net/questions/484578/lowest-eigenvalue-of-toeplitz-matrices-strategies) — наша проблема A3!
- Bombieri-Lagarias: Li criterion → Weil criterion

### 3. Wrappers для агентов

```bash
# Локальный поиск по Q3 (из любой директории)
q3search "твой запрос" -c

# Web search с AI-ответом
websearch "вопрос про математику"
```

**Location:** `~/.local/bin/`

### 4. Правила использования

**НЕ ДЕЛАТЬ:**
- `mgrep watch` — квота исчерпана (1.9M/2M)
- `mgrep --sync` — то же

**ДЕЛАТЬ:**
- `q3search "запрос" -c` — поиск по существующему индексу
- `websearch "вопрос"` — web search

## Конфиг

- **Guide:** `~/.claude/docs/MGREP_GUIDE.md`
- **Hook (patched):** `~/.claude/plugins/cache/Mixedbread-Grep/mgrep/0.0.0/hooks/mgrep_watch.py`
- **Store config:** `/full/q3.lean.aristotle/.mgreprc.yaml`

## Находки по текущей проблеме (Q_nonneg + A3_bridge)

### Проблема
- Wire `rayleigh_Q_eq_Q` into atoms chain
- Close A3_bridge через Rayleigh + RKHS cap

### Релевантные источники (websearch)

**Rayleigh quotient + Toeplitz:**
| Source | Match | Ключевое |
|--------|-------|----------|
| [StackExchange: smallest eigenvalue Toeplitz](https://math.stackexchange.com/questions/4468152/estimate-the-limit-or-bounds-of-the-smallest-eigenvalue-of-a-symmetric-toeplitz) | 92% | λ_min = min_x R(x) |
| [SJSU: Rayleigh Quotient](https://www.sjsu.edu/faculty/guangliang.chen/Math253S20/lec4RayleighQuotient.pdf) | 79% | PSD ↔ eigenvalues ≥ 0 |

**RKHS + Toeplitz:**
| Source | Match | Ключевое |
|--------|-------|----------|
| [Unipd: RKHS intro](https://www.math.unipd.it/~demarchi/TAA1718/RKHS_presentazione.pdf) | 83% | K PSD ↔ quadratic form ≥ 0 |
| [JMLR: RKHS prior + Toeplitz](https://jmlr.org/papers/volume25/22-1491/22-1491.pdf) | 83% | Adaptive RKHS on Toeplitz |
| [arxiv: Sarason Sub-Symbol](https://arxiv.org/pdf/1412.5969) | 73% | Toeplitz + Fourier coefs |
| [IIT: RKHS notes](http://amadeus.math.iit.edu/~fass/Notes590_Ch13Print.pdf) | 73% | TTOs on model spaces |

**Ключевая связь (из источников):**
> "A positive definite kernel K is associated with a unique RKHS.
> The positivity of a kernel is proven by showing its associated
> quadratic form is non-negative."

Это именно то что нам нужно для Q_nonneg!

### Для A3_bridge (lowest eigenvalue)

[MathOverflow: lowest eigenvalue strategies](https://mathoverflow.net/questions/484578/lowest-eigenvalue-of-toeplitz-matrices-strategies):
> "Szegő's strong limit theorem is a statement on the asymptotic
> distribution of most eigenvalues, unscaled. It does not have
> sufficient resolution near 0 for finding the lowest eigenvalue."

**Вывод:** Нам нужен direct Rayleigh bound (что уже есть в rayleigh_v1.lean),
а не asymptotic Szegő!

---

*Insight by Opus 4.5 + Ылша*
