# Twin Primes Q3 — Aristotle Formalization

## Структура

```
twins_q3_aristotle/
├── aristotle_input/     # Входные .md файлы для Aristotle
│   ├── Q3_twins_mod6.md     # Теорема: twins ≡ 5 (mod 6)
│   └── Q3_twins_exp_sum.md  # Q3 для экспоненциальных сумм
├── aristotle_output/    # Сгенерированные .lean файлы
├── submit_twins.py      # Скрипт отправки в Aristotle
├── project_ids.txt      # Сохранённые ID проектов
└── README.md
```

## Использование

### 1. Установить API ключ
```bash
export ARISTOTLE_API_KEY="arstl_your_key_here"
```

### 2. Отправить файлы в Aristotle
```bash
# Все файлы
cd /Users/emalam/Documents/GitHub/chen_q3/sobolev_q3/twins_q3_aristotle
uv run python submit_twins.py

# Конкретный файл
uv run python submit_twins.py Q3_twins_mod6.md
```

### 3. Проверить статус
```bash
uv run python submit_twins.py --status
```

### 4. Результаты
После COMPLETE скачиваются в `aristotle_output/`:
- `Q3_twins_mod6_aristotle.lean`
- `Q3_twins_exp_sum_aristotle.lean`

## Теоремы для формализации

### 1. Q3_twins_mod6.md — Структура mod 6
```
∀ p : ℕ, p > 3 → Prime p → Prime (p + 2) → p % 6 = 5
```

Все twin primes > 3 имеют форму (6k-1, 6k+1).

### 2. Q3_twins_exp_sum.md — Экспоненциальные суммы
```
|Σ_{p ∈ T(N)} e^{2πi·α·p·ln(3)}| = O(|T(N)|^{1/2-δ})
```

Q3 для twins с оптимальной фазовой функцией p·ln(3).

## Численные результаты

| f(p)      | β (numerical) | |S|/√N |
|-----------|---------------|--------|
| p·ln(3)   | **-0.31**     | 0.048  |
| p·ln(2)   | -0.16         | 0.061  |
| p·π       | -0.19         | 0.193  |

β < 0 означает |S| УМЕНЬШАЕТСЯ с N — сильнее чем стандартный Q3!

## Связь с основным Q3

Эти теоремы дополняют Q3 из `/full/q3.lean.aristotle/`:
- Основной Q3: для всех простых
- Этот Q3: специально для twin primes с mod 6 структурой
