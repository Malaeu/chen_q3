# План формализации RH_Q3.pdf в Lean

## Критический путь

```
thm_11_2 (RH) ← thm_11_4 (Main positivity) ← thm_8_35 (A3 bridge) 
    ← lemma_8_19 (Archimedean floor) ← lemma_8_14 (Archimedean floor)
    ← lemma_8_12 (Core contribution)
```

## Фазы формализации

### Фаза 1 (20 узлов)

| ID | Name | ERS | Type | Blocker |
|---|---|---|---|---|
| lemma_8_30 | Lemma 8.30 (Szegő-Böttcher discretisation) | 108.0 | lemma | hard |
| lemma_8_12 | Lemma 8.12 (Core contribution) | 100.8 | lemma | soft |
| lemma_8_16 | Lemma 8.16 (Digamma monotonicity) | 100.8 | lemma | soft |
| lemma_8_32 | Lemma 8.32 (Two-scale separation) | 48.0 | lemma | soft |
| lemma_8_13 | Lemma 8.13 (Shift-robust core mass) | 40.3 | lemma | none |
| lemma_8_15 | Lemma 8.15 (Core slope bound) | 36.0 | lemma | none |
| lemma_9_23 | Lemma 9.23 (RKHS-Weil isometry) | 33.0 | lemma | soft |
| lemma_8_5 | Lemma 8.5 (Lipschitz modulus for the periodized sy... | 30.0 | lemma | none |
| lemma_9_24 | Lemma 9.24 (Gaussian norm cap) | 25.2 | lemma | none |
| lemma_9_5 | Lemma 9.5 (Geometric tail bound for S_K(t)) | 20.4 | lemma | none |
| lemma_8_18 | Lemma 8.18 (Sample-point bounds for a) | 16.2 | lemma | none |
| lemma_9_1 | Lemma 9.1 (Gershgorin floor) | 10.2 | lemma | none |
| lemma_7_1 | Lemma 7.1 (Local finiteness of the prime sampler) | 9.6 | lemma | none |
| prop_5_1 | Proposition 5.1 (T0' — Guinand-Weil matching) | 9.0 | proposition | none |
| lemma_8_1 | Lemma 8.1 (Period-1 normalization audit) | 8.4 | lemma | none |
| lemma_9_8 | Lemma 9.8 (Effective weight cap) | 7.2 | lemma | none |
| lemma_9_10 | Lemma 9.10 (Node gap on compacts) | 6.0 | lemma | none |
| lemma_9_13 | Lemma 9.13 (Node separation) | 6.0 | lemma | none |
| thm_11_1 | Theorem 11.1 (Weil's positivity criterion) | 3.3 | theorem | none |
| lemma_6_2 | Lemma 6.2 (Compact support convolution reduction) | 2.8 | lemma | none |

### Фаза 2 (14 узлов)

| ID | Name | ERS | Type | Blocker |
|---|---|---|---|---|
| lemma_8_14 | Lemma 8.14 (Archimedean floor) | 132.5 | lemma | soft |
| thm_9_6 | Theorem 9.6 (Strict contraction) | 96.1 | theorem | hard |
| lemma_8_17 | Lemma 8.17 (Logarithmic growth bound) | 57.6 | lemma | none |
| prop_9_7 | Proposition 9.7 (Dataset-free RKHS schedule) | 36.1 | proposition | soft |
| lemma_8_23 | Lemma 8.23 (Analytic mean bound) | 34.8 | lemma | none |
| thm_9_12 | Theorem 9.12 (One-prime induction) | 32.2 | theorem | soft |
| thm_6_3 | Theorem 6.3 (A1' — density) | 30.1 | theorem | soft |
| lemma_8_11 | Lemma 8.11 (Lipschitz symbol P_A) | 28.2 | lemma | none |
| lemma_9_2 | Lemma 9.2 (Spectral floor for Gram matrices) | 22.3 | lemma | none |
| lemma_8_2 | Lemma 8.2 (Calibration of κ_{A3}) | 18.1 | lemma | none |
| lemma_7_3 | Lemma 7.3 (A2 — Lipschitz on C^+_even(K)) | 14.1 | lemma | none |
| def_8_20 | Definition 8.20 (Uniform Lipschitz constant) | 13.0 | definition | none |
| lemma_5_2 | Lemma 5.2 (T0: Q normalization crosswalk) | 11.5 | lemma | none |
| cor_7_2 | Corollary 7.2 (Lipschitz continuity on a compact w... | 9.5 | corollary | none |

### Фаза 3 (6 узлов)

| ID | Name | ERS | Type | Blocker |
|---|---|---|---|---|
| lemma_8_19 | Lemma 8.19 (Uniform Archimedean floor) | 223.8 | lemma | hard |
| prop_9_3 | Proposition 9.3 (Operator sandwich) | 51.7 | proposition | soft |
| lemma_8_24 | Lemma 8.24 (Analytic Lipschitz bound) | 37.1 | lemma | none |
| lemma_8_3 | Lemma 8.3 (Rayleigh identification) | 32.4 | lemma | soft |
| cor_7_4 | Corollary 7.4 (Explicit Lipschitz modulus for Q) | 13.1 | corollary | none |
| lemma_5_3 | Lemma 5.3 (Invariance under normalisation conventi... | 9.4 | lemma | none |

### Фаза 4 (5 узлов)

| ID | Name | ERS | Type | Blocker |
|---|---|---|---|---|
| cor_8_21 | Corollary 8.21 (Uniform discretisation threshold) | 150.6 | corollary | soft |
| cor_8_22 | Corollary 8.22 (Uniform prime cap time) | 134.7 | corollary | soft |
| lemma_8_33 | Lemma 8.33 (min P_A bound) | 84.0 | lemma | none |
| lemma_9_4 | Lemma 9.4 (Rayleigh sampling identification) | 42.7 | lemma | soft |
| lemma_8_34 | Lemma 8.34 (Modulus control) | 26.7 | lemma | none |

### Фаза 5 (5 узлов)

| ID | Name | ERS | Type | Blocker |
|---|---|---|---|---|
| thm_8_35 | Theorem 8.35 (Uniform A3 bridge) | 351.6 | theorem | hard |
| lemma_10_1 | Lemma 10.1 (Dispersion via A2/A3 data) | 166.5 | lemma | hard |
| prop_10_8 | Proposition 10.8 (AB(K) supplied by A3) | 131.0 | proposition | soft |
| cor_8_31 | Corollary 8.31 (Mixed lower bound) | 78.2 | corollary | soft |
| cor_9_11 | Corollary 9.11 (Two-scale decoupling) | 72.6 | corollary | soft |

### Фаза 6 (5 узлов)

| ID | Name | ERS | Type | Blocker |
|---|---|---|---|---|
| prop_8_4 | Proposition 8.4 (Bridge margin calibration) | 288.2 | proposition | soft |
| thm_11_4 | Theorem 11.4 (Main positivity on W) | 245.8 | theorem | hard |
| thm_10_6 | Theorem 10.6 (Structural prime cancellation) | 216.4 | theorem | hard |
| thm_10_2 | Theorem 10.2 (D3: Structural contraction) | 126.9 | theorem | hard |
| thm_10_9 | Theorem 10.9 (Amplitude gate without D3) | 122.8 | theorem | hard |

### Фаза 7 (3 узлов)

| ID | Name | ERS | Type | Blocker |
|---|---|---|---|---|
| thm_11_3 | Theorem 11.3 (Weil sufficiency pack) | 291.6 | theorem | soft |
| thm_11_2 | Theorem 11.2 (Riemann Hypothesis) | 76.7 | theorem | none |
| cor_10_3 | Corollary 10.3 (Amplitude closure) | 68.1 | corollary | soft |

## Статистика

| Метрика | Значение |
|---|---|
| Всего узлов | 58 |
| Всего рёбер | 79 |
| Фаз формализации | 7 |
| Суммарный ERS | 4199.9 |
| Средний ERS | 72.4 |
| Максимальный ERS | 351.6 |
| Hard blockers | 9 |
