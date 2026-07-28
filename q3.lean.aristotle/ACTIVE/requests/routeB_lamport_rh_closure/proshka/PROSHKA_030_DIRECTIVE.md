Worked for 9m 46s

# STATUS: OPEN — REPRESENTATION SHIFT



```
CHOSEN:
  (a) DIRECT FULL-SUM

STRENGTHENED FORM:
  coupled response-weighted full-sum certificate,
  not point sampling and not another K-escalation.

NOT CHOSEN:
  (b) one-sided tail — currently unsupported;
  (c) exact edge contact — plausible, but its zero identity is not proved.
```

029 correctly exhausted the old representation. Recomputed J/epsilon independently; live CF boundary at both cuts; symmetric zero-compatible envelopes ~10^{-102} (dK=20) and 3.2e-112 (dK=40). Neither L>=0 nor U<0 closed. Registered prediction confirmed; protocol => representation shift.

(Konspekt Mythos: полный текст в /mnt/user-data/uploads и в чате; здесь — ядро директивы + полный контракт 030 ниже.)

# 1. Почему (a) в связной форме: старый split P+r-eps уничтожал две корреляции: (1) между модами 0/4 в канонической разности; (2) между значениями Legendre-tail на разных nz. Нужно суммировать SAMPLED tail одним объектом.

# 2. (b) отклонено: rho>0 не даёт знак сэмплденного хвоста (P_{2k}(nz) осциллирует).

# 3. (c) отклонено пока: zero mass != tooth zero. Точное тождество: S*_r = r*TrapError_r(Psi) - (1/2)Psi(0). Плант-контрпример: Psi(t)=t^2-1/3: int=0, но S*_r=(r+1)/(6r)>0.

# 4. Coverage-аудит: 029 пропустил tooth r=257; 030 обязан: teeth 257/256/255.

# 5. Registered prediction (до 030): (1) S(1/256)=0 НЕ вытекает из zero-mass+midpoint; (2) coupled response уберёт почти всю ±1e-112 неопределённость; (3) истинные суммы на r=256,255 неотрицательные; минимум один boundary tooth может быть 0 или сильно меньше interior-margin; (4) строго отрицательного интервала не выживет. Главная возможная ошибка: истинная сумма строго отрицательна на микроинтервале, и прежние негативные E_star-наблюдения были настоящими.

# 6. Точный контракт 030 — в 030_coupled_full_sum_response.goal.md дословно.

# 7. ROUTE MAP: (a) CHOSEN; (b) при sign-theorem; (c) только при EDGE_FACTOR_REQUIRED; pivot — только после COUPLED_FULL_SUM_NEGATIVE_CELL_PROVED.

# STRONGEST ATTACK: 030 остаётся finite-cell (m=257, r=255,256); не доказывает остальные bands, клетки 13/53, cofinal, Poisson-contract. Если INCONCLUSIVE -> автоматически (c): ExactEdgeContactFactorization.

# META: smallest gap = CoupledSampledRecessiveTailResponse; убиты: ещё одна K-лестница, one-sided tail без theorem, zero-mass=>tooth-zero, пропуск r=257; запрет navsegda: P_core±r*eps как decisive. Route score 5/5. Лемма A не затронута.
