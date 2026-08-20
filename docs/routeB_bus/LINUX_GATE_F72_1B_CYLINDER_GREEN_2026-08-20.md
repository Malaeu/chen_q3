# LINUX GATE — F72.1B параболический цилиндр D0/D4: GREEN

```yaml
DATE: 2026-08-20
FLOOR: F72_1B_D0_D4_PHYSICAL_HERMITE_EXACT
MARKED: LEAN_READY, цена 2/10 (вердикт REQ-I, 082421cf)
AUTHORIZATION: судья требовал explicit execution authorization — владелец дал в чате
WRITTEN_BY: Linux-тело (Codex не поднят)
FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ParabolicCylinderD0D4Exact.lean
GIT_BLOB: 5253ef9a46438bf99c15c2b456a216631405119f
SHA256: 0d7d0ac198edc4d9fa39b09a67666da92307a69636052e62ce55ce121b1cc534
LINES: 150

PROVED:
  D0: parabolicCylinderD 0 (sqrt(4pi)*x) = exp(-pi*x^2)
  D4: parabolicCylinderD 4 (sqrt(4pi)*x)
        = exp(-pi*x^2) * (16*pi^2*x^4 - 24*pi*x^2 + 3)
  РАЗЛОЖЕНИЕ ПАКЕТА (сверх директивы):
      explicitCCMLimitH x = (1/16)*D4(sqrt(4pi)x) - (3/16)*D0(sqrt(4pi)x)

CONVENTION_LOCK (ловушка C04 судьи):
  D_n(t) = exp(-t^2/4) * He_n(t) = 2^(-n/2) * exp(-t^2/4) * H_n(t/sqrt2)
  He — ВЕРОЯТНОСТНЫЙ Эрмит, H — ФИЗИЧЕСКИЙ.
  Mathlib Polynomial.hermite = вероятностный (рекурсия He_{n+1} = X*He_n - He_n').
  Поэтому лишней степени двойки в файле НЕТ. Записать `2^(-n/2)` перед
  вероятностным He_n было бы ошибкой — судья её назвал заранее.
  Порядок цилиндра = n-m = (q-1)/2, то есть D_0 и D_4; D_q УБИТ судьёй.

WHY_THE_DECOMPOSITION_IS_A_CHECK:
  коэффициент 1/16 фиксируется ТОЛЬКО членом x^4.
  После этого член x^2 обязан дать -24*pi/16 = -3*pi/2 — и пакет CCM (7.1)
  несёт ровно это. Совпадение НЕ навязано, оно выпадает.
  Свободный член: 3*(1/16) - 3/16 = 0, тоже сходится сам.

ROUNDS:
  R1: 5 ошибок (зацикленный simp на числовых литералах, aeval числа, ring без цели)
  R2: 2 ошибки (rw ломает мотив на X^4; aeval не свернул литералы)
  R3: 0 ошибок

CHECKS:
  lake_env_lean: EXIT 0
  lake_build: "Build completed successfully (7756 jobs)" EXIT 0
  q3_check: "q3_check ok" EXIT 0
  axiom_profiles: 6 деклараций [propext, Classical.choice, Quot.sound]
  sorryAx: НЕТ

W9_LEDGER:
  CLOSES: [F72_1B_D0_D4_PHYSICAL_HERMITE_EXACT]
  OPENS: []
  общего parabolic-cylinder API НЕ строили — судья запретил, и не понадобилось

NOT_DONE:
  h0_h4_normalization: вторые равенства директивы (= 2^(-1/4) h_0 и = 2^(5/4) sqrt3 h_4)
    НЕ доказаны: объектов h_0, h_4 в проекте нет, а вводить их нормировку —
    это F72.0B, где судья ещё не выбрал R1/R2. Определять бумажный объект нашей
    формулой = C10-ловушка, которую он назвал прямо.
  вместо них доказано разложение через УЖЕ существующий explicitCCMLimitH —
  оно полностью определено и ничего не открывает.

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```
