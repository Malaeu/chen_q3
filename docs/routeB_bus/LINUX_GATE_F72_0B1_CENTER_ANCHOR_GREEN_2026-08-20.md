# LINUX GATE — F72.0B1 центральный якорь скаляра: GREEN

```yaml
DATE: 2026-08-20
FLOOR: F72_0B1_CENTER_ANCHOR_SCALAR_LOCK
MARKED: NEXT_EXECUTABLE_NODE, цена 1/10 (вердикт REQ-J, 7893786e)
WRITTEN_BY: Linux-тело (Codex не поднят)
FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CenterAnchorScalarLock.lean
GIT_BLOB: a4195440b1ad3edfca785a3568fa9c8605fd3ff1
SHA256: 491a81328ad11e2b92a0c3df72a5a6625cadd619882f98a346f4faf0a9b89e26
LINES: 149

ROUNDS:
  R1: 0 ошибок — с первого прогона

CHECKS:
  lake_env_lean: EXIT 0
  lake_build: "Build completed successfully (7838 jobs)" EXIT 0
  q3_check: "q3_check ok" EXIT 0
  axiom_profiles: 10 деклараций [propext, Classical.choice, Quot.sound]
  sorryAx: НЕТ

PROVED (весь список директивы + два сверх):
  f0(k,0) != 0                selectedFerrersCenterZero_ne
  f4(k,0) != 0                selectedFerrersCenterFour_ne
  a0(k) != 0                  centerAnchorScalarZero_ne
  a4(k) != 0                  centerAnchorScalarFour_ne
  a0(k)*f0(k,0) = 1           centerAnchorScalarZero_mul_center
  a4(k)*f4(k,0) = 3           centerAnchorScalarFour_mul_center
  СВЕРХ:
  вещественность центров      selectedFerrersCenter{Zero,Four}_im
  центры целей D_0(0)=1, D_4(0)=3, и совпадение якорей с ними
                              cylinder_centers,
                              centerAnchor_matches_cylinder_centers

SHELF_USED (ничего не создавали):
  normalizedPhysicalMode_zero_ne   D0Mode4FerrersNormalizedZeroCountTransport.lean:92
  normalizedPhysicalMode_im_eq_zero D0Mode4FerrersNormalizedActualModeLocalFields.lean:22
  оба применены к selectedFerrersPreAnchorSolution{0,4} через pair_spec.
  Судья закладывал код отказа F72_0B1_SELECTED_CENTER_REAL_OR_NONZERO_INTERFACE_GAP
  на случай, если этих двух на полке нет. Они есть — разрыв не открылся.

FIREWALLS_RESPECTED:
  c09_precommit: скаляр ОПРЕДЕЛЁН до всякого утверждения о рейте
  c10_no_fitting: скаляр читается с источника (значение в центре),
    а не подбирается по наблюдаемой ошибке
  бумажный ps_n НЕ определялся, h_0/h_4 НЕ вводились

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```
