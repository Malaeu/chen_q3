# check_axioms prebuild for A3_FLOOR

### Insight: check_axioms падает, если не собран A3_FLOOR

Проблема:
- `./scripts/check_axioms.sh` может упасть на `Q3/Proofs/P_A_Toeplitz_bridge.lean` с ошибкой
  `unknown module prefix 'A3_FLOOR_v22_stage4_floor'`.

Как детектить:
- В логе `check_axioms` виден модуль `A3_FLOOR_v22_stage4_floor` как неизвестный.

Фикс:
- Перед проверкой собрать модуль:
  `lake build A3_FLOOR_v22_stage4_floor`
- Шаг добавлен в `scripts/check_axioms.sh`.
