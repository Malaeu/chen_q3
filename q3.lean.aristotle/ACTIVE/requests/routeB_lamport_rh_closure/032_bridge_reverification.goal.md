# ГОЛ 032 — BRIDGE LOCAL REVERIFICATION + INTEGRATION (fail-closed)

От: Mythos. Статус: CHALLENGER / NOT_RH. BUS_010_VOID.
Основание: Aristotle standalone вернул RIEMANN_BOUNDARY_CELL_BRIDGE_PROVED.
Чужому облаку на слово не верим — переверификация с нуля локально.

## Вход
aristotle_bridge/ в шине: RequestProject/RiemannBoundaryCellBridge.lean
(SHA-256 d47a0e1d1c3aa81b7f14…), lakefile.toml, lean-toolchain, RESULT.md.
Теоремы: riemannBoundaryCellBridge_finiteReduction / _main / _zeroMass /
_Estar; def Estar.

## Задача
1. Свежая сборка: в чистой копии (scratch, вне mainline) `lake build`
   по их lakefile/toolchain (mathlib подтянется по lake-manifest из
   тарболла — при необходимости скопировать manifest из
   /tmp/ab/output-final_aristotle/). Exit code в отчёт.
2. Гварды: grep sorry/admit/axiom/native_decide = 0; никаких новых axiom.
3. `#print axioms` для всех четырёх теорем: ровно
   [propext, Classical.choice, Quot.sound] — вывод дословно в отчёт.
4. Семантический аудит (по Прошке): формулировки соответствуют контракту
   ARISTOTLE_TASK_RiemannBoundaryCellBridge.md (SHA 7161d737…) дословно:
   константа K*b + (‖h 0‖+K*b) + ‖h b‖ явная, Липшиц на Ico (НЕ на замкнутом),
   ∃C не подменяет явную константу. Любое расхождение = FAIL.
5. При зелёном: леджер-запись в compiler-ledger: RiemannBoundaryCellBridge
   scope=ABSTRACT verifier=LEAN (машинная теорема, безусловная); зеркало
   по правилу 014 (aristotle_bridge/ включительно).

## Отчёт
032_bridge_reverification.answer.md. РОВНО ОДИН код:
BRIDGE_LOCAL_REVERIFIED · BRIDGE_LOCAL_BUILD_FAIL (+лог) ·
BRIDGE_GUARD_VIOLATION (+что) · BRIDGE_SEMANTIC_MISMATCH (+где).
STATE не трогать.
