/-
  PrintAxioms.lean — быстрая проверка без внешних инструментов.

  Каждая строка обязана прочитаться как:
      '<имя>' depends on axioms: [propext, Classical.choice, Quot.sound]

  Текстовый подсчёт слов `sorry` и `axiom` в файлах на этот вопрос НЕ отвечает:
  он ничего не говорит о конкретной теореме. Отвечает только ядро.
-/
import Solution

#print axioms Q3Challenge.rplus_analyticOnNhd_shiftedHalfPlane_v3Class
