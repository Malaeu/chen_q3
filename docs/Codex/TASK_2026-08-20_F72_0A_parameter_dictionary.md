# TASK 2026-08-20 — F72.0A: параметрический словарь (директива судьи, дословно)

Порядок твоих задач после резета (пересмотр, заменяет прежний):
1. TASK_2026-08-19_supplier_contract_link.md — две однострочные правки цепи.
2. TASK_2026-08-20_return_briefing_and_preanchor_inhabitant.md раздел 5 —
   НЕ писать обитателя, он готов и РАТИФИЦИРОВАН судьёй (bc65b407);
   только независимая сверка (lean + q3_check + профили) и доклад.
3. ЭТА задача — первый новый Lean-узел стены L73.2.

Директива судьи (вердикт REQ-G, дословный блок):

TASK: F72_0A_SELECTED_FERRERS_PROJECT_PARAMETER_DICTIONARY

Create exactly one new file:
  Q3/Proofs/RouteB/G6N1SelectedFerrersPaperParameterDictionary.lean

Direct imports only:
  G6N1SelectedFerrersPreAnchorDataInhabitant
  D0Mode4FerrersDimensionlessFourierScaling

Prove and export the project-side dictionary only:
1. selectedFerrersPaperDegree j := 2*j.
2. selectedFerrersPaperLambda k := sqrt(k+2).
3. selectedFerrersPaperGamma k := 2*pi*(selectedFerrersPaperLambda k)^2.
4. gamma = 2*pi*(k+2).
5. gamma^2 = mode4JacobiG(k+2).
6. degree(0)=0 and degree(2)=4.
7. selectedFerrersPreAnchorPair k has the same lambda and the exact
   S0/S4 identities already exported by pair_spec/data_pair_spec.

Mandatory W9 ledger in the source header:
  CLOSES: [SELECTED_FERRERS_PROJECT_PARAMETER_INDEX_DICTIONARY]
  OPENS: []

Forbidden:
  - do not define ps_n or paper h_n,lambda;
  - do not state project mode = scalar * ps_n;
  - do not add Satz-9 or Fuchs assumptions;
  - do not introduce factor 4;
  - do not touch CCMLemma73PreAnchorPort;
  - do not touch F72.1 or F72.3;
  - no sorry/admit/custom axiom/native_decide.

Validation:
  lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersPaperParameterDictionary.lean
  lake build Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary
  scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersPaperParameterDictionary.lean

Success: F72_0A_SELECTED_FERRERS_PROJECT_PARAMETER_DICTIONARY_LEAN
  with exactly [propext, Classical.choice, Quot.sound].
Failure: F72_0A_PROJECT_PARAMETER_DICTIONARY_KERNEL_MISMATCH

Полный контекст: docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_G_SELECTED_FERRERS_PAPER_OBJECT_DICTIONARY_2026-08-20.md
Per-action OK владельца перед коммитом/пушем — как всегда для твоей цепи.
