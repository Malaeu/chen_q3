---
tags: [pipeline]
priority: medium
last_updated: 2026-02-08
---

# Search / Recall Cheatsheet

## Fast grep
- Find axioms: `rg -n "\baxiom\b" q3.lean.aristotle/Q3 -g '*.lean'`
- Find sorries: `rg -n "sorry|admit|exact\?" q3.lean.aristotle/Q3 -g '*.lean'`
- Find lemma usage: `rg -n "<lemma_name>" q3.lean.aristotle/Q3 -g '*.lean'`

## LaTeX ↔ Lean
- LaTeX section list: `rg -n '\\(input|include)\{' full/RH_Q3.tex`
- Map: `KB/maps/latex_to_lean.md`

## Embeddings (semi‑auto)
- From `q3.lean.aristotle/`: `./scripts/research_oracle.py query "keyword" -c q3_docs`

## Axiom status
- `lake env lean Q3/CheckAxioms.lean`
- `#print axioms Q3.Main.RH_of_Weil_and_Q3`
