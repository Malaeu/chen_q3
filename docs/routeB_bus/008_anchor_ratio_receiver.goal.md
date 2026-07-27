# CODEX DIRECTIVE

Один следующий локальный Lean-target:



```
D0AnchorFloorFromUnprojectedMassNormRatio
```

## Statement

Добавить corollary к уже доказанному theorem:

lean



```
theorem D0AnchorFloorFromUnprojectedMassNormRatio
    (D : CoefficientFamily)
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star : ...)
    (hbind : ...)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hmass_pos :
      0 <
        Real.sqrt (L_m i) *
          ‖inner ℂ (V_n_m i 0)
            (gTrial_m i hTrial_m hE_star)‖)
    (hratio :
      δ * ‖gTrial_m i hTrial_m hE_star‖
        ≤
      Real.sqrt (L_m i) *
        ‖inner ℂ (V_n_m i 0)
          (gTrial_m i hTrial_m hE_star)‖) :
    gTrial_m_N i hTrial_m hE_star ≠ 0 ∧
      (∃ ci : CentralIndex D, ci.1 = i) ∧
      δ ≤ Real.sqrt (L_m i) * ‖D.kTrial i 0‖ ∧
      δ ≤ ‖rawFplus D i 0‖
```

## Route

Set
$$
C:=\|g_m\|,
\qquad
a:=\delta\|g_m\|.
$$
From `hmass_pos`, infer $g_m\neq0$, hence $C>0$ and $a>0$. Apply

lean



```
D0AnchorFloorFromUnprojectedCentralMass
```

with:



```
hbound = le_rfl
hmass  = hratio
```

then simplify:
$$
\frac{\delta\|g_m\|}{\|g_m\|}=\delta.
$$

## Forbidden



```
no new axiom;
no separate constants a,C in the final consumer;
no numerical plateau;
no sign assumption;
no projection lower bound;
no theorem weakening.
```

## Validation

Bash



```
lake env lean Q3/Proofs/RouteB/D0AnchorFloor.lean
lake build
#print axioms D0AnchorFloorFromUnprojectedMassNormRatio
```

## Success code



```
ANCHOR_RATIO_RECEIVER_PROVED
```

После этого бумажный фронт окончательно называется:
$$
\boxed{
\texttt{EStarRelativeSourcePackage}
}
$$
а не двумя отдельными «mass lower» и «norm upper» задачами.

------


(Гол 008 извлечён Mythos из вердикта Прошки 2026-07-27-c. Это быстрый corollary к D0AnchorFloor: два source-числа (a,C) заменяются ОДНИМ scale-invariant отношением δ. Точные сигнатуры hE_star/hbind взять из уже доказанной D0AnchorFloorFromUnprojectedCentralMass.)
