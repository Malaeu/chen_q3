# kTrial → Lean — stage 1 answer

Verdict: `KTRIAL_STAGE1_CARRIERS_LOCKED`.

Lean file:
`Q3/Proofs/RouteB/D0KTrialStage1.lean`, lines `15-150`.

| D0 object | Lean lines | source lock |
|---|---:|---|
| `lambda_m`, `L_m` | 15-27 | `D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:27-28`; `H8ULBMAL/fulltext.md:285` |
| `dStar`, `I_m`, `H_m` | 29-51 | `D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:34-38`; `H8ULBMAL/fulltext.md:285-288,312-313` |
| `V_n_m` | 53-117 | `D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:43-51`; `H8ULBMAL/fulltext.md:108-112,285-290,333-335` |
| `E_m_N` | 119-127 | `D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:54-59`; `H8ULBMAL/fulltext.md:333-339,702-704,734-735` |
| `P_m_N` | 129-141 | `D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:61`; `H8ULBMAL/fulltext.md:702-704,734-735` |

Validation:

```text
lake build Q3.Proofs.RouteB.D0KTrialStage1
exit code: 0
sorry/admit/exact?: 0
```

`#print axioms`:

```text
lambda_m : [propext, Classical.choice, Quot.sound]
L_m      : [propext, Classical.choice, Quot.sound]
dStar    : [propext, Classical.choice, Quot.sound]
I_m      : [propext, Classical.choice, Quot.sound]
H_m      : [propext, Classical.choice, Quot.sound]
V_n_m    : [propext, Classical.choice, Quot.sound]
E_m_N    : [propext, Classical.choice, Quot.sound]
P_m_N    : [propext, Classical.choice, Quot.sound]
```

`ROUTE_B_STATE.md`: unchanged.
