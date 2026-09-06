# Semilocal sign table — implementation A

## How to rerun

```
python3 s1_model.py       # S1: |m(tau)|=1, DCT-I carrier checks, Slepian eigenvalues (2 channels)
python3 s1_check2.py      # S1: carrier F^2=I, Gaussian fixed point, uniform-grid alpha_n (shows the O(delta))
python3 semilocal.py      # S2: alias-free dilation Dil=(1/2)F Fhalf; raw F_S = J F J^{-1}
python3 polar.py          # S2: polar-regularised F_S = V F V*, ||B_S|| bounds
python3 s4_tracetest.py   # S4: decisive test that the carrier reproduces Tr(A(I-P-Q)) = L_S
python3 final_run.py      # S5: full family at lambda=1        -> rows_lam1.json,  run_lam1.log
python3 run_theorem.py    # THEOREM_CONTROL_CC20               -> rows_theorem.json, run_theorem.log
python3 run_vR.py         # canonical cutoffs v_R              -> rows_vR.json
python3 run_lambda.py     # lambda = 1, sqrt2, 2 subset        -> rows_lambda.json
python3 make_table.py     # assembles TABLE.md from the json files
```

## Files
- `s1_model.py`   multiplier m(tau); DCT-I carrier; two independent Slepian channels.
- `core.py`       tests, D(v), prime sums, L_S, Q(v), prolate angles on Gauss-Legendre panels.
- `semilocal.py`  alias-free dilation, J, J^{-1}, F_S^src.
- `polar.py`      polar-regularised F_S^pol.
- `carrier.py`    (superseded by semilocal.py/run_table.py; kept for the aliasing demonstration).
- `run_table.py`  carrier operators, projections, traces, and the independent spectral E_S route.
- `tests_family.py` the test family: bumps, pole-null tests, wide controls, f_0 and v_R.
- `theorem_ctrl.py` the CC20-constrained tests v = (d^3 - d/4)(1-(x/h)^2)^8.
