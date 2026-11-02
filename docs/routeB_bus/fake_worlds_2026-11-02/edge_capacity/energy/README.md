# Finite source energy split

`DIAGNOSTIC_NEVER_A_PROOF`. This package evaluates the exact finite algebra
of `PROSHKA_VERDICT_EDGE_LAW_RELLICH_v1_2026-11-02.md`, commit
`3fef776b3bd0ebeb9d87e665432ae3e423f2dfb1`, blob
`33a918fc7faad0a56005574d8b6e158eae4db9f2`, equations (5.4)–(5.7).

For the saved physically normalized selected vector f, the ordinary endpoint
trace is e=f(L/2). The constant indicator chi has modal coordinates
`(sqrt(L),0,...,0)`, and h=f−e*chi has zero ordinary endpoint trace. Use the
saved **full original** finite operator A, including all arithmetic, arch,
constant, and zeta pole terms. No pole is added to the DH source.

The finite head pairing is computed from the saved raw physical E. For zeta
its metric is `2 I` on the positive real zero rows. For a DH reflected pair
realified as `sqrt(2) Re(v), sqrt(2) Im(v)`, the corresponding metric is
`2 diag(+1,-1)`, producing the true signed quartet form, not a positive
capacity Gram. Multiplicity/orbit weights must already match the saved
source row metric. The script fails if a DH cell omits its signed metric.

Write K(x,y)=x^T A y and H(x,y) for that finite signed head. The evaluated
quantities are

    H_T=H(f,f),
    C_T=K(chi,chi)−H(chi,chi),
    X_T=2 e [K(chi,h)−H(chi,h)],
    V_T=K(h,h)−H(h,h),
    K(f,f)=H_T+e^2 C_T+X_T+V_T.

These are **finite operator algebra**. Although source equation (5.5)
identifies C_T with a formal endpoint tail, the calculation here is not an
independent infinite-zero-tail sum or an omitted-tail enclosure. No unknown
infinite zero series is numerically truncated.

For nonzero e, each of the four energy terms is divided separately by
`e^2 log(T)/(pi*T)`. Their scaled sum is checked against the selected
Rayleigh ratio R. In particular, the scalar contribution `pi*T*C_T/log(T)`
does not replace the full ratio after head/cross/volume are dropped.
For e=0 the unscaled identity is retained and no R ratio is formed.

`energy_split.py saved_cell.json --label case_name` writes the raw physical
amplitudes, all finite source/head bilinear pieces, all scaled R terms,
absolute and edge-scale identity residuals, normalization/endpoint checks,
and a precision comparison. The same serialized source coordinates are
evaluated at two arithmetic precisions; this checks arithmetic stability,
not the accuracy of the saved matrix, zero census, endpoint, or eigenvector.
The evaluator itself does not rebuild a matrix. For the nine larger source
cells whose saved files contain only the selected vector, `prepare_large.py`
reconstructs the unchanged full source with the pinned `edge_rellich/rellich.py`
moment helper at fixed m, 150 dps and 8-panel GL192, retaining the analytic
archimedean tail. It constructs the finite actual head from the pinned zero
tables, without searching for zeros or solving an eigensystem. Original
selected-vector precision remains recorded separately from the new arithmetic
precision; extra arithmetic digits do not improve that saved input.

No eigensystem, new zero search, route-state change, or RH export is performed.
