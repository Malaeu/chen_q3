# MP P1–P4 v2 pilots

DIAGNOSTIC_NEVER_A_PROOF; source floor empirical, not interval-certified.

The literal relative-gap selector chooses a one-dimensional face in every pilot. Full inherited quiet compressions fail the declared admissibility gate, so P2–P3 stop there. The selected face passes; its scalar price map has the dimension-forced large parameter kernel. The ones image is retained rather than set to zero.

|m|face|gap|J ratio|face ratio|budget kernel|scalar ball optimum|
|---:|---:|---:|---:|---:|---:|---:|
|16|1|867540.09|0.20455427|3.2908569e-38|6|2.2753829|
|24|1|1589363.0|0.36652641|1.618015e-54|9|2.2812377|
|40|1|6926791.8|0.085680079|1.8027581e-85|12|2.2700902|

The scalar analytic ball optimum is nonnegative. Float conic candidates are explicitly projected back to the MP budget gauge and unit ball, and their finite primal/dual quadratic data are recomputed in MP. This is not a claim of an MP optimizer or interval SDP certificate. A positive optimum rejects strictness of this face price problem; a kernel additionally prevents exclusion of nonzero parameter directions.

For P4 the PSD rank-one pole has an infinite upper ray structurally. Reported narrow widths for indefinite knobs do not apply to this pole. The raw knob inertia uses absolute1e-110 numerical floor; this is a reporting threshold, not a source error enclosure.

Reproduce: `STIFFNESS_BASE=/path/to/arithmetic_coupling_2026-11-03 STIFFNESS_LOCAL=/scratch/stiffness OPENBLAS_NUM_THREADS=1 python mp_prices.py prices 16 24 40` (install numpy/scipy/gmpy2/mpmath/cvxpy/clarabel or set PYTHONPATH to their environment). MP caches are reused and were built once per pilot by the unchanged pinned source and quiet constructors. The quiet builder uses its inherited kappa=1 reference.

Primary binary faces use the inherited summary precision_floor and are read verbatim from root binary_cells records; the raw NPZ numeric_radius comparison is retained only as a separately labeled sensitivity. Neither binary choice is substituted for the MP source-floor selection.

The exact MP scalar optimizer is recorded alongside the float conic candidate. Its trace-one Y=1 is a valid ball dual but is NOT an annihilating stress: the projected price residual is about2.27. Inherited MP and binary coupling endpoint carriers are normalized and compared with the selected MP face and quiet carrier, with all overlaps retained in JSON. P4 CSV includes knob inertia, finite-side offsets, witness residuals and overlap masses.
