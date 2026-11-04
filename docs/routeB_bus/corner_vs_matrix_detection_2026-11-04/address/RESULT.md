# DH failure addresses — B++

DIAGNOSTIC_NEVER_A_PROOF. CHALLENGER / NOT_RH. No RH claim or D0/route-state change. Preregistered AD1–AD3 at5500edb57a9f8963de4f721e2cba4b2b371f06a4 before address calculations.

The DH failures concentrate near off-line zero heights much more than either specified control does, but the prediction that90% lie within one grid step fails. The association with beta has the predicted sign among detected pairs, with substantial censoring and no independent-sample statistical claim.

## All events and census coverage

We reconstructed the original selected-entry screen for every integer m=2..2000 and j=1..m, without assembling matrices or solving eigenproblems. The event is the union Ajj<0 OR det(A[{0,j},{0,j}])<0, counted once per(m,j). Both event counts match the saved source at every one of the1999 m. A00 stays nonnegative.

There are18,811 events on1828 distinct m:18,799 have both negative diagonal and failed minor;12 are minor-only; none are diagonal-only. [events.csv](events.csv) records omega=2pi*j/log m, both flags and margins, nearest off-line pair/beta, nearest on-line zero, both distances in grid steps, and census-edge flags for every event.

The input numerical census contains26 off-line pairs and746 critical-line zeros below900, Git blob35396541cbc976d0dc8a1c76bf45802c8602bb84. It is inherited NUMERICAL_NOT_CERTIFIED data, not an independently certified zero census. Of our events,15,116 have omega<=900;3695 lie beyond its height bound. A nearest-zero result beyond900 means nearest in this supplied census, not necessarily nearest actual DH zero. No below900 event has its nearest off-line address ambiguous at the upper census boundary.

|population|events|within1 step of OFF-line|within1 step of ON-line|median OFF distance|median ON distance|OFF nearer than ON|
|---|---:|---:|---:|---:|---:|---:|
|all events, supplied census|18,811|68.1995%|34.0758%|0.89670|1.21495|57.0783%|
|omega<=900|15,116|84.8703%|42.4054%|0.84756|1.07607|71.0307%|

All medians use the left inverse weighted empirical CDF at1/2 (the lower median for even unweighted samples). Distances use absolute frequency differences, divided by2pi/log m. beta is sigma_right; displacement beta−1/2 is separately retained.

AD1 (P=.80): FAIL, both on the requested all-event census statistic and within900. A post-run arithmetic censor bound makes this robust to the unobserved higher zeros: there are12,829 known one-step hits below900; even if all3695 above900 events became hits, the total would be16,524/18,811=87.8422%, below90%, conditional on completeness of the supplied sub900 census. See [CENSOR_BOUND.json](CENSOR_BOUND.json); this does not certify the census itself.

AD2 (P=.85): supported by the preregistered comparison: off-line one-step hit rate is higher AND off-line median distance is smaller, both overall and within900. This is an association of failure locations with supplied zero heights, not causal identification of an individual zero's contribution.

## Null controls

Uniform control uses PCG64 seed20261104,1000 independent draws on[0,Omega_m] for each of the1828 event m, weighted by its event count. Zeta control uses the20 smallest physical zeta diagonals at each of those same m, including j=0; it retains both equal-m and event-count weights. Both are compared with the SAME DH zero census. Their frequency distributions differ by design: zeta's smallest diagonals tend to low modes.

|event-weighted population|OFF one-step hit|ON one-step hit|median OFF distance|median ON distance|
|---|---:|---:|---:|---:|
|DH events, all|68.1995%|34.0758%|0.89670|1.21495|
|uniform, all|3.7160%|70.4546%|17.1482|0.48577|
|zeta20, all|0.02605%|47.7008%|88.6627|1.04960|
|DH events, omega<=900|84.8703%|42.4054%|0.84756|1.07607|
|uniform, omega<=900|4.9314%|93.4992%|11.8568|0.35323|
|zeta20, omega<=900|0.02605%|47.7008%|88.6627|1.04960|

The20-diagonal equal-m result is OFF0.02735%, ON51.9557%; full weighted/equal-m metrics are in [SUMMARY.json](SUMMARY.json). Uniform samples outside900 have the same census limitation as events; the in-range rows are reported explicitly. Per-m random summaries are saved, with deterministic seed/code for exact regeneration, rather than a huge table of all1,828,000 draws. Individual zeta controls are in [zeta_small_diagonal_controls.csv](zeta_small_diagonal_controls.csv).

## First detection of each off-line pair

A pair is detected when ANY negative diagonal or failed corner-sharing minor has mode frequency within one step of its height, whether or not that pair is the mode's nearest zero. Thus this is an address test, not a proof that that pair caused the failure. First means every saved integer up to that m was screened. A missing detection is censored at>2000, never assigned an observed crossing.

|gamma|beta=sigma_right|first m|
|---:|---:|---:|
|85.69935|0.808517|75|
|114.16334|0.650830|622|
|166.47931|0.574356|>2000|
|176.70246|0.724258|179|
|240.40467|0.869531|207|
|320.87649|0.819550|291|
|331.05026|0.768223|302|
|366.64091|0.628508|1615|
|411.79674|0.815874|394|
|440.48451|0.708882|430|
|520.94380|0.515918|>2000|
|531.27973|0.846954|532|
|548.90679|0.729533|683|
|566.50971|0.786559|659|
|595.02338|0.582856|>2000|
|611.77510|0.628252|>2000|
|646.98682|0.610765|>2000|
|657.10837|0.760597|684|
|692.89249|0.788703|731|
|737.76700|0.777360|786|
|783.65301|0.853001|839|
|811.76579|0.668551|>2000|
|847.46573|0.561948|>2000|
|857.29589|0.856109|932|
|864.11809|0.680900|956|
|892.14903|0.688430|980|

All19 observed pairs have the same first diagonal/minor m in this one-step address test; seven are censored. The complete mode, Omega and separate firsts are in [pair_first_detections.csv](pair_first_detections.csv). [Plot: first m against beta and gamma](first_detection_by_beta_height.png) shows censored pairs with open triangles at2001, not measured detections.

AD3 (P=.65): predicted sign supported among the19 observed pairs: Spearman(beta,first m)=−0.322807. The descriptive independence-based p-value is0.178 and is NOT evidence of a significant independent-sample law. Assigning all censored firsts2001 gives−0.711459; partial rank correlation after linear removal of height ranks is−0.553842. These are sensitivity diagnostics, not substitutes for the preregistered observed-only statistic; selection/censoring and finite frequency admission matter.

## Owner example checks and validation

|m,j|nearest off-line gamma|OFF distance steps|nearest on-line gamma|ON distance steps|
|---|---:|---:|---:|---:|
|75,58|85.69935|0.888271|83.10884|0.891795|
|463,234|240.40467|0.839208|239.06817|0.466355|
|1800,137|114.16334|0.808549|116.72151|2.243227|

The requested Mythos examples are reproduced. The m463 example is actually closer to an on-line zero; it must not be used alone to assert an exclusive off-line address.

A fresh unchanged selected-entry MP source at320 bits confirms that all three example cells are events. An independently assembled full float zeta component matrix at m75,463,1800 reproduces all20 control indices, with maximum selected diagonal error5.56e-14. See [CONTROL_VALIDATION.json](CONTROL_VALIDATION.json). The entire1999-cell count-reconstruction gate is in [dense_reconstruction_gate.csv](dense_reconstruction_gate.csv). Strict screen signs are numerical; inherited selected confirmations do not turn every event into an interval certificate.

The producer loads the EXACT frozen DH calc/trigamma function bodies by AST to avoid historical machine-specific imports; only its return is augmented with existing intermediates. This preserves original DH operations. Those sine/cosine intermediates are reused for independently specified zeta diagonals, retaining all prime powers and the native pole. All source inputs carry SHA256 and Git-blob pins in inputs/SOURCE_PINS.json. The full address scan took161.6 wall seconds before output/plot bookkeeping and solved no eigenproblems.

Replay: `python3 address_probe.py`; `python3 verify_controls.py`; `python3 summarize_saved.py`. Requires NumPy/SciPy, gmpy2/python-flint, threadpoolctl and matplotlib. The final independent read-only review is in ../review/. These finite associations are diagnostic only.
