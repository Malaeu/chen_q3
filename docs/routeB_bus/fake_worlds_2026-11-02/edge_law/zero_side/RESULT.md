# Finite zero-side endpoint probe

DIAGNOSTIC_NEVER_A_PROOF. Exact identities and unconditional/conditional distinctions are in FORMULAS.md. The transform identities, exact finite-block square expansion and real-node remainder checks passed. The explicit absolute remainder bound is far too loose to prove the moving-cutoff endpoint law. No claim about the proposed asymptotic coefficient is promoted.

## Zeta known real-zero prefixes through400

Each energy includes both signs of the listed real spectral node. These are numerical critical-zero prefixes, not an assumption about unlisted zeros. Source−prefix is a labeled difference, **not an unconditionally positive infinite zero tail**.

|m|q|source lambda|zeros≤T|T<zeros≤400|source−prefix|head/source|
|---:|---:|---:|---:|---:|---:|---:|
|55|27|0.000107051246|5.2085025e-05|4.10819662e-05|1.3884255e-05|0.486543|
|80|41|3.81763316e-07|1.50024677e-07|1.97912817e-07|3.38258224e-08|0.392978|
|120|63|2.18296451e-08|1.07856131e-08|8.9179517e-09|2.12608029e-09|0.494081|
|120|64|6.13450066e-10|2.33585049e-10|3.00228702e-10|7.96363147e-11|0.380773|
|120|65|6.82204596e-12|3.02776069e-12|2.62735648e-12|1.16692878e-12|0.44382|
|160|89|4.78557636e-16|1.73254809e-16|2.08048926e-16|9.72539015e-17|0.362035|
|200|115|5.81805177e-23|2.54971947e-23|1.85923474e-23|1.40909757e-23|0.438243|
|240|139|2.34412717e-25|8.18653394e-26|7.61291687e-26|7.64182087e-26|0.349236|

The selected vector lies in J-perp=ran(E^T), not in J=ker(E). Its below-cutoff Fourier values are not required to vanish; the sizable head is consistent with the pinned kernel-orthogonality source.

## Exact finite-block endpoint square expansion

For E=2f(b)sin(bt)/t and R=F−E, on the finite real-zero block(T,400], the exact energy is2ΣE²+4ΣER+2ΣR². The following entries divide each term by the exact block energy, so their sum is1. The cross term is signed.

|m|q|endpoint square|cross term|remainder square|absolute error bound / block energy|
|---:|---:|---:|---:|---:|---:|
|55|27|0.7837077|-2.504031|2.720323|1060.187|
|80|41|0.4131136|-1.111254|1.69814|235515.8|
|120|63|0.4458801|-1.164714|1.718834|1.161314e+07|
|120|64|0.3813908|-0.9480452|1.566654|2.577063e+08|
|120|65|0.5240106|-0.969721|1.44571|2.367034e+10|
|160|89|0.3989187|-0.8037538|1.404835|2.131885e+14|
|200|115|0.3390256|-0.5936522|1.254627|1.373817e+21|
|240|139|0.2260668|-0.5669986|1.340932|3.655821e+23|

These finite data do not support discarding the below-cutoff contribution or the rational remainder. The large negative cross term and positive remainder-square term partly cancel; a positive endpoint-square heuristic alone misses that structure. The nonzero head disproves an exact tail-only identification in these finite cells, and the square expansion shows that endpoint-only is not the complete observed finite tail. These findings do **not** refute the empirical bounded-factor prediction R in[3,5], or a future asymptotic law for the selected family. At T=1.1Omega the fixed-m far-frequency expansion is not uniform. The phase-averaged bare endpoint coefficient2 belongs to a fixed-vector far-cutoff limit, not the joint m→infinity limit at T=1.1Omega. It does not by itself contradict coefficient4 in that joint limit; deriving that coefficient requires near-band, phase and head control.

## DH actual listed quartets through230

The special source−4nu uses the interpolating normalization F(z0)=i; nu denotes zero multiplicity. Generic ground vectors give4nu(a²−b²), with correction−8nu b² versus ordinary2G. Listed multiplicity1 below is a numerical census convention, not a new simplicity proof.

|matched case|height|Re F|Im F|actual quartet|correction vs ordinary2G|
|---|---:|---:|---:|---:|---:|
|dh_m120_q63_density_matched_lower|85.6993485|0.00116999616|0.649069838|-1.68516114|-3.37033323|
|dh_m120_q63_density_matched_lower|114.163343|-0.0296272988|-0.0110641978|0.00302144144|-0.000979331788|
|dh_m120_q63_density_matched_lower|166.479306|0.00816296781|-0.00282589793|0.000234593377|-6.38855929e-05|
|dh_m120_q63_density_matched_lower|176.702461|0.0149674526|-0.00348383673|0.00084755007|-9.7096947e-05|
|dh_m120_q65_density_matched_upper|85.6993485|0.0013711224|0.647997525|-1.67959565|-3.35920634|
|dh_m120_q65_density_matched_upper|114.163343|-2.08815406e-05|-0.0276956225|-0.00306818827|-0.00613638004|
|dh_m120_q65_density_matched_upper|166.479306|0.00784596577|-0.00271550132|0.000216740926|-5.89915792e-05|
|dh_m120_q65_density_matched_upper|176.702461|0.0144921541|-0.0033713958|0.000794624881|-9.09304773e-05|
|dh_m80_q41_density_matched|85.6993485|0.0224014191|0.00943731895|0.00165104236|-0.000712503912|
|dh_m80_q41_density_matched|114.163343|-0.0134255213|0.00523882018|0.000611197538|-0.000219561895|
|dh_m80_q41_density_matched|166.479306|0.00147320202|0.000684829921|6.80532872e-06|-3.75193616e-06|
|dh_m80_q41_density_matched|176.702461|-0.00300647893|-0.00148568733|2.73265947e-05|-1.76581347e-05|

The first quartet contributes a small positive amount on matched80 and about−1.69 on matched120. This is an actual selected-vector observation, not a rule that every off-line quartet is negative or equals−4nu. The script checks K_prefix=2G_positive−4M_im, where M_im is the sum of imaginary squares over **both** positive-height reflected nodes. M_im is not called nu. DH uses the saved230-height census, not an invented400-height census.

## Files, checks and scope

`zero_sums.csv` includes every saved ledger case, its actual cutoff, native/matched mode, endpoint, C_f remainder constant, partial metric decomposition, source-minus-prefix and exact square-expansion error. `node_values.csv` records every complex evaluation; `quartets.csv` the individual quartet pieces. `provenance.json` pins all input hashes and the zero tables. The zeta script automatically adds the new120dps/GL192 m160/200/240 publication cells when present. It normalizes each saved physical vector explicitly.

Reproduce with `python3 probe.py` then `python3 summarize.py` (mpmath). Computation uses120dps and no new eigensolves. Assertions check the independent shifted-sinc synthesis, exact partial metric identity, finite-block square expansion and every real-node remainder bound. No outward interval certificate, new zero census, assumption of RH above400, all-zero-tail positivity, or cofinal source bound is supplied.

The completed six-cell extended-DH comparison is in [DH_EXTENDED.md](DH_EXTENDED.md). Native240 falsifies the registered first-quartet-dominance hypothesis: its new240.405 quartet supplies about−4.09807, whereas the original85.699 quartet is only about−9.65e−6.
