# m248 spike and separator trend through m600

DIAGNOSTIC_NEVER_A_PROOF. Route B CHALLENGER / NOT_RH. Source `1d3818cd227bf5f27786adf0c82e5b5d5d9ab11b`; same literal even carrier, N=m,L=log m and strict γ<T sectors. No route-state change.

**The m248 spike is one quiet residual direction with substantial complement leakage, removed by the next zero constraint.** At q127,r122, the first two singular values of AQ are2.10503849 and.71184856. The leading mode carries89.6942% of ||AQ||_F² and has98.2260% squared overlap with the largest eigenmode of D=QᵀAQ (index121,λ_D=1.46327069). It is not itself that eigenvector. Its residual decomposes as

    δ²=||Dy||²+||By||²=2.10634921161+2.32483783977,
    B=UᵀAQ.

B contributes52.4654% ofδ². Only2.6861% carrier mass in a full-A eigenmode at7.51460560 contributes1.51680378 toδ²; small high-energy leakage explains why the normal λ_r≈2.154 does not control ||AQ||. The carrier coefficients n247/246 carry38.13%/15.36% of the mode norm; f(L/2)=5.29188. The vectors and profiles are saved in spike248/.

At Ω248=282.624484313, zero127 is included and128 excluded. The optimal sector is T∈(282.465114765,283.211185733], intersect κ≥1. Its representative midpoint is T*=282.838150249.

|zero|γ|distance from Ω in local spacings|distance from T* in local spacings|preceding gap / local spacing|
|---:|---:|---:|---:|---:|
|127|282.465114765|−.096529|−.225945|1.959938|
|128|283.211185733|+.355607|+.226101|.452203|

These are the only zeros within one local mean spacing of Ω or T*. Local spacing is2π/log(γ/(2π)). The127→128 gap is.746070968, or.452203 local spacings; its carrier normalization ΔγL/(2π) is.654669. Zero129 at284.835963981 is1.3424 local spacings aboveΩ, but.9863 above the sector's upper endpoint; the CSV distinguishes these cutoffs.

Adding zero128 removes85.9368% of the leading quiet mode's squared norm. The neighboring sectors and sizes show the spike is cutoff-sensitive:

|m|q,r|δ|λ_r|gap|scope|
|---:|---|---:|---:|---:|---|
|247|127,121|1.233647|1.555451|.321804|best admissible|
|248|126,123|7.363071|2.321396|−5.041675|belowκ1|
|248|127,122|2.105038|2.153838|.048799|best admissible|
|248|128,121|1.027817|1.067360|.039543|next sector|
|248|129,120|.620576|.357875|−.262701|next sector|
|249|127,123|4.564009|2.299223|−2.264786|belowκ1|
|249|128,122|1.223007|2.154869|.931862|best admissible|

At249,κ1 already includes zero128; it does not at248. Smallerδ in the next248 sector does not improve the best gap because λ_r also falls. All21 q125..131 comparisons, mode coefficients, node normalizations and768/1024-bit frame repeats are retained. See spike248/REPORT.md.

**Trend: no positive uniform margin is demonstrated at the current resolution.** All90 cells on m310,320,…,600 are complete, covering15073 nontrivialκ≥1 sectors by371 residual evaluations and14702 explicit spectral bounds. ζ has14 resolved numerical separators and16 UNRESOLVED cells; plant and DH have30 NO_NUMERIC each. Unresolved ζ cells are360,400,410,420,440,450,470,480,490,520,540,560,570,580,590,600. They are not declared to lack every sub-resolution strict separator. In particular, the plotted zero is a censoring convention, not an exact gap value.

We define δ_max(m)=max_(κ≥1)||AQ||. Because J shrinks withκ, this is exactly δ atκ1; it is not the residual at the sector maximizing the gap. Let g*(m)=max_(κ≥1)(λ_r−δ). BINS.csv uses six fixed five-m blocks and medians of g* across m, rather than medians over mostly tiny-residual κ sectors:

|m block|ζ block maxδ_max|ζ median g*|resolved passes|
|---|---:|---:|---:|
|310–350|5.15821|.616328|5/5|
|360–400|5.22120|.0123143|3/5|
|410–450|2.38599|unresolved around0|1/5|
|460–500|1.71867|unresolved around0|2/5|
|510–550|6.64867|.0634755|3/5|
|560–600|3.28935|unresolved around0|0/5|

Descriptive fits response=a+b log m:

|response|a|b|R²|
|---|---:|---:|---:|
|ζ δ_max,30 values|11.2585|−1.42951|.0362|
|ζ five-sample block maxδ_max|14.6081|−1.72705|.0366|
|ζ five-sample median g*|5.00338|−.801109|.4691|
|plant δ_max,30 values|11.2475|−1.42795|.0361|
|DH δ_max,30 values|−3.04910|1.08265|.00667|

The residual fits explain almost none of the variation. The median-gap fit is dominated by the first block: Theil–Sen slope is−.05265, and omitting one block changes the OLS slope over[−1.03851,+.03802]. Thus this is intermittent collapse to numerical resolution with rebounds, not evidence for a monotone logarithmic decay law or stabilization at a positive constant. Resolved isolated gaps persist through550. Exact asymptotic closure remains open.

An additional discriminator rejects δ spikes as an arithmetic signature: ζ and plant δ_max differ by at most.003435 on this grid (correlation.999999907). Exactly, J_plant⊂J_ζ and (A_plant−A_ζ)J_plant=0, hence δ_plant≤δ_ζ at the same cutoff. The observed near equality coexists with different separator outcomes. Full-spectrum rank placement and leakage matter; a residual trend alone does not separate the worlds.

A finite algebraic shortcut toward the stronger question is proved in spike248/TRACE_LEMMA.md: an actual separator with0<r<d/2 implies λ_min>−trA/(d−2r). A cofinal source-trace bound plus a uniform rank fraction and a proved separator could therefore replace direct bottom-eigenvalue estimation. Neither those cofinal hypotheses nor the required same-carrier off-critical witness comparison follows from these fits. At248 the trace bound is only−140.86, so it does not supply positivity.

Sources: GL256/320 pilots, m300 source regression, independent nullspace and high-precision frame checks, complete numerical DH census through900 and bounded review are included. The DH900 table has798 upper zeros,746 on the line and26 quartets; the original600-height coordinates are unchanged. All claims remain finite numerical diagnostics, without interval source/zero-completeness certification.
