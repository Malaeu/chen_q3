# Arithmetic-coupling PSD intervals, literal even CCM m16..300

DIAGNOSTIC_NEVER_A_PROOF. Route B CHALLENGER / NOT_RH. Mathematical source pin rh_clean1d3818cd227bf5f27786adf0c82e5b5d5d9ab11b; delivery preserves the later m248/trend commit. No route-state or RH export.

We split the unchanged source as A(u)=C+uB, C=A^(Gamma,poles), B=A^(arith). The ζ B includes every Λ(n)/sqrt(n) atom with its original form sign and all prime powers. DH uses all of its signed logarithmic-derivative coefficients, including non-prime-powers; it is not replaced by ζ weights. In the doubled-atom-2 family only the integer n=2 atom is doubled: B_double2=B_zeta+B_atom2, C_double2=C_zeta. Both parts are scaled together by u. The odd pole moment vanishes on this even carrier; the even pole and complete smooth source remain in C.

**All855 primary cells are complete.** The primary numerical tolerance is ε_m=100ρ_m, where ρ_m=1000 eps64(m+1) max_world(1,||C||₂+||B||₂). The same ε_m is used for all three worlds; it ranges from3.019e−9 to2.651e−7. These intervals are I_ε, not a measurement of the unrelaxed I_0.

|family|nonempty numerical interval|empty numerical interval|
|---|---|---|
|ζ|all285 m16..300|none|
|doubled integer2|none|all285 m16..300|
|DH|39 cells,m16..54|246 cells,m55..300|

DH51..54 may have negative baseline levels smaller than ε; their inclusion is an ε-relaxed result, not positivity of the original source. Empty means incompatible Rayleigh constraints over **all real u**, not merely failure near1 or on u>=0. The paired numerical dual witnesses have negative constants at least4.85e6 guard units from zero. They are retained separately from endpoints, which do not exist for empty sets.

Example ζ primary endpoints, always reported as offsets to avoid rounding them to1:

|m|ε_m|u_minus−1|u_plus−1|
|---:|---:|---:|---:|
|16|3.01894e−9|−3.88811e−9|1.13782e−9|
|80|3.67765e−8|−2.45298e−8|3.99489e−9|
|248|1.99789e−7|−1.03537e−7|1.16045e−8|
|300|2.65079e−7|−1.32555e−7|1.39312e−8|

SUMMARY.csv gives every m/family, endpoints, ε, precision guard, quiet-space comparison and status. ENDPOINTS.csv gives the first-exit generalized mode, arithmetic slope, source energy, residual checks and quiet membership. Full carrier vectors and infeasibility witnesses are in the lossless data archive. C alone is indefinite, so u=0 is not assumed to be an admissible anchor.

**Both first-exit carriers lie in the quiet space to numerical precision.** J is the κ1 space at T=2πm/logm. Every ζ endpoint has ||Qᵀx||²>=1−1.6e−15; across all nonempty ζ/DH cases the minimum is.99999999808. Double2 uses explicitly labeled REFERENCE_J_zeta: no matching altered-source zero census is invented. In eight selected windows, quiet-only and full-pencil endpoint offsets differ by at most7.72e−16. At the primary tolerance, however, many quiet eigenvalues are at the float floor, so an individual ordinal eigenvector inside that cluster cannot be identified reliably.

**The ε sensitivity is decisive.** All285 binary64 ζ smallest quiet eigenvalues are unresolved. A regression of the primary widths against their printed near-zero values would be meaningless. Independent400-bit source/120-digit pilots resolve m16,24,40, with ε reduced from1e−20 to1e−100:

|m|smallest quiet eigenvalue|u_minus−1 at ε1e−100|u_plus−1 at ε1e−100|
|---:|---:|---:|---:|
|16|5.45614e−38|−4.65920e−32|5.30697e−37|
|24|2.69051e−54|−4.18978e−48|2.57667e−53|
|40|2.98118e−85|−2.02388e−78|2.93395e−84|

The widths plateau at4.65926e−32,4.18981e−48,2.02388e−78 as ε decreases, in contrast to their much wider primary binary64 tubes. These are numerical small-window scales, not a cofinal extrapolation or an interval certificate. MP plots and the complete15-row ε sweep are included.

In those pilots, the **upper exit is the lowest quiet mode** (squared overlaps>.99999999998). The ratio (u_plus−1)/λ_quiet,min is9.7266,9.5769,9.8416. Its B slope is approximately−.103. The **lower exit is a mixture**, about93.3% lowest quiet mode and6.7% second quiet mode, with positive B slope≈.068; it is not just the second mode. Its much larger baseline Rayleigh scale explains the asymmetric lower endpoint. MP endpoint coefficients and overlaps are in mp_pilots/ENDPOINTS_m*.json. No universal relation based only on λ_quiet,min is inferred from three windows.

The computational shortcut is an exact finite congruence. At any strict feasible anchor a, G=C+aB+εI=LLᵀ and H=L^-1 B L^-T give u_minus=a−1/h_max and u_plus=a−1/h_min for positive/negative extreme h. Boundary carriers are normalized L^-T times the corresponding H eigenvectors. This computes the whole interval without scanning u. When no feasible anchor is known, global affine Rayleigh cuts find either an anchor or incompatible bounds; singleton/near-tangent cases would remain unresolved. None occurs in the855 primary cells. Source errors scale as e_C+|u|e_B, not a fixed u1-only radius.

Additional selected n=2-only scaling is in EXTRA_DIRECTIONS.csv; factor2 lies outside every tested n=2 interval. This distinguishes a single-atom direction from multiplying the whole arithmetic block. The inbox verdict70662bc531e7b90158cf7d0fd3dc415f3bd927eb supplies only that control definition here; INPUT_VERDICT.md has verified SHA256 f079197e61b57b2e3cf8c36f6cfed35b95912f7efc6691d938eb7f64ae7759a9 and Git blob d00a55c75448d0bf4d4da4aceb24a3b37f8fef2f. Its other mathematical claims are not newly adjudicated by this experiment.

Source regressions,48 additional tolerance cells, ε pilots,570 quiet frames, complete scalar/vector receipts and independent review are retained. Endpoint residuals are<=3.0e−15 in the primary survey and3.42e−115 in the MP pilots. All positivity, emptiness and scaling statements remain diagnostics for the stated tolerance and numerical source. Exact I_0 throughout m16..300 is not resolved by the primary survey.
