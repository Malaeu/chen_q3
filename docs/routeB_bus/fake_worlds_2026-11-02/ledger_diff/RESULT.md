# Equal-density and signed-ledger comparison: zeta versus DH

DIAGNOSTIC_NEVER_A_PROOF

Base: rh_clean `d26831357b6cb3b2b7d4a569d2031e454952b246`. The pinned kernel source is `c31645a3efd410417f6e2027b4474711bd443348`, blob `98380adf97aab19a900e332b6583c8f731b6d3f6`; its exact bytes are retained in SOURCE_KERNEL_PINNED.md and verified in source_pin.json.

## A. Equal constraint density

For zeta the baseline is T=1.1*(2pi m/log m). DH T is the midpoint between consecutive distinct zero heights giving the same real constraint count q. Each off-line reflected pair supplies two real constraints. Rank=q and dim J=m+1-q in these cells. No row scaling is used for the reported singular values. Delta is the full operator norm ||A Q||, not just the compressed form norm. The count includes all levels below delta*(1+1e-6).

At m=120 the requested exact match is impossible: zeta has q=64, while the DH count jumps from63 to65 at the reflected pair of height114.163342730757. Splitting that pair would change the quiet-space definition. Both DH neighbors are retained. Additional zeta q63/q65 cells give exact same-cardinality bracket comparisons; they are explicitly additional to the zeta kappa1.1 baseline q64.

|m|world|q=rank|dim J|T|delta|sigma_min(F)|N(delta+)-dim J|
|---:|---|---:|---:|---:|---:|---:|---:|
|20|dh|8|13|24.72016873|6.146795191|0.7733222176|7|
|20|zeta|8|13|46.1423332|0.357453775|0.5506904094|0|
|40|dh|18|23|44.01419985|6.542091758|0.4831054821|16|
|40|zeta|18|23|74.9442092|0.1571250602|0.04726911181|1|
|60|dh|29|32|62.49080305|10.32489446|0.5220300281|28|
|60|zeta|29|32|101.2836668|0.05362566021|0.001233109826|2|
|80|dh|41|40|81.12667474|11.15069893|0.5635683826|40|
|80|zeta|41|40|126.1791297|0.00883334827|2.144607462e-6|3|
|120|dh|63|58|113.2698685|9.877013891|0.6741304303|61|
|120|zeta|63|58|169.5032459|0.005667607189|1.390246196e-7|4|
|120|zeta|64|57|173.2390373|0.001667141252|3.325373139e-9|5|
|120|dh|65|56|115.4424282|9.556435554|0.4448708451|62|
|120|zeta|65|56|174.082864|0.0004723759168|1.281275234e-10|5|

The equal-density DH kernels are not quiet: residuals are roughly6–11, while their raw capacities remain of order0.4–0.8. Thus the previous small DH residuals at the same kappa were not preserved by equalizing the number of constraints. This finite comparison does not establish an asymptotic rate or a uniform zeta bound. At the chosen zeta baseline only m20 saturates its own residual count among these exact baseline cells; the other finite count excesses remain explicit.

## B. Signed form on the complement minimum

All components are evaluated on the **same unit vector f** within each case: f minimizes U^T A U and is lifted by orthonormal U. This is the complement bottom, not necessarily the full-carrier bottom. Different worlds/cutoffs have different minimizing vectors, so subtracting their entries is descriptive rather than a common-vector operator comparison.

Because B did not separately specify its cutoff, both density-matched complements and native kappa1.1 complements are included. At m120 the extra zeta bracket complements are included as well:12 ledgers total. The native comparison is shown first below. Every arithmetic entry is the signed form contribution **minus P**; plus/minus labels refer to the sign of b(n), not the sign of the evaluated summand. Scalar H has positive kernel coefficient, c is the signed negative constant, and the pole coefficient is positive for zeta and absent for DH. Empty bins are exact zeros.

The original ledger is lambda=H_original+c+pole−sum P. It uses j_zeta=exp(−s/2)/(1−exp(−2s)), c_zeta=−gamma−log(8pi)−pi/2; DH uses j_D=exp(−3s/2)/(1−exp(−2s)), c_D=−gamma−log(8pi/5)+pi/2, and no pole.

|signed component|zeta55|DH55 native|zeta80|DH80 native|zeta120|DH120 native|
|---|---:|---:|---:|---:|---:|---:|
|H_original|7.793516693|4.817564991|8.170411857|4.841837782|8.466904397|4.84133945|
|c|-5.372183419|-0.6211528532|-5.372183419|-0.6211528532|-5.372183419|-0.6211528532|
|pole|0.03190216505|0.0|0.01009311153|0.0|0.007359515947|0.0|
|prime; b positive|-2.303161592|-0.4656918022|-1.864339136|-0.3224203111|-2.419621859|-0.1070177629|
|prime; b negative|0.0|-0.6718676368|0.0|-0.7691536623|0.0|-0.6956220553|
|square; b positive|-0.08691832652|0.0|-0.6335182968|0.0|-0.3995778743|0.0|
|square; b negative|0.0|-0.9829215302|0.0|-0.8039279966|0.0|-0.5435451015|
|higherpower; b positive|-0.06304846877|0.02701261042|-0.3104637347|0.04211495352|-0.2828807596|0.1141431036|
|higherpower; b negative|0.0|-0.002068501062|0.0|-0.004103483967|0.0|-0.01458491442|
|nonprimepower; b positive|0.0|-1.467990228|0.0|-1.805105479|0.0|-2.247203868|
|nonprimepower; b negative|0.0|-1.296805697|0.0|-1.798775962|0.0|-2.314609687|
|sum = complement lambda|0.0001070512462|-0.6639206461|3.817633164e-7|-1.240687012|6.134500659e-10|-1.588253688|

The full signed split for all12 cases is in ledger_groups.csv; per-atom values, coefficient signs, endpoint zeros and vectors are in ledger_cells/. At native DH m120 the non-prime-power contribution alone is about−4.56181355 on that selected vector (both coefficient signs contribute negatively). This is a same-vector ledger observation, not the minimum eigenvalue of a matrix with those atoms removed.

## Boundary, interior and compensation

The pinned Markdown actually numbers the relevant formulas (2.2), (2.4)–(2.5), (3.3)–(3.4), and (6.1); it has no displayed equation(12). SOURCE_CONVENTIONS.md gives precise source line anchors. To avoid silently assigning a meaning to the different labels in the request, the following definitions are explicit:

- B=2 f(L/2) integral a(s) f(L/2−s) ds.
- I=T_half+Bulk, with T_half=integral a(s)Q(s)/2 ds and Bulk=−2 integral a(s) integral f(x)f'_int(x+s) dx ds.
- All three pieces are saved separately; the Q/2 term is never omitted.

For zeta a=exp(−s/2)[psi(exp s)−(exp s−1)], so P−I_L=B+I, with I_L=integral exp(s/2)Q(s)ds. The compensated zeta identity is lambda=H_plus+(4−cstar)−B−I, where H_plus uses exp(−5s/2)/(1−exp(−2s)). H_original, c_original and the pole must not be mixed with that compensated formula.

For DH the canonical arithmetic Abel split uses a_D=exp(−s/2)Psi_D(exp s), giving P_D=B_D+I_D and lambda=H_D+c_D−B_D−I_D. We additionally evaluate the same x−1 reference subtraction as zeta for comparability: P_D−I_L=B_ref+I_ref and lambda=H_D+c_D−I_L−B_ref−I_ref. This additional reference is **ARBITRARY_REFERENCE_NO_POLE_CANCELLATION**; it does not manufacture a DH pole or main term.

Native kappa1.1 comparison using the common x−1 reference:

|world|m|B_ref|T_half_ref|Bulk_ref|I_ref=T_half+Bulk|I_L|
|---|---:|---:|---:|---:|---:|---:|
|zeta|55|0.001212858036|-0.0005999345866|2.424701578|2.424101643|0.02781388572|
|dh|55|0.1932692967|-0.003996777093|4.667618533|4.663621756|0.003441731715|
|zeta|80|3.862510977e-5|0.001508336322|2.797821393|2.799329729|0.008952812685|
|dh|80|-0.04996439633|-0.003518771265|5.513702392|5.510183621|0.001152717215|
|zeta|120|1.39298731e-6|-0.0006693687218|3.096077856|3.095408487|0.00667061248|
|dh|120|0.05559519615|-0.002809715176|5.753421237|5.750611522|0.002233567288|

The canonical raw-DH boundary/interior are also retained, separately labeled. Boundary signs and magnitudes depend on the selected vector and the reference subtraction. These data do not justify deleting the interior derivative term or attributing the entire sign change to the boundary.

## All selected complement bottoms

|world|m|q|cutoff mode|complement minimum|
|---|---:|---:|---|---:|
|dh|55|27|density_matched|0.5487554397|
|dh|55|50|native_kappa1p1|-0.6639206461|
|zeta|55|27|native_kappa1p1|0.0001070512462|
|dh|80|41|density_matched|0.6543603738|
|dh|80|73|native_kappa1p1|-1.240687012|
|zeta|80|41|native_kappa1p1|3.817633164e-7|
|dh|120|63|density_matched_lower|-1.547784258|
|dh|120|65|density_matched_upper|-1.557014625|
|dh|120|108|native_kappa1p1|-1.588253688|
|zeta|120|63|density_matched_lower|2.182964511e-8|
|zeta|120|64|native_kappa1p1|6.134500659e-10|
|zeta|120|65|density_matched_upper|6.822045956e-12|

In particular, matched DH55/80 complements remain positive (+0.54875544,+0.65436037), while their native kappa1.1 complements are negative. Both matched DH120 branches are negative. Cutoff selection is therefore part of the reported result, not a hidden normalization choice.

## Validation and reproduction

Matrices/spaces use120dps; the ledger evaluation uses140dps and an independent160-point,8-panel archimedean quadrature. The fast zeta builder agrees with saved180dps m20 entries within2.90e-119 (Frobenius6.90e-119). Physical exponential-product correlations independently check the modal q_even contraction and the moving-boundary derivative identity. Abel integrals use exact exponential moments separately on every[log n,log(n+1)], including signed DH non-prime-power coefficients. All n=m atoms are retained with exactly zero correlation weight.

Maximum absolute closure errors:

- direct_ledger_minus_Rayleigh: 1.520865e-119
- Abel_closure_error: 8.056203e-139
- derivative_identity_coefficient_error: 3.224449e-139
- independent_correlation_error: 3.883772e-139
- reference_Abel_closure_error: 1.230244e-138

These are multiprecision agreement checks, not outward-rounded interval certificates. The DH zero census and80-digit nodes retain the qualifications of the parent fake-world dataset. No cofinal bound, new RH sign, or route promotion is claimed.

Run `python3 unpack_cells.py` to verify and restore the raw matched_cells/ directory from the split lossless archive. MATCHED_ARCHIVE.json records every source/cell SHA-256. matched.py reproduces matrix/space cells; ledger.py produces the signed and Abel ledgers; summarize_ledger.py validates saved identities and recreates this report. density_plan.py independently checks the exact-count cutoff plan. SHA256SUMS covers the committed package.
