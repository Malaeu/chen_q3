# Endpoint capacity and endpoint-zero slice

**DIAGNOSTIC_NEVER_A_PROOF.** Saved complement spaces only; physical endpoint normalization, no row/endpoint rescaling. Lower cells use archived full source matrices and complement bases. Shared high-cell A/E/U/Q inputs were reconstructed from pinned helpers before this capacity module used them; no full-carrier eigensystem was rebuilt.

For G=U^T A U and t=U^T d_b, d_b=(1,sqrt2,...)/sqrt(log m), the algebraic inverse quantity is cap=1/(t^T G^(-1)t). It equals the affine constrained minimum when the computed reduced G is positive definite. An indefinite DH G receives no positive-capacity interpretation, even if its algebraic inverse quantity is positive.

The endpoint-zero minimum is the lowest eigenvalue of Z^T G Z, where the columns of a stable Householder Z form an orthonormal basis of t-perp. This is the requested new constrained compression, not a new full-carrier eigenproblem. The second eigenvalue of G uses the archived compressed spectrum where available; otherwise the requested reduced G spectrum is recomputed at high precision. It is independently replayed in float arithmetic with an explicit resolution flag, which does not replace tiny high-precision eigenvalues.

## Zeta cells

|m|q|cap*pi*T/logT|R=lambda*pi*T/(e² logT)|relative difference|lambda2(G)|endpoint-zero minimum|slice/bottom|
|---:|---:|---:|---:|---:|---:|---:|---:|
|55|27|0.9061732847|3.580529528|0.74692|0.008355155028|0.0001430872889|1.33662|
|80|41|0.6749571135|4.300051399|0.84304|4.373203262e-5|4.526750451e-7|1.18575|
|120|63|0.5854108884|4.436850719|0.86806|9.956959536e-7|2.51346494e-8|1.1514|
|120|64|0.5050447306|4.251664264|0.88121|4.443918195e-8|6.959472045e-10|1.13448|
|120|65|0.441832896|3.925332888|0.88744|9.895274866e-10|7.68647039e-12|1.12671|
|160|89|0.346962377|3.919361712|0.91147|1.01591211e-13|5.250124203e-16|1.09707|
|200|115|0.2588150649|4.525479493|0.94281|1.772191602e-20|6.170887224e-23|1.06064|
|240|139|0.2375409487|4.143167889|0.94267|1.642236776e-22|2.486683011e-25|1.06081|

## Registered predictions (all eight cells required)

- P2: 0/8 cells; all-eight criterion FAIL.
- P3: 0/8 cells; all-eight criterion FAIL.

## DH controls

|m|q|cutoff|negative saved G levels|denominator sign|algebraic cap*pi*T/logT|endpoint-zero minimum|
|---:|---:|---|---:|---:|---:|---:|
|55|27|matched|0|1|20.02144688|0.6822561691|
|55|50|native_kappa1p1|1|1|0.5401857041|-0.5468342928|
|80|41|matched|0|1|19.55484966|0.6658452886|
|80|73|native_kappa1p1|2|1|0.35681176|-1.202532359|
|120|63|matched|1|1|23.82417481|-1.342359325|
|120|65|matched|1|1|23.94542741|-1.356298727|
|120|108|native_kappa1p1|2|1|0.2722680046|-1.577098949|
|160|144|native_kappa1p1|4|1|0.2071208308|-1.946575217|
|160|89|matched|2|1|20.42608274|-1.86371856|
|200|115|matched|4|-1|-23.9084278|-2.184740233|
|200|180|native_kappa1p1|4|1|0.1646148584|-2.29288239|
|240|139|matched|4|1|142.9983752|-2.511107349|
|240|216|native_kappa1p1|5|1|0.1426250253|-3.644085725|

DH negative eigenvalues and signed inverse denominators are retained. A favorable-looking scaled inverse number does not establish positive complement coercivity in an indefinite control. Saved tiny inertia signs are floating diagnostics, not interval certification.

Raw results and source hashes: capacity.json/capacity.csv; prediction scoring: capacity_scored.json; separate higher-precision worst-case replay: precision_validation.json. Inverse-solve, nullspace, orthogonality, trace and interlacing checks are retained per cell.

## Precision validation

Highest zeta m240q139 was rerun at80 and110dps. All five comparisons pass the1e-40 relative criterion; maximum relative difference is 2.5047768e-56 (endpoint-zero minimum).

The most ill-conditioned DH native m240q216 inverse was separately recomputed at110dps without an eigenproblem: relative capacity difference 8.5119738e-18 versus its80dps value. Explicit1e-8 relative criterion: PASS. Its smallest absolute G eigenvalue at80dps is about1.62e-66; no70-digit accuracy claim is made for this ill-conditioned inverse.
