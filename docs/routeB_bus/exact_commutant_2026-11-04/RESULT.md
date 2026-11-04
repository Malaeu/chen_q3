# Gate 0 and literal even CCM commutants

Route B = CHALLENGER / NOT_RH. DIAGNOSTIC_NEVER_A_PROOF.

**Gate 0 passes. The commutant scan is void:** the literal class contains the scalar identity, so its optimized minimum is zero for every nonzero matrix, including the random negative control. Separately, the prescribed nonconstant Slepian operator fails the requested finite-Galerkin positive-control tolerance. No CCM commutant scan, source repair or quotient scan was run.

**COMMUTANT_SIGN_BLIND — scalar identity only; no non-scalar commutant claim.**

## Registration before numerical work

The exact PREDICTIONS.md blob `4bbcdb94bfdc2b3165d7dc4db6d4f0c80a9f376b` was committed in immutable registration object [76ddfb77](https://github.com/Malaeu/chen_q3/commit/76ddfb77a7d9b1f9e5e1bfa6cb5747f14ab48ec3) at2026-11-04T09:45:22Z. Gate0 began09:49:16Z; controls began09:51:28Z. The registration object did not move rh_clean. The final delivery is one branch commit from the specified base, carrying exactly that prediction blob and PREREGISTRATION.json. The preliminary source reads were not numerical runs.

## Gate 0: PASS, no source change

At80 mpmath decimal digits, the unchanged pinned analytic builder was evaluated with320 requested bits (360 working,392 special-function bits). Its constant mode was compared with Suzuki Theorem1.1(1.1), and with a separate scalar evaluation of the pinned source. This is a high-precision point diagnostic, not an interval certificate.

| m | H₀₀, full Gamma | P₀₀ | B₀₀, positive atom sum | A₀₀=H₀₀+P₀₀−B₀₀ | largest absolute term/full discrepancy |
|---:|---:|---:|---:|---:|---:|
|16|−2.992331100395|6.492127684000|3.466656110760|0.033140472846|9.36e−81|
|80|−3.614039884713|12.881848326601|9.247274509192|0.020533932696|1.82e−80|
|300|−3.945624080265|21.569185951166|17.611453884881|0.012107986020|3.38e−80|

Every comparison is below1e−40. GATE0.json records the unrounded values and separate residuals for H₀₀, P₀₀, −B₀₀, the required pole expression, the builder/scalar comparison and A₀₀−2Ψ(L)/L.

In particular,

P₀₀=32 sinh²(L/4)/L=8(e^(L/2)+e^(−L/2)−2)/L.

The full Gamma term includes the source tail beyond L. Its Suzuki counterpart is

(2/L){(L/2)[ψ(1/4)−logπ]+[π²+8G−e^(−L/2)Φ(e^(−2L),2,1/4)]/4}.

All von Mangoldt prime powers are included, with the endpoint n=m contributing exactly zero. SOURCE_REVIEW.md independently verifies the algebra and primary Suzuki formula. INPUTS.json pins both unchanged source blobs and the higher-moments verdict. The repository PDF is an LFS pointer; the downloaded433447-byte PDF matches its declared SHA256 exactly.

This validates the requested constant-mode identity only. It does not by itself validate other higher-moment claims, a full operator identity on another domain, or a non-scalar symmetry.

## Literal optimization: an exact scalar short circuit

For d=m+1 choose the permitted coefficients

a(x)=0, b(x)=1/√d.

Then D=I_d/√d, ‖D‖F=1 and [D,X]=0 exactly for every matrix X. Hence, whenever X≠0,

r(X)=0.

Frobenius normalization removes overall scale; it does not remove scalar matrices. R.csv therefore contains30 **analytical scalar-witness rows**, one for each requested piece×m, with the exact minimizing coefficients. They are explicitly marked SCAN_VOID and are not numerical scan results. The condition X≠0 is stated; no undefined0/0 value is converted into a measurement. H+P, A, A+Q and all other listed pieces share this identity witness independently of their source details. No Q or source matrix was constructed for a scan.

These rows say nothing about the existence or absence of further non-scalar minimizers. In particular, finding the scalar witness does not establish universal same-D robustness: [A+Q,D]=[A,D]+[Q,D]. Only the chosen scalar minimizer is automatically blind to the prescribed quartet or any other perturbation.

## Mandatory controls and stop

The first control cell is m16, on the same physical window, with cb=1, b=L/2. The positive kernel is exactly sin(c(x−y))/(π(x−y)); the prescribed nonconstant differential expression is

D_S=((b²−x²)f′)′−c²x²f.

Its finite even-cosine Galerkin matrix and the kernel matrix were evaluated at80dps, using smooth one-dimensional integrals. Five differential-matrix entries were also checked by direct weak-form integration.

| Control | Result |
|---|---|
| prescribed Slepian ‖[D_S,K]‖F/(‖D_S‖F‖K‖F) | **5.38921914377833044e−5**, fails≤1e−25 |
| prescribed Slepian [D_S,K]₀₁ | −1.40071263014173713e−5 |
| literal optimized r(K) | 0 exactly, via I/√17; vacuous positive pass |
| random symmetric17×17, seed20261104, literal optimized r | 0 exactly; fails intended nonzero order-one discrimination |

The positive-control failure refers to the **prescribed nonconstant operator**, not to the unconstrained minimum, which is already zero for an unrelated scalar reason. Both obstructions are retained; the metric is not silently changed to make a control pass. CONTROLS.json records the numerical magnitudes, exact rational random-matrix construction, threshold and stop flags. CONTROL_IMPLEMENTATION_REVIEW.md independently checks the implementation without rerunning it.

Continuous Slepian commutation does not imply finite Galerkin commutation. If Π projects onto the cosine carrier, the compressed commutator retains cross-projection terms ΠD(1−Π)KΠ−ΠK(1−Π)DΠ. CLASS_REVIEW.md gives a strict analytic noncommutation witness at cb=1 for every finite m≥1, including m16. Thus the observed residual is compatible with a projection defect. The numerical magnitude is an80dps quadrature diagnostic, not a rigorous quadrature enclosure.

Per the requested kill-switch, this ends the computation before the CCM scan. No higher-order or repaired-class search was substituted.

## Prediction scores

| Prediction | Outcome |
|---|---|
| G0 (0.90): all three identities within1e−40 | **PASS**, measured term by term |
| R1 (0.85): r(A)≥1e−3 on grid | **FALSE under the literal metric**: scalar witness gives0 whenever defined |
| R2 (0.35): r(H)≤1e−6 somewhere | **TRUE but tautological**; not evidence of a Gamma/prolate symmetry |
| R6 (0.70): same-D plant robustness | chosen scalar minimizer: **exactly blind, uninformative**; non-scalar/universal version **NOT TESTED** because the scan is void |

A meaningful successor would have to specify how scalar image matrices are excluded and provide a control consistent with the same finite projection. That would be a new experiment with a new registration. This task does not silently make either change. No conclusion about RH or route status is drawn.
