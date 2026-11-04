# Analytic review of the literal D1 commutant class

DIAGNOSTIC_NOT_RH. No scan, source replay, eigensystem or numerical optimization was run for this review. This report leaves the preregistered class and metric unchanged. Gate0 remains the independent source-identity prerequisite; a Gate0 failure stops the scan regardless of this class review.

## Exact scalar short circuit

Let E_m be the stated physical even cosine carrier, with its orthonormal basis and dimension d=m+1. The class is

`D f=(a f′)′+b f`, with real even polynomials a,b of degree≤4,

compressed by Galerkin to E_m. The literal admissibility condition is `||D_m||F=1`, and the objective is `r(X)=min ||[X,D_m]||F/||X||F`.

The admissible choice

`a(x)=0, b(x)=1/sqrt(d)`

gives exactly `D_m=I_d/sqrt(d)`. It has Frobenius norm1 and commutes with every finite matrix X. The negative choice gives a second explicit minimizer. Since a norm is nonnegative,

**For every nonzero X, the literal minimum is exactly r(X)=0.**

This statement holds in every requested cell, for A, H, each source component, any planted-quartet matrix and every random symmetric negative control. It is an exact algebraic degeneracy, not a rounding effect, near-commutant or small-m phenomenon. If X=0 the displayed normalized metric is undefined, rather than an additional test result.

Consequences for the immutable preregistration: R1 (`r(A)≥10^−3`) is impossible under the printed class and metric; R2 is automatically true for every nonzero H. For R6 the scalar minimizer gives `SCALAR_MINIMIZER_PASS_UNINFORMATIVE`: this particular same D commutes with A and A+Q. A claim quantified over every qualifying D is stronger and does not follow; the non-scalar/universal R6 assertion is `NOT_TESTED`. In general [A,D]=0 does not imply [A+Q,D]=0 because the latter adds [Q,D]. A random negative control has the same exact zero as a nominal positive control. Passing the literal positive control therefore cannot validate discrimination, and a mandatory negative-control requirement of a nonzero minimum is mathematically impossible.

A numerical implementation returning appreciable positive minima for this literal problem would contradict the explicit scalar witness. Tiny nonzero residuals would measure arithmetic/orthogonality error in that witness, not a feature of the CCM source.

## Precise description of minimizers

Let V_m be the image of the six-dimensional coefficient space spanned by a=1,x²,x⁴ and b=1,x²,x⁴ under the Galerkin map. Let `Z(X)={D:[X,D]=0}`. The complete set of image-matrix minimizers for nonzero X is

`{D∈V_m∩Z(X): ||D||F=1}`.

It always contains ±I_d/sqrt(d), and may contain further matrices. No assertion that these are the only minimizers is needed or justified without identifying this intersection for the particular X. At the coefficient level every preimage of such a matrix is a minimizer; a possible kernel of the Galerkin coefficient map creates extra parameter nonuniqueness, not a nonzero objective. This matters especially in small carriers where the symmetric matrix space has dimension below six.

The objective is homogeneous in X, invariant under adding a scalar multiple of I to X in its numerator, and has its own scalar D null direction. Frobenius normalization of D removes overall scale but does not remove that direction. Frobenius normalization of a coefficient vector instead would also leave a nonzero constant-b identity witness; it would not resolve the issue.

A quotient or constraint that removes scalar image matrices would define a different problem. It is not performed here. Merely requiring a nonzero derivative coefficient without a quantitative separation from the scalar direction can still leave an infimum of zero as the derivative coefficient tends to zero; it is not an automatic repair of the printed metric. Removing constant b alone is also not the abstract same thing as removing the scalar image direction if the compressed coefficient map has a kernel. Any future modified problem must specify its image-space constraints, normalization and new preregistration explicitly.

## Galerkin symmetry and boundary conventions

For the cosine basis every basis derivative vanishes at ±L/2. Thus direct strong-form compression gives

`<φ_i,Dφ_j>=−∫_I a φ_i′ φ_j′+∫_I b φ_i φ_j`,

because the integration-by-parts boundary term `[φ_i a φ_j′]` is zero. This is a real symmetric Galerkin matrix for real a,b and preserves parity for even coefficients. There is no need to discard the constant-b term to obtain symmetry. The formula presupposes the stated strong differential expression and carrier; a separately chosen operator domain or a different weak boundary condition must not silently be substituted.

## Slepian positive control: full commutation does not automatically survive compression

The classical prolate differential expression on a symmetric interval has quadratic even coefficients, for example after scaling `D_c=((h²−x²)f′)′−c²x² f`, with h=L/2 and the appropriate frequency scaling. The vanishing leading coefficient at the interval endpoints pays the continuous boundary terms in the familiar sinc-kernel commutation argument. Subject to its natural domain, that gives a full-operator identity, not yet a finite cosine-Galerkin identity.

Let P project onto E_m and Q=1−P. Where the full commutation identity is valid on the needed domain,

`[PKP,PDP]=P[K,D]P−PKQDP+PDQKP`.

Thus even if `[K,D]=0`, the compressed commutator equals `PDQKP−PKQDP`; these cross-projection terms must be checked. A finite cosine carrier is generally not invariant under the variable-coefficient prolate differential expression: x²cos(ωx) and x sin(ωx) have components outside that carrier. Endpoint cancellation alone does not remove the projection terms. It would be incorrect to demand an exactly zero finite Galerkin commutator solely from the full Slepian theorem. This is a warning about an unproved inference, not a claim that every particular compressed prolate pair necessarily fails; special cancellation would require its own demonstration.

Likewise a known commuting tridiagonal matrix for a discretized prolate/sinc problem is not automatically the Galerkin image of the printed polynomial differential class. Replacing one control by that different pair must be labeled as a different control with a justified same-class connection.

For the literal optimization in this task, the scalar witness makes the Slepian control zero regardless of these projection subtleties. Consequently neither a zero optimized Slepian residual nor a zero optimized random-matrix residual diagnoses whether the intended nontrivial prolate operator survived compression.

## Review outcome

The D1 class has an exact universal scalar short circuit. The literal minimum is0 for every nonzero input, and the requested positive/negative discrimination is unavailable in that metric. No source conclusion, hidden-symmetry conclusion or robustness-to-plant conclusion follows from obtaining that minimum. Gate0 must be reported on its own terms, and a failure there must not be bypassed by this class observation. No repair, scan or export is made by this report.

## Explicit prescribed Slepian control at cb=1

A stable one-dimensional construction follows directly from the Fourier representation of the sinc kernel. Put z=bt and ρ=cb=1, and define

`F_0(z)=sin(z)/z` with F_0(0)=1,

`F_j(z)=sqrt(2) z sin(z)/(z²−π²j²)`, j≥1.

Then the exact cosine-Galerkin matrix is

`K_ij=(2/π)∫_0^1 F_i(z)F_j(z) dz`.

There are no internal poles: for j≥1, |z|≤1<πj. This formula requires only one-dimensional integration, not a double integral with a removable diagonal singularity.

For the prescribed differential expression, define even sequences

`J_0=2/3`, `J_n=4(−1)^n/(π²n²)` for n≠0,

`T_0=4/3`, `T_n=−J_n` for n≠0.

With d_0=1 and d_j=sqrt(2) otherwise, its exact Galerkin entries are

`D_ij=−d_i d_j(−1)^(i+j)/4 * [π²ij(T_(i−j)−T_(i+j))+ρ²(J_(i−j)+J_(i+j))]`.

These follow by integrating y² cos(πny) on[−1,1] and using products of sines/cosines in the weak form. In particular D_00=−1/3 and D_0k=−2sqrt(2)/(π²k²) for k≥1 at ρ=1.

There is also an analytic strict obstruction to exact compressed commutation, without a scan. For k>m≥1,

`D_1k=[8k²−4(k²+1)/π²]/(k²−1)²>0`,

while K_0k<0 and K_1k>0. From the positive integral representation,

`K_1k/(−K_0k) ≤ sqrt(2)/(π²−1)`.

This is the maximum on[0,1] of `(−F_1)/F_0=sqrt(2)z²/(π²−z²)`. The explicit D entries give

`D_1k/(−D_0k) > sqrt(2)/(π²−1)` for every k≥2.

For example this last comparison follows immediately using π²>9 and k≥2; the left side is already greater than 7π²/(2sqrt(2)), while the right side is less than sqrt(2)/8. Therefore every summand

`D_0k K_k1−K_0k D_k1`

is strictly positive. The convergent projection-tail identity consequently gives

`[K_m,D_m]_(0,1)=sum_(k>m)(D_0k K_k1−K_0k D_k1)>0`.

Thus the prescribed nonconstant continuous Slepian differential operator does **not** commute exactly with its finite even-cosine Galerkin compression, including m16 at ρ=1. This is stronger than merely noticing a possible projection error. It does not determine whether a particular *normalized numerical threshold* passes or fails; that magnitude belongs to the separate prescribed high-precision control receipt. It also does not alter the universal scalar-zero minimum of the original optimization problem.

The parent reported Gate0 PASS at80 decimal digits for m16,80,300 and is separately computing the prescribed Slepian control. No numerical execution was done for this analytic addition, and no source scan is authorized by this report.
