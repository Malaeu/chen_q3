# Quiet-space κ scan: normalization, exact dimension, and count guards

Read-only algebraic/source-interface review. No new numeric scan, cofinal
theorem, or Git operation. Keep the physical identity Gram metric throughout.

## 1. Which product and polynomial represent the physical transform?

Let `L=log m`, `ω_n=2πn/L`, and use the real even orthonormal carrier

`φ_n(x)=d_n(−1)^n cos(ω_n x)/√L`, `|x|≤L/2`,
`d_0=1`, `d_n=√2` for n≥1, zero outside.

For `f=Σ_(n=0)^m v_n φ_n`, put `a_n=d_n v_n`, `X=z²`, and

`D(X)=Π_(n=1)^m(X−ω_n²)`,
`P_f(X)=v_0 D(X)+Σ_(n=1)^m a_n X D(X)/(X−ω_n²)`.

Then `deg P_f≤m` and the requested formula is

`f̂(z)=2sin(zL/2)/(√L z) · P_f(z²)/Π_(n=1)^m(z²−ω_n²)`.

The product in this particular formula starts at **n=1**. There is no extra
alternating sign in a_n: the physical basis's `(-1)^n` cancels the corresponding
modal sine phase in the rational-times-sine representation.

Equivalently,

`f̂(z)=2z sin(zL/2)/√L · Σ_(n=0)^m a_n/(z²−ω_n²)`.

If the common denominator includes n=0 while retaining the requested `1/z`
prefactor, its numerator must instead be `X P_f(X)`, of degree at most m+1,
with a mandatory factor X=z² to cancel. By contrast, using the `2z sin`
prefactor and the product starting at n=0 gives the original P_f of degree
at most m, generally **not** divisible by X. These are different bookkeeping
conventions; mixing them would lose or duplicate the constant mode.

Useful checks of the removable values:

`f̂(0)=√L v_0`,
`f̂(ω_j)=d_j(−1)^j√L v_j/2` for1≤j≤m.

For k>m, every carrier transform vanishes at the common structural points
`z=2πk/L`. Those exterior lattice zeros must not be counted as independent
quiet-space constraints.

## 2. Exact rank of zero-evaluation constraints

The map `v↦P_f` is an invertible linear map from the d=m+1 carrier coordinates
to polynomials of degree at most m. For example,

`v_0=P_f(0)/D(0)`,
`v_j=P_f(ω_j²)/(d_j ω_j² Π_(k≠j,1≤k≤m)(ω_j²−ω_k²))`.

Suppose the retained q positive ordinates are distinct, nonzero, and nonmodal,
and that the prefactors in the displayed transform are nonzero. Then imposing
`f̂(γ_k)=0` is equivalent to imposing `P_f(γ_k²)=0` at q distinct points.
The polynomial evaluation/Vandermonde map has rank `min(q,d)`. The same rank
follows from the Cauchy matrix `1/(γ_k²−ω_n²)` after its nonzero row factors.
Thus the exact quiet space J has

`dim J = max(0,m+1−q)`.

For q≤m, the polynomial form is
`P_f(X)=Π_(k=1)^q(X−γ_k²) R(X)`, `deg R≤m−q`.
For q≥m+1 only the zero polynomial remains. This is an exact dimension count,
not a claim that constructing the coefficients is well conditioned.

Nonmodal here must exclude the **entire** exterior structural lattice as well
as the interior denominator nodes: an exterior structural zero supplies an
identically zero row. Interior modal points are handled by the sinc limits,
but the nonmodal Cauchy proof cannot simply be applied there unchanged.
At finite precision, a nonzero sampled prefactor is a diagnostic check rather
than an exact enclosure unless its error is controlled.

Repeated ordinates/multiplicity weights do not add independent evaluation
constraints. To enforce a zero with higher multiplicity one needs derivative
conditions and the corresponding confluent rank argument. Negative ordinates
add no independent constraints for an even carrier.

## 3. Which N_ζ and which Riemann–von Mangoldt comparison?

The exact d−N expression means `max(0,d−q)` for the actual distinct,
nonstructural, positive critical-zero evaluation rows. Replacing q by the
standard N_ζ(T) requires a finite-height completeness/simplicity statement:
N_ζ counts **all** nontrivial zeros through T, with multiplicity, whereas the
evaluation rows use critical-line ordinates. Such a statement may be verified
at a finite height without assuming global RH, but the distinction remains.
Use the same strict endpoint convention `γ<T`; avoid a zero at T or account
for its boundary contribution explicitly.

Away from zero ordinates the standard count comparison is

`N_ζ(T)=T/(2π) log(T/(2π))−T/(2π)+7/8+S(T)+O(1/T)`.

Equivalently the exact phase formula is `N_ζ(T)=θ(T)/π+1+S(T)` with the usual
continuous-argument convention. S(T) is not absent; an unconditional coarse
error is O(log T). The `7/8` constant therefore matters in a finite comparison
but does not turn the leading expression into an exact integer count or give
a certified rounding rule.

For `Ω_m=2πm/L`, `T=κΩ_m`, the mean-count algebra gives

`d−N̄_ζ(κΩ_m)=(1−κ)m+(κm/L)(log L−log κ+1)+1/8`.

Actual d−N_ζ differs by `−S(T)+O(1/T)`, and quiet-space dimension is clamped at0.
At κ=1 the mean residual dimension is
`m(log log m+1)/log m+1/8`, not asymptotically merely m/log m.
For other κ the `(1−κ)m` term cannot be dropped. These are count comparisons,
not residual estimates or confinement conclusions.

## 4. NOESCAPE's saturation theorem still needs the full residual

Source: `PROSHKA_VERDICT_NOESCAPE_2026-10-30.md`, blob
`453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc`, L12 lines634–663 and
L13 lines669–691. For a genuine r-dimensional quiet-space basis B with
`M=B*B>0`, form its physical orthonormal frame `Q=B M^(−1/2)` and compute

`δ=||A_m Q||`,
`δ²=λmax(Q* A_m² Q)`.

This is the full operator residual, **not** `||Q* A_m Q||`, a collection of
Rayleigh values, or the compressed energy spectrum alone. Cross-block leakage
from J to its orthogonal complement is part of the required quantity.
Ill-conditioned polynomial synthesis must be paid through the Gram matrix
or avoided with a verified orthonormal frame.

If `δ<μ`, `μ>0`, and the **signed** upper count `#{λ(A_m)<μ}≤r` holds,
L12 yields `A_m≥−δI`. The absolute near-zero count alone is insufficient:
`#{λ<μ}=#{|λ|<μ}+#{λ≤−μ}`. Every negative level consumes the guard.
The zero-dimensional quiet space when q≥d is not a nontrivial L12 supplier;
do not label its vacuous residual0 a successful construction.

Zero conditions at a finite set cancel only that part of the explicit-formula
sum. They do not imply full radicality, small δ, a positive remaining zero
tail, or any global zero-location claim. In particular the unexcluded
off-critical zero contributions cannot be replaced by absolute squares.

For the direct growing-rank lower-floor route, a cofinal δ_m→0 with the same
strict threshold/count guards would suffice via L13. Fixed-rank(5.9) and
uniform fixed-jet overlap are separate stronger interfaces. None is supplied
by the exact dimension formula or by a finite κ scan.
