# Finite ladder step certificates

DIAGNOSTIC_NEVER_A_PROOF / CHALLENGER / NOT_RH.

All six finite node sets below have verified positive screw-Gram matrices.
Arithmetic backend for the executed runs: **mpmath.iv directed intervals**,
512-bit primitive precision, explicit dilogarithm series remainder below
1e-50, and outward decimal endpoint serialization. Native python-flint
was unavailable; its optional code path was not used for these results.

| Window | Mesh | Nonzero distinct nodes | Certified lower eigenvalue exceeds |
|---|---:|---:|---:|
|log3|1/32|49|0.0006484745999|
|log5|1/32|107|0.0000981496803|
|log7|1/32|166|0.0000611372481|
|log3|1/64|97|0.0008140163758|
|log5|1/64|211|0.0001783811777|
|log7|1/64|329|0.0001172554057|

These are conservative **lower bounds**, not measured eigenvalues. Different
factorizations give different lower bounds, so their ordering across meshes
does not assert increasing eigenvalues under refinement.

For window logW and denominator M, exact node labels are
`k/M+log(r)`, `r=1,...,W`, whenever the point lies in [0,logW]. This is
the uniform grid plus the exact endpoint, closed under forward prime-power
shifts within the window. The closure includes log6 at W7, although 6 is
not a von Mangoldt atom. No approximate merge tolerance is used. The exact
structural zero node is removed; every adjacent ordering and every source
arithmetic threshold is decided by a directed interval or symbolic equality.
The certificates cover all subsets of this finite alphabet (and PSD for
repetitions), including its finite step subblocks.

The source is unconditional: all von Mangoldt prime powers within support,
the complete archimedean closed form and both pole terms. No zeta zero list,
RH premise or numerical sign hypothesis constructs its entries. The Li2
transform and geometric tail used by the fallback are stated in
FALLBACK_PREREGISTRATION.md. The nearest-rounded numerical matrices are
used only to construct dyadic witnesses in the residual method.

At M32, interval LDL directly certifies every pivot. A W3 replay at 768 bits
with a 1e-60 series remainder lies inside all 49 original pivot intervals.
Seven independently evaluated MP80 source values, including exact prime
hinges, lie inside the source intervals. These MP controls check normalization;
they are not inputs to the interval acceptance criterion.

At M64 the direct interval LDL certifies W3 but its widths inflate for
W5 and W7 at pivot 159, enclosing zero. Both failed records are retained.
This is interval wrapping, not a negative source certificate. The alternative
validated residual method certifies all three M64 matrices:

- Freeze numerical Cholesky L and inverse approximation B as exact dyadic
  integer arrays. Recompute BL-I by exact integer arithmetic, and verify
  both induced norm bounds epsilon1, epsilonInf<1.
- Bound the lower eigenvalue of LL^T by
  `(1-epsilon1)(1-epsilonInf)/(norm1(B)*normInf(B))`.
- Reconstruct the complete source A in directed intervals. The products
  LL^T are exact integer sums divided by a power of 2. Bound the symmetric
  residual A-LL^T by its maximum absolute row sum and subtract this bound.
- Accept only a strictly positive outward lower endpoint. Approximate
  eigenvalues, Cholesky signs or inverse residuals never decide acceptance.

The source residual upper norms are 1.03e-15,3.60e-15,6.74e-15 for
W3,W5,W7 at M64. Exact dyadic witnesses and interval certificates are saved.
The replay path needs no NumPy/SciPy or approximate matrix.

## Between-node contribution and the remaining gap

The independently checked analytic modulus omega_T(epsilon) is evaluated
outward in INTERSTITIAL_BUDGET.json. Moving each of N nodes by at most
epsilon, with both configurations remaining inside [0,logW], changes each kernel entry by at most
`omega_T(2epsilon)+2omega_T(epsilon)` and the matrix norm by at most N
times this value. Nearest-grid displacement 1/(2M) gives bounds of about
30.7/82.6/145.7 at M32 and 31.4/83.7/147.9 at M64. These are vastly larger
than the available lower eigenvalue bounds. The resulting interstitial
lower estimate is negative, which means **this bound cannot certify the
continuum**, not that the continuum kernel is negative.

The same bound does certify small neighborhoods of the **same finite
configurations**, with each corresponding coordinate moved by the stated
epsilon and remaining inside [0,logW]: 1e-7 for W3/M32,1e-8 for W3/M64,
1e-9 for the other cases. It does
not allow arbitrary additional points or arbitrary cardinality. Collisions
under nearest-node mapping create singular reference directions; the N
penalty also prevents a cardinality-uniform continuation argument. An
all-node coercive/Schur budget is the precise unpaid input.

Reproduce from this directory:

```
python3 certify.py --mesh 32 --bits 512
python3 certify_residual.py --mesh 64 --bits 512
python3 certify_residual.py --mesh 64 --bits 512 --window 7 --replay
LADDER_LI2_TAIL_TARGET=1e-60 python3 certify.py --mesh 32 --bits 768 --window 3
python3 validate_source.py
python3 modulus_intervals.py
```

Source and
verifier hashes, exact node CSVs, outward pivot intervals, fixed dyadic
witnesses, failed LDL records, source checks and interstitial budgets are
retained. No all-point positivity, RH, or route promotion is claimed.
