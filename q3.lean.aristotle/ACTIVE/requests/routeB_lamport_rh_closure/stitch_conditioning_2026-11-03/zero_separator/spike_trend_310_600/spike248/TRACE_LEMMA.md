# Finite trace shortcut, conditional on an actual separator

Let A be a real symmetric d-dimensional matrix with sorted eigenvalues
lambda_0<=...<=lambda_(d-1). Let Q have r orthonormal columns, where
0<r<d/2, and suppose the strict separator holds:

    delta=||AQ|| < lambda_r                 (zero-based r).

Then lambda_r>0 and the following finite inequalities hold:

    lambda_0 > -lambda_r,
    tr A > (d-2r) lambda_r,
    lambda_0 > -tr A/(d-2r).

Proof. The r-th smallest singular value of A, indexed one-based, is at
most ||AQ||, so at least r eigenvalues satisfy |lambda_j|<lambda_r.
No index j>=r can satisfy that strict inequality because lambda_r>0 and
lambda_j>=lambda_r. Hence all indices0,...,r-1 must satisfy it. In
particular lambda_0>-lambda_r. Their sum is strictly greater than
-r lambda_r, while the remaining d-r eigenvalues sum to at least
(d-r)lambda_r. This proves the trace inequality. Divide by d-2r>0 and
combine with lambda_0>-lambda_r to obtain the last inequality.

The hypothesis is important: ||AQ||>=|lambda_0| is false for an arbitrary
Q, and is not used. The argument is conditional on a strict separator.
At r=d/2 the trace conclusion only gives tr A>0 and cannot be divided to
bound lambda_0; for r>d/2 division reverses direction and gives no stated
lower bound. r=0 is a different, vacuous quiet-space case.

For the frozen zeta m248 matrix, d=249 and its float trace is
704.3035243000062. At the observed best sector r=122, d-2r=5 and the trace
shortcut is lambda_0>−140.86070486000125. At the other observed passing
sector r=121, d-2r=7, it is lambda_0>−100.61478918571517. These are weak
finite bounds and do not establish source positivity. The matrix trace
and separator are numerical diagnostics, not interval-certified hypotheses.
If ||A_source−A_point||<=e were actually established, an upper trace bound
could use tr(A_point)+d*e; a heuristic numeric radius does not establish
such an operator error enclosure.

Conditional analytic reduction. For a sequence of genuinely proved
separators with d_m−2r_m>=eta*d_m for a fixed eta>0, an upper trace bound
tr A_m<=d_m H_m gives lambda_min(A_m)>−H_m/eta. To contradict this using
an off-critical witness would require an independently established witness
Rayleigh value below−H_m/eta on the SAME carrier and normalization, at the
same unbounded sequence of m. Neither existence nor a growth rate for such
witnesses follows from these computations. Without a uniform rank fraction
eta, the relevant denominator is the actual d_m−2r_m, which may be small.
No RH or continuum implication is asserted here.

DIAGNOSTIC_NEVER_A_PROOF. No route-state export.
