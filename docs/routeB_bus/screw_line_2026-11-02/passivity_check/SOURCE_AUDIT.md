# Screw kernel, pullback, and radius contract

DIAGNOSTIC_NEVER_A_PROOF. The following source identification was independently
checked by a bounded read-only worker; it produced no data or repository writes.
No Hilbert positivity or canonical Hamiltonian is assumed for the computation.

## Primary-source pins

Suzuki, [2206.03682](https://arxiv.org/html/2206.03682), equations (1.1),
(1.4), (1.8)–(1.9), Theorem1.2: g=-Psi and
`G_g(t,u)=g(t-u)-g(t)-g(-u)+g(0)`; global positivity is equivalent to RH.
His string construction in §9 is under RH, not an unconditional identification
of the present native CCM truncations with a positive canonical system.

Suzuki, [2209.04658](https://arxiv.org/html/2209.04658), equations (1.2),
(1.10): the direct relation to the Weil form uses derivatives of tests.
The screw-line norm interpretation in its introduction is under RH.

Langer–Pruckner–Woracek,
[2106.07391, §2.1, Lemma2.1](https://arxiv.org/html/2106.07391): a normalized
positive canonical system has radius `1/(2 Im(z) nabla_22)`, with
`nabla=integral W H W*`. Identifying the present inverse-evaluation form
with that entry requires an additional same-source transfer/normalization
theorem. It is not supplied by writing a positive scalar reciprocal.

## Literal bridge, including the endpoints

For the zero-extended carrier e_n^0 on [-b,b],

    d(e_n^0)=e_n'(x)dx + e_n(-b)delta_-b - e_n(b)delta_b,
    A_ij=integral integral G_g(t,u) d(e_j^0)(u) d(conj(e_i^0))(t).

This follows by differentiating G in both variables in the distributional
source identity, then integration by parts. A_m is a derivative-measure
pullback of the continuous kernel, not a direct matrix of sampled curve
points. For the constant carrier the interior derivative is zero, but
the endpoint masses give `A00=2Psi(L)/L`, generally nonzero. The independent
Python validation checks this identity. Omitting those masses would give
the wrong zero matrix entry even before a sign question.

## Source-first g used for both worlds

For t>=0 define, with the full original source constants,

    Psi(t)=c*t/2 + integral_0^infinity j(s)min(t,s)ds
           +pole_Psi(t)
           -sum_(n<=exp(t)) b(n)/sqrt(n)*(t-log n),
    g(t)=-Psi(|t|).

For zeta, c=-EulerGamma-log(8pi)-pi/2,
j=exp(-s/2)/(1-exp(-2s)),
pole_Psi=4(exp(t/2)+exp(-t/2)-2), and b=Lambda, retaining all prime powers.
For DH, c=-EulerGamma-log(8pi/5)+pi/2,
j=exp(-3s/2)/(1-exp(-2s)), no pole, and every signed logarithmic-derivative
coefficient is retained. The source integral is finite: s*j(s)->1/2.
The implementation evaluates it as integral_0^t s*j(s)ds plus its exact
arch tail. The zeta expression is independently compared with Suzuki's
special-function expression; no zero-tail or RH assumption enters g.

## Distinct geometries and passivity traps

When C=U*AU is positive, its inverse evaluation is a finite RKHS quantity.
After C becomes indefinite it remains an algebraic inverse form, not a
Hilbert norm. Real rho=1/(Im(z)K) may have either sign, but rho² cannot be
negative. K=0 gives a reciprocal pole; C singularity and a diagonal K sign
change need not coincide. Three diagonals do not determine kernel inertia.

The native family changes order, window, constraints and often rank at each
m, so it is not a nested piecewise extension of one passive device. Genuine
curve tests below use fixed old nodes, never regridding them.

Finally, `v*(C-zI)^-1v` is Herglotz for EVERY Hermitian C, even indefinite:
its imaginary part is `Im(z)|| (C-zI)^-1v ||²`. It cannot serve as a
DH-sensitive physical impedance. Global Q=i Lambda'/Lambda is evaluated
separately; no fictitious finite-end m_t is named from either inverse.
