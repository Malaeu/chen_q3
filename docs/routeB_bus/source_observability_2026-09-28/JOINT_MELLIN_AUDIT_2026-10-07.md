# Joint Mellin answer2 — bounded audit

Source: PROSHKA_JOINT_MELLIN_INLINE_2026-10-07.md. Same original carrier.
Assigned independent checks completed below; acceptance is limited to their stated scope.

## Root independent pass: derivative absorption is false

For g=e_m=L^-1/2 exp(i Omega x), Omega=2pi m/L, the two integrands in
K_g,g(h) are exp(+/-i Omega h)/L because exp(i Omega L)=1. Thus
K=2h cos(Omega h)/L and K'=2cos(Omega h)/L-2h Omega sin(Omega h)/L.
For h_m=L/m(floor(m/4)+1/4), Omega h_m=2pi floor(m/4)+pi/2.
Hence |K'(h_m)|=2h_m Omega/L>=2Omega/5 eventually. Moreover h_m~L/4,
while L-log(ceil sqrt m)~L/2, so the witness lies in the actual range.

The accepted a(Omega)<=4+0.5log(1+4Omega²) (signed packets answer7)
gives a(Omega)<=L+8 eventually. The window correction is also explicit:
 D_arch(e_m)-a(Omega)
 =(2/L)int_0^L s J(s)cos(Omega s)ds+2int_L^infty J(s)cos(Omega s)ds.
For L>=1, sum_(k>=0)(2k+1/2)^-2<5 and the geometric tail estimate give
an absolute bound<20. Thus D_arch(e_m)<=L+28 including the window.
For any fixed C>0 and real A, C L^A(D_arch+1)-sup|K'|
 <=C L^A(L+29)-4pi m/(5L)<0 eventually.
Accept the kill of answer2 Eq18 only. This top mode is not asserted to lie
in the exceptional subspace or to equal J_rv. Signed derivative integrals,
restricted estimates, full Schur and SP are not refuted.

## Independent algebra/Euler pass

causal_algebra_audit passed §§1–4 once. The original a-flux annihilates
all b>X tails because a>U and UX=m; both logarithmic derivatives preserve
that support. Product Leibniz retains -(delta A)Q. For P+(b)>V, b=pc and
allowed d are exactly divisors of c, proving beta_V(b)=0, not cancellation
of the continuous compensator. The primitive retains all original intervals.
Euler trace conventions count an included singleton1 correctly; the log
boundary vanishes at1. The long means combine to +mu(d)logu/2; the -2
mean cancels only the wheel M_U density, leaving original D_U in Theta.
Z0 and Z1 follow by divisor inversion; differentiating x^(1-s)H_o(x)
cancels the H_o,m_o terms, leaving exactly Abel's formula with psi_o.
Thus the finite-inversion/Euler cancellation completion is STALLED at the
original prime-power staircase, coefficient1, not at a smaller remainder.
This is an exact source-specific obstruction to that completion, not a
counterexample to all signed Mellin methods or SP.

## Independent norm and return-budget pass

growth_symbol_attempt passed assigned §§5–6 once, conditional on accepted
predecessor ledger. Euler traces give |E0|<=(1+|s|)/sqrt ell and
|E1|<=(1+L)(1+|s|)/sqrt ell using logu<=L on the finite interval.
The combined d terms cost2(1+L)(1+|s|), nonempty d<=m/a, and
sum d^-1/2<=2sqrt(m/a). Integrating |drho|/a<=2h_U(1+L) gives8h_U
(1+L)^2(1+|s|)sqrt m; the -2 term fits the second8 via the Q10
sqrt-a mass. The continuous Theta bound has slack at16h_U(1+L)^3sqrt m.
The exact joint d/h map retains cross modes and endpoint traces. Actual
Schur retains Delta_V||v||||J_rv||, no normJ bound. Signed restoration of
Q lowers the paid error toDelta10 only by restoring R_* exactly.
Delta10 contains the inherited L+8 diagonal allocation; subtracting it
once in deltaV is correct. No repair in this scope.

## Accepted conclusion and next attempt

Answer2 accepted PAPER in the above scope. Stop finite inversion -> absolute
Euler variation -> free archimedean derivative absorption. The exact source
returns its prime-power remainder coefficient1; the derivative interface is
false on an original carrier mode. Neither claim kills signed Mellin methods,
actual exceptional estimates, SP, G1/G3 or RH.
Root ODD_POISSON_OWN supplies the next exact Fejer alias representation,
including all endpoint halves and fixed-cell dominated convergence through
the original a-flux; causal_algebra_audit independently checked it once.
This is a representation, not an alias estimate. Bounded alias-hunt used
Fourier-comb/Dirichlet-Jordan, Euler-sawtooth and Poisson-Mellin dictionaries.
Shelf INCOMPLETE is not absence. Duran–Estrada–Kanwal DOI10.1006/jmaa.1997.5767
is an excluded lead: primary full text inaccessible, no theorem/quote/hash
verified. Bhatnagar1940 DOI10.1017/S0013091500027206 is an excluded mismatch,
not a supplier. No external theorem is being attributed to the own formula.
Next question executes the complete stationary/nonstationary alias sum plus
Theta before norms, with exact Schur and inherited errors retained.
