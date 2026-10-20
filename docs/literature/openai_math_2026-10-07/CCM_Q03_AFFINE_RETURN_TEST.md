# Own Q03-cycle attempt 3: affine density subtraction retains the unpaid joint remainder

2026-10-20. Read-only bounded worker ccm_next_mechanism supplied the calculation;
root checked against CCM_LOG_DENSITY_CANCELLATION.md (previous PAPER acceptance).
This is a no-gain test of a supplier, not a new arithmetic bound.

Write c_R(t)=sum_(R<d<=t) mu(d)/d log(t/d). Keep original A_m(t), P and all
cutoffs. C=int_1^m A_m(t)c_R(t)dt, V=C+E_slow from Q02. For any real a,b
chosen at this fixed cell,

 C = -a P H_(1/2)P + b P J P
       + integral_1^m A_m(t)[c_R(t)-a-b log t]dt,
 ||a P H P||+||b P J P|| <=4|a|+8|b|.

The first two identities are the existing full-window rank-two and first
log-moment cancellation. No differentiation of P is used. The exact remaining
joint object also includes E_slow, with no favorable sign supplied.

Using only ||Q||<=2 gives

 ||integral_1^m A_m(t)[c_R(t)-a-b log t]dt||
   <=4(sqrt(m)-1) sup_(1<=t<=m)|c_R(t)-a-b log t|.

For this particular sufficient bound to be subpower, one would need the
supremum to be m^(-1/2+o(1)), while paying a,b and E_slow. This is not proved
and is not asserted necessary for the original matrix estimate. The trivial
|c_R(t)|<=L(1+L) gives only O(sqrt(m)L(1+L)) at a=b=0.
Higher log moments are not automatically killed: second differentiation of
v_+(a)v_-(a)* produces terms with both factors differentiated, not annihilated
by the original P. We do not assert that every higher moment is unbounded;
we assert that the two existing identities do not supply their needed control.

Q02's complete Mellin return restores -zeta'/zeta+zeta'U_R. Subtracting an
affine smooth term does not bound that signed remainder. Thus this attempt
does not improve the complete exponent. The cheaper affine term was already
on the shelf; do not report it as a new discovery.

Backtracking guard: SELBERG_SCALAR_AUDIT_2026-10-07.md already shows the exact
mixed-prime cancellation in mu*log^2-Lambda*Lambda. Repeating this identity
under a product-only weight leaves Lambda log with coefficient one; it is not
an independent positive credit. Nonlocal arithmetic use remains possible.

Decision: after three own bounded tests (scalar upper-primitive cone,
endpoint sign, affine subtraction), send one concrete Q03 request about the
actual joint signed form. Full V, T, sparse receiver, SP and RH remain OPEN.
