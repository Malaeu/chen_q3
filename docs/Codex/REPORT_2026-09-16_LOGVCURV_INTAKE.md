# LOGVCURV intake: the logarithmic entrance is too strong for the full V

STATUS: ACCEPTED_LIMITED_PAPER. No Lean certification or canonical admission.
PX_RH_CLAIM: NOT_MADE. Original V positivity and RH remain open.

## Exact subject and receipt

Request `REQ-2026-09-16-LOGVCURV`, boundary
`GOAL058_FULL_INTEGRATED_V_LOG_CURVATURE_ENTRANCE`, was sent once in the
unchanged living chat. The request is committed at
`35d3fe676855fa9bed6c5b05106cea791c4a8d72`; its native attachment readback
matches 83412 bytes, 1729 LF, SHA256
`4646b45b430b95242e914196c9be4715f4693f984852daeae0113f4b7bc0a734`.

Raw response, retained without changes:
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_LOGVCURV_2026-09-16.md`,
commit `6f4da4917734c92fba9459316494dd70ebbe77b5`, blob
`7debb9197cc804ddacd911827688053ef38e820d`, 55333 bytes / 567 LF / 0 CR /
final LF, SHA256
`e33ee8eee31a36c6b2de2e590f8c4ce94a658ed20662f505df204d7592e364f5`.
Its commit adds only the assigned response file. Native turn
`45741bc7-f078-4b5f-88dc-2c6bc6b75e3a` completed, error null, with the same
commit in the final answer; the chat is idle. No reply is pending.

The tested object is the complete integrated kernel

    V(x,y) = integral_0^infinity (2X+x+y) f(X+x) f(X+y) dX,
    C(x,y) = partial_x partial_y log V(x,y),
    I = (-log(2)/2, 0).

The already accepted SCHUR_REPEATABILITY S5--S11 proves that C PSD on I
would imply PSD of every entrywise power V^tau, tau>0, hence of V itself.
The response refutes precisely this stronger entrance. It does not refute
ordinary positive Gram representations of V.

## I1. A positive complex Hermitian diagonal, without assuming V PSD

The full source is holomorphic and even on S={z: |Im z|<pi/4}; its full
theta derivative bounds justify the original integral on S x S. For
z=a+ib in S, exact reflection gives

    V(conj(z),z) = 2 integral_|a|^infinity u |f(u+ib)|^2 du > 0.

This is only a diagonal statement. It supplies a finite positive norm
budget for the conditional feature continuation in I2, not all-row PSD.

## I2. Why the stronger entrance would forbid every complex pair zero

For each integer n, conditional C PSD supplies the real-interval PSD
kernel V^(1/n). Near a real diagonal point its analytic Taylor coefficient
matrices are PSD by finite differences. Their Hilbert vectors converge
with the explicit Cauchy bound sqrt(M) rho^(-j).

The positive real-analytic function g_n(z)=V(conj(z),z)^(1/n) exists on
all of S. On a compact path its local holomorphic polarizations have a
common radius rho and bound M, because the diagonal stays strictly
positive. Derivatives of the existing Hilbert map have squared norms
equal to the mixed Taylor coefficients of this local polarization.
Their Taylor series therefore continues the SAME Hilbert map along the
path. This does not assume PSD at new points. Monodromy on the simply
connected strip makes the continuation single valued.

The resulting global holomorphic kernel H_n satisfies H_n^n=V on S x S.
A nonzero slice of V with a zero of finite order q cannot have a
holomorphic (q+1)-st root. Therefore the conditional entrance forces V to
be zero-free on the whole complex product. Continuing C through possible
poles, or assuming a global logarithm, is not used.

## I3. The complete theta source violates this necessary condition

Let A(zeta)=sum n^4 exp(-pi n^2 zeta) and
B(zeta)=sum n^2 exp(-pi n^2 zeta). Their exact period is 2i, while

    r(zeta) = 4 pi^2 [zeta A(zeta) - 3 B(zeta)/(2 pi)]

retains its nonperiodic affine factor. Even/odd splitting and the full
Jacobi identity give, with c_j=pi(2j+1)^2/4,

    A(a+i) = a^(-9/2)/pi^2
             * sum_j exp(-c_j/a) [c_j^2-3c_j a+3a^2/4].

At a=pi/16 this is positive with the LV14 bound 1/64; at a=1 the full
relative n>=2 tail is less than 1/31, so A(1+i)<0. The resulting zero of
A lies strictly in Re zeta>0. On a small circle around it,

    r(zeta+2ik)/(8 pi^2 i k)
       = A(zeta) + [zeta A(zeta)-3 B(zeta)/(2 pi)]/(2ik).

For sufficiently large finite k the retained second term is less than
half the positive boundary minimum of |A|. Rouche yields a zero of full
r, hence a zero z_* of full f in S by z_*=(Log t_*)/2.

For real x->infinity, lambda_x=2 pi exp(2x), the exact normalized slice

    lambda_x V(x,z)/(x f(x)) -> f(z)

converges locally uniformly on S. The physical X=0 boundary, the whole
linear weight, and every theta mode are retained in LV18--LV20; the
dominating function is a constant times (1+v) exp(-v/2). A second Rouche
argument transfers z_* to a pair zero V(x,w)=0 in S x S. This contradicts
I2. These are zeros of the spatial source and the pair kernel, not zeros
of xi.

The parent checked the exact theta convention against
[DLMF 20.2.E4](https://dlmf.nist.gov/20.2.E4) and
[DLMF 20.7.E32](https://dlmf.nist.gov/20.7.E32). The new obstruction is the
response's analytic argument, not a theorem imported from those pages.

## I4. The conclusion returns to the original real interval

Consequently C is not PSD on ANY nonempty real open interval J. At every
a in J, some finite Taylor matrix

    [partial_x^j partial_y^k C(a,a)/(j! k!)]_(0<=j,k<=M)

has a real negative vector b, normalized to value -2. Otherwise all local
Taylor sums would be PSD, contradicting I2--I3. The finite-difference
coefficients are

    c_k(h) = sum_(j=k)^M b_j (-1)^(j-k) binom(j,k)/(j! h^j),
    x_k = a+k h.

The full local derivative bound B of LV26 gives, for sufficiently small
positive h with all nodes in J,

    sum_(r,s) c_r(h) C(a+r h,a+s h) c_s(h) <= -2+h B < -1.

This is analytic finite-row existence in I, not an effective rank, jet
order, numerical node list, or a negative row of V. The real coefficients
are valid within the required complex coefficient class.

## I5. Why the independently positive tail limit does not conflict

The separate LOGVCURV_PREFLIGHT report proves the full-source two-end
curvature limit with A(d)=sech^2(d), B(d)=csch^2(d)-d^(-2). Its Fourier
symbol is positive; every FIXED finite offset family is eventually
positive at large R. Neither its threshold nor its positive margin is
uniform over all families.

The new obstruction says that at every fixed exterior interval some
finite family is negative. Its family can depend on the interval and R.
Thus the two quantifiers do not contradict each other. The optional
uniform exterior C-positivity proposal in the preflight is now excluded
by the received result; the asymptotic identities and their positive
limiting kernel remain valid. No further C-positivity request is opened.

## I6. Decision effect for the original task

Do not try to repair this entrance by a new positive curvature constant,
a different finite rank, or a uniform comparison to the positive limit.
The obstruction concerns the entire infinitely divisible kernel class,
not one guessed feature map. The original V needs only ordinary Gram
positivity, which permits complex pair zeros (for example, K(x,y)=1+xy).
Any future candidate must preserve the original all-row target without
silently reintroducing fractional-power positivity or complex zero-freedom.

The square-rate structure is used concretely here: integer squares give
the exact imaginary period and parity split, and Jacobi reciprocity gives
the positive sign at the other endpoint. This is not a newly proved
property of prime factorization, nor a lower energy estimate for V.

This intake records a falsified stronger sufficient criterion. It does
not shrink the unpaid comparison for the original signed V, complete the
native RH goal, reset source-sign counters, or authorize a new route by
itself. Next selection must start from the original V/Schur target and
the accumulated exact filters, not from another name for C.

## Independent acceptance

Raw response review: `f4dcef883d82c47146436f2df834a838f628c3f78d69b7fbed71a9fd3ddaceca`.
Source-zero audit: `1406a3d76c737d286668e919917d0b3c87d4ed18922d142c9b1cc01c566524f8`.
CLEAN_INTAKE review: `f9681be4e0624a4a9c69115eda562ff3466850e59f7617fc25f62a4328507aea`.
Full review texts and pins are preserved in the accompanying certificate.
