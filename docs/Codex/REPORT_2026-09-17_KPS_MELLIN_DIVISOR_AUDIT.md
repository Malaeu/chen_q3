# What the exact KPS shift identity does and does not supply

STATUS: ACCEPTED_LIMITED_PAPER; S1--S3 independently reviewed.
Base: 98722205a0b57689fc7756c74537c9fe0c597bac. Isolated analytic research.
The existing KPSQUOTIENT proof job remains live; this is a local interface
check, not a replacement request or a claim about the sign of original V.

Source inputs:
- REPORT_2026-09-17_KPS_FORCED_QUOTIENT.md, SHA256
  8b5cc3a609cf73ef977ee67c6036e5cfaef6294d496f9b0f78f6ba847558f1ff.
- REPORT_2026-09-17_KPS_MOMENT_INTERFACE.md, SHA256
  8db1503625708a8271f63ea9b1ff33ed5d38ecbe131718ab152688b322e528a0.
- KPS journal PDF, SHA256
  05f75d661af5d94d64c5c66b6a9c1ee22a73d53e13c5afd8ceb7a76a5cf14a19;
  definition (4.14), Theorem 4.4, printed p396.
All normalizations, original V, complex-family quantifiers and source are
unchanged. In this note rho(s)=q(sqrt(s)), q=Phi/integral_R Phi.

## S1. The actual quotient has one exact gamma-normalized shift form

Let a_k=rho^(k)(0)/k!. The actual rho is real analytic at zero. Indeed,
the full series for r(t) is normally convergent in a complex neighborhood
of t=1 contained in Re(t)>0, and Phi(x)=exp(5x/2)r(exp(2x)) is analytic
near x=0. Its proved evenness makes its local series a convergent series
in s=x^2. This is local analyticity, not a claim that Phi is entire.
The actual rho and rho' have the full rapid positive-axis decay already
used in the pinned quotient proof.

Start with D(u)=int_0^infinity s^(u-1/2)rho(s)ds, Re(u)>-1/2.
Choose epsilon>0 inside the radius of the local rho series. For M>=1,

 D(u)=int_epsilon^infinity s^(u-1/2)rho(s)ds
     +int_0^epsilon s^(u-1/2)[rho(s)-sum_(k=0)^(M-1) a_k s^k]ds
     +sum_(k=0)^(M-1) a_k epsilon^(u+k+1/2)/(u+k+1/2).       (S1)

The first integral is entire in u by full tail decay; the second is
holomorphic for Re(u)>-M-1/2 by the O(s^M) remainder. Formulae for
different M agree in their common original domain and hence throughout
all overlapping continuation domains. Thus D continues meromorphically
to C, with at most simple poles at u=-k-1/2, residue a_k.

Define

 H(u)=D(u)/Gamma(u+1/2).                                (S2)

Since Gamma has a simple pole there of residue (-1)^k/k! and has no
zeros, H is entire, real on the real axis, and

 H(-k-1/2)=(-1)^k k! a_k.                              (S3)

This includes a_k=0, where H has a zero instead of a nonzero limiting
value. H is not the Fourier transform F and is not presumed zero-free.

For Re(u)>1/2, integration by parts in N gives

 N(u)=(u-1/2)D(u-1).

The origin boundary has strictly positive real power u-1/2 and the
infinity boundary is paid by the full derivative/source tails. Gamma's
recurrence cancels exactly the factor u-1/2. Consequently the forced
quotient from the accepted report has the meromorphic continuation

 phi_*(u)=4 H(u-1)/H(u), u in C.                       (S4)

This is equality of meromorphic functions, not pointwise division at an
unresolved 0/0. It agrees with 4N/D on the previously proved half-plane.
No zeros of H have been located to obtain the identity.

There is also a paid real-axis consequence: analytic continuation of
H(u-1)=N(u)/Gamma(u+1/2) gives H(v)>0 for every real v>-3/2, because
N(v+1)>0 and Gamma(v+3/2)>0 there. No closed-endpoint sign is
needed here. This is only a real-axis zero exclusion, not a complex
zero-free half-plane.

## S2. Cancellation is precisely the remaining issue in reading separation

For any z in C let m(z) be the multiplicity of the zero of the entire H
at z, or zero when H(z)!=0. The order of the meromorphic quotient is

 ord_z phi_*=m(z-1)-m(z).                              (S5)

Positive order is a zero, negative order a pole. This accounts for all
cancellations and multiplicities. In particular, a simple isolated zero
t of H with H(t-1)H(t+1)!=0 gives a pole of phi_* at t and a zero at t+1.
But a chain of consecutive zeros of H can cancel the intermediate entries.
Thus the shift identity alone does NOT establish the KPS condition
rho_k=z_k-1>z_(k+1) for the surviving zeros and poles.

No Pick property, reality or simplicity of H zeros, absence of unit chains,
or global ordering is obtained from (S4). These are not free consequences
of writing the same quotient as a ratio of shifted entire functions.
The next explicit control shows the cancellation issue inside the positive
Abel/moment setting rather than only for an arbitrary formal quotient.

## S3. Positive full-profile control: even Pick does not force 1-separation

This section changes the source deliberately. It is NOT actual theta.
Put

 rho_c(s)=exp(-s)(s^2+3s+15/4),
 q_c(x)=rho_c(x^2)/(6sqrt(pi)).

Gaussian even moments give integral_R q_c=1. The profile is positive,
even and rapidly decreasing. Its squared-coordinate log profile is
strictly concave, because with P(s)=s^2+3s+15/4,

 (log rho_c)''(s)=[2P(s)-(2s+3)^2]/P(s)^2
                 =-(2s^2+6s+3/2)/P(s)^2<0, s>=0.

Also rho_c'(s)=-exp(-s)(s^2+s+3/4)<0. It therefore has the same elementary
positive planar Abel construction. The overall probability constant
cancels in every moment quotient below.

The gamma integrals evaluate the unnormalized D exactly:

 D_c(u)=Gamma(u+1/2)[(u+1/2)(u+3/2)+3(u+1/2)+15/4]
       =Gamma(u+1/2)(u+2)(u+3), Re(u)>-1/2.

Hence H_c(u)=(u+2)(u+3), up to the positive normalization constant, and

 phi_c(u)=4 H_c(u-1)/H_c(u)=4(u+1)/(u+3).               (S6)

This IS both Bernstein and Pick. For u>0 it has the explicit positive
Levy representation

 phi_c(u)=4/3+8 int_0^infinity (1-exp(-ut))exp(-3t)dt.

For Im(z)>0, Im phi_c(z)=8 Im(z)/|z+3|^2>0. Nevertheless its only zero
is -1 and its only pole is -3. Their separation is 2, not the stipulated
1. This is cancellation of the consecutive H zeros -3,-2. Thus phi_c
fails B_P1 specifically at separation, despite satisfying the full Pick
and Bernstein conditions and arising from a positive decreasing profile.

In this control, the Fourier transform even has ONLY REAL zeros:

 F_c(z)=exp(-z^2/4)(1-z^2/4+z^4/96).                  (S7)

To check this, differentiate sqrt(pi)exp(-z^2/4) twice and four times
under the Gaussian integral and combine the x^4+3x^2+15/4 coefficients.
The polynomial roots obey z^2=12+-4sqrt(3)>0, so all four zeros are real;
the exponential has none. This control is not a negative V witness.
It confirms by an elementary exact example that this particular KPS
1-separation entrance is sufficient, not necessary for real Fourier zeros.
No conclusion about actual theta Pick/separation membership follows.

## Consequence for the live job

The exact theta quotient already supplies the unit SHIFT of H, with its
entire continuation and divisor formula. It does not supply the unit GAP
of the surviving phi zeros/poles. The distinction survives even positive
Abel laws, strict squared-coordinate log concavity and Bernstein--Pick
membership. If the live test fails solely on separation, report that
specific stronger-route failure; do not describe it as a refutation of
all positive representations, actual Pick membership, original V or RH.
No additional Pro request was sent and no source-sign counter is reset.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated PAPER only.

## Independent acceptance

Candidate SHA256: `12a28c6fc8745f4762ad8d70b6b5458d7715465e9704792eed0f07e11325a7e3`.
Review SHA256: `ac3066e32ee9a541cc74ca1426a667cacb9c22768c972d9eed3f46737b5c2ca0`.
Verdict: `ACCEPT_EXACT_MELLIN_SHIFT_DIVISOR_AND_SEPARATION_CONTROL_ONLY`.
The complete independent review and parent check are in the paired certificate.
An unused closed-endpoint assertion was removed before final acceptance.
Only the exact meromorphic shift interface and the explicitly different-source
control are accepted. No actual theta class membership or full V sign follows.
No new Proshka request, canonical admission, or source-sign counter reset.
