# Q19 own attempt: fixed-line shift of the entire complex pair transform

2026-10-25. Rollback before positive-forcing/lobe cap. Same original P,
fixed hypothetical w=delta+i gamma,0<delta<1/2, multiplicity r and separate
partner constants. Sources: Q18 verdict10.3, Q17 pair averaging and receivers.
This is not a rerun of uniform averaging: the tested extra operation is a
vertical-line shift of the ENTIRE finite-prime pair transform. Q14 used
logarithmic-derivative error contours; this is a different finite entire input.
No mathematical global novelty claim, no new favorable full exponent.

## Full source, no independent sign payments

C(s)=integral conjugate(g(t))k(t+s)dt, v=-conjugate(w),
A(z)=(z²-1/4) M_G(z),
M_C(z)=kappa A(z)^2/(z+conjugate(w))^(2r),
kappa=(-1)^r/(conjugate(c_w)c_v)=1/conjugate(c_w)^2.
The apparent pole at v is removable with M_C(v)=1. The source profiles and
all fixed derivatives have the inherited double-exponential tails, so M_C
is entire and rapidly decreasing in imaginary direction on each fixed
vertical strip, by integration by parts. No uniform growing-strip bound is
asserted. These properties can also be obtained directly from C, avoiding
any division estimate near v.

For the ACTUAL finite polynomial
 D_m(z)=sum_(2<=n<=m)Lambda(n)/sqrt(n) [n^z+n^(-z)]
we have M[J(y/2;m)](z)=D_m(z)M_C(z), with both time signs and all prime powers.
For every fixed real sigma Fourier inversion of exp(sigma y)J gives
 J(a;m)=1/(2pi) integral_R D_m(sigma+it)M_C(sigma+it)
                                      exp(-2a(sigma+it))dt.       (1)
Moving between two fixed lines gives no residues: D_m is finite/entire,
and the apparent pole in M_C is removable. The contacts at +-1/2 are zeros,
not poles producing a free favorable residue. The same identities hold
before applying any inequality or splitting real signs.

Let h=L/2-log L,1<=T<=h/2 and retain the positive average of forms:
 B_T=Re [1/(2pi) integral D_m(z) M_C(z) F_T(z)dt],
 F_T(z)=[exp(2(i gamma-z)h)-exp(2(i gamma-z)(h-T))]
                                    /[2T(i gamma-z)].            (2)
F_T is entire; F_T(i gamma)=1. The phase resonance therefore survives the
mean exactly. It is not an actual pole and not a constructed numerical zero.
All exchanges in (1)-(2) use finite n, bounded a interval, and integrable
vertical transform at each fixed m, not an infinite prime Dirichlet series.

## Completed bound for this fixed-line attempt

Define L_C(sigma)=(1/(2pi))integral|M_C(sigma+it)|dt < infinity,
W(m)=sum Lambda(n)/sqrt(n)<=6sqrt(m).
Only at this completion do we use
 |D_m(sigma+it)|<=2m^|sigma| W(m),
 |F_T(sigma+it)|<=V_sigma,
 V_sigma=exp(-2sigma h)(exp(2sigma T)-1)/(2sigma T),sigma!=0,
 V_0=1.
Consequently
 B_T>=-12 L_C(sigma) m^(.5+|sigma|) V_sigma.              (3)
This keeps the full complex expression until the displayed modulus bound.
It is NOT a lower bound on the true size of B_T.

For T=alpha L with fixed0<alpha<1/4 (eventually within h/2), the power in
this explicit sufficient budget is
 sigma>0: 1/2+2alpha sigma, with log factor L^(2sigma-1),
 sigma=0: 1/2,
 sigma<0: 1/2+2|sigma|, with log factor L^(2sigma-1).
No fixed vertical line improves on half-power in this completion. In
particular decay exp(-2sigma a) cannot be used without the simultaneous
m^|sigma| growth of the actual finite prime polynomial. Allowing sigma to
depend on m would require uniform bounds for L_C(sigma); no such strategy
is declared impossible or paid here. Even this fixed-line cap is weaker
than the inherited physical-localization averaged sqrt(m)/L² bound.

## Full return and comparison to the requested signal

The source pair remains f_a=exp(-i gamma a)tau_a g-exp(i gamma a)tau_-a k.
Its full prime form is self_g+self_k-2Re(exp(2i gamma a)J), self terms O_w(1).
Apply the inherited cutoff/Fourier/three-contact receiver to THIS WHOLE pair;
no P is commuted through a contour or applied separately to frequencies.
For one fixed q>1/epsilon+2 the same rho_K,rho_S=o(1) cover every projection
mixed term, uniformly on [h-T,h]. Archimedean price D_w(50L+8) once.
Thus (3) gives the completed lower bound
 average z* K_m z >= -24 L_C(sigma) m^(.5+|sigma|)V_sigma
                    -D_w(50L+8)-O_w(1)-rho_S.           (4)
No auxiliary theta cutoff is used, so no new theta-index fee or unpaid
E1/E2/FU is introduced: the full C transform is used BEFORE that integration
by parts. If one later introduces such a representation its fees must return.
Conditional witness E_T=exp(2delta h)(1-exp(-2delta T))/(2delta T)
is unchanged. At T=alpha L it has order m^delta/L^(2delta+1).
Even sigma0 in (4) leaves a power deficit1/2-delta. Keep the stronger old
sqrt(m)/L² budget; do not promote this attempt to a new arithmetic result.

## Concrete next test, distinct from moving the same contour

At sigma0 pair frequencies about gamma: t=gamma+s and gamma-s. Define
 N_+(s)=A(i(gamma+s))²D_m(i(gamma+s)),
 N_-(s)=A(i(gamma-s))²D_m(i(gamma-s)).
Then EXACTLY, after pairing t on the whole real line,
 B_T=1/(2pi) integral_0^infinity Re{
 kappa [N_+(s)F_T(i(gamma+s))/(delta+is)^(2r)
       +N_-(s)F_T(i(gamma-s))/(delta-is)^(2r)]}ds.        (5)
The denominators are conjugate and F_- =conjugate(F_+) for real h,T.
But N_- is NOT known to be conjugate(N_+): A(it) is real/even around zero,
not automatically symmetric around gamma. D_m(it)=2sum Lambda/sqrt(n)
cos(t log n) is real, also even around zero, not around gamma.
Even if those numerators matched, complex kappa must still remain.
In fact N_+,N_- are REAL on this line. Let Z=F_T(i(gamma+s))/(delta+is)^(2r).
The real paired integrand in (5) is exactly
 Re(kappa)Re(Z)(N_++N_-) - Im(kappa)Im(Z)(N_+-N_-).       (6)
A(it)^2 is nonnegative, but D_m(it) is sign-changing, so N_± have no automatic positivity.
This exposes the actual sum AND reflection defect with their distinct signed
weights. Neither can be discarded. It is a finite-source identity, not yet
an inequality.

Q19 candidate: exploit the exact difference between these two actual
numerators jointly, using the common entire A and its zero/normalization
structure; test whether a source-specific signed pairing estimate before
moduli pays the required signal. Do NOT assume the reflection defect small,
replace A² by a modulus square off its legitimate line, or turn conditional
adverse zero identity into a favorable supplier. If this pairing offers no
real mechanism, return its precise unpaid line and an earlier substantive
rollback rather than repeating (3) or renaming the target.
The fixed-line completion is the concrete documented impasse authorizing
Q19 preparation under the owner's scenario. This note itself does not prove
(5) is easier or that it provides new cancellation.

## Verification

experiments/ccm_q19_complex_contour/check.py:52 exact local checks of the
mean multiplier/removable value, finite exponent bookkeeping and conjugate
denominators. First run failed a SymPy sinh-versus-exponential structural
comparison; rewriting sinh as exponentials fixed the test without changing
mathematics. No source numerical values, Lean or Arb.
Independent bounded PAPER audit: q19_complex_contour_audit PASS (2026-10-25): fixed-strip justification, completed exponents, full return and identities (5)-(6). Checker executed by root; reviewer did not rerun it. This is a bounded audit, not a verification of the entire inherited proof chain.
