# Actual pair phase delay: resonance preflight before Q23

2026-10-25. Conditional on the same actual w=delta+i gamma, multiplicity r,
separately normalized Q17 profiles; no zero is assigned a numerical value.
Original P and schedule unchanged. This is an exact phase discriminator,
not a new bound on full CCM, and not a claim of novel all-pass algebra.

From Q17 (1.6), Q19 §2 and the post-Q22 affine preflight,
M_k(it)=U(s)M_g(it), s=t-gamma,
U(s)=eta[(delta-is)/(delta+is)]^r, eta=c_w/conjugate(c_w).
For J(a;m), Fourier inversion of C at 2a-log(n) gives the s-dependent
phase (apart from the constant eta*n^(i gamma))

    phi_n(s)=(log(n)-2a)s-2r atan(s/delta).
    phi_n'(s)=log(n)-2a-2r delta/(delta^2+s^2).

The other time orientation replaces log(n) by -log(n), so its derivative
is strictly negative for a>0. The first orientation has real stationary
points precisely when

    0 < log(n)-2a <= 2r/delta.

For a strict inequality below the upper endpoint there are two points
s=+/-sqrt(2r delta/(log(n)-2a)-delta^2). At the upper endpoint they
coalesce at zero: phi''(0)=0, phi'''(0)=4r/delta^3. Thus nonstationary
integration by parts over every prime is not valid; even a uniform
nondegenerate stationary-phase estimate misses the coalescence.
The zero lower endpoint has no finite stationary point; it cannot be
included by division by log(n)-2a. The amplitude is |M_g(i(gamma+s))|^2,
not a freely chosen bump. The complex eta*n^(i gamma) remains.

## Actual mass and what a separate payment costs

The resonant prime-power band is

    exp(2a) < n <= exp(2a+2r/delta).

For a in [h-T,h], h=L/2-log L, T=alpha L, fixed alpha<1/4, it lies below
m eventually, uniformly in a, and its lower endpoint tends to infinity.
Ordinary PNT on this fixed relative interval, including all Lambda(n), gives

    sum_band Lambda(n)/sqrt(n)
       = (2(exp(r/delta)-1)+o_w(1)) exp(a).

This is a mass asymptotic, NOT the signed band contribution. The modulus
bound |C(y)|<=||g|| ||k||=||g||^2 would pay O_w(exp(a)) for this band.
Averaged over a it costs

    O_w(exp(h)(1-exp(-T))/T)=O_w(sqrt(m)/L^2).

Relative to E_T asymp_w m^delta/L^(2delta+1), this payment has order
m^(1/2-delta) L^(2delta-1), which diverges. Constants depend on fixed w,r;
no uniform delta->0 assertion. This only diagnoses that separate modulus
payment cannot give the desired signal margin; it is not a lower bound
for the actual signed band or for all phase-delay arguments.

No off-band estimate is claimed here. The already accepted complete pair
budget O_w(sqrt(m)/L^2+L)+o(1), including original-P return, stays unchanged.
The same conditional profiles permit inherited fixed-q return; no unitary
multiplier is commuted through P or the cutoff. Any frequency/prime-band
splitting must reassemble both sides and all interfaces BEFORE invoking
that return. The continuum D0 contribution is small only after its full
signed assembly and may not be charged separately in every band.

Two symbolic derivative identities and the coalescence value were checked
exactly with existing SymPy. These are algebra controls, not numerical
evaluation of an actual off-critical zero or full CCM spectrum.

Concrete next question: test a JOINT phase-delay/resonant-band estimate
using the actual source amplitude and the arithmetic constant n^(i gamma),
including coalescence, both time signs and the complementary continuum
credit. If this cannot improve the full price, give a worked earlier
source rollback. This question is justified by the concrete surviving
resonance, not by pretending three independent failures have occurred.
