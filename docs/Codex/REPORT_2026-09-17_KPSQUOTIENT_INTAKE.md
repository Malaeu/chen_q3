# KPSQUOTIENT: accepted denominator filter; class membership remains open

STATUS: ACCEPTED_LIMITED_PAPER.
Date: 2026-09-17. Isolated research branch; canonical production untouched.
Producer: 8d3a63ae28c1ac92f06f433cd7e1b8d4ec266679.
Response: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_KPSQUOTIENT_2026-09-17.md.
Response SHA256: 14dcccc1270d83595d03dfcdb784c0b419e946b8fe2a966bfdaa153d5cd6647d.
Verdict: ACCEPT_KPSQUOTIENT_DENOMINATOR_FILTER_ONLY.

## What was independently accepted

The complete 387-line producer response was read by the parent and the
independent reviewer. Its full-source bounds, local Taylor constants,
concentration, continuation, zero propagation with cancellations, and exact
unsigned derivative/sine formulae passed the bounded analytic check.
The source remains rho(s)=q(sqrt(s)), q=Phi/int_R Phi, with all theta modes.
The target is still the original L2-normalized V on every finite admissible
complex family. No class membership or full-sign proof was accepted.

For D(u)=int_0^infinity s^(u-1/2)rho(s)ds, p=a+1/2>0, and
m_a=D(a+1)/D(a), the proved estimate is

 |D(a+i tau)/(D(a)m_a^(i tau))-1| <= 2|tau|/sqrt(p)+8/p.

In particular p>=64(1+tau^2) implies |D(a+i tau)|>=5D(a)/8>0.
The existing strict log concavity pays Var(S/E S)<1/p under the power
weighted density, and a two-event phase estimate pays the constants.
This is a parameter-wide bound for the full source, not finite sampling.
It is not a zero-free result for the whole plane or the whole half-plane.

Taylor subtraction continues D and N meromorphically to C with possible
simple poles only at the specified negative half-integers. The identity
N(v)=(v-1/2)D(v-1) holds with its cancellations, including the nonzero
value N(1/2)=rho(0). This agrees with the independently accepted entire
H=D/Gamma(u+1/2) and phi_*=4H(u-1)/H(u) audit.

If a nonreal zero u0 of this full D were established, the parabolic bound
would force the forward integer-shift zero set to end. At the point v
one step after its last zero, D(v)!=0 and D(v-1)=0. Hence phi_*(v)=0
holomorphically, with the exact numerator multiplicity. A nonconstant
Pick function cannot take a real value in the open upper half-plane.
Initial numerator/denominator cancellation therefore cannot rescue Pick.
A local Cauchy estimate supplies a strictly negative imaginary part nearby.
If the original D zero lies in Re u>-1/2, the same argument also excludes
ordinary Bernstein interpolation, using Re phi(a+i tau)>=phi(a)>0.

These are CONDITIONAL negative tests. No such theta zero was found here.
The tests do not claim that failure of a sufficient class refutes RH.

The remaining full signs are written exactly as

 phi_*''(u)=4 E_u[(h-E_u h)(log S-E_u log S)^2],

 Im phi_*(a+i tau)=4/|D(a+i tau)|^2 int_0^infinity W_a(r)sin(tau r)dr,

where W_a is the complete positive weight specified in producer (KQ19).
The independent check pays its Jacobian, orientation, integrability and
logarithmic moments. Neither positivity of W_a nor monotonicity of h
pays the remaining signs. These are formulas for the same open problem,
not a positive supplier for the original V.

## Decision and stopping point for this request

The request is answered with a limited TRY result. Actual Bernstein,
Pick and unit-separation membership remain undecided. No actual source
negative witness, sign improvement of full V, or RH proof was obtained.
The special arithmetic placement of the square rates has not supplied
an additional sign mechanism in this filter. Do not repeat the same
class-membership request without new source information.

The parent is separately checking the classical coefficient-transform
consumer on the already constructed H. That private candidate is NOT
accepted by this intake and no new proof request is sent by this commit.

Review SHA256: fde1b165acc3fb4adc9ef436b69296af1301e25c60cb0884e53c2cf56ddf8a0e.
Parent check SHA256: 526606414b4b57b5a8176583af7164b2ffc2f9dc16b085d11b5020c45405e203.
The paired certificate embeds both complete reviews and their exact source
binding. This is an isolated PAPER result, not Lean or canonical admission.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET.
FULL_V_SIGN: OPEN. RH: OPEN. SOURCE_SIGN_COUNTER_RESET: false.
