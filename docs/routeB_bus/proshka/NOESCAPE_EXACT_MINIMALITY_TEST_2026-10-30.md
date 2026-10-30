# Exact-minimality test: finite-carrier phase curvature

Status: OWN ATTEMPT, independently checked algebra; not a supplier for T. This implements the
owner refinement without restricting competitors to modulus repair. It gives
an exact test and identifies an unpaid sign. It does NOT claim that naming
this test supplies the missing source property.

## Same-carrier competitor with no norm or return approximation

Let P=P_m, A=A_m, f a unit exact even bottom, lambda=k[f]. Choose the explicit
real even multiplier chi(x)=exp(-x²), and B=P M_chi P on the even carrier.
B is self-adjoint, ||B||<=1, and U(t)=exp(i t B) is unitary ON THAT CARRIER.
Thus g(t)=U(t)f is exactly normalized, even, and uses the original cutoff m.
Complex competitors are allowed for the Hermitian form. If a strictly lower
complex competitor is found for a real matrix, at least one nonzero real or
imaginary component, separately normalized, has strictly lower energy too.

For E(t)=<U(t)f,A U(t)f>, exact eigenrelation gives E'(0)=0, and

    D_m(f):=E''(0)=<f,[B,[A,B]]f>
       =2<Bf,(A-lambda)Bf> >=0.                           (M1)

The last inequality uses EXACT MINIMALITY, not merely stationarity. A
source proof D_m(f)<0 under escape would give an actual competitor for small
t!=0. All matrix entries in A are the original source entries: diagonal,
arch integral, all prime powers through m, and both poles.

For example if D_m(f)<=-kappa<0, ||B||>0 and ||A||>0, Taylor's theorem and
||ad_B^3(A)||<=8||A||||B||³ show

    E(t)-lambda <=-kappa t²/2+(4/3)||A||||B||³|t|³<0

whenever 0<|t|<3kappa/(8||A||||B||³). The margin kappa may tend to zero.
No lower bound independent of m is required. This is a quantitative implication,
not a proved negative curvature for our bottoms.

## Exact raw-source decomposition and projection costs

To compare with a physical-space formula set

    z=chi f,  r=(I-P)z,
    s=(I-P)(chi²f),  t=P(chi r).

Then Bf=z-r and B²f=chi²f-s-t, so exactly

    D_m(f)=D_phys(f)-4 Re k(z,r)+2k[r]+2 Re k(f,s+t),     (M2)
    D_phys(f)=2k[chi f]-2 Re k(f,chi²f).

These mixed and projection terms may not be discarded. Bounded smooth
multiplication preserves the relevant piecewise smooth window form domain.
Every pairing in(M2) is the full raw form on that domain. Outside-prime
correlations vanish only because all arguments have support in the same I.

Writing C_f(x,y)=Re(conj(f(x))f(y)), the exact physical expression is

    D_phys = integral_I integral_I j(|x-y|)(chi(x)-chi(y))² C_f(x,y) dxdy
      +2 sum_{2<=n<=m} Lambda(n)/sqrt(n)
           integral_R (chi(x+logn)-chi(x))² C_f(x,x+logn) dx
      -integral_I integral_I p(x)p(y)(chi(x)-chi(y))² C_f(x,y) dxdy
      +integral_I integral_I q(x)q(y)(chi(x)-chi(y))² C_f(x,y) dxdy. (M3)

Here p=sqrt2 cosh(x/2), q=sqrt2 sinh(x/2); f is zero outside I.
The last line is zero for even f and even chi, by expanding the square into
odd pole pairings, not by deleting that sector from the definition.
The diagonal constant cancels algebraically. The arch s>L diagonal tail
also cancels by the same multiplication identity. All prime powers remain.

C_f is signed, so the positive jump weights alone supply no sign to(M3).
The even pole has the opposite sign; the exact finite projection adds(M2).
Neither jet escape nor its integral representation through H(t)=4xi(1/2-it)
has been shown to impose a negative upper bound on the SUM (M2)-(M3).
Sign reversal does nothing: replacing f by -f leaves all expressions unchanged;
choosing chi constant gives B proportional to identity and D_m=0.

## Control against the escaping radical trials

For ANY unit trial v, let q_v=<v,Av>, R_v=(A-q_v)v. Then

    D_m(v)=2<Bv,(A-q_v)Bv>-2 Re<R_v,B²v>.                 (M4)

The extra residual term has modulus at most2||R_v||||B||². A small residual
therefore gives only an absolute small error, not a strict sign on a
vanishing curvature scale. For the constructed escaping radical trials,
q_v->0, ||R_v||->0, and weak escape holds, but A-q_v need not be positive
semidefinite. That is the exact line where they fail to satisfy the bottom
hypothesis used in(M1).

Since this chi is fixed and localized, the specifically constructed translated
radical trials also satisfy ||Bv_m||<=||chi v_m||->0. However ||A_m|| may grow,
so this observation alone does not even prove convergence of the first term
of(M4), let alone its sign. No curvature sign is asserted for those trials.
A proposed bound with a vanishing negative margin must be compared against
the actual residual term in(M4), rather than replacing it by zero.

## Current outcome

This is a concrete direction test, not an answer to the main source question.
It would become useful only with a NEW source-derived inequality, for example
an explicit negative upper bound for(M2)-(M3) forced by escape together with
exact-bottom restrictions. That inequality has not been obtained. Calling
D_m(f)<0 the desired property without deriving its source sign would merely
rephrase descent in a chosen direction. We do not count that as a supplier.

The exact-minimality premise is A-lambda I>=0 on the entire finite carrier.
The task remains to combine its consequences with source structure and escape
to violate one checkable inequality; small energy, small residual, phase
language, and finite moment cancellation do not supply that violation.
Pending Proshka was not interrupted or sent this intermediate calculation.

Independent read-only mathematical check confirmed M1-M4, projection terms,
prime/pole signs and the Taylor remainder. No negative source sign or new
cofinal supplier was obtained or accepted.
