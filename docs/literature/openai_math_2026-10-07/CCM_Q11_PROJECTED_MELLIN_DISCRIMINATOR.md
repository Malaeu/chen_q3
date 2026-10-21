# Post-Q10 own attempt 1: the original projector does not remove slow Mellin modes

2026-10-21. Original sparse CCM carrier, N=m,L=log m,
M=floor(m^epsilon), all three original constraints. Root derivation and bounded independent
q11_mellin_probe_review PAPER PASS. This is a control-source obstruction, NOT a result
about actual Lambda, mu, zeros or the full CCM spectrum.

## Scope and shelf

Q10 paid geometric reconstruction but left the signed source-weight pairing
unbounded. Test the possible shortcut that original P itself kills the slow
source term, before another arithmetic assumption is introduced.

Local ask.sh query `CCM Mellin exponential projection` returned INCOMPLETE
(semantic freshness); kb.py found old normalization warnings, not a supplier.
No absence claim. Direct reads of CCM_CONTINUOUS_RANK_TWO_TEST.md,
CCM_SPARSE_BAND_RECEIVER.md, CCM_Q03_ENDPOINT_SIGN_TEST.md and
CCM_Q03_ACTUAL_PRIME_BLOCK_OBSTRUCTION.md identify an existing exact probe.
The probe is reused, not claimed as newly discovered. The new calculation is
its response to a whole fixed-a family of Mellin source modes.

## Same original vector, no additional constraints

Let omega=2pi/L and

    g(t)=(1-cos(omega*t))^2,
    f(t)=(D^2-1/4)g(t)
        =-3/8+2(omega^2+1/4)cos(omega*t)
                    -(4omega^2+1/4)cos(2omega*t)/2.

This is exactly half the Q03 even endpoint probe. It uses only modes |j|<=2,
so belongs to every fixed-epsilon sparse band eventually. No frequency scale
or source schedule changed. Its original Fourier coefficients are padded by
zero outside these modes.

Since g=g'=g''=0 at both endpoints, f(0)=f(L)=0. Integrating twice by parts,

    integral exp(bt) f(t)dt=(b^2-1/4) integral exp(bt)g(t)dt.

Thus both moments at b=+/-1/2 vanish exactly. The endpoint equation b*c=0
also holds. Consequently f/||f|| is in ran(original P).
Orthogonality of the real Fourier modes gives

    ||f||^2=L D(omega),
    D(omega)=35/128+(5/4)omega^2+4omega^4>0.                 (1)

All mixed terms of the eventual translation form remain in f.

## Exact full-weight response, before Cauchy

Fix a in (0,1/2) before m grows. Define G_a as the original finite Fourier
compression of kernel exp(a|t-u|), equivalently integral_0^L exp(as)Q(s)ds.
The same algebra as the existing continuous rank-two test gives

    exp(a|t-u|)=exp(at)exp(-au)+exp(-at)exp(au)-exp(-a|t-u|).

The decaying kernel H_a is positive and has norm at most2/a. For example,
exp(-a|t-u|)=2a integral_{-infinity}^{min(t,u)}
exp(-a(t-v))exp(-a(u-v))dv is a Gram representation; Schur row mass is<=2/a.
These facts survive finite Fourier compression.

Put I_-=integral exp(-at)f(t)dt. Direct cosine integration yields

    I_-=(a^2-1/4) 6omega^4(1-exp(-aL))
                       /[a(a^2+omega^2)(a^2+4omega^2)].     (2)

f(L-t)=f(t), so I_+=exp(aL)I_-. Hence for the original UNIT coefficient
vector c representing f/||f||, the exact signed identity is

    c*G_a c=2m^a I_-^2/(L D(omega))-c*H_a c,               (3)
    0<=c*H_a c<=2/a.

For fixed a, I_-/omega^4 tends to6(a^2-1/4)/a^5, a nonzero constant;
D tends to35/128. Therefore there is c_a>0 and a late threshold such that

    c*P G_a P c >= c_a m^a/L^9-2/a.                       (4)

At a=1/2 the factor in (2) vanishes, recovering the old negative decaying
kernel exactly. That special cancellation does not extend to (0,1/2).
The constants/threshold in (4) depend on fixed a; no uniform limit a->0 or
changing-a-with-m claim is made.

## Consequence and exact limitation

For the CONTROL source E_z(x)=x^z-1, z=a+1/2, and the literal matrix weight
H_m(x)=x^(-1/2)P Q(log x)P, substitution x=exp(s) gives

    integral_1^m H_m(x)dE_z(x)=z P G_a P.                  (5)

Thus the complete source-weight pairing, retaining the exact original P,
can have positive size at least a fixed multiple of m^a/L^9. This already
occurs in five original modes. It excludes an automatic subpower bound
from the three constraints and narrow mode count alone, even for this
explicit smooth power-source family.
It is stronger than merely observing the leading derivative in Q10 §8.3:
that derivative survives the actual complete projected pairing as well.

This control is NOT actual Lambda or an actual zero contribution (whose
coefficient and complex phase cannot be changed). It is not a lower bound
for S_m, T_{>R}, or K_m. It does not exclude arithmetic cancellation or a
source-specific directed argument. Richardson reconstruction of the same
model cannot change (5); any separately estimated pieces must sum back to it.

Decision: do not pursue projection-only cancellation as a supplier. This is
one post-Q10 no-gain discriminator, not an arithmetic improvement. The next
candidate must identify an actual Lambda/mu relation unavailable to E_z, or
use a different already-proved source-specific sufficient interface.
Goal ACTIVE; RH OPEN; no new Pro message.

## Verification

56 rational exact controls check the Fourier normalization, endpoint,
Laplace coefficient identity and both zero moments at four rational omega
values and six rational a values. They are local algebra controls, not proof
of the continuous/asymptotic claims. Script: ccm_projected_mellin_q11_checks.py.
No SymPy dependency was installed (repository venv lacks it); the executed
checker uses only Python Fraction. No Lean, Arb or actual CCM spectra.
Independent readonly q11_mellin_probe_review PAPER PASS on this payload:
verified all constraints, kernel sign, Jacobian, exact coefficients, asymptotic
and control-only scope. No material finding. Wording about generic smoothness
was narrowed to this explicit power-source family, as the reviewer requested.
Two additional mpmath45 noninterval quadratures of the original5x5 Q matrix
checked the full growing+decaying identity, at(L,a)=(40,1/4),(80,1/8).
Relative residuals4.64e-44 and2.82e-44; not interval certificates or actual
prime sums. They check normalization only, not the asymptotic theorem.
