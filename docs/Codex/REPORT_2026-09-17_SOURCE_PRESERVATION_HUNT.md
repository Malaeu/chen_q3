# Source-preservation hunt: a positive moment defect and a nonmatching PF brother

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete.
Base: fd8db9472169d081170ecfddae995f5707e0aa93.
Scope: isolated analytic research, not canonical proof admission.
Original full V and RH remain OPEN. No new Pro proof request is proposed.

## 1. Exact return point and paid source

The completed PICKVAR result controls one necessary comparison of two
logarithmic variances for every u>=U_*. It does not prove the global Pick
property. This hunt returns to the source transformation, not a subdivision
of the remaining interval.

Use the complete positive density r, extended by zero to t<=0, with

    L_r(v)=integral_0^infinity exp(-vt)r(t)dt
          =product_(n>=1)(1+v/(pi*n^2))^(-2)
          =(sqrt(pi*v)/sinh(sqrt(pi*v)))^2,
    r(1/t)=t^(5/2)r(t),
    Phi(x)=exp(5x/2)r(exp(2x)), q=Phi/Z, Z=xi(1/2)>0,
    rho(s)=q(sqrt(s)), s>=0.

The Laplace identity initially holds in its convergence half-plane and
then meromorphically. The reciprocal products used below are entire in v;
their square-root notation denotes the single-valued even power series.
The actual rho is positive and strictly log-concave on (0,infinity);
all its polynomial moments are finite. Additive PF infinity of r, exact
reciprocity, and these full-source bounds are accepted inputs.

Keep D(u)=integral s^(u-1/2)rho(s)ds and
N(u)=integral s^(u-1/2)(-rho'(s))ds for Re u>-1/2;
H(u)=D(u)/Gamma(u+1/2) is the already proved entire continuation.
The unchanged sufficient consumer is global Pick of 4H(u-1)/H(u) => RH
=> original V>=0 for every admissible finite complex family. A direct
proof that this H has only real negative zeros would also fit the
already paid order/coefficient/Laguerre part of that consumer.
Neither source assertion is proved here.

## 2. Primary mechanisms and exact limits

A. Klartag--Lehec, *Poisson processes and a log-concave Bernstein theorem*,
author PDF https://www.math.tau.ac.il/~klartagb/papers/log_concave_bernstein.pdf.
PDF SHA256 918eab5c3ad0da9ca41520c944c705a21b84820a557ab81fbf203fd2d2f9503a.
Theorem 1.5, printed p.3, equation (4); proof printed p.11.
Short quotation: "there exists a finite, non-negative measure".
For a finite log-concave measure mu, it represents
a_tau(l)a_tau(m)-a_tau(k)a_tau(n) as a Laplace transform of a positive
measure whenever k<=l<=m<=n are nonnegative integers and k+n=l+m,
where a_tau(j)=integral s^j exp(-tau*s)dmu(s)/j!.
Their alternating derivative condition is called completely monotone
here, regardless of the terminology in the PDF.

This is a source theorem with a checked application to dmu=rho(s)ds.
The parameter tau is an added Laplace damping parameter. It is NOT our
Mellin parameter u. The theorem does not compare rho with -rho'.
Section 3 below proves one exact application directly, including its
positive measure, without importing the proof of the general theorem.

B. Pickrell, *A Question About Total Positivity and Newman's Fourier
Transforms with Real Zeroes*, arXiv:2104.05143v1,
https://arxiv.org/pdf/2104.05143v1.
PDF SHA256 fe048cec42e0df081fb7a3194f0c540c7aa13750c80dab3a426da57760722306.
Theorem 1.1(b), p.3; section 1.1, p.4; section 2.1, p.5.
Short quotation, p.5: "is not equal to a Z".
The proposed bridge uses the characteristic function p of a PF density
and a reciprocal evaluated at an imaginary square, followed by a Fourier
transform. It is not a Mellin transformation of that density.

There is a literal sign discrepancy: the measure in section 1.1 is
1/p(-ix^2), whereas its following Z_b integral prints 1/p(+ix^2).
We do not silently choose a sign or import a general real-zero assertion
for every real PF parameter. Section 4 computes BOTH substitutions for our
actual r and independently proves the relevant conclusions. The full
Newman classification and infinite matrix interpretation are not used.

C. Craven--Csordas, *The Fox--Wright functions and Laguerre multiplier
sequences*, JMAA 314 (2006), 109--125, DOI 10.1016/j.jmaa.2005.03.058.
Author PDF https://math.hawaii.edu/~tom/mathfiles/fox_wright.pdf.
PDF SHA256 9c12ca03623129950b2f4cc937311327c5057bb48c8d10aa2970f0929b09673d.
Theorem 2.4(3), printed p.113; Example 2.7, p.114.
Short quotation: "a complex zero decreasing sequence".
The theorem takes an already Laguerre--Polya function with nonpositive
zeros and uses its integer values as a multiplier sequence. Substitution
of our H therefore still requires its unproved real-zero property.
The reciprocal-Gamma examples are genuine preservers but do not show
that the full Mellin factor being normalized belongs to the input class.
This is the existing downstream mechanism, not a new source supplier.

## 3. An exact positive defect for the complete rho

For tau>=0 put

    A_j(tau)=1/j! integral_0^infinity s^j exp(-tau*s)rho(s)ds,
    C(tau)=A_1(tau)^2-A_0(tau)A_2(tau).

All these integrals are finite. Absolute Fubini, followed by symmetrizing
the two variables and setting y=s+t, gives exactly

    C(tau)=integral_0^infinity exp(-tau*y)m_rho(y)dy,
    m_rho(y)=integral_0^y
        [ (3/2)s(y-s)-y^2/4 ]rho(s)rho(y-s)ds.           (P1)

This is the (k,l,m,n)=(0,1,1,2) instance of source A. We now prove
m_rho(y)>0 for every y>0 directly from the paid strict log concavity.

Set z=s/y, a=(1-1/sqrt(3))/2 and

    K(z)=(3/2)z(1-z)-1/4,
    W_y(z)=rho(yz)rho(y(1-z)).

Both functions are symmetric about 1/2. K is negative on (0,a) and
(1-a,1), positive on (a,1-a), and integral_0^1 K(z)dz=0.
Strict log concavity makes W_y strictly increasing on (0,1/2) and
strictly decreasing on (1/2,1). Consequently

    K(z)[W_y(z)-W_y(a)] >= 0,

strictly on subsets of positive measure. Thus

    m_rho(y)=y^3 integral_0^1 K(z)[W_y(z)-W_y(a)]dz > 0. (P2)

The subtraction is justified by the exact zero integral of K. It does
not change C. Its role is to account together for a negative edge part
and a positive central part of the SAME conditioned integral.
Absolute integrability of m_rho follows by bounding its polynomial kernel
by a constant times (s+t)^2 and using the finite rho moments.
Thus m_rho(y)dy is a finite positive measure and C(tau)>0 for every
tau>=0. All derivatives in tau also have the alternating sign, since
every further y moment is finite for the full source.

An exponential profile w(s)=exp(-alpha*s), alpha>0, gives W_y constant
and m_w identically zero. Any smooth strictly log-concave positive profile
with sufficient moments gives the strict version above. Hence this is a
worked exact compensation mechanism, not a property peculiar to primes.

What P1 does NOT pay:
- C is a two-moment defect of ONE density, not the original V or E_loss.
- It concerns powers s^j and damping tau, not a variance of log s under
  two differently normalized densities.
- The required VAR uses P_D proportional to s^(u-1/2)rho(s) and P_N
  proportional to s^(u-1/2)(-rho'(s)). No identity replaces their
  difference of log variances by P1.
- The prior control rho_epsilon(s)=exp(-s-epsilon*s^3) has strict log
  concavity, hence satisfies P1-P2, but for sufficiently small epsilon>0
  its forced quotient has (log phi_epsilon)''(1)>0 and violates VAR.
  This analytic control is already independently accepted. Thus P1,
  even on the whole damping half-line, cannot by itself imply VAR/Pick.

No general continuous-parameter Borell curvature bound is imported from
an introductory sentence. The finite-moment application above is exact.

## 4. The actual PF input produces two explicit different sources

Use the convention

    p(z)=integral exp(izt)r(t)dt=L_r(-iz)

where the integral converges, and retain its meromorphic continuation.
Let b>0 and a0=sqrt(pi). The two entire reciprocal substitutions give

    w_b^-(x)=exp(-b*x^2)/p(-ix^2)
            =exp(-b*x^2)[sin(a0*x)/(a0*x)]^2,           (P3)
    w_b^+(x)=exp(-b*x^2)/p(+ix^2)
            =exp(-b*x^2)[sinh(a0*x)/(a0*x)]^2.          (P4)

Values at x=0 are defined by continuity. P3 outside |x|<sqrt(pi)
uses analytic continuation, not a convergent positive moment-generating
integral. At poles of p the reciprocal extends to zero.
Both w_b^+ and w_b^- are nonnegative, even, integrable, and have Gaussian
tails up to a linear exponential factor. Normalizing their masses does
not change any zero conclusion.

### P3 does not have the advertised real-zero Fourier output

Let F_b^-(z)=integral exp(izx)w_b^-(x)dx. The identity

    [sin(a0*x)/(a0*x)]^2
      =1/(4*a0^2) integral_(-2*a0)^(2*a0)
                      (2*a0-|t|)exp(itx)dt

and the Gaussian integral show F_b^-(z)>0 for EVERY real z. Moreover
F_b^- is an even entire function of order at most two, with
|F_b^-(z)|<=sqrt(pi/b)exp((Im z)^2/(4b)).
If it had no zeros anywhere, Hadamard's zero-free finite-order
factorization would give F_b^-(z)=C exp(Az^2), C>0.
Evenness removes the linear term, reality makes A real, and decay along
the real axis forces A<0. Fourier uniqueness would then make w_b^- a
strictly positive Gaussian. This contradicts its zeros at x=k*sqrt(pi),
k a nonzero integer. Both densities are continuous, so almost-everywhere
uniqueness suffices for the contradiction.

Therefore F_b^- has a nonreal zero and no real zeros, for EVERY b>0.
This is an exact analytic counterexample to applying the minus-sign
recipe without additional restrictions even to this valid PF input.
It is a DIFFERENT Fourier transform, not xi or an original-V witness.
No numerical zero coordinate or challenge to the correctly stated
Newman theorem is claimed.

### P4 has real-zero Fourier output, proved directly

For a finite m write

    w_(b,m)^+(x)=exp(-b*x^2)
                  product_(n=1)^m(1+x^2/(pi*n^2))^2.

Its Fourier transform is

    F_(b,m)^+(z)=
       product_(n=1)^m[1-(pi*n^2)^(-1)partial_z^2]^2
                      sqrt(pi/b)exp(-z^2/(4b)).        (P5)

Each factor 1-c*partial_z^2, c>0, splits into
(1-sqrt(c)*partial_z)(1+sqrt(c)*partial_z).
For a real-rooted polynomial P, P+dP' is real-rooted for real d:
away from the real roots, Im(P'/P)=-Im(z)sum_j |z-r_j|^(-2)
cannot be zero, whereas a nonreal zero of P+dP' would make P'/P
real. Constants are immediate. Therefore these operators preserve
the Laguerre--Polya class by locally uniform polynomial approximation
and locally uniform convergence of derivatives. The Gaussian in P5
belongs to that class, for example by the approximants
(1-z^2/(4*b*k))^k. Hence each F_(b,m)^+ has only real zeros.

The product for sinh implies 0<w_(b,m)^+<=w_b^+ on R.
For |z|<=R, exp(R*|x|)w_b^+(x) is integrable. Dominated convergence
therefore gives locally uniform convergence of F_(b,m)^+ to F_b^+.
The limit is not identically zero because F_b^+(0)>0. By the definition
of the Laguerre--Polya class (or Hurwitz off R), F_b^+ also has only real
zeros. This proof uses the actual complete square-rate product, not a
finite source declared exact and not a generic statement from source B.

Reflection of the PF input r interchanges the two characteristic
substitutions. Thus sign/orientation is a genuine structural input.

### Neither output equals the target source

P3 has real zeros as a density whereas q is strictly positive.
For P4, the exact large-|x| comparison is

    log w_b^+(x)
      =-b*x^2+2sqrt(pi)|x|-2log|x|-log(4*pi)+o(1),
    log q(x)
      =-pi*exp(2|x|)+(9/2)|x|+O(1).                   (P6)

The second formula uses the full theta tail and evenness. Consequently
no mass normalization and no fixed b>0 identify P4 with q. In particular
its real-zero Fourier theorem cannot be applied to F=xi/xi(1/2).
No identity of its energies with original V has been produced.
Additive PF and the fixed square rates work in P5. P4 does not implement
the fixed logarithmic transformation r -> q; evenness survives, but
equality with the original reciprocal source is false by P6. Its inverse
logarithmic pullback can satisfy the same weighted reciprocal identity,
as in Q5 of the forced-quotient report; that does not make it our r.

## 5. Decision, controls and stopping condition

| Mechanism | Paid application | Missing or false original-source transfer |
|---|---|---|
| Positive Berwald--Borell defect measure | P1-P2 for the complete rho, all tau>=0 | Controls a different defect; accepted rho_epsilon control excludes automatic VAR/Pick |
| PF reciprocal at -ix^2 | Exact P3 from actual r | Nonreal Fourier zeros for every b>0; no generic real-zero implication |
| PF reciprocal at +ix^2 | P4-P5, all b>0 and all product factors | Different source with incompatible tail P6, not original xi |
| Laguerre integer-value preserver | Published theorem has the right downstream strength | Its input condition on actual H is still OPEN |

This bounded search supplies a worked compensation and a worked
real-zero brother, with explicit failure of the naive map back.
It supplies no new sufficient source property for original V.
Do not dispatch another full Pick task, inverse realization request,
compact-interval scan or derivative hierarchy from these results.

A continuation on P1 would first need an exact identity for the actual
two-density logarithmic-variance defect, with a sign mechanism that
excludes rho_epsilon; another positive moment measure is insufficient.
A continuation on P4 would first need an independently proved
source-preserving operation taking its real-zero kernel to exact q;
equality is already false, and arbitrary positive mixing does not
preserve the needed class. These are stopping conditions, not newly
accepted proof tasks or claims that such operations exist.

## 6. Search and source accountability

The saved brief's second-return section preceded three registered shelf
queries. All returned INCOMPLETE because semantic-index freshness
validation failed. The local Schoenberg PDF and previous matrix/Sheffer
and reciprocity controls were read; they do not supply the new transfer.
The already recorded mgrep authentication failure was not retried.
Three bounded Consensus dictionaries and one adaptive primary-source
lookup found A-C. Consensus records for Pickrell and Craven--Csordas were
fetched; a geometric log-concavity search lead was fetched and excluded.
Only the primary PDF bytes, read theorem/proof locators and direct
arguments above support the mathematical claims.

Prior source papers are not relabeled new results: Schoenberg's
characterization uses the reciprocal Laplace transform, not our Mellin
transform; the multiplicative matrix route requires false PF infinity
of Phi; Sheffer's polynomial factor leaves xi's zeros unchanged.
No novelty or exhaustive-search claim is made.
No theta quadrature, numerical root scan, Lean run, canonical dispatch,
new agent, source-sign counter reset, phase change or RH claim occurred.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; exploratory PAPER only.

## 7. Exact project pins

- REPORT_2026-09-17_PICKVAR_INTAKE.md:
  e0ea0c275b5157f6425935440f9a3b70a896a886be29ad0e607ba9ab8649ffb6.
- REPORT_2026-09-17_DIRECT_PICK_BRIDGE.md:
  f015fc2df3d0a5c1ab86937b2c077495fb104331d50a4153c34bfd8c4184d97d.
- REPORT_2026-09-17_GLOBAL_PICK_MECHANISM_HUNT.md:
  db1e3b3be3ca08df4e24657b63f5cb62c3fc9219ae9162b581478adc56744c27.
- REPORT_2026-09-17_KPS_FORCED_QUOTIENT.md:
  8b5cc3a609cf73ef977ee67c6036e5cfaef6294d496f9b0f78f6ba847558f1ff.
- REPORT_2026-09-17_SOURCE_SIBLINGS_AUDIT.md and the source PF intake:
  hashes recorded in the paired review/publication manifest after full
  local reads. No scope expansion of their accepted statements.

## Independent acceptance

Verdict: ACCEPT_POSITIVE_DEFECT_AND_TWO_PF_TRANSFORM_CONTROLS_ONLY.
Final candidate SHA256: 422917099f3a5d3a0e71045b93e9efd621fc885a4307bef7243b81bfe88c49c4.
Complete review SHA256: 48ef0fda7b5318e98d92f59cbd493215048de8dc85368f88ef83b1806745156e.
Parent check SHA256: a06031fe39c35c696baf94382105185817f32b911591e517274445a792d4de5c.
The paired certificate binds exact project and primary-source bytes and embeds
both checks. The reviewer corrected one scope sentence: the new even source
can have the same weighted reciprocity after inverse logarithmic pullback;
what fails is equality with the fixed original source. Final P1-P6 formulas
needed no correction. Root read the complete final review before publication.
No original-V sign result, actual Pick theorem, RH conclusion, canonical
admission or source-sign counter reset follows.
