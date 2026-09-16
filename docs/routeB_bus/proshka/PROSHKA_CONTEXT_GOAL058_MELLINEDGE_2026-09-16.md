# Proshka Context Pack
Generated: 2026-09-16T13:14:26
Repo: /Users/emalam/.codex/visualizations/2026/09/12/01a092ef-bf89-7693-aca8-42c3b691138a/gamma-reciprocity-worktree
Branch: codex_mac/gamma-reciprocity-20260914
HEAD: 42e5bf9a
Commits: last 2

## Working tree
```text
## codex_mac/gamma-reciprocity-20260914
```

## Commit list (oneline)
```text
42e5bf9a [CODEX_MAC][gamma-reciprocity] Verify raw finite-source Mellin formula and sufficient cofinal edge target
631b15d5 [CODEX_MAC][gamma-reciprocity] Audit nonlocal transfer without replacing the physical V flux
```

## Range diff summary
```text
.../REPORT_2026-09-16_MELLIN_EDGE_PREFLIGHT.md     | 174 ++++++++++++
 ...PORT_2026-09-16_NONLOCAL_TRANSMUTATION_AUDIT.md | 191 ++++++++++++++
 .../MELLIN_EDGE_PREFLIGHT_20260916.json            |  29 ++
 .../NONLOCAL_TRANSMUTATION_AUDIT_20260916.json     | 292 +++++++++++++++++++++
 4 files changed, 686 insertions(+)
```

## Per-commit stats
```text
42e5bf9a [CODEX_MAC][gamma-reciprocity] Verify raw finite-source Mellin formula and sufficient cofinal edge target
 .../REPORT_2026-09-16_MELLIN_EDGE_PREFLIGHT.md     | 174 +++++++++++++++++++++
 .../MELLIN_EDGE_PREFLIGHT_20260916.json            |  29 ++++
 2 files changed, 203 insertions(+)
```
```text
631b15d5 [CODEX_MAC][gamma-reciprocity] Audit nonlocal transfer without replacing the physical V flux
 ...PORT_2026-09-16_NONLOCAL_TRANSMUTATION_AUDIT.md | 191 ++++++++++++++
 .../NONLOCAL_TRANSMUTATION_AUDIT_20260916.json     | 292 +++++++++++++++++++++
 2 files changed, 483 insertions(+)
```

## File snapshots

### docs/Codex/REPORT_2026-09-16_MELLIN_EDGE_PREFLIGHT.md
```text
# Raw finite-source Mellin edge: exact arithmetic formula and a closed sufficient target

STATUS: INDEPENDENTLY_ACCEPTED_PAPER_PREFLIGHT_AND_SUFFICIENT_TARGET_ONLY.
Base: 631b15d506fde2188394e51f825d170d5923cf46.
This is a bounded source-route preflight. No RH/full-V sign, canonical
admission, or positivity of a finite-source replacement V is asserted.

## E0. Why this object, and what is preserved

The renewal, coupled-flux and nonlocal-transmutation tests did not supply
the sign of the physical V. Instead of appending levels to those fields,
return to the exact finite gamma source BEFORE geometric or arithmetic
reciprocal assembly. No positive energy is substituted for V.

Pinned inputs:
- REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md G1-G4, SHA256
  7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621;
- REPORT_2026-09-15_ARITHMETIC_RECIPROCITY.md AR1-AR4, SHA256
  b128c925d794693fdbc5b1e8257e5587060c92d60770a650f2f8d26ee6838f53;
- REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, SHA256
  1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.

Let r_N be the density of T_N=sum_(n=1)^N Gamma(2,1)/(pi*n^2), and

    M_N(s)=int_0^infinity t^(s-1)r_N(t)dt, Re s>1-2N.

Here N counts finitely many rates. It is NOT the alpha indexing convolution
powers of the full source in COUPLEDFLUX. Its limit r is the original full
source, whose Mellin transform is M(s)=2 xi(2s-2). The target critical line
is Re s=5/4. Finite r_N does not obey the full reciprocal identity.

## E1. Limit on the needed half-plane and exact sufficiency

The pinned full-source estimates give r_N(t)<=C exp(-pi*t/2) uniformly in N,
and uniform real convergence r_N->r. For a compact subset of Re s>0, choose
0<a<=Re s<=b. On (0,1), C*t^(a-1) dominates t^(s-1)r_N(t); on [1,infinity),
C*t^(b-1)exp(-pi*t/2) does. The same bounds with powers of |log t| justify
holomorphy and derivatives. Dominated convergence, applied to the supremum
over the compact parameter set, gives

    M_N -> M=2 xi(2s-2) locally uniformly on Re s>0.       (E1)

One sufficient property is

    there exists an unbounded sequence N_j such that
    M_(N_j)(s)!=0 for every Re s>5/4.                    (EDGE)

If EDGE holds, Hurwitz on that half-plane makes M zero-free there: its
identically-zero alternative is excluded by M(2)=E T=pi/3>0. Hence xi has
no zero with Re z>1/2. Its exact functional equation xi(z)=xi(1-z) excludes
Re z<1/2 as well. This proves RH, and the independently established full-sign
transfer then gives the ORIGINAL V>=0 for all finite complex rows in I.
There is no additional unproved energy, boundary or density transfer after
EDGE. This is sufficiency only; RH need not force EDGE for this sequence.

This differs from a real-zero theorem for the geometric G_N or arithmetic
H_N Fourier assemblies. Their known failures/limitations do not prove or
disprove EDGE. No finite M_N is called self-reciprocal or entire.

## E2. The complete finite formula, using the exact square spacing

Write lambda_n=pi*n^2, H_j=sum_(k=1)^j 1/k, H_0=0, and

    w_(N,n)=(N!)^4 / ((N-n)!^2 (N+n)!^2),
    d_(N,n)=n[H_(N+n)-H_(N-n)]-3/2.

Then, for Re s>0,

    M_N(s)=4 pi^(1-s) Gamma(s) D_N(s),
    D_N(s)=sum_(n=1)^N w_(N,n) n^(2-2s) [s+d_(N,n)].      (E2)

Proof: the rational Laplace transform has only double poles:

    product_(j=1)^N (lambda_j/(q+lambda_j))^2
      =sum_(n=1)^N [A_n/(q+lambda_n)^2+B_n/(q+lambda_n)],
    A_n=lambda_n^2 product_(j!=n)(lambda_j/(lambda_j-lambda_n))^2,
    B_n=-2 A_n sum_(j!=n)1/(lambda_j-lambda_n).

Factoring j^2-n^2=(j-n)(j+n) gives A_n=4pi^2 n^4 w_(N,n). Also

    sum_(j!=n)1/(j^2-n^2)
       =[H_(N-n)-H_(N+n)]/(2n)+3/(4n^2),
    lambda_n B_n/A_n=d_(N,n).

Inverse Laplace transformation gives
r_N(t)=sum (A_n*t+B_n)exp(-lambda_n*t). Each term is Mellin integrable for
Re s>0, so ordinary gamma integration proves E2. This does not require
integrating individually divergent terms closer to Re s=1-2N.

Because Gamma(s) has no zeros or poles on Re s>0, the zeros relevant to EDGE
are exactly those of the explicit entire exponential polynomial D_N. The
standard Gamma fact is recorded in DLMF 5.2(i), paragraph after equation
5.2.1: https://dlmf.nist.gov/5.2 . No zero theorem for D_N is imported.

The coefficients expose exact square-rate arithmetic, not just min lambda=pi.
In particular

    w_(N,n)=[binom(2N,N-n)/binom(2N,N)]^2.                 (E3)

Positive binomial weights do not by themselves give complex non-cancellation.
No independent property of primes is yet spent by E2-E3; the multiplicative
frequencies log n remain explicit rather than being replaced by absolute values.

## E3. Two complete base cases, not a cofinal theorem

For N=1, M_1(s)=pi^(1-s)Gamma(s+1), so M_1 is zero-free on Re s>0.
For N=2, the exact expression is

    M_2(s)=(16pi/27)Gamma(s)pi^(-s)
             [(3s-2)+4^(-s)(3s/4+2)].                  (E4)

This agrees with the pinned literal finite two-rate density G12. For Re s>=1,
write

    (3s/4+2)/(3s-2)=1/4+(5/6)/(s-2/3).

Its modulus is at most 1/4+(5/6)/(1/3)=11/4; |4^(-s)|<=1/4. Therefore

    |4^(-s)(3s/4+2)/(3s-2)|<=11/16<1.                 (E5)

The bracket in E4 cannot vanish, and neither can its other factors.
Thus the entire closed half-plane Re s>=1 is zero-free for this N=2 Mellin
transform. This proves the two starting cases of the stronger all-N EDGE
proposal. It does NOT bound zeros for N>=3 or supply the unbounded sequence.

## E4. A naive extension is already excluded

Do not ask to repeat E5 using an N-independent absolute first-term budget.
For a fixed real sigma in (5/4,3/2], consider the ratio of the sum of moduli
of n>=2 terms in D_N(s) to the modulus of its n=1 term at s=sigma+i*tau.
As |tau| tends to infinity with N fixed, its limit is

    B_N(sigma)=sum_(n=2)^N [w_(N,n)/w_(N,1)] n^(2-2sigma). (E6)

For every fixed n, w_(N,n)/w_(N,1)->1 as N->infinity; this follows directly
from the finite factorial ratio. Every term is nonnegative. Given any finite
L, liminf_N B_N(sigma)>=sum_(n=2)^L n^(2-2sigma), and the latter tends to
infinity as L->infinity when sigma<=3/2. Consequently

    B_N(sigma)->infinity for each sigma in (5/4,3/2].     (E7)

So even inside the requested right half-plane, the first term cannot dominate
the sum of absolute values for all sufficiently large N and all imaginary
heights. E7 is a failure of THAT estimate, not a zero of D_N, M_N, xi or V.
It demonstrates precisely why the complex relations among the remaining
arithmetic frequencies must be retained by a successful proof of EDGE.

## Decision for the next bounded joint attempt

The next candidate is raw finite-source Mellin stability (EDGE), with its
explicit E2 coefficient structure. The two base cases and the complete
downstream implication have been paid. The uniform stability mechanism
remains UNVERIFIED; neither total positivity of r_N nor E3 establishes it.

The global task is to exploit the coupled binomial/harmonic coefficients and
the multiplicative log-n frequencies to prove a cofinal right-edge bound, or
derive a scoped analytical obstruction for this family. A finite off-edge
zero rejects all-N stability only. To reject EDGE itself one must show such
zeros for every sufficiently large N (or otherwise exclude every unbounded
zero-free subsequence). No claim about RH follows from rejecting EDGE.

Do not launch a serial N=3,4,5 campaign, use a finite grid as evidence for
EDGE, reopen geometric all-plane real zeros, or erase the harmonic term.
If the available argument only restates EDGE, record INCOMPLETE with the
missing source-level operation and stop that attempt. This is one concrete
candidate to test with Proshka, not a claim that RH is now easier or proved.

AUTOPSY: dropped=COUPLING; note=The absolute first-pole domination budget diverges with N inside the required half-plane; a cofinal Mellin argument must keep arithmetic phase interactions.

## Independent acceptance

Candidate SHA256: `0fb0395993bb99f4c89893bed156b3cab5e7a340c52c46a7c64c0f8513907e40`.
Read-only reviewer `/root/sibling5_check`; review SHA256: `3676cedda926ab7a06454a34553cd1a7f4b4ff6bf75906991819da30493b2c9b`.
Parent independently derived and checked E1-E7. Only the status and this receipt were added after review. EDGE remains unproved. No canonical admission or Lean verification.
```

### docs/Codex/REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md
```text
# Geometric reciprocity of finite gamma densities

STATUS: REVIEWED_ANALYTIC_PARTIAL_BRIDGE_AND_ACTIVE_EXPLORATORY_BRIEF.
SOURCE_BASE: e6b9b3d30fe378ed51311129e2afe02716ba2ba5.
OWNER: renewed instruction to pursue a purely analytical proof of RH.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; no canonical edge or admission.
The convergence bridge and the first member are proved below; preservation
of real zeros for an unbounded sequence of members is OPEN. No RH proof is
claimed. No numerical zero search or finite-grid sign check is used.

## G0. Why this is the next object

The actual additive gamma density has total positivity of every order. Its
raw and weight-conjugated convolution maps failed the earlier target, and
the centered Hardy map has a nonzero full-theta defect. Preserve those
exclusions. Here we test a different operation: restore the exact reciprocal
symmetry of finite gamma densities by a geometric mean before Fourier
transformation. This provides a family converging to the actual source,
with a familiar positive-energy proof for its first member.

Source inputs: the reviewed THETA_TN_INFINITY intake, its raw source
PROSHKA_THETA_TOTAL_POSITIVITY_SOURCE_TEST_2026-09-12.md (SHA256
654c1a3bfe0a4eb570adce71c6d62d7b97deca110765de79a7776dd6878b5bd7),
and the exact Fourier normalization in FULL_SIGN_TRANSFER_AUDIT and
ALL_ODD_TO_RH. The neighboring receipt pins the used files and sources.

Search dictionaries: (i) reciprocal geometric symmetrization and Hellinger
midpoint; (ii) gamma convolutions, total positivity and Lee-Yang preservation;
(iii) imaginary-order Bessel zeros, positive Sturm-Liouville energy and
Hurwitz limits. The proposed preservation property is UNVERIFIED, not a
consequence attributed to a publication. Existing convolution/Hardy failures
are not repeated. A bounded source search must find a matching preservation
theorem with its hypotheses or retain the precise missing implication.

## G1. Exact finite family

Let all Gamma_(2,n) be independent gamma variables with shape 2 and rate 1.
For N>=1 let r_N be the density of

    T_N=sum_(n=1)^N Gamma_(2,n)/(pi n^2).

Each r_N is positive and smooth on t>0, integrates to one, and its additive
translation kernel is totally nonnegative of all orders. The accepted
infinite density r satisfies

    ||r_N-r||_infinity <= 2pi/N,
    r(1/t)=t^(5/2) r(t),
    Phi(x)=exp(5x/2)r(exp(2x)).                            (G1)

Define, always using the positive real square root,

    G_N(x)=sqrt(r_N(exp(2x))r_N(exp(-2x))),
    Z_N=integral_R G_N(x)dx,
    M_N(z)=Z_N^(-1) integral_R G_N(x)exp(-izx)dx.          (G2)

G_N is real, positive and even. It is not asserted to be entire as a function
of x. Its Fourier transform M_N will be entire as a function of z.
There is no ambiguity of a complex square-root branch in definition (G2).

Probability interpretation: p_N(x)=2exp(2x)r_N(exp(2x)) is the density of
(log T_N)/2, and sqrt(p_N(x)p_N(-x))=2G_N(x). Thus G_N/Z_N is the normalized
geometric, or Hellinger, midpoint between that density and its reflection.
This identification supplies no general real-zero preservation theorem.

## G2. Uniform full-tail bound

Let q(t)=pi^2 t exp(-pi t) for t>=0, extended by zero to t<0; r_1=q.
For alpha=pi/2,

    q(t) <= (2pi/e)exp(-alpha t),   t in R.               (G3)

For negative t the left side is zero. Put
S_N=sum_(n=2)^N Gamma_(2,n)/(pi n^2), with S_1=0. Convolution and (G3) give

    r_N(t)=E q(t-S_N)
       <= (2pi/e)exp(-alpha t) E exp(alpha S_N).

For n>=2, v=1/(2n^2)<=1/8 and -2log(1-v)<=2v/(1-v)<=8/(7n^2).
Since sum_(n=2)^infinity n^(-2)<=integral_1^infinity s^(-2)ds=1,

    E exp(alpha S_N)
       =product_(n=2)^N (1-1/(2n^2))^(-2) <= exp(8/7).

Consequently, uniformly in N and t>0,

    r_N(t)<=C exp(-pi t/2),  C=2pi exp(1/7),
    G_N(x)<=C exp[-(pi/2)cosh(2x)].                      (G4)

This is an exact bound for every finite full density, independent of N.
It controls all exponential moments and all polynomial-weighted exponential
moments of G_N. No tail is replaced by the first mode of the theta series.

## G3. Analytic convergence to the actual xi function

Equation (G1) and reciprocal symmetry imply pointwise

    G_N(x) -> sqrt(r(exp(2x))r(exp(-2x)))=Phi(x).          (G5)

The suprema of r_N and r are at most sup q=pi/e. The inequality
|sqrt(u)-sqrt(v)|<=sqrt(|u-v|), u,v>=0, even gives

    sup_(x in R) |G_N(x)-Phi(x)| <= 2pi/sqrt(eN).         (G6)

For any R>=0, (G4) also dominates exp(R|x|)|G_N(x)-Phi(x)| by an
integrable function independent of N. Dominated convergence therefore gives

    integral_R exp(R|x|)|G_N(x)-Phi(x)|dx -> 0.           (G7)

The same bound with |x|^k justifies all z-derivatives. Thus every M_N is
entire, Z_N -> Z=integral_R Phi(x)dx=xi(1/2)>0, and

    M_N(z) -> xi(1/2-iz)/xi(1/2)                         (G8)

locally uniformly on the whole complex plane. In particular the exact
infinite theta source is reached; no unproved approximation at zeros is used.
This probability normalization does not replace the physical f=Phi/||Phi||_2.

Conditional consequence: if there is an unbounded sequence of integers N_j
such that each M_(N_j) has no zeros outside the real axis, then RH follows.
Indeed the normalized nonzero limit in (G8) is zero-free on each open upper
and lower half-plane by Hurwitz's theorem. The alternative of an identically
zero limit there is excluded by analyticity and its value 1 at z=0.
This is a sufficient criterion; a converse for this sequence is not claimed.

## G4. The first member: a complete analytic real-zero proof

For N=1,

    G_1(x)=pi^2 exp[-pi cosh(2x)],
    M_1(z)=K_(iz/2)(pi)/K_0(pi).                         (G9)

Here K_nu is the modified Bessel function. Equation (G9) follows directly
from DLMF 10.32.9 after u=2x. The integral itself makes M_1 entire and even.

Suppose K_(iz/2)(pi)=0 and set psi(t)=K_(iz/2)(pi exp(t)), t>=0.
DLMF 10.25.1 gives

    -psi''(t)+pi^2 exp(2t)psi(t)=(z^2/4)psi(t),
    psi(0)=0.                                          (G10)

The large-argument K asymptotic in DLMF 10.40.2 and its derivative version
10.40.4 show that psi, psi' decay sufficiently fast for the following
integration by parts, and psi is not identically zero. Multiplying by
conjugate(psi), integrating on [0,infinity), and retaining both endpoints,

    integral_0^infinity [|psi'|^2+pi^2 exp(2t)|psi|^2]dt
          =(z^2/4) integral_0^infinity |psi|^2 dt.        (G11)

The boundary product is zero at 0 by the assumed zero and at infinity by
the K asymptotic. Both integrals are finite and strictly positive. Hence
z^2 is a positive real number, which forces z to be real. This proves
real-zero location for the whole first transform; it assumes no RH result.
It is the standard positive Sturm-Liouville energy mechanism, already used
in REPORT_2026-09-13_BESSEL_MULTIPLIER_OBSTRUCTION.md. No novelty about
imaginary-order Bessel functions is claimed. The new proposed bridge here
is the exact finite gamma family and its full-source analytic limit.

Primary equation sources:
https://dlmf.nist.gov/10.32.E9
https://dlmf.nist.gov/10.25.E1
https://dlmf.nist.gov/10.40.E2
https://dlmf.nist.gov/10.40.E4

## G5. The first genuinely unpaid step is explicit

One more gamma summand gives exactly

    r_2(t)=(16pi/27)[(3pi t-2)exp(-pi t)
                              +(3pi t+2)exp(-4pi t)].    (G12)

This follows by convolving pi^2 t exp(-pi t) with
(4pi)^2 t exp(-4pi t), or by partial fractions of their Laplace product.
Definition (G2) fixes G_2 and M_2 completely from this formula.
No argument above proves the zeros of M_2 real, much less those of all M_N.

The proposed strong lemma is: every M_N in (G2) has only real zeros.
A preservation theorem for r_N -> r_N*q_(pi(N+1)^2), where q_lambda(t)
=lambda^2 t exp(-lambda t), would prove that lemma from (G11).
It must refer to the geometric reciprocal operation in (G2), not merely to
additive convolution or ordinary Fourier convolution. The weaker cofinal
property in G3 would also suffice and might follow by a different invariant.

A proved failure at one N would exclude the strong all-N assertion only;
it would not refute RH or automatically exclude every cofinal subsequence.
A proof just for N=2 would be a finite advance, not proof of the criterion.

## G6. Why the previously excluded positive-multiplier class is not reused

For each fixed N, finite exponential convolution gives

    r_N(t) ~ c_N t^(2N-1) as t->0+,
    r_N(t) ~ d_N t exp(-pi t) as t->infinity,

with c_N=product_(n=1)^N (pi n^2)^2/(2N-1)!>0 and
d_N=pi^2 E exp(pi S_N)>0. For the second asymptotic, write r_N(t)
=pi^2 exp(-pi t) E[(t-S_N)exp(pi S_N)1_(S_N<=t)] and divide by t;
dominated convergence is allowed since the finite S_N has rates >=4pi.
The first asymptotic follows by convolving 2N exponential densities at zero.

It follows, as x->+infinity, that

    G_N(x)/exp[-pi cosh(2x)] ~ C_N exp[-2(N-1)x], C_N>0. (G13)

For N>=2 this ratio tends to zero. Thus G_N cannot be C exp[-b cosh(2x)]
times L(x)=exp(beta x^2)product_j(1+alpha_j x^2), with C,b>0,
beta,alpha_j>=0 and sum alpha_j<infinity, the specific class previously
excluded as a theta approximation. Indeed 0<=log L(x)<=O(x^2) forces b=pi
by the leading cosh tail. For b=pi, L(x)>=1 contradicts (G13).
The new finite family does not claim preservation of that old mechanism.

## G7. Control, scope and next analytic task

Even positive weights with the earlier squared-coordinate concavity need
not have real-zero transforms: the reviewed f0=exp(-u^2)-exp(-2u^2)/4
has a negative full four-node row. Its Fourier transform is explicitly
sqrt(pi)exp(-z^2/8)[exp(-z^2/8)-1/(4sqrt(2))], which has nonreal zeros.
It does not belong to our gamma-density
class: its inverse density t^(-5/4)f0(log(t)/2) has a logarithm whose second
derivative is [3/4+(log t)/2+o(1)]/t^2>0 for large t, violating TN2.
This control forbids using evenness and concavity alone. It does not prove
that additive total positivity survives the particular operation (G2).

Return point: additive gamma convolution, reciprocal geometric averaging,
and preservation of Fourier zeros under their composition. The exact
first-member proof and the limit are supplied; a positive operator or a
preserver for the composition is not supplied. Search that mechanism and
check its actual hypotheses before any new proof claim.

The current analytical research continues at (G12) and the all-N/cofinal
preservation problem. No numerical campaign, canonical transaction or RH
closure is authorized by this conditional bridge. Independent review and
the GitHub request will keep this open status explicit.
```

### docs/Codex/REPORT_2026-09-15_ARITHMETIC_RECIPROCITY.md
```text
# Arithmetic reciprocal assembly of the exact finite gamma source

STATUS: ANALYTIC_PAPER; exact-payload independent review is recorded in the adjacent SPACE_SIBLING_HUNT_20260915 certificate.
This is one bounded source reconstruction test in response to the user's suggestion, not a claimed real-zero theorem or a replacement of the CRITICALSTRIP request.

## Pinned source facts

Use r_N and r of REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md G1-G4, SHA256 7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621.
T_N=sum_(n<=N) Gamma(2,1)/(pi n^2), r_N=density(T_N), lambda_n=pi n^2.
We have uniform real convergence r_N -> r, r(1/t)=t^(5/2)r(t), Phi(x)=e^(5x/2)r(e^(2x)), and r_N(t)<=C exp(-pi t/2), C=2pi exp(1/7), all N,t>0. The complete-source Fourier transform is xi(1/2-iz).

## AR1: explicit reconstruction and exact limiting source

Set a_N(x)=e^(5x/2)r_N(e^(2x)) and

H_N(x)=(a_N(x)+a_N(-x))/2.

Every H_N is real, strictly positive and even on the real axis. Pointwise, a_N(x)->Phi(x) and a_N(-x)->Phi(-x)=Phi(x), hence H_N->Phi. This is a different approximating family from G_N=sqrt(r_N(e^(2x))r_N(e^(-2x))), with the SAME exact limiting source. It changes the finite assembly, not the limiting xi function.

## AR2: every fixed spectral strip has a common integrable bound eventually

For fixed M>=1, the convolution-simplex formula for the M shape-two gamma densities implies

r_M(t)<=C_M t^(2M-1), t>0,
C_M=product_(n<=M) lambda_n^2 / Gamma(2M).

Indeed the density integrand is product lambda_n^2 u_n times exp(-sum lambda_n u_n)<=product lambda_n^2 u_n, and its convolution integral equals t^(2M-1)/Gamma(2M). Extend r_M by zero to negative arguments. For N>=M the positive independent remainder gives
r_N(t)=E r_M(t-(T_N-T_M))<=C_M t^(2M-1), t>0.

For x>=0 and N>=M it follows that

0<H_N(x)<=1/2 [C e^(5x/2) exp(-pi e^(2x)/2)+C_M e^(-(4M+1/2)x)].    (AR2)

Evenness supplies the same bound in |x|. Given B>=0 choose M with B<4M+1/2. Then e^(B|x|) times the right side is integrable, independent of N>=M. Pointwise convergence, the same bound for Phi, and dominated convergence prove

integral_R e^(B|x|)|H_N(x)-Phi(x)|dx ->0.                           (AR3)

Put Z_N^A=integral_R H_N>0 and Z=integral_R Phi>0. Then Z_N^A->Z and the normalized transforms

A_N(z)=(Z_N^A)^(-1) integral_R H_N(x)e^(-izx)dx

are holomorphic on |Im z|<4N+1/2 and converge uniformly on every fixed closed horizontal strip |Im z|<=B once N is large enough. The limit is xi(1/2-iz)/xi(1/2). Derivatives under the integral follow on smaller substrips using polynomial-weight domination. The finite transforms are not claimed entire.

## AR3: the old source branch mechanism is absent, with an explicit price

For every fixed N the partial-fraction formula expresses r_N(t) as a finite sum (d_n t+e_n)e^(-lambda_n t). This gives an entire continuation in t and hence a_N and H_N are entire in x. There is no complex square root in this definition and therefore no square-root branch divisor of the kind used in GAMMA_COFINAL_BRANCH_OBSTRUCTION B1-B8.

The price is a finite Fourier strip for each fixed N. The simplex formula also gives r_N(t)~C_N t^(2N-1) as t decreases to zero, so

H_N(x)~(C_N/2)e^(-(4N+1/2)|x|) as |x|->infinity.

Therefore the ordinary defining Fourier integral is absolutely convergent exactly for |Im z|<4N+1/2 and diverges on its boundary. This is an integral-domain claim, not a claim that meromorphic continuation outside the strip is impossible. The strips expand with N, which is sufficient for the usual fixed-compact analytic limit and Rouché arguments. No claim about the zeros inside those strips has been obtained.

## AR4: transform identified without an unknown correction

Define L_N(s)=integral_0^infinity t^(s-1)r_N(t)dt, initially Re s>1-2N. Then substitution t=e^(2x) gives exactly

A_N(z)=[L_N(5/4-iz/2)+L_N(5/4+iz/2)]/[2 L_N(5/4)].                 (AR4)

For N=1 this specializes to
L_1(s)=pi^(1-s)Gamma(s+1),
A_1(z)=[pi^(iz/2)Gamma(9/4-iz/2)+pi^(-iz/2)Gamma(9/4+iz/2)]/[2Gamma(9/4)].
This is an exact formula, not a real-zero claim. Positive evenness of H_N, and the cancellation of source branch defects, do not prove real zeros or V_(H_N)>=0.

## Decision

This family is a source-faithful rebuilt approximation with a proved eventual-strip limit, not a solved sign mechanism. It removes one specifically identified obstruction (finite source square-root branches) and exposes its exact analytic cost (finite but expanding Fourier strips). Any continuation must prove a sufficient zero-exclusion property inside the critical strip from these explicit Mellin transforms; that step remains open. Do not apply the former geometric-family no-go to this different family, and do not treat its absence as a positive theorem. Publication-time update: CRITICALSTRIP has now been answered and independently reviewed; REPORT_2026-09-15_CRITICALSTRIP_INTAKE.md compares its geometric-family curvature mechanism with this arithmetic family. No duplicate request was sent.
```

### docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md
```text
# Full theta sign to Weil sign — direct audit of the terminal transfer

STATUS: PAPER_AUDIT_PENDING_INDEPENDENT_CHECK.
SOURCE_BASE: 7653a3503d20be4dba91a333ff96e5eea30c738c.
PX_RH_CLAIM: NOT_MADE. No Lean certification or canonical admission.

This audits the previously inherited SLACK arrow. The result is an equivalence
between two all-test signs, not a proof of either sign. It reduces a named
audit dependency of GOAL_MAT and does not reset the open ODD2 sign counter.
The argument below needs no radical theorem, central/far allocation,
finite-field analogy, or bounded inverse multiplier on a function space.

## 1. Statement and exact objects

Let theta(t)=sum_(n>=1) exp(-pi n^2 t), t>0, and define

    r(t)=4t theta''(t)+6 theta'(t),
    Phi(x)=exp(5x/2) r(exp(2x)), A=||Phi||_2, f=Phi/A.

Thus Phi is exactly the full source

    sum_(n>=1) (4pi^2 n^4 exp(9x/2)-6pi n^2 exp(5x/2))
                   exp(-pi n^2 exp(2x)).

Define alpha(t)=exp(-t/2)/(1-exp(-2t)), c_A=gamma+log(8pi)+pi/2,
w_n=Lambda(n)/sqrt(n), and M_+/-(g)=integral g(x)exp(+/-x/2)dx.
For complex compact smooth g, let

    D(g)=integral_0^infinity alpha(t)||g(.+t)-g||_2^2 dt,
    Q(g)=D(g)-c_A||g||_2^2 +2Re(M_+(g)conj(M_-(g)))
         -2 sum_(n>=2) w_n Re integral conj(g(x))g(x+log n)dx.

Set

    V(x,y)=integral_0^infinity (x+y+2t) f(x+t)f(y+t)dt.

**Theorem T.** The following assertions are equivalent:

1. Q(g)>=0 for every g in C_c^infinity(R;C).
2. For every N>=1, real x_1,...,x_N, and c in C^N,
   sum conj(c_i)V(x_i,x_j)c_j>=0.

Together with the classical Weil criterion, these are equivalent to classical
RH. The theorem is an exact transfer; assertion2 is still unproved. The ODD2
subspace is necessary for assertion2 and is not substituted for it.

## 2. Source normalization and decay without a critical-strip premise

Use the Jacobi identity

    1+2theta(t)=t^(-1/2)(1+2theta(1/t)).

It is DLMF20.7.32 at z=0, tau=it with the positive square root. Differentiating
twice gives `r(1/t)=t^(5/2)r(t)`, hence Phi(-x)=Phi(x).
For t>=1 every term of r is positive: 2pi n^2 t-3>0. Reciprocity then gives
r>0 everywhere. The series and its fixed derivatives converge locally
uniformly for t>0. For x>=0, each fixed x-derivative of Phi is bounded by a
finite sum of terms C n^M t^M exp(-pi n^2 t), t=exp(2x)>=1.
The sum of n^M exp(-pi(n^2-1)) is finite; absorbing t^M into exp(pi t/2)
gives a bound C_k exp(-(pi/2)exp(2x)). Evenness gives the same bound at the
other end. This proves every exponential-weighted fixed derivative moment
needed below, and 0<A<infinity.

For Re(s)>1 put a=s/2. Two integrations by parts give

    integral_0^infinity t^a r(t)dt
      =(4a(a+1)-6a) integral_0^infinity t^(a-1)theta(t)dt
      =s(s-1) pi^(-s/2) Gamma(s/2) zeta(s)=2xi(s).

All boundary terms vanish: near zero theta=O(t^-1/2), theta'=O(t^-3/2)
by Jacobi; the factors in both integration-by-parts boundaries are
O(t^((Re(s)-1)/2)). At infinity the series decays exponentially. Absolute
Fubini for the last equality follows from Re(s)>1 and the gamma integral.
With the Fourier convention F(z)=integral f(x)exp(-izx)dx, t=exp(2x) gives

    F(z)=(1/(2A)) integral t^(1/4-iz/2)r(t)dt
         =xi(1/2-iz)/A

whenever Re(1/2-iz)>1, in particular in an open neighborhood of Im(z)=2.
F and its derivatives exist everywhere by the proved envelopes, but no
critical-strip zero location is used in this calculation.

## 3. The control space and the unchanged full pairing

Let X be the space of measurable functions with

    ||g||_X^2=||exp(|x|)g||_2^2+D(g)<infinity.

Its inner product is the weighted L2 inner product plus the L2 pairing of
translation differences with measure alpha(t)dt dx. It is complete: the map
g -> (exp(|x|)g, (g(x+t)-g(x))) has a closed graph in the product L2 space,
as follows by distributional testing (or subsequences and Fubini) from a
convergent sequence in both coordinates.

Polarization of Q defines an antilinear-first Hermitian B on X. Write
W_g=||exp(|x|)g||_2. Then

    |integral conj(g(x))k(x+t)dx| <= exp(-|t|)W_g W_k,
    |M_+/-(g)| <= sqrt(4/3)W_g,
    |B(g,k)| <= (|c_A|+14)||g||_X||k||_X.                 (T1)

The first bound uses |x|+|x+t|>=|t| and Cauchy-Schwarz. The pole norm follows
from integral exp(+/-x-2|x|)dx=4/3. The two prime correlations cost at most
2 sum_(n>=2)(log n)n^-3/2 W_gW_k <10 W_gW_k by the integral test; the D
pairing is bounded by sqrt(D(g)D(k)). Thus every prime is present with an
absolutely convergent bound on X. For original compact tests the sum is in
fact finite. The constant14 is a harmless explicit upper bound.

Translation tau_b g(x)=g(x-b) has norm at most exp(|b|) on X and leaves B
unchanged. Its D-part is translation invariant, as are the correlations;
the two pole moments acquire opposite factors exp(+/-b/2).
Translations are strongly continuous: in the D-part apply ordinary L2
translation continuity to each difference g(.+t)-g, dominated by its
fourfold squared norm. Weighted L2 translation continuity follows by
compact L2 approximation and the displayed locally uniform operator bound.
This argument precedes and does not presuppose smooth density.

For a smooth cutoff chi_R tending to1, with bounded derivative O(1/R),
expand the translated difference of (chi_R-1)g. One term is bounded by
4|g(x+t)-g(x)|^2 and converges to0; the commutator term is bounded by
min(C^2t^2,4)|g(x)|^2 and converges to0. Both are integrable against
alpha(t)dt dx. Weighted L2 convergence is dominated convergence. Thus
chi_R g -> g in X. Mollifying each compactly supported chi_R g converges in
X by strong translation continuity and Minkowski's inequality. Consequently
C_c^infinity(R;C) is dense in X. This licenses later discontinuous atoms;
it is not an assumption that X=L2 or that derivatives must lie in L2.

## 4. Exact atoms with both poles and the grouped archimedean constant

Fix h=2 (the formulas below also hold for fixed h>1), sigma=h+1/2, and set

    q_(h,u)(x)=1_[0,infinity)(x) exp(-hx+iux), u in R,
    R_h(u)=1/(sigma-iu)+1/(sigma-1-iu)-log(pi)/2
           +psi((sigma-iu)/2)/2
           -sum_(n>=2) Lambda(n)n^(-sigma+iu),
    K_h(u,v)=(conj(R_h(u))+R_h(v))/(2h+i(u-v)).

The q atoms belong to X. Direct integration gives

    ||exp(|x|)q_(h,u)||_2^2=1/(2(h-1)),
    D(q_(h,u))=(1/h) integral alpha(t)(1-exp(-ht)cos(ut))dt,
    ||q_(2,u)||_X <= sqrt(6)*sqrt(1+u^2).                 (T2)

Indeed 1-exp(-ht)cos(ut)<=ht+u^2t^2/2,
integral t alpha(t)dt<5, integral t^2 alpha(t)dt<18, by the positive
geometric expansion and decreasing-tail integral tests.

Let d=2h+i(u-v). The atom mixed L2 product is1/d. The two translated
correlations are exp(-(h-iv)t)/d and exp(-(h+iu)t)/d. The D numerator is
integral alpha(t)(2-exp(-(h-iv)t)-exp(-(h+iu)t))dt.
Each pole product has denominators a,b with a+b=d. Multiplying it by d
therefore gives1/a+1/b. This produces all four reciprocals in
conj(R_h(u))+R_h(v); neither pole is discarded.

For the archimedean terms use DLMF5.9.16:

    psi(z)+gamma=integral_0^1 (1-t^(z-1))/(1-t)dt, Re(z)>0.

At z=1/4 substitute t=v^4. The resulting rational integral gives
psi(1/4)=-gamma-3log2-pi/2. Subtracting this value in the same convergent
integral yields, for Re(s)>0,

    (psi(s/2)-psi(1/4))/2
       =integral_0^infinity (exp(-t/2)-exp(-st))/(1-exp(-2t))dt.

Apply this to s=sigma-iv and its u conjugate. Their sum, minus log(pi),
is exactly the D numerator minus c_A. The small-t differences remain
grouped throughout. The prime part equals the original two translated
correlations term by term, with absolute convergence. Hence

    B(q_(h,u),q_(h,v))=K_h(u,v).                           (T3)

This is a pairing for a form whose sign is unknown; no positive Gram
representation was assumed.

## 5. Every original complex test is reached in the correct norm

For an original g choose b so g_b=tau_b g is supported strictly in (0,infinity).
Let G(u)=F_(g_b)(u+ih), the Fourier transform of exp(hx)g_b(x). It is Schwartz.
By T2 the Bochner integral

    g_b=(1/(2pi)) integral G(u)q_(h,u)du                   (T4)

converges absolutely in X. Evaluation in weighted L2 and ordinary Fourier
inversion identify this integral with g_b: on x>0 multiply the inversion
of exp(hx)g_b by exp(-hx); both sides vanish for x<0. The endpoint is null.

T1–T3 now give, with absolute convergence,

    Q(g)=(1/(4pi^2)) integral integral conj(G(u))K_h(u,v)G(v)du dv. (T5)

For completeness, this is also a finite-coefficient limit. Tail truncation
at |u|<=M has X error at most
sqrt(6)/(2pi) integral_(|u|>M)|G(u)|sqrt(1+u^2)du.
The map u->q_(2,u) is continuously differentiable in X with derivative ixq:
xq has weighted norm squared1/4, and its weak x-derivative has L2 norm
squared(4+u^2)/32. Its value is0 at the jump point, so no delta derivative is
present. The bound on integral t^2 alpha gives

    ||xq_(2,u)||_X^2 <= 5/2+9u^2/16.

Dominated difference quotients give the asserted X derivative. Riemann
sums on [-M,M] therefore converge in X; for mesh delta their extra error is

    (2M delta)/(2pi) sup_(|u|<=M)
       (|G'(u)|sqrt(6(1+u^2))+|G(u)|sqrt(5/2+9u^2/16)).

If the total X error is e, T1 bounds the quadratic error by
(|c_A|+14)e(2||g_b||_X+e). All estimates are for each fixed arbitrary complex
test and retain every source term. A test-dependent support shift is valid
because B is translation invariant; no uniform inverse bound is asserted.
It follows that Q is nonnegative on all original tests iff every finite K_h
matrix is PSD: use T4 for one direction, and X-density to approximate any
finite sum of q atoms for the other.

## 6. The only division is on finite coefficient spaces

The Euler product on Re(s)>1 is absolutely convergent with a nonzero value;
its logarithmic derivative is -sum Lambda(n)n^-s. Gamma has no zeros there
(and its reciprocal entire product proves this classical fact). Thus the
nonzero F_h(u)=F(u+ih)=xi(sigma-iu)/A obeys

    R_h(u)F_h(u)=iF'(u+ih)=integral x f(x)exp(hx-iux)dx.   (T6)

Differentiation is justified by section2. For every finite node set the
diagonal matrix diag(F_h(u_i)) is invertible. Therefore the finite K_h
matrices are PSD iff the finite matrices of

    W_h(u,v)=conj(F_h(u))K_h(u,v)F_h(v)

are PSD. The inverse is allowed to depend on the chosen finite nodes. There
is no map sending a general Fourier coefficient G to G/F_h in this proof.

## 7. The exact physical kernel and its sign transfer

Expand T6 in the numerator of W_h and insert

    1/(2h+i(u-v))=integral_0^infinity exp(-2ht-iut+ivt)dt.

Absolute Fubini is bounded by

    (1/(2h)) integral integral |X+Y| |f(X)f(Y)|exp(h(X+Y))dX dY <infinity.

Substitute X=x+t, Y=y+t. The result is

    H_h(x,y)=exp(h(x+y))V(x,y),
    W_h(u,v)=integral integral H_h(x,y)exp(iux-ivy)dx dy.  (T7)

The same estimate proves H_h in L1(R^2); compact-local tail domination
proves its continuity. These two facts suffice for all following limits;
a global L2 realization of Q or an inverse function-space multiplier is
unnecessary.

Finite H_h matrices are PSD iff its quadratic form is nonnegative on all
complex compact smooth spatial tests. Forward: compact rectangle Riemann
sums. Reverse: smooth approximate point masses at a finite set, combining
coefficients if nodes repeat; continuity controls the limit.

A nonnegative H_h form gives finite W_h PSD: use spatial tests
chi_R(x)sum_j c_j exp(-iu_j x). Dominated convergence with H_h in L1 gives
exactly sum conj(c_i)W_h(u_i,u_j)c_j.
Conversely, finite W_h PSD gives nonnegative frequency integrals against
compact smooth coefficients by Riemann sums. W_h is bounded by ||H_h||_1,
so L1-tail truncation extends this to Schwartz coefficients. For a compact
smooth spatial a choose

    eta(v)=(1/(2pi)) integral a(y)exp(ivy)dy.

It is Schwartz and a(y)=integral eta(v)exp(-ivy)dv. T7 and absolute Fubini
identify its nonnegative frequency form with integral conj(a(x))H_h(x,y)a(y).
No sign assumption was used to justify a limit.
Finally, finite H_h matrices are congruent to finite V matrices by the
positive diagonal exp(hx_i). Combining sections5–7 proves Theorem T.

## 8. Connection to the published final consumer

For C_g(t)=integral g(x)conj(g(x-t))dx, C_g(-t)=conj(C_g(t)). Substituting this
into Suzuki's explicit formula(3.3) gives precisely Q above. The constant
conversion uses

    2 integral_0^infinity (1-exp(-t/2))alpha(t)dt=log2+pi/2.

The pole integrals give 2Re(M_+ conj(M_-)); both prime-power sums give the
stated real correlation sum. The introduction states the classical Weil
criterion for all complex compact smooth tests. Thus its scope matches T1,
not only the odd or even sector. The published explicit formula and Weil
criterion remain named primary theorem dependencies; their entire classical
proofs are not reconstructed here.

## 9. Evidence, delta, and limits

Full SLACK producer49446bytes/657LF was read and rehashed:
1d658eb3d6d828d3bc651967087dabf8e2f9774d179b02c7607f25c7ffe54588.
Current full SLACK check37796bytes/467LF was rehashed:
14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc.
Its earlier acceptance is context; the transfer proof is rederived above.

Primary formulas read directly on 2026-09-12:
- [Jacobi modular identity, DLMF20.7.32](https://dlmf.nist.gov/20.7#E32).
- [Digamma integral, DLMF5.9.16](https://dlmf.nist.gov/5.9#E16).
- [Euler product, DLMF25.2.11](https://dlmf.nist.gov/25.2#E11).
- [Suzuki, introduction and(3.3)](https://arxiv.org/html/2301.00421).

Classical background used: Fourier inversion/uniqueness, elementary Lebesgue
convergence theorems, completeness of L2, the gamma integral and nonvanishing
of Gamma on Re(s)>0. No RH-equivalent spectral theorem is hidden among these.

Before this audit GOAL_MAT inherited V=>Q only by the SLACK receipt. This note
rederives the source normalization, complete arithmetic pairing, all-test X
limit, finite congruence, and spatial/frequency transfer in one proof.
This is an audit completion at PAPER scope if independently accepted.
It supplies no new proof of V>=0, no result of the pending ODD2 request, and
no reset of the same-obstacle mathematical counter. No new Proshka send.

## 10. Independent audit acceptance

This receipt supersedes the initial pending status, preserving the preceding
14110bytes unchanged. ACCEPTED_PAPER_TRANSFER_AUDIT for Theorem T and its
source normalization/domain proof. The sole read-only checker
`/root/sibling5_check` checked exact SHA256
`8c0ff365de0838fb922a05c21ada76665935998bd6ecae5117f3fd7910703b60`
and returned ACCEPT: Mellin IBP coefficient/boundaries, noncircular X density,
atom jumps, both poles and digamma constant, X limits, finite nonzero
congruence, exact Fourier signs, H in L1 and both PSD transfer directions.
It retained the named DLMF/Suzuki formulas as published dependencies; their
historical full proofs were not reconstructed. Parent also checked the
Jacobi differentiation and all constant factors directly.

The parent additionally read [DLMF5.2(i)](https://dlmf.nist.gov/5.2#i),
including Euler's gamma integral and the explicit nonvanishing statement,
on 2026-09-12. This makes the gamma background source locator explicit; it
does not add a zero-location premise for zeta.

No sign premise was proved. No ODD2 result or no-progress counter reset is
claimed. The active all-test RH goal remains incomplete.
```

### docs/Codex/REPORT_2026-09-16_NONLOCAL_TRANSMUTATION_AUDIT.md
```text
# Nonlocal transmutation: equation transfer and the unpaid physical flux

STATUS: INDEPENDENTLY_ACCEPTED_PAPER_TRANSFER_AND_SCOPED_METRIC_OBSTRUCTION_ONLY.
Exploratory search: INCOMPLETE_NO_CONSUMABLE_TARGET in the canonical formal
workflow; one source-verified partial analogue, no formal admission.
Own analytic result proposed below: explicit intertwining and endpoint/norm
audit only. No full-V sign, RH claim, or exclusion of all nonlocal methods.

## Frozen input and consumer

Base: bd30dcdf922dc3a8de4b42a2f20e1c01d4455ec5.
Brief: docs/Codex/BRIEF_2026-09-16_COUPLEDFLUX_NONLOCAL_HUNT.md,
SHA256 7546cb16d6e907c109fee3ae49bbd65911ae9bb2f04c1e057b782340db4a6bb5.
COUPLEDFLUX response: 4a4575555554947d3db865819ee74652f9ec7639,
docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_COUPLEDFLUX_2026-09-16.md,
SHA256 258fe6d40ab6b92b4c7a5645fb75ad5dadecd7848a7567e18c0553a65b28b0c4.
Its accepted intake has SHA256
79b56d8acadf8efcb4502cebd1d989d746c72b57aa0e57ed2f68c1a9ff0de45e.

All shifts lie in I=(-log(2)/2,0), coefficients are arbitrary finite complex
rows. The full source and its convolution powers are unchanged. Write
Y_k=(Y_(2,k),Y_(4,k)), A0=D^2-1/4 and

    Ltilde=A0 I2-6 exp(-2X) N, N=[[0,1],[0,0]], X>=0.
    Ltilde Y_k=F_k,
    F_(2,k)=2pi(D-5/2)R_(2,k),
    F_(4,k)=20 exp(-2X)Y_(6,k)+8pi(D-9/2)R_(4,k).

Definitions of Y and R are CF15-CF16 of the pinned response. The only consumer
is E_c(k)=int exp(-(4+4k)X)|Y_(2,k)|^2 dX and
A^2 V[c]=-E_c'(0)/2>=0. Neither forcing component may be omitted.

## Bounded search receipt

The three registered shelf queries were run once with --defer-external:
`Sylvester nonlocal symmetrizer`, `Volterra transmutation boundary`, and
`boundary storage physical flux`. All exited 2, status INCOMPLETE, because
q3_docs semantic-index freshness validation failed. This is not a no-hits
or absence result. No index repair or repeat was performed.

Inspected local hits: Goal058PolarizedVolterra.lean is a finite Fourier
convolution identity, not the required differential/domain transfer.
D0Mode4HermitianNegativeCountStability.lean:780-838 concerns Sylvester
inertia, not the commutator equation. The returned R6BoundaryCellBridge.lean
path was unavailable. Other metadata-only hits remain unverified.

One external metadata batch used the three dictionaries in the brief.
It returned candidates but status INCOMPLETE: an 8-second batch limit
exhausted two arXiv queries; one Crossref query returned HTTP 429. There was
no retry. Exactly one selected primary article body was fetched.

Log SHA256 values, in query order:
08333eb7b0dc73db071695bdaed2b916dac3537d4c4ed7289c09e57202a84329;
51c0cfffc85739b6e5c93c7c827b3795656cdc35fa173e07350c2255ed3c1094;
d2a2316098e5d4eb06b99d32216e41c5300dfcca7d60922b5274c986116cc4c1.
Metadata JSON SHA256:
542fe54a0dfdcca570c3bfb119fc7ded73d136daa0e27c0d0e02385b1448d02a.

## One published partial analogue

Kravchenko, Morelos, Torba, arXiv:1412.5237v1, *Liouville transformation,
analytic approximation of transmutation operators and solution of spectral
problems*: https://arxiv.org/html/1412.5237v1 . Fetched HTML SHA256
b292563edfd58432859c43f1c835610e65c2414188e0237f69f8c009cf41634d.
Read scope: section 2 hypotheses, section 4 Theorems 4.1-4.3 and proof of
4.3, and initial-data discussion through Theorem 4.5. The article attributes
4.1-4.2 to its reference [11]; we verify their printed statements, not a
separate independent proof of those cited results.

Short quote, Theorem 4.2: “The inverse operator \(\mathbf{T}^{-1}\) exists and has the form”. Locator for the substantive
statement: Theorem 4.1, equation (4.1), B T w=T A w for C^2[-b,b]; Theorem
4.2 gives the inverse integral formula. Theorem 4.3, equation (4.3), composes
this with the Liouville map.

Mapping: its scalar A=-D^2 corresponds to -A0 after a constant shift; its
scalar potential and symmetric finite interval do not match our two-channel
nilpotent coupling on a half-line. Its nonvanishing normalized solution
and Goursat kernel conditions are not supplied by our block. No theorem
there identifies our weighted norm, k-flux, forcing, or endpoint domain.
The finite Jordan control is outside those differential hypotheses.
Verdict: PARTIAL_ANALOGUE for integral intertwining, not a positivity supplier.

## N1. Direct half-line intertwiner

We now test the brief's own explicit candidate, independently of that article:

    Kq(X)=(3/2)exp(-X) int_X^infinity exp(-t)q(t)dt,
    T=[[I,K],[0,I]], T^{-1}=[[I,-K],[0,I]].

Take C^2 functions whose q, q', q'' decay faster than every exponential;
the actual fixed finite source rows and their needed k derivatives satisfy
this by CF4. Compactly supported smooth half-line functions are also valid.
The differentiations and two integrations by parts below have zero terms
at infinity. Directly,

    (Kq)'=-Kq-(3/2)exp(-2X)q,
    (Kq)''=Kq+(9/2)exp(-2X)q-(3/2)exp(-2X)q',
    K(q'')=Kq-(3/2)exp(-2X)(q'+q).

Therefore [A0,K]q=6exp(-2X)q and

    Ltilde T Z=T diag(A0,A0) Z.                         (N1)

The integral kernel is (3/2)exp(-X-t)1_(t>=X). Its squared L2 norm on the
quadrant is 9/32, so K is bounded on L2(0,infinity), and T and T^{-1} are
bounded there. This does not by itself identify any self-adjoint domain.

For the actual fields set Z_k=T^{-1}Y_k. The exact equations become

    A0 Z_(2,k)=F_(2,k)-K F_(4,k),
    A0 Z_(4,k)=F_(4,k).                                  (N2)

Thus both forcing entries survive; in particular Y6 has not disappeared.
No task for the sign of Y6 is created.

## N2. The endpoint is transformed, not erased

Let J(q)=(3/2)int_0^infinity exp(-t)q(t)dt. Then

    Kq(0)=J(q), (Kq)'(0)=-J(q)-(3/2)q(0),
    Z2(0)=Y2(0)-J(Y4),
    Z2'(0)=Y2'(0)+J(Y4)+(3/2)Y4(0).                       (N3)

For example, a test pair Y with both components smooth and compactly
supported strictly inside (0,infinity) has Z2(0)=-J(Y4), Z2'(0)=J(Y4).
Generally Z2(0) is nonzero. Therefore T^{-1} does not preserve the usual
Dirichlet domain. This example is a domain diagnostic outside the actual
source family, not a negative V witness. A pulled-back closed domain would
need a separate construction and would still not identify the physical flux.

## N3. Exact original energy after the transfer

Put PZ=Z2+KZ4 and w_k(X)=exp(-(4+4k)X). The unchanged energy is exactly

    E_c(k)=int w_k |P Z_k|^2
          =int w_k (|Z2,k|^2+|KZ4,k|^2
                    +2 Re(conj(Z2,k)KZ4,k)).              (N4)

For source rows all derivatives under this integral are justified by CF4
and the tail-integral bound defining K. Since T is k-independent,

    A^2 V[c]=2 int X w_0 |P Z_0|^2
             -Re int w_0 conj(P Z_0) P (partial_k Z_k|0). (N5)

No X integration by parts was used in (N4)-(N5), so no endpoint term has
been dropped. If N2 is used to integrate by parts, the traces N3 must be
retained. Formula N5 is an exact rewrite; it is not a new lower bound.

There is a decisive control against replacing N4 by the positive auxiliary
energy ||Z_k||_L2^2. For an actual single shift x in I, the gauge definition
gives Y_(alpha,k)=exp(-2kx)Y_(alpha,0), hence Z_k=exp(-2kx)Z_0. T is invertible
and the source is nonzero, so N=||Z_0||^2>0. Consequently

    -1/2 d/dk ||Z_k||^2 at k=0 = 2x N < 0,                (N6)

whereas V(x,x)=2 int_|x|^infinity u f(u)^2 du>0.
Thus this positive nonlocal metric's unweighted k-flux is demonstrably
not the physical V. The same conclusion holds for any fixed strictly
positive quadratic form on these gauge fields with finite nonzero value.
It says nothing against the physical k-dependent weight in N4.

## What this pass changes

The explicit nonlocal equation transfer works and the simple Jordan
obstruction to local multiplication metrics does not prohibit it. But the
candidate does not furnish the missing sign: boundary traces, forcing, and
the mixed observation P remain explicit. The tempting unweighted positive
metric replacement fails on an actual permitted one-shift row.

K depends on the coupling coefficient 6 and the half-line differentiation,
not on the arithmetic spacing pi*n^2. It exposes no newly proved property
of the full source that bounds the last term in N5. We stop this particular
diagonalization test rather than introducing another auxiliary energy or
more convolution levels. Other nonlocal constructions and full V remain open.

Next bounded research question, before any new request: return to the full
source's exact arithmetic structure and require a candidate to preserve the
physical observation from the outset. A new route must name the particular
source property it spends and one sufficient full-form inequality. N5 alone
does not qualify as that supplier. No Proshka request is pending or dispatched
by this report; canonical production HOLD remains unchanged.

## Independent acceptance

Candidate SHA256: `3161cd840a02ab5109d6de7d065460e04aa90a5042562fa5471413db0e9d4710`.
Read-only reviewer `/root/sibling5_check`, review SHA256: `e3db7624b53bc547e1da3c8cc6bf9317ac66a239066fed91da89f9865d8b103f`.
The parent independently checked N1-N6 and the exact primary theorem mapping.
Only the status and this receipt were added after review.
No canonical mathematical admission or Lean verification is claimed.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The positive unweighted nonlocal metric has the wrong k-flux on an actual one-shift source row; retain the physical weighted observation instead.
```
