# One-prime transition: literal weight and repetition test

2026-10-08. Owner-authorized bounded test following the prime-property screen.
Baseline 4247b9ad, N=m, L=log m. PAPER identities and scoped tests independently checked.
RH/SP OPEN. No Pro send, no change of the pending Q6 consumer.

## Outcome and exact consumer

The Duffin-Schaeffer matching rule is a translation-orbit construction, not
multiplication of the integer argument by a prime. Its first-mass identity
has been checked against a weighted observable below. It yields an explicit
covariance defect, not automatic preservation of the CCM pairing. Naive
multiplication is tested separately and fails even for a legal projected
positive test matrix. Neither finding refutes a construction using the actual
adaptive spectral weight; no such complete construction is claimed here.

Use a prime ell and moment order r to keep the two roles distinct. For fixed
even r>=4, m>=2^(r-1), x=m^(1/(r-1)), d=2m+1, b=ones/sqrt(d), Pi=I-bb*, retain

    S=Pi K_m Pi=U-V, W=S_-^(r-1), M=Tr S_-^r,
    V=integral_(log x,L] Pi Q(s) Pi dnu(s),
    dnu=sum_(n>=2) Lambda(n)/sqrt(n) delta_log(n)
         -exp(s/2)ds+exp(-s/2)ds.

Q has the literal diagonal 2(1-s/L)cos(2pi j s/L), off-diagonal
[sin(2pi k s/L)-sin(2pi j s/L)]/[pi(j-k)], and norm<=2.
Let rho_W(s)=Tr(W Pi Q(s) Pi), g_W(n)=rho_W(log n)/sqrt(n).
The unproved target is Tr(WV)<=theta M+C_r m^A L^B_r, theta<1,
with A finite independent of arbitrarily large fixed r. All prime powers,
both continuous terms, all modes, and both cutoffs stay in the consumer.
Definitions: PROSHKA_VERDICT_FULL_CCM_HIGHER_MOMENTS_Q05.md (1)-(2),
CCM_ONE_SIDED_LONG_MOMENT_TEST.md (1),(6).

## Source checked, not a certification of the external manuscript

OpenAI corpus pin adc7f1241b42e322a6451854ab7e4b4c146bf78a,
The-weak-inhomogeneous-Duffin-Schaeffer-conjecture-September-25-2026,
build/sections/tables.tex, lines 216-276 (definitions also 47-145).
SHA256 35fed37cec711b80e2d7b4c325fb74f6866e06c09860928ac4350b8b36c77468,
verified against the local original /tmp/openai-math/preprints/.
URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-weak-inhomogeneous-Duffin-Schaeffer-conjecture-September-25-2026/build/sections/tables.tex
Quote: "the total first mass per unit length is preserved by every sparse update."

The source has positive labelled lists, a mask probability law, equivariant
pre-link weights and matching, and a translation core containing ell^nu.
Success means numerator divisible by ell. Translation by 1/ell^nu traverses
all ell residues; its success indicator Z has orbit mean 1/ell. After
residual scaling, a matched amount a has before-prime masses a/ell and
(1-1/ell)a, and after-prime masses a Z and a(1-Z), in units of the after-mask
law. This calculation applies for nu=1 and nu>=2 AFTER the specified
residual factor (1-1/ell)^[nu>=2] is included. It is not a law about random
primes. Positive lists, core equivariance, and the source's quantitative
alignment/partition inputs have no established full CCM map.

## 1. Exact weighted-observable identity

At a single matched pair of retained locations, insert real observables
h_+,h_- without changing the source update. Then

    before = a[h_+/ell+(1-1/ell)h_-],
    after  = a[Z h_++(1-Z)h_-],
    after-before = a(Z-1/ell)(h_+-h_-).                 (T1)

This is a pointwise algebraic identity, including varying orbit observables
and matched amounts when evaluated at the same orbit point. On any finite
translation orbit with mean Z=1/ell, put F_t=a_t(h_+,t-h_-,t). Then

    average(after-before)=[average(F | Z=1)-average F]/ell. (T2)

On an ell-point orbit with one success this reduces to
(F_success-average F)/ell. The full translation orbit at ell^nu may have
ell^nu points; only the success fraction 1/ell is used, including nu>=2.

Consequently the absolute average defect is at most osc(F)/ell, where
osc(F)=max F-min F. If F is constant on the orbit, it vanishes exactly.
Constancy of total mass uses h_+=h_-=1; it says nothing by itself about g_W.
Equivariance of the external construction cannot be asserted for the inserted
CCM observable without proving that additional map. Unpaired portions,
mask laws, births, deletions and cutoffs require their own explicit returns;
T1 is the matched part, not a full-source transport formula.

T2 identifies the needed structural input: successful residues must not
systematically select a larger matched observable difference. Arbitrary
weights can violate it: F_t=Z_t gives defect (1-1/ell)/ell. This is a negative
control for an unrestricted observable claim, NOT a model of the actual W.

## 2. Literal multiplication check, distinct from the source transition

For n>=2 and a prime ell,

    Lambda(ell n)=Lambda(n) if n is a positive power of ell,
    Lambda(ell n)=0 otherwise.

Thus multiplying a power of a different prime creates a zero Mangoldt
coefficient. Multiplication does not even preserve the atomic support.
On the surviving ell-chain, with s=k log ell,

    a_k=log(ell)/ell^(k/2), a_(k+1)=ell^(-1/2)a_k,
    a_(k+1)rho_W(s+log ell)-ell^(-1/2)a_k rho_W(s)
       =ell^(-1/2)a_k[rho_W(s+log ell)-rho_W(s)].       (T3)

The scalar geometric factor is exact. Dropping the bracket is not exact.
For an analytic finite witness choose m=16, r=4, ell=2, and
v=(e_0-e_2)/sqrt(2), W0=vv*. Then Pi v=v and

    rho_W0(s)=(1-s/L)[1+cos(4pi s/L)]+sin(4pi s/L)/(2pi),
    rho_W0(log 4)=1, rho_W0(log 8)=0.                  (T4)

Both 4 and 8 lie in the actual long interval (16^(1/3),16]. Their full
weighted contributions are log(2)/2 and zero. No constant scalar multiplier
ell^(-1/2) transports this observable. W0 is a permissible PSD probe on the
actual full carrier, NOT the uncomputed actual S_-^3. T4 rejects a universal
PSD-weight transport assertion, not a possible special identity for actual W.

The two continuous densities also transform differently: setting s=t+log ell
in an interval J gives

    integral_J exp(+-s/2)rho(s)ds
      =ell^(+-1/2) integral_(J-log ell) exp(+-t/2)rho(t+log ell)dt.

The translated interval must remain explicit. This does not discard either
continuous term or identify the translated integral with the original one.
The already-paid higher-prime-power block is not the central unknown; this
chain check tests the proposed transition, not a new obstruction to removing
that block with its established correction fee.

## 3. Exact mass preservation need not contract higher moments

The external lemma gives an absolute raw-cell cap and an averaged first mass;
it is not an assertion that every higher moment decreases at each step.
For its matched pair take a constant a>0. The before-list weighted masses
are a/ell and a(1-1/ell), and the after-list masses are (a,0) or (0,a).
Total mass is a in each case, but for any r>1

    sum(after masses)^r = a^r
      > a^r[ell^(-r)+(1-1/ell)^r] = sum(before masses)^r. (T5)

Here each power is taken entry by entry before summing. At ell=2 the factor
is 2^(r-1). This example is consistent with the source cap and mass lemma.
It concerns list masses, NOT spectral moments of K_m. It rules out inferring
higher-moment contraction from that lemma alone. The source's additional
alignment, first-join and partition estimates cannot be skipped; even their
second-moment conclusion would require a further higher-moment CCM return.

## 4. Quantitative entrance for a repaired matching

There is a direct sufficient way to pay T1 without assuming its sign, if a
faithful matching can actually be constructed. Define

    A_m(n)=Pi Q(log n)Pi/sqrt(n), 1<=n<=m,
    g_W(n)=Tr(W A_m(n)).

The inherited discrete Hilbert matrix H_jk=1/(j-k), H_jj=0 has norm<=pi
(Q05, section 3.3). With Dsin=diag(sin(omega_j s)),

    Q(s)=2(1-s/L)diag(cos(omega_j s))+[H,Dsin]/pi,
    ||Q'(s)||<=D_m:=(2+8pi m)/L.

The diagonal derivative costs 2/L+2 omega_max and the commutator derivative
at most 2 omega_max, omega_max=2pi m/L. Hence for real u,v>=1 in [1,m],

    ||A_m(u)-A_m(v)||
      <=(1+D_m)|u-v|/min(u,v)^(3/2),                   (T6)
    |g_W(u)-g_W(v)|<=Tr(W)||A_m(u)-A_m(v)||.

This is an actual full-kernel estimate, valid for actual W as well as all
PSD probes. It includes the varying 1/sqrt(n), not only the phase.

For any proposed finite sequence of matched updates on this fixed m and W,
let their same-source observable differences be A_m(n_+)-A_m(n_-), with
matched amounts a>=0. Define the TOTAL matching charge across all steps

    E_m=sum_steps,pairs a |Z-1/ell|
                         ||A_m(n_+)-A_m(n_-)||.        (T7)

Then the total absolute matched-pair defect is <=Tr(W) E_m. All other
returns must be added separately. In particular, if the COMPLETE charge
including those returns can be bounded by C_r L^D_r, then

    Tr(W) E_m <= eta M+C_(r,eta)m L^(r D_r),            (T8)

by Tr(W)<=d^(1/r)M^((r-1)/r) and Young. The polynomial exponent is one,
independent of r. A power-sized charge E_m~m^beta would instead cost
m^(1+beta r). T8 pays a correction; it still needs a useful bound for the
transported endpoint. It is not itself the missing one-sided estimate.

No lists encoding the complete signed CCM source with this total charge
bound have been constructed. T6-T8 are a concrete acceptance test for such
lists, not an assertion that the hypothesis holds.

## Decision and stopping condition

This bounded test is complete once T1-T8 and source mapping are independently
checked. Direct scalar multiplication and mass-only moment contraction are
rejected in precisely the scopes above. The source's genuine translation rule
remains a partial analogue; preservation of actual CCM weights is OPEN.

A useful next construction must give positive matched lists, the exact
signed-source reconstruction (including both integrals), and control of the
TOTAL charge T7 plus all returns, or a signed estimate stronger than that
absolute charge. Same-location pairs make T1 zero, but duplicating each
original atom into two co-located labels is a null repair: after either
selection their summed matrix remains the original one. It preserves weights
and the complete matrix under repetition but supplies no endpoint estimate.
A useful construction must additionally produce an independently bounded
endpoint. Finding pairs with small T7 and a tractable endpoint is the next
entrance, not merely splitting every coefficient into two copies.
Do not iterate a first-mass identity and label it concentration control.
Do not start a new Pro question while Q6 remains pending.

## Independent check

Read-only prime_transition_source verified the external mask transitions for
nu=1 and nu>=2 and the distinction from dilation. Independent nonauthor
prime_transition_audit returned PASS for T1-T8, the exact m=16 witness,
normalizations, derivative constants, Young exponent and restricted rejection
scopes. Its orbit-length clarification has been incorporated in T2: conditional
success average, not an assumed ell-point full orbit. Root verified that
revision and the original source hash. No full arithmetic bound is admitted.
