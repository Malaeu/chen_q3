# Direct Abel test after Q01: continuous piece and remaining discrete error

20 October 2026. Own bounded attempt; original sparse P, N=m, L=log m.
Full signed target OPEN. This is not a new full exponent.

## Exact continuous variation

Use Q01(16): B_(m,d)=C_m(d)+E_(m,d), with

    C_m(x) = (1/x) integral_x^m log(t/x) A_m(t) dt,
    A_m(t) = t^(-1/2) P Q_M(log t) P.

The same definition is valid for real 1<=x<=m, with m and P fixed.
Q01 continuous identities give ||C_m(x)||<=20/sqrt(x), and
integral_1^m A_m=-H_P, ||H_P||<=4. Since ||A_m(t)||<=2/sqrt(t),

    ||integral_x^m A_m(t)dt||
       <=4+integral_1^x 2/sqrt(t)dt =4 sqrt(x).

Leibniz differentiation has no lower boundary term because log(x/x)=0:

    C_m'(x)=-C_m(x)/x-(1/x^2) integral_x^m A_m(t)dt,
    ||C_m'(x)|| <=24 x^(-3/2).

At the upper endpoint C_m(m)=0 exactly. Let M_mu(x)=sum_(d<=x)mu(d).
For integer R<m, finite Stieltjes partial summation preserves all signs:

    sum_(R<d<=m)mu(d)C_m(d)
       = -M_mu(R)C_m(R)-integral_R^m M_mu(t) C_m'(t)dt.

Consequently, IF |M_mu(t)|<=K t^theta for t>=R, its norm is at most

    20 K R^(theta-1/2)+24 K integral_R^m t^(theta-3/2)dt.

For theta>1/2 the displayed upper budget has exponent theta-1/2;
for theta=1/2 it costs at most 20K+24K log(m/R). This is a conditional
budget, not a proof of the Mertens premise. The unconditional trivial
|M_mu(t)|<=t gives <=48 sqrt(m), including the lower endpoint.

## What has not been paid

Q01 only supplies ||E_(m,d)||<=(20+16 Omega)/sqrt(d). Its signed sum
cannot be discarded after controlling C_m. Triangle gives at most
2(20+16 Omega)sqrt(m), so the full direct bound still has a fixed
one-half power (plus the band fee). No derivative or total-variation
bound for E is inherited from its amplitude bound.

Even an additional hypothetical variation estimate
||B_m'(x)||<=K_band x^(-3/2) would only transfer a supplied Mertens
power theta to theta-1/2, with the band fee. A subpower improvement
relative to the trivial t bound cannot by itself make theta approach
one-half. This diagnoses this particular absolute Abel return, not
impossibility of a source-specific one-sided estimate.

## Decision

The full-k continuous cancellation is compatible with Abel summation, but
that alone does not remove the discrete signed error. Next test must use
its actual sawtooth structure or a direct one-sided matrix mechanism;
assuming an RH-strength Mertens bound is not a supplied mechanism.
No Q02 has been sent. No change to CF22, SP, G1/G3 or RH status.

## Second bounded test: exact sawtooth cancellation

For real t>=1 define F0(t)=sum_(d<=t)mu(d)floor(t/d) and
F1(t)=sum_(d<=t)mu(d)floor(t/d)log(t/d). The exact identities are

    F0(t)=1,
    F1(t)=psi(t)+log(t),   psi(t)=sum_(n<=t)Lambda(n).

Proof of the second identity, including integer endpoints: write floor(t/d)
as sum_(k<=t/d)1 and log(t/d)=log(k)+log(t/(dk)). The first double sum
is sum_(n<=t)(mu*log)(n)=psi(t); the second is
sum_(n<=t)log(t/n) sum_(d|n)mu(d)=log(t), since only n=1 survives.
Thus the log weight required by the actual source retains psi with coefficient
one even though the unweighted floor convolution collapses to one.

For beta_d(t)=floor(t/d)-t/d the exact full weighted sum is therefore

    sum_(d<=t)mu(d) beta_d(t)log(t/d)
       =psi(t)+log(t)-t sum_(d<=t)mu(d)/d log(t/d).

Restricting to d>R subtracts the complete short-divisor terms on both sides;
it does not delete psi. Hence applying only the easy unweighted identity to
the actual logarithmic sawtooth error loses an essential term. This exact
calculation supplies no upper sign or new exponent. It identifies the unpaid
arithmetic in this second attempted shortcut; the full matrix route stays open.

Read-only bounded collaborator ccm_next_mechanism confirmed the continuous
variation calculation and lack of a supplied full E variation bound.
Do not cite the existing psi zero-free audit as a proved Mertens input.

Next candidate (UNVERIFIED mechanism, not an estimate): exact Euler error
E_d=-integral_d^m beta_d(t) d[log(t/d)A_m(t)]. Both endpoint products vanish
for this full matrix (log1=0, Q_M(log m)=0). The constant part of beta also
integrates to zero. A sawtooth Fourier expansion produces reciprocal phases
e(h t/d), which do not have the earlier log-phase separability. Whether
actual mu, truncation, low frequencies and full continuous return can be paid
is entirely open; do not use a finite Fourier truncation without its error.
