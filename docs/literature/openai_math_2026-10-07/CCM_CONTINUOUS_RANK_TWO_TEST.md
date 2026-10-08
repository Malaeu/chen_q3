# Actual continuous kernel: rank-two reduction and unpaid return

2026-10-08. Root calculation independently checked by negative_moment_transfer for the kernel and short/long norms. Restricted moment corollary independently PASS in the same bounded audit. Not sent to Pro during Q6. RH/SP OPEN.

Use the original Q05 Fourier synthesis phi_j(t)=L^(-1/2)exp(2pi i j t/L) on [0,L], zero outside, j=-m,...,m, L=log m. For translation T_s f(t)=f(t-s), direct integration gives Q_jk(s)=<phi_j,(T_s+T_s*)phi_k>, including the original diagonal and offdiagonal. Thus G_a=int_0^L exp(as)Q(s)ds is the finite Fourier compression of the kernel exp(a|t-u|), with no additional factor.

The exact kernel identity is

    exp(a|t-u|)=exp(at)exp(-au)+exp(-at)exp(au)-exp(-a|t-u|).

Let v_+,v_- be the Fourier coefficient vectors of exp(±t/2). With omega_j=2pi j/L,

    (v_+)_j=(sqrt(m)-1)/(sqrt(L)(1/2-i omega_j)),
    (v_-)_j=(1-m^(-1/2))/(sqrt(L)(1/2+i omega_j)).

Let H_full be the compressed decaying kernel exp(-|t-u|/2). Then

    G_full=v_+v_-*+v_-v_+*-H_full,    0<=H_full, ||H_full||<=4. (1)

Positivity follows, for example, from the integral Gram representation of exp(-a|t-u|); the norm follows from the Schur row integral<=2/a. Finite Fourier compression contracts the norm.

Let b=ones/sqrt(2m+1), Pi=I-bb*, and P be the orthogonal projection onto span{b,v_+,v_-}^perp. Its removed dimension is at most3, with no Gram inverse assumption. P Pi=P and P G_full P=-P H_full P. This only controls that restricted subspace, not the full matrix.

For Q05's fixed even p>=4, x=m^(1/(p-1)), split at s0=log x. From ||Q(s)||<=2,

    ||G_short||<=4(sqrt(x)-1),
    ||P G_long P||<=4sqrt(x),
    ||H_long||<=4.                                             (2)

Both continuous pieces have been retained with their actual signs. For the literal long prime-power adjacency

    A_long=sum_(x<n<=m) Lambda(n)/sqrt(n) Q(log n),
    V=Pi(A_long-G_long+H_long)Pi,

we get the exact restricted identity

    P V P=P A_long P+E,
    E=P H_full P+P G_short P+P H_long P,
    ||E||<=4sqrt(x)+4<=8sqrt(x).                               (3)

Consequently

    Tr|E|^p<=3*8^p m^(1+p/(2(p-1)))<=3*8^p m^(5/3).            (4)

The previously checked positive-part Schatten norm comparison applies in both directions. A common-exponent positive-moment bound for P V P is thus equivalent to one for P A_long P, up to exponent max(A,5/3). This pays a restricted continuous return, not the actual full long-source moment.

## What remains unpaid

Removing the directions has NOT been justified for the original full spectral consumer. The full growing-continuous rank-two term can have size of order sqrt(m), and the prime couplings to these directions may cancel or reinforce it. The generic full-source second moment does not pay a subpolynomial Schur/low-rank return. Rank at most3 alone does not control the most negative eigenvalue.

Alternatively, one could prove directly that every off-critical zero forces the same negative growth already in the P-restricted source. That requires a separate same-family receiver, not supplied by (1)–(4). The subsequent CCM_RESTRICTED_PRIME_RECEIVER.md provides an independently checked conditional construction; its prime spectral supplier is still OPEN. Naively applying a fullband second derivative to impose Laplace moment constraints costs m² and is not an acceptable return.

The prime adjacency in (3) has deterministic shifts log n and original Fourier projections. It is not the OpenAI residue/divisor graph: no stochastic independence, conditional centering or path contraction has been imported. Estimating its nontrivial positive spectrum is still a source-specific arithmetic problem. No full floor or RH gain is claimed.
