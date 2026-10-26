# Post-Q48: newer additive prime bound does not remove the central debt

Status: source-statement and conditional budget screen, no new CCM theorem.
Source: Maynard--Pandey--Radziwill, Exponential sums over primes,
arXiv:2608.14777v1, Theorem1.1, https://arxiv.org/html/2608.14777v1 .
Archived HTML sources/maynard_pandey_radziwill_2608_14777v1.html,
562819 bytes, SHA256 ad0a88d75e5b367dc64fb225c732df4fb059f7e77873f60690abd0684552019f.
Short exact quote from introduction: "The most important range for our result".
The statement replaces N^(4/5) by N^(19/24) in
 |sum_(n<N) Lambda(n)e(n alpha)| <= N^o(1)(N/sqrt(B)+N^(19/24)),
B=max(q,qN|alpha-a/q|), (a,q)=1, q<=sqrt(N),
|alpha-a/q|<=1/(q sqrt(N)). Source statement checked, full proof not audited.
Lemma3.6 imports reference[1] (Chen--Gupta--Li, arXiv2507.08296), a
preprint; no independent certification of that dependency is claimed.
We test the displayed theorem as an input, not admit a new proof premise.

## Exact source map

Use the inherited Q31/Q32 original-P split, not a new object:
h(x)=x^-1/2 P Q_M(log x)P, K=1+Omega, shell X<=n<=Y=min(4X,m),
b(n)=Lambda(n)-1 and a_j(n)=chi_j(n)h(n). The scalar arithmetic cutoff
is an indicator and the smooth cutoff occurs exactly once on the matrix.
All proper powers, both temporal signs, mixed entries and terminal jets
h(m)=h'(m)=0 remain. Exact shell = integral bhat_j(t) ahat_j(-t) dt.
Inherited ||ahat_j(t)||<=C K² X^-3/2 |t|^-2 away from0.

For the two literal prefixes take N=floor(Y)+1 and N=ceil(X),
so X<=N<=4X+1. For X sufficiently large and |t|<=1/(3sqrt(X)),
q=1,a=0 is valid for BOTH prefixes. This rational numerator a is not
our matrix cutoff a_j. For lambda=X^-gamma, 1/2<gamma<1,
and lambda<=|t|<=1/(3sqrt(X)), we have B~X|t|>=1 and hence
 |bhat_j(t)| <= C X^o(1)[sqrt(X/|t|)+X^(19/24)] + C/|t|.
The last term is the exact subtracted constant-model geometric sum;
it is not silently dropped. Endpoint atoms are included in the prefixes.

## Complete annulus bill

Integrate the product of the two displayed bounds on BOTH signs of t:
 ||annulus_j|| <= C K² { X^o(1)[X^-1 lambda^-3/2
                         +X^-17/24 lambda^-1]
                         +X^-3/2 lambda^-2 }.
For gamma=5/8, the three shell exponents are respectively
 -1/16, -1/12, -1/4.
Replacing19/24 by the older4/5 changes only -1/12 to -3/40;
that term was already smaller than -1/16. The dominant cost is unchanged.
At gamma=2/3 the first exponent reaches0, while the newer second remains
-1/24 (old -1/30). This identifies a limit of THIS displayed norm bill,
not a lower bound for the signed pairing or a universal limit for the paper.

The short remaining strip 1/(3sqrt(X))<|t|<X^-1/2 is paid by the
trivial |bhat_j|<=C X log X: its complete norm is <=C K² log X.
Summing all shells contributes O(K² L²). The inner annulus with gamma5/8
has geometric negative powers; interpret the uniform source o(1) as, for
every fixed delta>0, a bound with C_delta N^delta, and choose delta<1/32,
absorbing its constants for fixed epsilon. With X>=ceil(m^(2epsilon)),
K=1+2pi floor(m^epsilon)/L, both costs are O_epsilon(m^(2epsilon)).
The inherited base/far/constant costs also remain O_epsilon(m^(2epsilon)).
Thus the same central N_star, |t|<X^-5/8 in each shell, is still unpaid:
 A_prime=N_star+E, ||E||<=C_epsilon m^(2epsilon).
This reproduces Q32's paid region; it supplies no new central sign.

For ANY separately established N_star<=sP, the complete consumer return is
 T_>R <=(s+C_epsilon m^(2epsilon)+b_div)P,
 PK_mP >=-(s+C_epsilon m^(2epsilon)+50L+8)P.
No extra divisor fee in direct K, no second continuous fee, no mixed loss.
No such new s was obtained. Retain the inherited fallback, rather than
add this auxiliary bill to it. The goal and actual source remain OPEN.

Negative control: at t=0, the uncentered theorem allows order N because
q1,B1. Subtracting the constant main term in b does not create a signed
error bound by itself. This diagnoses the theorem-to-consumer mismatch;
it is not an assertion that the centered source is actually order N.

Decision: do not upgrade Q32 by merely replacing its4/5 numeral. A useful
next source must control the actual centered central pairing, or bypass
that absolute-product completion with a proved joint comparison. No Q49
sent on this partial substitution. Local shelf search previously INCOMPLETE;
no global novelty or absence claim.

## Independent bounded cross-check

Read-only researcher post_q48_new_additive_bound returned qualified PASS
on prefix hypotheses, geometric constant-model return, all three integrated
powers and the fixed outer strip. No substantive error; inherited matrix
cutoff decay and external theorem as stated remain assumptions. Root checked
four exponent differences in exact rational arithmetic. No actual CCM
numerical evaluation, Lean run, or theorem admission was performed.
