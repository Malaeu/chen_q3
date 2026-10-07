# Exact left-contour branch of the parity-restricted completion

2026-10-07. Uses the checked identity (3) in PARITY_REFLECTION_TEST.md. Goal: expose the new scale before applying a norm. This calculation is for each fixed d and character row; uniform moving-data estimates remain open.

Assume Psi(d) is nonzero. Write b_p=conjugate(alpha(p))^3 Psi(p)^3, extend b multiplicatively to ideals supported on d, and put k=omega(d). Thus |b_p|=1. On Re s<0, inversion of the finite geometric factors gives

product_{p|d}(1-z_p(s)^2)^(-1)
 = (-1)^k b_d^(-2) q_d^(6s-1)
   sum_{rad(r)|d} b_r^(-2) q_r^(6s-1).                       (1)

The series is absolutely convergent on every fixed left line. This uses inverse local ratios, not the divergent original n-series on that line.

Let C_V(Y;Psi') denote the source's unmarked completed sum, equivalently its Mellin integral with entire T(s,Psi'). Let J_left(X;d,Psi) be the integral defining our restricted row on a fixed left line Re s=b<0 after meromorphic continuation by (3). Then

J_left(X;d,Psi)
 = C_d (-1)^k b_d^(-2) q_d^(3/2)
   sum_{rad(r)|d} b_r^(-2) q_r^2 C_V(X q_d^5 q_r^6;Psi').     (2)

Power check: q_d^(-s) q_d^(6s-1) q_r^(6s-1) times X^(s-1/2) becomes
q_d^(3/2) q_r^2 (X q_d^5 q_r^6)^(s-1/2).

For fixed arithmetic data, the source's entire continuation and polynomial strip growth allow the unmodified T integral to move between left and right lines without residues. Rapid Mellin decay allows interchange with the inverse geometric series on a sufficiently far-left line. The resulting C_V(Y;Psi') decreases faster than any inverse power of Y as Y tends to infinity for these fixed data, by choosing an arbitrarily far-left line; hence the r series in (2) converges absolutely. None of these statements bounds its constants uniformly in d or the row.

## What happens to the actual reflected scale

For the actual row character Psi=nu*chi_bullet(m), Psi(d)!=0 forces (d,m)=1; d is good and avoids fixed S. The new twist has exponent 4 at every prime of d. In the source reflection (1758–1804), those primes are necessarily active, and each contributes

B_p(mu)=q_p^(-1/2)(-1+q_p*1_{p|lambda^4 mu}).

Every old active subset therefore has a corresponding new denominator c_new=c_old*d (up to an irrelevant normalizing unit). In each term of (2), the reflected kernel argument becomes

q_mu X q_d^5 q_r^6 / q_c_new^2
 = (q_mu X/q_c_old^2) q_d^3 q_r^6.                          (3)

The explicit kernel-scale gain q_d^3 must be kept together with the outer q_d^(3/2), the Ramanujan factors, and the conductor/row sums. It is not yet a norm saving. In particular the branch with p|mu carries the larger local factor and cannot be discarded.

## Scope of the identity

Equation (2) describes the left-contour part only. The original restricted completion also has the contour corrections from the candidate poles on Re s=1/6. For d=p the residue sum is explicit and absolutely convergent as established in PARITY_REFLECTION_TEST.md. For several primes, retain coincident poles with their multiplicities and define contour corrections through the actual rectangular shifts; no unproved absolute rearrangement of near-colliding residue families is used here.

## A uniform single-term bound by reindexing the row

For the actual row, Psi'=nu*chi_bullet(m*d^4). Thus the fixed finite family nu need not be enlarged: write m'=m*d^4 and apply the source unmarked moment at the new row scale. This is a legitimate possibility not supplied by simply applying the old bound at the old scale.

For fixed d,r with q_d=Z^delta, q_r=Z^rho, original row ball q_m<=C Z^M, powerful-part dyad Z^O, and X=Z^N, the nonzero branch has (m,d)=1. Therefore

M_new=M+4delta, O_new=O+4delta, N_new=N+5delta+6rho.

The m to m' map is injective, so its sparse image can be bounded by the full nonnegative moment sum. On bounded exponent ranges, the source moment gives

sum_m |C_V(X q_d^5 q_r^6; m*d^4,nu)|^2
 << Z^[O/2+2delta+max(M-O,2M-O-N-delta-6rho)+epsilon] M_V^2.

In the balanced squarefree-row case M=N,O=0, this is Z^(M+2delta+epsilon). With the squared outer weights q_d^3 q_r^4 in (2), the single summand costs Z^(M+5delta+4rho+epsilon). This is a uniform single-term bound with an explicit cost, not a saving. Summing it over the infinite r series is not justified: it grows with r. One must retain the reflected kernel's decay, or prove a sharper restricted-row moment, before summing. The contour correction is separate and still unbounded uniformly.

Independent bounded check: mobius_source_audit verified (1)–(3), absolute interchange for fixed data, the row reindex and its three changed exponents. The direct enlarged-row moment above is therefore available with its stated cost; the aggregate remains open.

### Sharper frozen-d count

The proof at 3170–3280 retains d as fixed instead of counting all powerful parts of size Z^(O+4delta). The actual frozen parts are m_pow*d^4, so their count is only O(Z^(O/2)); the active radical exponent is at most O/2+delta, since every new d prime is active once. With H<=M-O and N_new=N+5delta+6rho, the displayed block bound gives, conditional on the source block estimate,

sum_m |C_V(X q_d^5 q_r^6;m*d^4,nu)|^2
 << Z^[O/2+max(M-O,2M-O-N-3delta-6rho)+epsilon] M_V^2.

This sharper bound is an adaptation of the proof, not the lemma's literal statement. In the balanced squarefree case it keeps the moment at Z^(M+epsilon), before the outer q_d^3 q_r^4 squared weight. It does not sum the r tail or control residues. Independent source-block mapping check PASS: unchanged residual width (3180–3189), active-radical contribution, E0/T0 estimate (3238–3254), and fixed-d powerful-part count (3261–3276). The source claims block constants independent of the moving frozen local set at 2997–3000; bounded log-length ranges and all remaining source hypotheses are retained. This checks the adaptation's hypothesis and exponent bookkeeping, not an independent audit of the entire source proof.

No low exponent or RH status changes.
