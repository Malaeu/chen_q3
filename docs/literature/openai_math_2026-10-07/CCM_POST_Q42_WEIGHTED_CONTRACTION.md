# Post-Q42: actual balanced primitive contracts in a different weight

2026-10-26. Own bounded continuation of Q42, original source and P unchanged.
Independent read-only q32_annulus_audit qualified PASS, including weight optimization. This is one attempted transfer, not a source upper.

Use Q42 cofinal U>=64, v=U+1, S=Q_U+|tau_U| and actual G_tilde.
Set h(t)=1-G_tilde(exp(t)) for t>=0. Q42 gives h(t)=0 for t<log(v),
|h(t)|<=1+S, and (1+S)/v<=4/5. Its exact transform is
 Y_tilde(s)/s=integral_0^infinity h(t)exp(-s*t)dt, Re(s)>0.
Indeed Q42(3.6) divided by s equals the integral of 1-G_tilde over [v,infinity).
All original mu and the balancing atom remain in this h; no model substituted.

On L2(0,L) let H_sigma f(t)=integral_0^t exp(-sigma*u)h(u)f(t-u)du.
Young's inequality gives ||H_1||<=integral |h(u)|exp(-u)du
 <=(1+S)/v<=4/5, uniformly in cofinal U and L.
Thus ||(I-H_1)^(-1)||<=5. This is a genuine full-interval auxiliary
contraction, stronger in domain than a small complex disk, but for Y/s.

Return to the original half-line weight sigma=1/2. With
(Df)(t)=exp(-t/2)f(t), exactly D H_(1/2) D^(-1)=H_1.
On the uncompressed physical space ||D||=1, ||D^(-1)||=exp(L/2)=sqrt(m).
Consequently the direct similarity certificate gives
 ||(I-H_(1/2))^(-1)||<=5sqrt(m).
This is an upper allowance, NOT a lower bound or a necessary source price.
D does not preserve the original Fourier/contact subspace; no intermediate
P is inserted. Compression can only be performed after returning the full
physical operator. An identity for a similarity is not a Loewner congruence;
no favorable Hermitian sign is transferred by it.

There is no hidden infinite-tail issue here. H_sigma has causal support
>=log(v), hence H_sigma^K=0 on [0,L] for K=ceil(1/epsilon), v^K>m.
The inverse above is exactly sum_{j=0}^{K-1}H_sigma^j, retaining every
ordered mixed convolution. Nilpotence does not make its norm <=5 in the
original weight; the latter estimate used sigma=1.

Crucial source map: H_sigma is NOT Y_tilde itself. The exact Laplace symbol
of H_sigma is Y_tilde(sigma+z)/(sigma+z). Recovering Y_tilde requires the
causal derivative (d/dt+sigma); in distributional form
 (d/dt+sigma)H_sigma f = Y_sigma f,
where Y_sigma is convolution by the actual Dirichlet coefficient measure
of y_tilde, weighted n^(-sigma). The jump at log(v) and all later jumps
are retained by this distributional derivative, not discarded.
On a smooth input, derivatives commute with full causal convolution after
zero extension, with any endpoint distributions retained. No estimate of
these derivatives by a bounded operator on arbitrary L2 is assumed.

The actual Q42 channel is D_zeta(s)[1-Y_tilde(s)^K], not 1/(1-Y_tilde(s)/s).
Thus the contractive inverse supplies no automatic upper for that channel.
Using the exact finite reconstruction still returns
 A=-kappa H_d+F, F=C0-e_U^K H_d,
with C0 coefficient1. This identifies the concrete impasse before pretending
that a resolvent of a different symbol is the original source.

## Complete decision and budget

Auxiliary half-weight inverse certificate: at most5sqrt(m). No independent
favorable signed F bound obtained. Preserve the better direct source budget
 A<=s_keep P, s_keep<=6sqrt(m)+6m^(1/4),
 T_gtR<=(s_keep+b_div)P, PK_mP>=-(s_keep+50log(m)+8)P.
No additional similarity fee is added to that already available direct bound.
Both times and every complex mixed term are kept by the exact source map.
No RH/zero-free/Mertens premise added; no Lean/Arb/production spectrum.
Rollback before the weighted resolvent: it is an auxiliary contractive object,
not a supplied signed estimate for the full CCM. Local or primitive contraction
alone is not enough; a useful next claim must bound the actual differentiated
full remainder on the original metric. No impossibility claim. No Q43 sent.

## Optimizing this particular weight certificate

For 1/2<=sigma<=1 the same displayed Young majorant is
 q_sigma=(1+S)/(sigma*v^sigma).
Whenever q_sigma<1 it gives the scalar allowance
 B_sigma=m^(sigma-1/2)/(1-q_sigma).
This is specifically the bound using the constant envelope 1+S, not the
actual integral norm and not the true resolvent norm.

An elementary union bound gives Q_U>=U/4: every nonsquarefree integer is
in some d^2-multiple class, d>=2, and
 sum_{d>=2}1/d^2 <=1/4+integral_2^infinity x^(-2)dx=3/4.
Thus q_sigma>=U/(4sigma*v^sigma). The condition q_sigma<1, with sigma<=1,
forces v^sigma>U/4, and hence
 1-sigma<log(4v/U)/log(v)<=log(8)/log(v).
Since log(m)/log(v)<1/epsilon on the original schedule,
 B_sigma>=m^(sigma-1/2)>8^(-1/epsilon)*sqrt(m).
For sigma>=1 the similarity factor alone is >=sqrt(m).
Therefore optimizing sigma within this constant-envelope Young/similarity
certificate cannot produce eta(epsilon)->0. The prefactor may depend on
fixed epsilon; its power in m remains1/2. This lower price belongs ONLY to
this specified certificate; actual signed primitive/correlation estimates
and actual resolvent norms are not bounded below by it.
