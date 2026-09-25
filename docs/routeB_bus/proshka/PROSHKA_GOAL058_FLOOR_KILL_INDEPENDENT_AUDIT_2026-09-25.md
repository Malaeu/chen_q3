# Goal058: audit of the constant complement-floor counterexample

Status: PAPER audit of a theorem-shape counterexample, not a Route B or RH claim.
Request: `REQ-2026-09-25-INDEPENDENT-COMPLEMENT-FLOOR`, SHA-256
`79207d2da49851bc31ff0899f1053aa0571955dac80f2395a11b7d255e6fbb1f`.
Source pin: `6b7f2d981adcb894a3186a6c698e7e0f12b6ffa7` (ancestor of the
audit checkout's `6e2a7cd7befcff9a7a107d28fba6824fc1dbf333`).
Original answer and its attached `VERDICT.md`: [Proshka chat](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6aafb38a-a7a4-83eb-9940-84a574eae168),
answer turn `b25bee45-b2b8-4d45-aab5-4d3916696ed1`, heading
`KILL_GOAL058_UNIFORM_LITERAL_COMPLEMENT_FLOOR`. The full response copied from
that browser answer is preserved as
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_INDEPENDENT_COMPLEMENT_FLOOR_2026-09-25.md`
(29,275 bytes, 617 text lines, no final LF, SHA-256
`08753f55fafaa044d802dc950c493cdf8a0027c9f42dea5e99a14ffdd71f5b41`).
The attached `VERDICT.md` was downloaded from that answer's preview in Chrome
on 2026-09-25 at approximately 22:37 Europe/Berlin and preserved as
`docs/routeB_bus/proshka/PROSHKA_ATTACHMENT_GOAL058_INDEPENDENT_COMPLEMENT_FLOOR_2026-09-25.md`
(34,744 bytes, 471 LF characters, SHA-256
`e80a26c654928fad714b6cebf2dab347ff68a9eff6b5f0ff430447e5122aad15`).
It is **not byte-identical** to the copied UI response: the latter includes
the inline summary and attachment link, whereas the file adds source metadata
and gives a fuller proof. Both sources are retained separately.
The user-pasted extract at
`/home/chirurgie/.codex/attachments/bd1f984d-b8de-476d-a219-92167a3d8b89/Eingefügter Text.txt`
has SHA-256 `fb6e1eaf1affeb8c7872004128045d3cd575c64a5a43e9b17d5eebea624e41ca`
but is visibly truncated/corrupted; it is not an exact local copy of the answer.
This file records the independently checked argument, not a verbatim transcript.

## The assertion actually killed

For the one selected port and tail, `m_j=N_j=preAnchorTailStart(P)+j+2`, let
`K_j` be the literal CCM source matrix on modes `-m_j,...,m_j`, let `q_j` be
the unit selected Ferrers row, and set `a_j=q_j* K_j q_j` (real). The proposed
constant interface says that **one** `beta>0` eventually satisfies

`y*(K_j-a_j I)y >= beta ||y||_2^2` for every `q_j* y=0`.

The counterexample supplies unit `y_j` in that exact complement with
`y_j*(K_j-a_j I)y_j <= U_j`, where `U_j -> 0`. Thus no such fixed `beta`
exists. It does not decide whether each cell has a positive floor `delta_j`,
whether `||r_j||/delta_j -> 0`, or whether the terminal family can be tracked.

## Check of the radical identity (R)

The two real, even, rapidly decreasing tests are generated from

`h*(x)=(24*pi*x^2-16*pi^2*x^4) exp(-pi*x^2)` and
`G(t)=exp(t/2) sum_{r>=1} h*(r exp(t))`.

The physical Fourier transform fixes `h*`, while `h*(0)=int_R h*=0`.
Poisson summation therefore gives `G(-t)=G(t)`. On `t>=0`, the Gaussian
sum and every derivative decay faster than any exponential; evenness gives
the same bound on `t<=0`. Direct Gaussian integration yields

`int_0^infty h*(x)x^(s-1) dx = 2s(1-s) pi^(-s/2) Gamma(s/2)`.

Initially for `Re(s)>1`, absolute summation gives, for
`s=1/2-iz`, `Ghat(z)=-4 xi_zeta(s)`. Both sides are entire, so this holds
everywhere. Consequently `Ghat(z_rho)=0` at every nontrivial zeta zero,
where `z_rho=i(rho-1/2)`. Also `widehat(G'')(z)=-z^2 Ghat(z)`.

The required extension of CCM §3 (arXiv:2511.22755, formulas (3.1)-(3.11))
is legitimate for each finite-window Fourier synthesis `f` used here.
Choose smooth compact cutoffs `G_R=chi(t/R)G`. The log-coordinate
correlations of `G_R` and `f` are compactly supported and belong to the
paper's Weil class, so (3.2) applies. For `z_rho`,
`|Im(z_rho)|<1/2`. Weighted integration by parts gives, uniformly in `R`,
`|Ghat_R(z_rho)| <= C_N(1+|Re(z_rho)|)^(-N)` for every `N`; the compact
window gives `|fhat(z_rho)| <= ||f||_1 exp(L/4)`. The standard zero count
`N(T)=O(T log T)` makes the zero sum absolutely and uniformly convergent
for `N>2`. Moreover `G_R -> G` in every exponentially weighted `C^k` norm.
This passes the pole terms, the archimedean distribution (including its
value at 0), and the entire prime-power sum to the limit: at `log p^n`,
choose a weight `exp(A|t|)` with `A>1` to dominate
`sum_{p,n} (log p) p^{-n/2-An}`. The same proof applies to `G''`.
For real even `G` and `G''`, conjugation in the first factor of the
sesquilinear zero sum does not alter the zero factor. Hence, without RH,
`W(G,f)=W(G'',f)=0` for every finite-window synthesis `f`. This is the
global form radical identity only; no finite projection is declared null.

## Remaining source and finite-dimensional checks

The source-form/matrix crosswalk retains the full `W02-W_R-sum_p W_p`
diagonal, the `(-1)^n` Fourier phase and `N=m`. The window projection
error is controlled in `L2`, derivative `L2`, and both boundary values.
The mixed-form bound includes all prime powers up to and beyond `m`, the
archimedean value-at-zero cancellation from orthogonality, and both jumps
at the window edge. Its interior and exterior envelopes tend to zero;
therefore `||K_m coeff(Pi_m g)||_2 -> 0` for both normalized directions
`g0=G/||G||_2` and `g1=(g0''+||g0'||_2^2 g0)/||...||_2`.
This is a norm estimate, not merely a small Rayleigh quotient. The
two projected directions remain linearly independent and can be
orthonormalized with `sup_{||w||=1,w in span{u_m,v_m}} ||K_m w|| <= eps_m -> 0`.
The verified paper `hmode` is used only to give
`|<q_m,u_m>|^2 -> 1` on the same cofinal schedule. No limit for `a_m`
is assumed. The two-case Hermitian linear-algebra argument gives either
a unit vector in that plane and `q_m^perp` with quotient at most
`7 eps_m`, or a unit vector in `q_m^perp` with negative quotient.
Thus the fixed-`beta` floor is contradicted. The audit checked the
complex conjugations and the `a_m < -6 eps_m` case separately.

Scope: the **constant** complement-floor theorem shape and any wrapper
that requires it are blocked for this literal selected family. The
conditional `complement floor => odd floor` lemma remains valid as an
implication, but cannot provide a fixed odd floor through this input.
The next open paper target is a positive cellwise `delta_j` with a
quantified residual/consumer rate on the same family. No such result is
asserted here. No Lean or workflow runtime was run for this audit.

## Independent review disposition

Native adversarial reviewer, two consecutive on-target PAPER/documentation
passes on this scope: no unresolved CRITICAL, HIGH, MEDIUM, or LOW findings.
In pass 2 the reviewer initially labelled source completeness LOW after
reading through physical line 616; the final paragraph is present on text
line 617. The reviewer explicitly withdrew that LOW after checking the
file tail. The source copy has 617 text lines, 616 LF characters, and no
final LF. Its SHA-256 above is unchanged. The sole remaining suggestion was
WORDING of that line-count description, applied here. Those passes covered the
copied UI answer, before the distinct attachment was downloaded. The attachment
is reviewed separately below. No Lean or workflow runtime was run.

## Exact attachment review, 2026-09-25

The recovered attachment was checked on the source pin, not substituted for the
copied response. In (C), the off-diagonal and diagonal correlations reproduce
`ccmQKernel`; the Laplace factors reproduce `ccmW02Entry`; and integrating the
archimedean tail beyond `L` gives precisely the `log(tanh(L/2))` term of
`ccmWREntry`. The CCM paper's §3, equations (3.2), (3.10), and (3.13)–(3.16),
was read from the local `docs/routeB_bus/litreview/pdfs/2511.22755.pdf`.

For (N), two integrations by parts give the claimed `n^-2` Fourier coefficient
bound, including the derivative jump. Parseval and absolute convergence give
the three estimates (P). The interior mixed form retains every prime power up
to `m` and both endpoint jumps. For the exterior tail,
`|Q_(t_m,f)(x)| <= 2 sqrt(m) exp(-|x|) T_g(m)` follows from weighted
Cauchy–Schwarz; summing with `Lambda(ell)/sqrt(ell)` uses the finite
`sum_(ell>=2) log(ell)/ell^(3/2)`. The terms in (I) and (T) tend to zero.
The overlap (A) uses the stated PAPER hmode only; the finite-dimensional
B1/B2 split needs no limit of the Rayleigh shift. These checks support only the
fixed-positive-floor theorem-shape counterexample, not a cellwise floor, a
tracking rate, or RH. The attachment's claim of 35 algebraic checks was not
independently reproduced here.

Native adversarial attachment review: two consecutive on-target passes on the
unchanged SHA-256 above, with no CRITICAL, HIGH, MEDIUM, or LOW findings. Pass 2
also checked CCM §3 and §4 directly, including the zero-sum limit and the
complex first factor. The reviewer did not re-prove the upstream PAPER hmode or
run Lean. This is a PAPER acceptance of the fixed-constant obstruction only.
