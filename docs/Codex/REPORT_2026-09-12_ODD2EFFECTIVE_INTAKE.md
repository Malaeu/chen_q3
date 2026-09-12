# ODD2EFFECTIVE intake: S=20 and explicit global localization L=2000

Status: ACCEPT_EXPLICIT_S20_ODD2_COFINAL_SUPPLIER_ONLY.
Combined localization: ACCEPTED_PAPER_EXPLICIT_MAX_NODE_L2000.
No global ODD2, IC, higher odd/even PSD, Lean, canonical admission or RH claim.

## Received exact source and independent review

Request REQ-2026-09-12-ODD2EFFECTIVE, boundary
GOAL058_ACTUAL_THETA_ODD2_EFFECTIVE_COFINAL_COVERAGE, same living mathematical
chat6aa52001-4094-83eb-9520-01a09f54eff2. Request commit
2645e5bf6da902b8f79d77412d3a6dca229c7967; request SHA256
428a6037cf8af475064d9984b51fdc9aafaa6b83f58fdfddbb160772d4b780cd.

The natural final Proshka UI displayed34m41s. The complete Markdown was
downloaded via the existing chat, without interrupting or Answer now:

    docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODD2EFFECTIVE_2026-09-12.md
    73274 bytes;1060 LF; final LF;0 CR; valid UTF-8
    SHA256 06a009eae972027f01f8e0e2d096b7a1e6a453e7b03e55f4a5b7cbd217a29f94

The response remains unchanged. Parent and sole independent checker
/root/sibling5_check both read all1060 lines. All17 request source frames
were decoded and matched against pinned source bytes, sizes, LF counts and
SHA256. The checker returned
ACCEPT_EXPLICIT_S20_ODD2_COFINAL_SUPPLIER_ONLY, with no found mathematical gap.

The parent's exact extraction of Appendix B has2193 bytes/46LF and SHA256
a4ddc2a5d03556fabd8b354c5df9fcbf9acb83099b5ad7883460adf08870acd3.
Executing this source reproduced all25 exact rational checks and the
unchanged1179-byte/37LF output, SHA256
f16ddd8d81b59883b88e87f9aaa1c2f44c5e19e4169eac206f4f19326563d8d9.
The independent checker separately executed the same mathematical block;
its output has the same exact SHA256. These checks supplement the full
analytic audits; they are not a numerical source-sign test or self-admission.
No new theta node evaluation or quadrature was used for this supplier.

## Accepted mathematical scope

The source remains f=Phi/A, A=||Phi||_2, with the full integrals

    V(s,t)=integral_0^infinity (s+t+2v)f(s+v)f(t+v)dv,
    K(s,t)=V(s,t)-V(s,-t),
    Delta(x,y)=K(x,x)K(y,y)-K(x,y)^2.

Put m=(s+t)/2, d=s-t and alpha_z=pi exp(2z).
The new accepted source-specific result is

    partial_s partial_t log K(s,t)>=1/160
              whenever m>=20 and |d|<=3.                       (E1)

Consequently every x,y>=20 satisfies ODD2 on all complex coefficients.
For |x-y|<=3 the explicit budgets are

    Delta(x,y)>= (m-2)^2 (x-y)^2 f(x)^2 f(y)^2
                         /(309760 alpha_x alpha_y),             (E2a)

    c* K_2 c>= (m-2)^2 (x-y)^2
                 /[464640(x alpha_y+y alpha_x)]
                 *[f(x)^2 |c1|^2+f(y)^2 |c2|^2].                (E2b)

For gap>=3, the accepted min1/gap3 theorem applies. At x=y, exactly
Delta=0 and c* K_2 c=K(x,x)|c1+c2|^2. The full original V form on
(x,y,-x,-y), with coefficients(c1,c2,-c1,-c2), is twice c* K_2 c.
The physical normalization and all complex phases are retained.

The main request for all x,y>=1 is still open only within the conservative
ordered residual1<=y<20,0<x-y<3, plus transpose. In particular mixed pairs
y<20<x<y+3 remain included; the residual is not just[1,20]^2.

## Parent and checker proof audit

Both reviews verified the complete mathematical chain, not just constants:

- Complex H reciprocity and the entire theta series give |H(q)|<2 on
  |arg q|<=1/4 for every |q|>0. Thus the small reflected H argument remains
  controlled all the way to zero. Only the initial denominator uses a
  large-argument lower bound.
- Independent complex mu/delta disks of radius1/64 give uniform sector
  bounds for every moving argument. Horizontal arcosh geometry and evenness
  of H(alpha e^w)H(alpha e^-w) remove the c=1 branch point before
  differentiating. Phi's unrelated normalization is not changed.
- The common full-halfline bound |J_z|<=2^15(M+1)(1+z)^4 gives an integrable
  bound for the complete difference J(z)-J(0), with both direct/reflected
  terms and all endpoint cancellations retained.
- Holomorphic domination, followed by Cauchy's formula in each independent
  variable, pays every actual composed m/d derivative of R through order2.
  No contour motion of the original v integral is assumed. The full relative
  remainder has nonzero L throughout the polydisk.
- The quadratic term in the second derivative of log(1+epsilon) is retained;
  its total curvature loss is less than1/65536. The exact main curvature is
  at least1/121-1/1296. Their difference exceeds1/160.
- E1 holds on every point of the square between the two nodes, so integrating
  it produces the exact (x-y)^2 factor. Congruence, determinant/trace and
  parity assembly give E2 for all complex coefficients.

The parent also directly verified the operative classical Cauchy formula
and its hypotheses against NIST DLMF section1.9(iii), equations1.9.30/31:
https://dlmf.nist.gov/1.9#E30 and https://dlmf.nist.gov/1.9#E31.
On a circle the derivative formula immediately yields the factorial/radius
bound; iterating it gives the two-variable estimate used here. The source
specific holomorphy and domination are proved in the response itself.

## Combined corollary: explicit max-node cutoff L=2000

This corollary uses three separately reviewed full-source theorems:

1. The present S=20 result: all min(x,y)>=20.
2. REPORT_2026-09-12_ODD2_REGIONAL_MIN1_GAP3.md, accepted commit
   4b8171f49b7750d17c6f98a5ba6d352a576d9cb4:
   min(x,y)>=1 and |x-y|>=3.
3. REPORT_2026-09-12_ODD2_SMALL_NODE_EFFECTIVE_TAIL.md, accepted commit
   a5ef8cc64f1116e74be715f8f4a8a07e2f53f2d3, SHA256
   918ebee2be455792c45012d852c23126907dcbdb3a72233a24b80928f268f138:
   x>=2000 and0<y<=1, or the transposed region, uniformly down to the axis.

Order x>=y>0 and suppose x>=2000. If y<=1, theorem3 applies. If1<y<20,
then x-y>1980>3 and theorem2 applies. If y>=20, theorem1 applies.
These cases cover every y>0, with y=1 and y=20 included. Therefore

    max(x,y)>=2000  ==>  Delta(x,y)>=0 and K_2>=0 on C^2.      (L)

If x!=y the determinant is strictly positive in these regions. Equality
on x=y is retained. Hence every possible actual negative ODD2 witness has
both nodes strictly between0 and2000. This is a new explicit localization,
not the incorrect substitution S=20 for a max-node threshold.

The already accepted whole-origin-quarter theorem, commit
 ef472574a339d3b4ee68ebb607bda79cba1cd9bd, also excludes all0<x,y<=1/4.
Using these results and removing the exact diagonal, a conservative ordered
outer set containing every still possible negative pair is the union

    Omega_low = {0<y<1, max(y,1/4)<x<2000},
    Omega_mid = {1<=y<20, y<x<y+3}.                          (R)

Add their transposes for unordered nodes. Previously accepted AX/DG blocks
can also be subtracted from(R); we do not relabel those known positive
points as unknown. The word outer set is intentional: this is a safe
remaining-coverage description, not a claim that every point of(R) is unpaid
or that a negative witness exists there. Full ODD2 still requires the sign
on every remaining pair, including axis and diagonal limits.

## Acceptance and next consumer

The cofinal S20 theorem has independent and parent acceptance at PAPER scope.
The exact intake and corollary(L)/(R) were independently reviewed CLEAN
as recorded below. This intake grants no production closure.

The next bounded source supplier is the whole Omega_mid strip, preserving
all independent parameters and the exact diagonal factor; together with
S20 and min1/gap3 it would finish ODD2 for all x,y>=1. The Omega_low part,
higher odd/even matrices, full V/Q sign and RH would still remain.
The current no-delta count remains0. Effective numerical thresholds refine
actual accepted source families; no artificial reset is based on paperwork.

## Final exact intake confirmation

The sole independent checker /root/sibling5_check reviewed all7800bytes,
154LF of the pre-receipt intake, SHA256
0fa58f109756901177809a1bb586566d63ea8f34bf06deea4b6ada0ee86a84c6,
and returned CLEAN. It independently verified the three source commits,
the small-node theorem hash, the exhaustive L=2000 case split, and both
conservative residual outer sets, including the quarter-square exclusion.
Only pending-status prose and this receipt changed afterwards.
The original Proshka response and reviewed mathematical assertions remain
unchanged. Full ODD2, IC, all-rank signs and RH remain open.
