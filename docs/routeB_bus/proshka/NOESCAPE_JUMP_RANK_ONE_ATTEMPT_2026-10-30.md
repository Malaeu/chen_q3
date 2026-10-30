# Parallel own check: jump form plus one pole moment

Status: bounded PAPER own identity/candidate, not a source sign or NOESCAPE proof.
DIAGONAL subsequently arrived by GitHub; see DIAGONAL_VERDICT_AUDIT.
This is another permitted competitor, not a replacement or mandatory network path.

## Full source and finite carrier

For real even f in the original V_m^E, zero-extended from I=[−L/2,L/2], define
T_s f(x)=f(x+s), c_n=Lambda(n)/sqrt(n), p=sqrt(2)cosh(x/2), and

 J_m[f]=integral_0^infinity j(s)||f−T_s f||² ds
         +sum_(2<=n<=m) c_n||f−T_logn f||²,
 C_m=c_*+2sum_(2<=n<=m)c_n.

Since ||f−T_s f||²=2||f||²−Q_ff(s), CONFINE (1.3) gives exactly

 k[f]=J_m[f]+|<p,f>|²−C_m||f||².

The odd pole vanishes by parity, not by omission. All prime powers remain.
At n=m the jump square is 2||f||² and its scalar subtraction cancels exactly.
The infinite arch tail remains: s>L contributes
2||f||² integral_L^infinity j(s)ds. It must not be dropped.
Finite Fourier zero-extensions have translation-square difference O(s),
so the integral is finite at zero. The retained arch tail already gives J_m[f]>=
2(integral_L^infinity j(s)ds)||f||²>0 for nonzero f. This explicit lower
bound depends on m and tends to zero; no uniform spectral floor follows.

Let J denote the exact finite compression of this form and u=P_m^E p in its
orthonormal coefficient coordinates. Then A=J+uuᵀ−C_m I. This is not a
change of source or a new Fourier truncation. Let mu_1<=mu_2<=... be J's
ordered eigenvalues. Rank-one min-max gives for the exact source bottom
lambda_1+C_m<=mu_2, while J>=mu_1 I. Hence any unit exact bottom f satisfies

    |<p,f>|² <= mu_2−mu_1.                       (R1)

This is a quantitative growing-window moment constraint. It is not fixed-jet
retention, and it does not imply positivity, simplicity or a nodal pattern.

## Explicit admissible competitor and exact use of minimality

Choose real orthonormal J eigenvectors e_1,e_2 and put b_i=<p,e_i>.
If b_1²+b_2²>0, define

    g=(b_2 e_1−b_1 e_2)/sqrt(b_1²+b_2²).

Otherwise take g=e_1. In either case g is normalized, even and in the SAME
finite carrier, <p,g>=0, and k[g]<=mu_2−C_m. Thus a sufficient strict gain
against ANY unit f is

    J_m[f]+|<p,f>|²>mu_2,

or the stronger separately estimated condition |<p,f>|²>mu_2−mu_1.
The competitor retains the full jump energy including all mixed terms.
Exact minimality is used at k[f]<=k[g]; it prohibits this strict inequality.
A small residual alone supplies no such global comparison. This identifies
an actual moment test but does not show that escaping bottoms violate it.
Merely substituting exact J_m[f] in the first comparison would rename descent.
An independent source upper bound on the gap and lower bound on the pole
moment under escape would be genuinely additional input, neither proved here.

## Controls and limits

The positive jump form has a modulus contraction on its physical domain, but
|f| generally exits the finite Fourier carrier, and the full source adds the
positive pole cost. The existing VARIATIONAL modulus counterexample and
projection-return cost still apply. Perron/nodal assertions for an unrestricted
physical operator do not transfer to the finite compression or its rank-one
perturbation without proof. No mandatory central-frequency nodes are inferred.

For normalized symmetric radical translates
r_a=(T_a h+T_-a h)/sqrt(2||h||²+2<h,T_2a h>),

 |<p,r_a>|²=2 cosh²(a/2)|<p,h>|²/(||h||²+<h,T_2a h>).

Here <p,h>=2sqrt(2) from H(i/2)=4xi(1)=2. At a=L/8 the expression is
asymptotic to 4m^(1/8)/||h||². The superpolynomial finite-carrier repair
preserves this asymptotic because ||p||_L²(I) grows only polynomially in m.
These trials are not bottoms. The crude bound mu_2−mu_1<=C_m+o(1), obtainable
from a two-dimensional near-radical trial plane and J>=0, is only
O(sqrt(m)log m) using Lambda(n)<=log m. It does not exclude this moment size.
This is a comparison with a crude upper bound, not an estimate of the actual gap.
Moreover BOUNDARY's finite-functional null combinations can cancel the pole
moment exactly while escaping; they need not be nonnegative or exact bottoms.
So escape alone does not supply the needed pole-moment lower bound. Other
moments, competitors or sharper exact-minimum consequences remain open.

Verification: jump_rank_one_scope independently checked source factors,
arch/prime endpoints, finite rank-one interlacing and the moment inequality.
Root derived the displayed explicit normalized competitor directly.
Shelf query returned ASK_STATUS: INCOMPLETE; no global absence assertion.
The radical-moment comparison and conditional two-dimensional min-max bound
were independently confirmed. The well-conditioned two-packet construction
is available in BOUNDARY Lemma 6; if invoking a different trial plane, its
conditioning and residual must be checked separately.

## Finite control of the concrete competitor

The same g is an effective excited-state control: if mu_1<mu_2 and b_2!=0,
its jump energy is strictly below mu_2, whereas the first excited eigenvalue
of J+uuᵀ is at least mu_2 by interlacing. This is not a bottom contradiction.
90-dps literal diagnostics m=4,8,16 give g energies respectively
1.7181723312e−5, 4.1284746314e−15, 3.0517985109e−32, below the first excited
energies but above the bottoms. The measured jump gaps are about
2.83127, 4.51015, 6.48967. These finite observations do not supply any
eventual estimate. Script/data: noescape_rank_one_probe.{py,json}.
The exact pole coefficients used are
u_i=4sqrt(2)d_i L^(3/2)sinh(L/4)/(L²+16pi²i²); no sampled physical grid.
They follow by integrating p against the original orthonormal even modes.

## Actual bottom overlap check (diagnostic, not a retention theorem)

While DIAGONAL was pending, the bounded worker ground_overlap_diagnostic
computed the actual lowest even eigenvector for m=8,16,24,32 at 160 dps.
Unlike the earlier excited controls, these are the selected numerical bottoms.
The physical h overlap uses H(t) minus the directly integrated exterior theta
tail, not periodized coefficients mislabeled as physical coefficients.
All source matrix terms and the original orthonormal even basis are retained.

| m | lambda_bottom | first gap | squared normalized physical h overlap |
|---|---:|---:|---:|
| 8 | 1.0239258710e−19 | 6.3726260399e−15 | 0.9996889777061910 |
| 16 | 5.4561380117e−38 | 4.7334130203e−32 | 0.9984375105475905 |
| 24 | 2.6905128126e−54 | 4.2761989283e−48 | 0.9982912520996606 |
| 32 | 8.1805955424e−70 | 2.5033758048e−63 | 0.9984112135908399 |

Residual/gap is below 2e−98 in all four cells; total runtime109.876s.
Norm h squared≈5.11602899138594056. Script and raw data:
../thetagrade_2026-10-28/noescape_ground_overlap_probe.{py,json}.
Root independently recomputed m8 via 80-dps direct physical x-integrals,
using twelve theta terms and integration to x=3 for the norm, without any
xi transform or exterior subtraction. It gave
0.9996889777061910416195290420021350988770393815898267751.
This corroborates phase, parity and normalization numerically. No rigorous
quadrature error or eigenpair enclosure is supplied here; residuals against
a numerical matrix are not certificates for the exact source.
The near-unit overlaps support the entrance on these cells only. Four small
cells do not exclude slow escape or prove any cofinal lower bound.

## Shelf return for localization: the missing inverse-weighted budget

Read-only radical_localization_shelf searched de Branges/Sonine,
extremal-entire-function/uncertainty, and spectral-concentration/sampling
names. ask.sh remained INCOMPLETE; no theorem absence is claimed. Local
spectral-synthesis results do not provide finite-carrier localization and
were not imported. The closest actual source bridge is already NOESCAPE
(4.7)–(4.9): physical coefficients include the exterior correction, and

 sum_(i>=1,lambda_i!=0) |F_mi+X_mi|²/(Z_m² lambda_i²)+z_m <= c<1

would retain a fixed fraction in the projected h direction. Here z_m is the
excited zero-eigenspace mass. Root reread the exact source formula; the
absolute X bound alone does not pay these inverse eigenvalue weights.
The present finite overlaps do not establish this inequality on an unbounded
family. This is an existing sufficient comparison, not a newly proved supplier,
and not a mandatory replacement for the ongoing variational test.
