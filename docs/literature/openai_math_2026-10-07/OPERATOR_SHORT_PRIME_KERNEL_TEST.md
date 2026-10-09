# A short-prime-only null correction cannot satisfy the full PSD certificate

2026-10-09. Own concrete restriction of O12-O14 after09f47ccf.
Independent read-only mobius_short_transfer K1-K3 PASS.
This tests a certificate shape, not RH or MB34.

Keep the actual physical Gram G of O9-O11 on all good ideals qn<=X,
X>=beta D, and the exact original rows, amplifiers and common profile W.
Restrict the correction to A_p with qp<=R, but allow its Y_p matrices
to be entirely arbitrary, including mixed-prime coupling:

 S=B e1e1*-G-sum_(qp<=R)(A_p*Y_p+Y_p*A_p).                    K1

## K2. Explicit retained kernel vector

Choose an omitted good prime ideal q with qq>R. Define f_q(n)=mu(s)
when n=s q and every prime of s has norm<=R, and zero otherwise.
In particular f_q(1)=0 and f_q(q)=1. For every included p,
A_p f_q=0: removing powers of p leaves the same R-rough part, and
on that part the full p-power identity is exactly A_p mu=0 on s.
Divisor closure of I_X retains every required smaller coordinate.
No squarefree restriction is imposed on the coordinate space.

Therefore f_q*S f_q=-f_q*G f_q for ANY B and ANY included Y_p.
If its actual observation is nonzero, K1 is not positive semidefinite.

## K3. Make the observation a single ACTUAL column

For nonzero smooth compact W on (0,infinity), let beta be the upper
endpoint of its support. Choose t0>beta/2 with W(t0)!=0. Such a point
exists by the definition of beta. Let L=qq/t0 and D=L; all nonunit
integral ideals s have qs>=2. Thus W(qs qq/L)=0 for s!=1, and

 sum_n t_(u,a)(n) f_q(n)
   =L^(-1/2)nu(q)chi_q(u)^epschi 1_((q,a)=1) W(t0).           K2

Fix r in[28/25,113/100] and put U=L^(1/r), H=D^(1+c0),
P=U^p as before. For any fixed 0<delta<r choose R=U^delta.
Along good primes q tending to infinity, qq=t0 U^r exceeds R,
the upper rho row norm O(U), and P. Exclude finitely many primes
where fixed nu vanishes. Hence neither u nor a is divisible by q,
and every character value in K2 has modulus1. Consequently

 f_q*G f_q=G_qq
 =|nu(q)W(t0)|²/L * #{good a:qa<=P} * sum_(u6free)rho(qu/U)>0. K3

The positivity assertion requires the actual row mass to be nonzero.
For the standard nonzero nonnegative smooth rho it holds eventually:
sixth-power-free lattice elements have positive density, also after
restriction to a fixed set of permitted S-valuations. One elementary
proof expands 1_(u6free)=sum_(d^6|u)mu(d) and uses weighted lattice
counting. Main term is a positive constant times U; the error is
O(sqrt(U) sum_d qd^(-3)+U^(1/6))=O(sqrt(U)), and the tail of
the main absolutely convergent ideal sum is O(U^(1/6)). Fixed S
restrictions change its positive Euler factors. Alternatively K3 is
an exact finite test whenever positive row mass is directly known.

There are infinitely many good prime ideals after deleting any finite
set; no prime-in-short-interval theorem is used, since L is chosen from q.
These L=D lie on the permitted upper-band endpoint. This establishes a
cofinal sequence of certificate failures, sufficient to rule out K1 as
a uniform certificate on the full prescribed parameter domain.

## Scope and consequence

Even arbitrary large Y_p and mixed couplings cannot repair the missing
constraints: their quadratic form is zero on f_q. The obstruction holds
for ANY budget B placed only in the unit coordinate, not just target eta.
It does NOT show that the actual Mobius energy is large: f_q is a
diagnostic coefficient vector, not mu. It does NOT reject an all-prime
locally constructed correction, a paid extra majorant on rough modes,
or direct bounds for MB34/high values.

A repair must either include constraints seeing these omitted prime
columns or explicitly budget their observation on the right-hand side.
The latter creates a rough-sector estimation obligation; it is not free
from the smaller dimension. Do not rerun the restricted-prime ansatz
with more elaborate Y_p while keeping the same missing kernel modes.

## Bounded alias return

Three shelf queries: facial reduction/semidefinite equality kernel
compression; sum of squares modulo a linear ideal; Finsler lemma and
structured lossless S-procedure. All INCOMPLETE (q3_docs freshness),
not evidence of absence. A local source analogue was actually reread:
q3.lean.aristotle/Q3/Proofs/RouteB/RankOneCorrectionWeightedSymmetry.lean,
lines14-50, SHA256f31875b4dc48e10cb61380400f47cfb47e4af14711cd51a9ce5786e1ac661204.
Quote: “The normalization `⟨η,ξ⟩=1` makes the corrected operator kill `ξ`.”
Its D'=D-|D xi><eta| kills xi and is weighted symmetric under explicit
commutator and TDxi=-beta assumptions. There is no matching map to
our A_p,Y_p and no positivity or budget theorem. It is an excluded
supplier, a partial kernel/symmetry analogy only; no Lean rerun claimed.
The actual obstruction here is positivity on the enlarged retained kernel,
not merely knowing how to annihilate one vector.
