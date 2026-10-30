# Gridnev–Garcia: Green-function domination versus CCM localization costs

Status: source-verified partial analogue; direct CCM transfer NOT established.
Owner pointed to this paper after the threshold alias hunt. It was previously
only a search lead; the worked proof below was not already processed.
This is different from Bellazzini–Frank–Lieb–Seiringer 1301.5370, though both
study retention at a closing binding threshold.

Primary source: D. K. Gridnev and M. E. Garcia,
*Rigorous conditions for the existence of bound states at the threshold in
the two-particle case*, arXiv:math-ph/0610038v2 (6 November 2006),
https://arxiv.org/pdf/math-ph/0610038 .
DOI: 10.1088/1751-8113/40/30/022.
Fetched PDF SHA256: df4e154f60ed0fade7fbd430cab7d0e9994bf3c33a6ecf98a0ec12b745790ed7.
Quote, Theorem2 p.6: “where g ∈ L2 and En → 0”.
Root read Theorems2–3, equations(4)–(6),(18),(45)–(47), the Green comparison
Lemma1, and AppendixA's compactness argument. No repeated broad search.

## The actual mechanism

On L²(R³), H(lambda)=-Delta+lambda(W_+-W_-), W∈L²+L∞;
W_- is supported in a fixed ball. Exact bound states satisfy E=-k²<0.
Their equation is

    phi=lambda(-Delta+k²+lambda W_+)^{-1} W_- phi.

The inverse has a positive kernel. A positive exterior comparison potential
eta=A/r² outside R0, A>3/4, gives kernel domination uniformly as k decreases
to zero. Equations(45)–(47) yield

    |phi(x)| <= 2lambda_cr integral_{|y|<=R0} G_k(x,y) W_-(y)|phi(y)|dy,
    |phi(x)| <= C1 |x|^(-3/2-delta)             (|x| large, delta>0),
    |phi(x)| <= C2 [integral_{|y|<=R0} |x-y|^-2 W_-(y)²dy]^(1/2)
                                                    (|x| bounded).

Both pieces form ONE k-independent L² majorant. The tail follows from
the zero-energy Green solution r^(-1-a), a(a+1)=A, and a>1/2.
After shifting the source y in the fixed ball, the proof chooses a slightly
smaller comparison coefficient still >3/4. The interior squared majorant
is integrable by Tonelli: integral_{|x|<=R}|x-y|^-2 dx is bounded uniformly
for y in the source ball, and W_- has finite L² norm on that ball.

There is a source typo after (45): it prints W_-(y)=0 for |y|<=R0.
The integration domain, previous discussion and assumptions require >=R0
(outside the ball). This is not an alternate support convention.

Theorem2 uses the majorant for tightness, then AppendixA uses local
compactness (Rellich / localized free-resolvent compactness) to obtain a
nonzero weak limit and norm convergence. An L² majorant ALONE does not
exclude weakly vanishing oscillation. In particular, the proof does not
turn an arbitrary dominated L² sequence into a retained eigenstate.
The theorem concerns exact bound eigenstates, including excited states;
it does NOT use exact bottom minimality or construct a lower-energy competitor.

## Comparison with the current CCM localization attempt

Bellazzini pays an IMS localization error by a surviving exterior repulsive
term. Gridnev–Garcia instead controls propagation from a FIXED bounded
attractive source through a positive Green kernel; its argument need not
cut and reproject each eigenfunction. This is a distinct useful mechanism,
not another name for the same localization-error estimate.

The existing exact CCM jump identity yields

    A_m=J_m+u_m u_m* - C_m I,
    (J_m-beta_m)f_m=-u_m<u_m,f_m>, beta_m=lambda_m+C_m.

For exact bottoms, mu1(J_m)<=beta_m<=mu2(J_m). Therefore J_m-beta_m
is NOT supplied as a strictly positive operator with a positive inverse:
it is nonpositive on a lowest J mode and may be singular. The right side
is a growing-window pole vector, not W_- supported in a fixed ball.
Using J_m+tau instead gives

    (J_m+tau)f_m=(beta_m+tau)f_m-u_m<u_m,f_m>, tau>0.

Now the forcing contains f_m on the whole growing window. This rewrite
has not produced the fixed-source Green bound needed in (45).
Indeed ||(beta_m+tau)(J_m+tau)^(-1)||=(beta_m+tau)/(mu1+tau)>=1;
the simplest norm-contraction absorption of that global forcing fails.
The negative scalar -C_m I cannot silently be treated as compactly
supported attraction. The numerical threshold 3/4 is for the three-dimensional
Laplacian; it is not a CCM or one-dimensional constant.

Even when an unrestricted jump generator preserves positivity, compression
to the finite even Fourier carrier need not preserve pointwise positivity
of its semigroup/resolvent. Likewise adding the positive rank-one pole
does not automatically preserve a positive integral kernel. These missing
order properties prevent taking absolute values as in (6)/(45).

For the current IMS approach, chi f and eta f leave V_m,E. The full
localization budget still includes the signed jump remainder, pole cross
terms, carrier return and normalization. A Green-function proof could
avoid this particular cutoff operation ONLY if established directly for
the exact finite source, or if every ambient-to-carrier defect is included.
An ambient equation generally has (I-P_m)Hf as an extra forcing; projected
stationarity does not make it zero.

For an admissible approximate state, an invertible Green rewrite includes
G_m r_m. The bound is ||G_m r_m||<=||G_m|| ||r_m||, not just ||r_m||.
At threshold ||G_m|| may diverge, and kernel-weighted control may be more
relevant than operator norm. Superpolynomially small absolute residual
therefore does not by itself reproduce (45)–(47). No residual term is
present in the exact eigen-equation used by this paper.

## Negative control and precise unpaid bridge

The accepted escaping translated-radical packets cannot share a uniform
L² envelope, since such an envelope gives uniform tail tightness while
their mass moves to infinity. Signed finite-functional cancellations do
not cure this issue. A proposed Green estimate valid for all small-energy,
small-residual trials must fail on them somewhere. The source paper's
fixed attractive support, positive resolvent comparison, exact equation
and local compactness are explicit premises, not consequences of escape.

To use this mechanism for CCM, prove a decomposition/resolvent comparison
for the FULL finite source yielding a common L² envelope (or uniform
tail bound), together with local compactness for its exact bottoms.
It must retain every prime power and pole and quantitatively control
any projected-equation defect. The standard jump-plus-pole decomposition
above does not meet those premises. Even a successful retention proof
would need the accepted fixed-jet density bridge to produce T.
No strictly cheaper same-carrier competitor or NOESCAPE proof is obtained.

Independent bounded read-only audit confirmed the finite-resolvent obstruction,
including the noncontractive global forcing. It is a failure of this direct
transfer, not an exclusion of every alternative source decomposition.
