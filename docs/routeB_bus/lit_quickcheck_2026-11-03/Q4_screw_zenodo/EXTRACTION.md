# Q4 — retrieved claims and normalization

DIAGNOSTIC_NEVER_A_PROOF. Source: Rainer Andreas Mittermeier, *A Zero-Side
Positivity Certificate for Suzuki's Screw Function through4·10²⁰: Window
Means and One-Sided Criteria — Companion to Part5*, Zenodo23481975,v1,
19October2026. Primary PDF SHA256 and URL are in SOURCES.json. The following
are extracted claims, not independently audited proofs or priority findings.

## Exact statements requested

(a) Theorem1.1(i), PDFp2: without RH, Psi(t)>0 for0<t<=47.48,
equivalentlyF(X)<C0 for1<X<=exp(47.48), hence through4·10²⁰.
Theorem1.1(ii) additionally asserts positivity of unit-window means through
t104.63. Section6,pp9–14, combines a known finite-height RH verification
T*=3·10¹², explicit absolute high-zero budgets, and an outward certificate
from3000 enclosed zeros. We did not rerun that zero-side certificate.

(b) Theorem4.2(ii), PDFp7: if for everyepsilon>0 there exist C_epsilon
and T_epsilon with Psi(t)>=-C_epsilon*exp(epsilon*t) for t>=T_epsilon,
then RH holds. Bounded-belowPsi is a special case. Part(iii) asserts that
if RH fails, Psi(t)<-exp(theta*t) arbitrarily late for every
theta<Theta-1/2, whereTheta is the supremum of zero realparts.

Proof structure, not an independent verification: Lemma4.1,p7 takes
G>=0 with Laplace convergence beyondtheta and Psi+G>=0. Its transform is
s^-2*(xi'/xi)(1/2+s)+Laplace(G). Landau's one-sign principle puts its
abscissa at or belowtheta because the expression is regular on the positive
realaxis. A zero with realpart>1/2+theta would force a nonrealpole there.
For(ii), takeG=K+C_epsilon exp(epsilon*t), use a compact-intervalK, let
epsilon↓0 and reflect zeros by the functional equation. The source identifies
this as a one-sided counterpart to Suzuki's boundedness criterion, not a
new proof of RH from an established sourcebound.

(c) Theorem4.3,p7: unconditionally liminf_(t→infinity)Psi(t)<=0. UnderRH
that limitinferior is0, and for everyepsilon>0 the times with
0<Psi(t)<epsilon are relatively dense. Its proof invokes Bohr recurrence
underRH; if eventualnonnegativity holds, part(b) suppliesRH, otherwise
negative values occur arbitrarily late. No loweredge equality conditional
on simplicity/linearindependence is silently imported.

(d) Theorem3.2,p6: both strict signs occur arbitrarily late for
`Y(t)=-Psi'(t+)` and for
`eta(x)=sum_(n<=x)Lambda(n)/sqrt(n)-2sqrt(x)+zeta'(1/2)/zeta(1/2)`.
The proof studies the Laplace transform after subtracting the smooth
archimedean remainder, applies Landau to either eventual sign, and compares
the unavoidable nonreal zero pole with regularity on the real axis.
Prime-power halfweights versus fullweights are explicitly distinguished
on p5; the integral/smoothed formulas are unaffected at a singlepoint.

## Exact classical dictionary

Proposition2.1, PDFp5 (notation on p4):

`alpha=(EulerGamma+log(8pi)+pi/2)/2=zeta'(1/2)/zeta(1/2)`,
`C0=pi²/4+2Catalan-8`,
`r_infinity(X)=4 sum_(k>=1) X^(-(4k+1)/2)/(4k+1)²`,
`F(X)=sum_(n<=X) Lambda(n)/sqrt(n)*log(X/n)-4sqrt(X)+alpha logX+r_infinity(X)`,
`Psi(logX)=C0-F(X)`.

Substitution of psi_Gamma(1/4)=-EulerGamma-pi/2-3log2 and separating
the k0 term of the original Lerch series shows the dictionary has the
same normalization as our source. Twenty fixed MP85 comparisons and the
alpha logderivative check are in crosswalk.csv/json; no adjustable constant
or factor2 is fitted.

## Search instruction correction

SourceEq(6)–(10),p4 gives Psi=A-W_j*t+L_j between consecutive log-prime
powers, with Psi''=A''=(x³-x-1)/(sqrt(x)*(x²-1))>0 forx>=2.
At an atom, Psi' jumps **down** byLambda(n)/sqrt(n). Thus a prime-power
event is not generically a localminimum, and minima can lie inside a cell.
The brief's claim that left-eventvalues are minima byconstruction is not
correct for this normalization. We retain those checks and independently
locate the interior derivative roots. This correction is a better numerical
discriminator, not a theorem-proof or an external-law acceptance.
