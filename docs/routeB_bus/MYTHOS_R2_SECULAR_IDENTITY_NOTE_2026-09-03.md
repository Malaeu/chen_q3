# MYTHOS R2 — secular identity and Loewner source audit

STATUS: R2_IDENTITY_EXISTS_BUT_DOES_NOT_EVALUATE_CURVATURE
DATE: 2026-09-03
ROUTE: GOAL058_CURVATURE_CENTER_SCHUR_STIELTJES
BOUNDARY: PAPER_ONLY
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
HONESTY_STATE: CHALLENGER_NOT_RH

K6 priors frozen before derivation:

- P_SECULAR_IDENTITY_EXISTS: 0.55
- P_LOEWNER_CLAIM_SOURCE_FAITHFUL: 0.60

K6 scores:

- P_SECULAR_IDENTITY_EXISTS: CONFIRMED_AT_DETERMINANTAL_SCOPE;
  REFUTED_AS_FREE_CURVATURE_EVALUATOR.
- P_LOEWNER_CLAIM_SOURCE_FAITHFUL: CONFIRMED_AT_STRUCTURE_SCOPE;
  DOES_NOT_CLOSE_THE_MIXED_RESOLVENT_PAIRING.

## 1. Scope and notation lock

This note addresses R2 in §4 of
PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md.
It does not use the finite diagnostics as proof.

To avoid the collision between the curvature function called S in the task and
the odd hyperbolic vector called S in Silva, write

\[
R_D(z):=(D-zI)^{-1},\qquad
\Sigma(z):=\langle c,R_D(z)b\rangle,
\]

and denote Silva's hyperbolic vectors by \(C_{\rm hyp}\) and \(S_{\rm hyp}\).
The curvature bracket is

\[
\frac1{12}-\Sigma(\lambda_1).
\]

All vectors and matrices in the central-block calculation are real:
\(b,c\in\mathbb R^N\) and \(D=D^T\), as in CCM Lemma 5.1. The central block
decomposition and ground equation are

\[
K=\begin{pmatrix}a_0&b^T\\ b&D\end{pmatrix},\qquad
K\binom{\xi_0}{x}=\lambda_1\binom{\xi_0}{x}.
\]

The resolvent formula used below requires

\[
\lambda_1\notin\operatorname{spec}(D).
\tag{H}
\]

For a simple eigenvalue of a real symmetric \(K\), (H) is equivalent to
\(\xi_0\ne0\): if \(D-\lambda_1I\) were singular, its null vector is either
coupled to \(b\), contradicting the block eigen-equation with \(\xi_0\ne0\), or
orthogonal to \(b\), producing a second \(K\)-eigenvector at \(\lambda_1\).
Conversely, (H) rules out a nonzero eigenvector with zero central coordinate.
This is finite-cell nonvanishing, not a uniform lower bound for \(|\xi_0|\) along
a cofinal family.

Under (H),

\[
x=-\xi_0R_D(\lambda_1)b,
\]

which is the stated ground-row formula.

## 2. The exact scalar secular equation

For \(z\notin\operatorname{spec}(D)\), the Schur determinant identity is

\[
\det(K-zI)=\det(D-zI)F(z),
\qquad
F(z):=a_0-z-\langle b,R_D(z)b\rangle.
\tag{2.1}
\]

Thus \(\lambda_1\) is a root of the scalar Weinstein--Aronszajn equation

\[
F(\lambda_1)=0,
\qquad
\langle b,R_D(\lambda_1)b\rangle=a_0-\lambda_1.
\tag{2.2}
\]

Without (H), the polynomial form remains valid,

\[
\det(K-zI)
=(a_0-z)\det(D-zI)-b^T\operatorname{adj}(D-zI)b,
\tag{2.3}
\]

but \(\Sigma(\lambda_1)\) is then not defined by the displayed inverse.
Equation (2.2) is source-faithful and gap-free. It determines the self-pairing
\(\langle b,R_Db\rangle\), not the mixed pairing
\(\langle c,R_Db\rangle\).

## 3. What polarization gives — and what it does not

Because \(R_D(z)\) is symmetric on the real resolvent set,

\[
\Sigma(z)=\frac14\left(
\langle c+b,R_D(z)(c+b)\rangle
-\langle c-b,R_D(z)(c-b)\rangle
\right).
\tag{3.1}
\]

This is exact, but it does not reduce the amount of unknown source information.
Define two auxiliary bordered matrices

\[
K_\pm:=
\begin{pmatrix}
a_0&(b\pm c)^T\\
b\pm c&D
\end{pmatrix}
\]

and their Schur functions

\[
F_\pm(z):=a_0-z-
\langle b\pm c,R_D(z)(b\pm c)\rangle.
\]

Then Weinstein--Aronszajn gives the strongest direct determinantal identity

\[
\boxed{
\Sigma(z)=\frac{F_-(z)-F_+(z)}4
=\frac{\det(K_--zI)-\det(K_+-zI)}{4\det(D-zI)}.
}
\tag{3.2}
\]

In particular, (3.2) evaluates \(\Sigma(\lambda_1)\) only if the two auxiliary
determinants, or equivalent spectral data for \(K_+\) and \(K_-\), are already
known. The source gives that \(\lambda_1\) is a root of \(F\); it does not give
\(F_+(\lambda_1)=0\) or \(F_-(\lambda_1)=0\). Generically neither vanishes.
Computing the two determinants at \(\lambda_1\) is therefore an exact
repackaging of the mixed resolvent calculation, not a closed evaluation.

### First exact failure of line 1

The first failure occurs at the attempted replacement

\[
F(\lambda_1)=0
\quad\Longrightarrow\quad
\text{known }F_+(\lambda_1),F_-(\lambda_1).
\]

There is no such implication. Polarization creates two self-pairings whose
secular data are not supplied. A norm estimate for either pairing returns to
the distance from \(\lambda_1\) to \(\operatorname{spec}(D)\), precisely the
absolute complement-floor debt that R2 was meant to avoid.

## 4. Why the rank-two pole slice does not fill the gap

Silva, Zenodo 20694588, pp. 2--3, equations (1)--(4), writes the pole term as

\[
W_{0,2}=2|C_{\rm hyp}\rangle\langle C_{\rm hyp}|
-2|S_{\rm hyp}\rangle\langle S_{\rm hyp}|.
\tag{4.1}
\]

This is a self-published, non-peer-reviewed source; every claim imported from
it is RELAY_UNVERIFIED.

For a pole-free operator \(B\), the rank-two Weinstein--Aronszajn determinant is

\[
\frac{\det(B+W_{0,2}-zI)}{\det(B-zI)}
=(1+2m_C(z))(1-2m_S(z))+4m_{CS}(z)m_{SC}(z),
\tag{4.2}
\]

where the three entries are resolvent pairings of \(C_{\rm hyp}\) and
\(S_{\rm hyp}\) against \((B-zI)^{-1}\). For real \(z\) in the resolvent set
of Hermitian \(B\), the last product is \(4|m_{CS}(z)|^2\). If \(B\) preserves parity,
\(C_{\rm hyp}\) is even and \(S_{\rm hyp}\) is odd, then \(m_{CS}=0\) and the
determinant factors. This gives the two sector equations reported in that note,

\[
1+2\langle C_{\rm hyp},(B_e-zI)^{-1}C_{\rm hyp}\rangle=0,
\qquad
1-2\langle S_{\rm hyp},(B_o-zI)^{-1}S_{\rm hyp}\rangle=0.
\tag{4.3}
\]

Equations (4.3) concern a different block resolvent and the hyperbolic pole
vectors. The curvature vector \(c_n=1/(2\pi^2n^2)\), the central coupling \(b\),
and the auxiliary vectors \(c\pm b\) are not identified in CCM or the cited
Silva note with \(C_{\rm hyp}\) or \(S_{\rm hyp}\). Hence (4.3) supplies no
missing value in (3.2). The shared phrase “rank two” is not an algebraic
crosswalk.

## 5. Source audit of the Loewner claim

The structural claim is correct, with a necessary distinction between the
kernel contribution and the signed full matrix.

CCM arXiv:2511.22755, p. 4, equations (2.9)--(2.10), gives for
\(y\in[0,L]\)

\[
q_{nm}(y)=
\begin{cases}
\dfrac{\sin(2\pi my/L)-\sin(2\pi ny/L)}{\pi(n-m)},&n\ne m,\\[6pt]
2(1-y/L)\cos(2\pi ny/L),&n=m.
\end{cases}
\tag{5.1}
\]

For fixed \(y\), define the odd function

\[
\psi_y(t):=\frac1\pi\sin\!\left(2\pi t(1-y/L)\right).
\tag{5.2}
\]

At integer nodes,

\[
\frac{\psi_y(m)-\psi_y(n)}{m-n}=q_{nm}(y),
\qquad
\psi_y'(n)=q_{nn}(y).
\tag{5.3}
\]

The diagonal equality is essential: it uses
\(\cos(2\pi n(1-y/L))=\cos(2\pi ny/L)\). Thus the exact Lean definition
ccmQKernel reproduces the Loewner matrix of \(\psi_y\), including its diagonal,
not merely the off-diagonal divided differences.

CCM p. 16, equations (5.1)--(5.2) and Lemma 5.1, represents the full entry as
the action of the real Weil distribution on \(q_{nm}\). Equivalently, after
including the endpoint atom/distributional term, each pole, archimedean and
finite prime contribution must act linearly on the same kernel family (5.1).
Under this source representation, linearity makes the full matrix the Loewner
matrix of the single odd function

\[
\psi_\mu(t):=\int_0^L\psi_y(t)\,d\mu(y).
\tag{5.4}
\]

This explains the source entries

\[
b_n=-\frac1\pi\int_0^L\sin(2\pi ny/L)\,d\mu(y),
\qquad
a_n=2\int_0^L(1-y/L)\cos(2\pi ny/L)\,d\mu(y):
\]

they are respectively \(\psi_\mu(n)\) and \(\psi_\mu'(n)\).

For the Lean prime builder, ccmPrimeEntryN1 is a finite von-Mangoldt-weighted
sum of ccmQKernel; it is therefore the Loewner matrix of the corresponding
finite sum of the odd functions (5.2). In the full definition
ccmWeilTauN1 = ccmW02Entry - ccmWREntry - ccmPrimeEntryN1, the prime symbol
enters with the final minus sign. This matches the signed Weil decomposition.
The inspected Lean file is explicitly an \(N=1\) literal pilot, so it validates
the formula but is not by itself a theorem for every production dimension.

Every odd differentiable \(\psi\) of this form can be written on the
nonnegative squared-node variable as

\[
\psi(k)=k h(k^2),
\qquad
h(u)=\frac{\psi(\sqrt u)}{\sqrt u}\ (u>0),
\quad h(0)=\psi'(0).
\tag{5.5}
\]

Consequently the parity-sector identities in Silva, Zenodo 20737111, pp. 1--2,
equation (1) and Proposition 1, are algebraically consistent with the CCM
source. That document remains a self-published, non-peer-reviewed
RELAY_UNVERIFIED source; the Loewner statement itself does not need its
authority because (5.2)--(5.4) derive it directly from CCM.

### Decisive diagonal audit

Off-diagonal data alone would not establish the claim: an interpolant matching
only \(\psi(n)=b_n\) need not satisfy \(\psi'(n)=a_n\). The first place a false
Loewner reconstruction would fail is therefore the diagonal, already at
\(n=0\). The canonical source function (5.4) passes that test exactly:

\[
\psi_\mu'(0)=2\int_0^L(1-y/L)\,d\mu(y)=a_0.
\tag{5.6}
\]

So this is an audit checkpoint, not a failure of the canonical
source-faithful construction. The concrete \(h\) printed in Silva has not been
cross-identified term by term with \(\psi_\mu\): SILVA_H_VS_CANONICAL_PSI_MU:
UNTESTED. Its decisive first-cell check is \(\psi'(0)\) against the right-hand
side of (5.6).

### First exact failure of line 2 as an R2 closure

The Loewner identification stops being useful exactly when one asks it to
evaluate

\[
\langle c,(D-\lambda_1I)^{-1}b\rangle.
\]

Neither divided-difference form nor its rank-two displacement relation gives a
closed scalar recurrence for this mixed pairing. Commuting the squared-node
diagonal through the resolvent generates further moments/pairings rather than a
closed equation. Global operator monotonicity of the arithmetic \(h\) is not
established by the checked primary-source formulas, so Loewner's positivity
theorem cannot be imported as a supplier here. The RELAY_UNVERIFIED Silva note
itself describes oscillating arithmetic values and leaves the doubly-critical
finite-node regime open. Therefore the first missing input is an
arithmetic-specific inverse/sign identity for the exact full signed Loewner
matrix, not the Loewner representation itself.

## 6. Diagnostic cross-check, not evidence for closure

The read-only ledger reports at \(m=13\)

\[
\frac1{12}-\Sigma(\lambda_1)
=\frac{a_1}{\xi_0}
=\frac{2\kappa}{L^2}
=0.00787244394607.
\]

It also reports nearly one-signed residues. These observations are compatible
with a Stieltjes/Herglotz route but do not supply the missing cofinal sign law,
closed evaluation, or uniform bound. No numerical claim is scored here.

## 7. Verdict

1. A scalar secular equation with root \(\lambda_1\) exists: (2.1)--(2.2).
   Polarization yields the exact determinantal identity (3.2).
2. Neither equation evaluates the curvature pairing for free. The first line
   fails because \(\lambda_1\) is a root only of the original Schur function,
   not of the two polarized auxiliary Schur functions.
3. The production CCM matrix is source-faithfully a Loewner matrix of one odd
   function, and the diagonal branch of ccmQKernel is exactly what makes that
   statement true rather than an off-diagonal interpolation slogan.
4. The Loewner line first fails as a curvature proof only after that successful
   identification: no source theorem closes the arithmetic mixed resolvent
   pairing, and global operator monotonicity is unavailable in the production
   arithmetic regime.
5. R2 therefore remains open, but its obstruction is narrower: prove an
   arithmetic-specific scalar inverse/sign identity for
   \(\langle c,(D-\lambda_1I)^{-1}b\rangle\), or prove equivalent spectral data
   for the two bordered matrices \(K_\pm\), without estimating the complement
   resolvent norm.

## Sources read

- Connes--Consani--Moscovici, arXiv:2511.22755, p. 4, equations (2.9)--(2.10),
  and pp. 16--17, equations (5.1)--(5.3), Lemmas 5.1--5.2.
- docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md,
  §§3--4.
- docs/routeB_bus/litreview/SURVEY_WALLS_A_B_DELTA_2026-09-03_APPENDIX_LOEWNER.md.
- Silva, Zenodo 20694588, pp. 2--3, equations (1)--(6),
  RELAY_UNVERIFIED, self-published and not peer-reviewed.
- Silva, Zenodo 20737111, pp. 1--3, equation (1), Proposition 1, Theorem 1 and
  Proposition 2, RELAY_UNVERIFIED, self-published and not peer-reviewed.
- q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean, exact
  definitions ccmQKernel, ccmPrimeEntryN1, and ccmWeilTauN1.
- docs/routeB_bus/phase5_scripts/out/edge_ledger_schur.md and
  docs/routeB_bus/phase5_scripts/out/edge_ledger_dualcert.md, diagnostic only.
