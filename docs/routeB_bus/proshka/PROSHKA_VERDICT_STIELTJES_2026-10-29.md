# STATUS: TRY_STIELTJES_UNREDUCED_COFACTOR_POSITIVITY

```yaml
OPERATIVE_CLASS: TRY_STIELTJES_UNREDUCED_COFACTOR_POSITIVITY
REQUEST_ID: REQ-2026-10-29-STIELTJES
BOUNDARY_ID: GOAL058_G1A_ODD_RESOLVENT_SIGN
REQUEST_COMMIT: 87fb6133560e9521876e37fb4cb460b5c09acdd3
REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_STIELTJES_2026-10-29.txt
REQUEST_GIT_BLOB: 7aadb387e2d0efe3922f49acd29cbdd4b939d998
REQUEST_SHA256: fa686400c06b49b14feb798bd99563da440c21ffae8c4045b0279e657eeec2a6
REQUEST_BYTES: 13365
REQUEST_LINES: 217
REQUEST_FINAL_LF: true
REQUEST_HASH_VERIFIED: true
SOURCE_BASE_COMMIT: bac124388928b9e16fae3754ab80f294f5a993ed
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_SELECTED_FERRERS_FAMILY
Q1: G1A_REDUCED_TO_POSITIVE_SIGN
Q1_SIGN: UNREDUCED_COFACTOR_POLYNOMIAL_POSITIVE_ON_CLOSED_EXTERIOR_HALF_LINE
Q1_EQUIVALENT_FINITE_CERTIFICATE: POSITIVE_CONSTANT_AND_NONNEGATIVE_OTHER_COEFFICIENTS_AT_LOWEST_EVEN_ROOT
Q1_FIRST_UNPAID_TERM: COFINAL_SOURCE_LOWER_ENVELOPES_FOR_THESE_COEFFICIENTS
N1: CONFIRMED_WITH_SHARED_EIGENVALUE_ZERO_CASE
N3: RATIONAL_IDENTITY_CONFIRMED_POLE_AND_ZERO_LISTS_REQUIRE_CANCELLATION
N4A: CONFIRMED_WITH_SIMPLE_EVEN_BOTTOM_ODD_SIMPLICITY_NOT_NEEDED
N4B: CONFIRMED
N4C: SUFFICIENT_WITH_SIMPLE_EVEN_BOTTOM_NOT_NECESSARY
N4D: CONFIRMED_FOR_DISTINCT_EVEN_EIGENVALUES
Q2: ALTERNATION_PARTIAL
Q2_FIRST_UNPAID_TERM: SOURCE_LOW_RESIDUE_SIGNS_AND_NEGATIVE_TAIL_DERIVATIVE_BUDGET_PLUS_FIRST_RUNG
Q3: THETA_UNDECIDED
Q3_FIRST_UNPAID_TERM: ZERO_DEPENDENT_SIGN_OR_ROOT_OF_UNREDUCED_COFACTOR_BELOW_EVEN_BOTTOM
G1A_PROVED_COFINAL: false
G1B_REOPENED: false
RH_PROVED: false
PROGRESS_CLASS: FALSIFICATION_PROGRESS
SECONDARY_PROGRESS: REPRESENTATION_PROGRESS
PROGRESS_SCOPE: ABSTRACT_STRUCTURED_CLASS_AND_EXACT_FINITE_CELL_IDENTITIES
ROUTE_SCORE: 4
VERIFIER: PAPER
EXACT_SYMBOLIC_TESTS_EXECUTED: true
NEW_LITERAL_CCM_NUMERICS: false
ARB_INTERVAL_EXECUTED: false
LEAN_EXECUTED: false
REPOSITORY_WRITTEN: false
BROAD_NUMERIC_SCAN: false
ROUTE_PROMOTION: false
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## 0. Adjudication

**Q1 — `G1A_REDUCED_TO_POSITIVE_SIGN`.** The determinant/resolvent identities are correct. They need a cancellation qualification: a common even/odd eigenvalue can disappear from the scalar function. Under a simple even bottom, N4(a)–(c) give valid implications; simplicity cannot silently be discarded. I prove an exact, multiplicity-safe replacement using the **unreduced mixed cofactor**, and a finite positive-coefficient certificate for its exterior sign. This representation avoids even eigenvectors and does not subtract the two nearly equal terms in the lowest-odd-pole residue. **The source-specific cofinal coefficient inequalities remain unproved.**

There are two substantive restrictions on the proposed strategy. A positive lowest weight alone does not settle G1a, even in the exact CCM displacement class. Conversely, positive cumulative weights are **not necessary** for G1a, also within that same structured class. Explicit rational/algebraic examples below establish both points; they are not alternative arithmetic CCM matrices.

**Q2 — `ALTERNATION_PARTIAL`.** I give an explicit low-pole/negative-tail inequality that supplies a partial interlacing ladder once its first rung is established. No literal-source cofinal bound for that inequality is obtained. Exact commutation with an irreducible Jacobi matrix is itself insufficient: the eigenvalue ordering of K in the common basis is an independent obligation. An exact structured counterexample demonstrates this.

**Q3 — `THETA_UNDECIDED`.** No off-critical-zero implication forcing the required parity failure is proved. The first unpaid implication is identified in terms of the unreduced cofactor, including the shared-eigenvalue case. Negative-bottom information and the null plane do not supply its sign.

### 0.1 Transport and verification boundary

The complete request was fetched through the GitHub connector at the specified request commit. The fetched UTF-8 ranges were reassembled, including the final LF, and independently hashed locally:

```text
SHA-256  fa686400c06b49b14feb798bd99563da440c21ffae8c4045b0279e657eeec2a6
Git blob 7aadb387e2d0efe3922f49acd29cbdd4b939d998
bytes    13365
lines    217
final LF yes
```

Both hashes and both counts match the owner’s binding. The source pin is **not** moved to the request commit or current HEAD. The protocol was fetched from `rh_clean`. The locally available PARITYSPLIT attachment was independently matched to its pinned GitHub blob and SHA-256 before use:

```text
Git blob 879af6a3a65c9fd238fc7b51ca715e4613c596d8
SHA-256  055dd4ed51e2c36c86876c5695ed590371f07f825e4e31339824525cc76af33d
```

No Lean toolchain was used, no repository content was changed, and no new literal CCM eigensolve was run. The supplied high-precision tables remain **diagnostics**, not interval certificates. Only bounded exact symbolic checks of the algebra and explicitly synthetic structured matrices were executed. Primary CCM and Connes HTML sources were read directly; no theorem is imported merely because a usage card calls it proved. Sources and read scopes are recorded in §10.

### 0.2 Claim ledger

| ID | Scope / verifier | Result | Limitation |
|---|---|---|---|
| L1 | FINITE_CELL / PAPER | Unreduced cofactor identity, every literal cell, §1 | No sign supplied by the identity |
| L2 | ABSTRACT / PAPER | N1 residue formula and exact N3 cancellation rules, §2 | Simple odd pole required for N1’s displayed product |
| L3 | ABSTRACT / PAPER | Corrected N4 implications, §3 | Simplicity/noncancellation conditions retained |
| L4 | FINITE_CELL / PAPER | Exact positive-coefficient equivalence for G1a, §4 | Coefficients are not proved positive on the literal tail |
| L5 | ABSTRACT / PAPER | Three exact structured counterexamples, §5 | Refute general implications, not the arithmetic family |
| L6 | ABSTRACT / PAPER | Correct cross-Lanczos numerator and remainder, §6 | Diagonal Stieltjes positivity is not transferable |
| L7 | ABSTRACT / PAPER | Exterior and low-gap tail budgets, §§6–7 | Source spectral weights/gaps still unpaid |
| L8 | ABSTRACT / PAPER | Commuting Jacobi counterexample, §7 | Does not exclude a stronger source-specific intertwiner |
| L9 | COFINAL_FAMILY / CONDITIONAL | Cofinal certificate contracts, §§4, 7–8 | None of their missing inequalities is assumed true |

For every literal-source statement: m=N, L=log m, modes −m,…,m, the identity Gram metric, all prime powers through the original cutoff, and the complete archimedean and pole terms are retained. A change of basis is orthogonal unless its determinant/metric factors are explicitly accounted for.

## 1. The computing object: an unreduced mixed cofactor

**[FINITE_CELL | PAPER]** Fix one literal cell, suppress its subscript, and write E and O for the even and odd blocks. Set

\[
 A_n=K_{n,n},\quad b_n=nK_{n,0},\quad b_0=0,
 \qquad B=\operatorname{diag}(1,\ldots,m),
\]
\[
 h=(1,\sqrt2,\ldots,\sqrt2)^T,\quad
 e=(1,0,\ldots,0)^T,\quad J=(0\ B),\quad
 \beta=\sqrt2(b_1,\ldots,b_m)^T.
\]

The pinned source entries and CCM Lemmas 5.1–5.2 give

\[
 K_{n,k}=\frac{b_n-b_k}{n-k}\quad(n\ne k),\qquad
 A_{-n}=A_n,\quad b_{-n}=-b_n,
 \qquad JE-OJ=\beta h^T.                         \tag{1.1}
\]

Here and below, beta denotes the **odd-coordinate** vector, not a spectral floor. The explicit blocks are

\[
\begin{aligned}
 E_{00}&=A_0,& E_{0n}&=\sqrt2 b_n/n,\\
 E_{nn}&=A_n+b_n/n,&O_{nn}&=A_n-b_n/n,\\
 E_{nk}&=\frac{2(nb_n-kb_k)}{n^2-k^2},&
 O_{nk}&=\frac{2(kb_n-nb_k)}{n^2-k^2}\quad(n\ne k).
\end{aligned}                                                     \tag{1.2}
\]

These formulas are source-locked by [S2, S5, P1]; no positivity hypothesis appears in them.

Define the **unreduced** characteristic polynomials and cofactor

\[
 p_E(t)=\det(E-tI),\qquad p_O(t)=\det(O-tI),\qquad
 \chi(t)=h^T\operatorname{adj}(E-tI)e.              \tag{1.3}
\]

Then the exact polynomial identity is

\[
 \boxed{\chi(t)=p_O(t)\quad\text{for every real or complex }t.}       \tag{1.4}
\]

### Proof, including the coordinate factors

Let d=B⁻¹(√2,…,√2)ᵀ. Replace the even input x by s=hᵀx and y=Jx. Then x₀=s−dᵀy and x_tail=B⁻¹y. Replace the output z by (z₀,Jz). The transformed matrix of E−tI is

\[
 \begin{pmatrix}
 A_0-t&\beta^TB^{-2}-(A_0-t)d^T\\
 \beta&O-tI
 \end{pmatrix}.                                    \tag{1.5}
\]

The input substitution has determinant det(B)⁻¹ and the output map has determinant det(B); they cancel. Thus, away from the odd spectrum,

\[
 p_E(t)=p_O(t)f(t),\qquad
 f(t)=A_0-t+\big((A_0-t)d-B^{-2}\beta\big)^T(O-tI)^{-1}\beta.
                                                               \tag{1.6}
\]

For (E−tI)x=e, the transformed right-hand side is (1,0). Its solution has s=1/f(t). Since s=hᵀx,

\[
 g(t):=h^T(E-tI)^{-1}e=\frac1{f(t)}=\frac{p_O(t)}{p_E(t)}.          \tag{1.7}
\]

Multiplying by p_E(t) and using the adjugate formula proves (1.4) first on the common resolvent set, then everywhere by polynomial identity. This is a PAPER proof for all sizes, not an extrapolation from the numerical checks.

The full-coordinate expression ⟨eta,(K−tI)⁻¹e₀⟩ agrees wherever the full inverse exists. At an odd eigenvalue not in the even spectrum, the full inverse does not exist, but its **even-block scalar continuation** g is well-defined and zero. That distinction matters when calling an odd eigenvalue a zero of a resolvent element.

## 2. Q1(a): N1 and N3, with all exceptional cases

### 2.1 N1: the lowest-odd-pole coefficient

**[ABSTRACT | PAPER]** Suppose mu is a simple odd bottom, with unit eigenvector y, and let mu₂,…,mu_m be the other odd eigenvalues, counted with multiplicity. From (1.6),

\[
 \mathcal R=\lim_{t\uparrow\mu}(\mu-t)f(t)
 =\frac{p_E(\mu)}{\prod_{j=2}^{m}(\mu_j-\mu)}
 =\frac{\prod_{i=0}^{m}(\lambda_i-\mu)}
        {\prod_{j=2}^{m}(\mu_j-\mu)}.               \tag{2.1}
\]

This equals the displayed (v₀ᵀy)(yᵀbeta). The denominator is positive. Therefore

\[
 \operatorname{sgn}\mathcal R=(-1)^{\#\{i:\lambda_i<\mu\}}
 \quad\textbf{provided }\mu\notin\operatorname{spec}(E).           \tag{2.2}
\]

If an even eigenvalue equals mu, **R=0**; (2.2) without this exception is false. The coefficient R multiplies 1/(mu−t); the complex-analytic residue with denominator t−mu has the opposite sign.

The count interpretation is correct. It establishes neither necessity of R<0 for G1a nor an impossibility of finding a cheaper source identity for its sign. Logical equivalence to a count does not by itself establish computational cost. I do not reuse the cancellation-prone subtraction in N2 as an estimate.

For a multiple odd bottom, the simple-pole product formula as written does not apply. One must retain multiplicities in p_O and the full bottom spectral projector in (1.6).

### 2.2 N3: signed measure, not automatically a positive Stieltjes function

**[ABSTRACT | PAPER]** For an orthonormal even eigenbasis,

\[
 g(t)=\sum_i\frac{w_i}{\lambda_i-t},\qquad
 w_i=(h^T\xi_i)\xi_i(0),\qquad \sum_iw_i=h^Te=1.                 \tag{2.3}
\]

For a repeated eigenvalue lambda, the invariant weight is

\[
 w(\lambda)=h^TP_\lambda e,                                    \tag{2.4}
\]

not its basis-dependent decomposition into individual eigenvectors. This is a Cauchy/Stieltjes transform of a **signed** finite measure. Positivity of E or self-adjointness of K does not make its cross weights nonnegative.

If a has multiplicity r_E in E and r_O in O, then

\[
 \operatorname{ord}_{t=a}g=r_O-r_E.                             \tag{2.5}
\]

Thus an uncancelled even eigenvalue is a pole, an uncancelled odd eigenvalue is a zero, and common factors cancel. A scalar resolvent has only simple poles, so r_E−r_O≤1. This restriction is a consequence of the source identity, not an assumption about spectral simplicity.

**The sentence “its poles are the even eigenvalues; its zeros are the odd eigenvalues” is valid only after these cancellations have been accounted for.** A zero below the lowest even eigenvalue cannot be cancelled, since p_E has no root there. A common bottom, however, can be invisible in g. The unreduced cofactor (1.4) retains it.

N2 and N5’s numerical precision agreements were not re-executed. The relevant script and representative raw rows were read [S4, S6]. Neither finite precision agreement nor the observed negative-mass total is used as a cofinal premise.

## 3. Q1(a–b): corrected N4 and the first exact endpoint sign

### 3.1 The strict parity inequality supplies simplicity

**[ABSTRACT | PAPER]** Let lambda=λ_min(E), mu=λ_min(O). If lambda<mu and Ex=lambda x, hᵀx=0, then (1.1) gives

\[
 (O-\lambda I)Jx=0.
\]

Hence Jx=0. Its kernel is the central coordinate line, and h does not annihilate a nonzero vector on that line. Thus x=0. The h-functional is injective on the even eigenspace at lambda, which must consequently be one-dimensional. It follows that

\[
 \boxed{\mathrm{G1a}\ \Longleftrightarrow\ \lambda<\mu.}           \tag{3.1}
\]

No sign of lambda is used. The strict ordering gives a simple full bottom and nonzero eta-pairing; equality would create a full-space degeneracy.

### 3.2 N4(a) and (b)

**[ABSTRACT | PAPER]** Assume the lowest even eigenvalue lambda is simple. Then

\[
 w_0=\lim_{t\uparrow\lambda}(\lambda-t)g(t)
     =\frac{p_O(\lambda)}{\prod_{i=1}^{m}(\lambda_i-\lambda)}.     \tag{3.2}
\]

The denominator is strictly positive. Since g(t)=−1/t+O(t⁻²) as t→−∞,

\[
 \boxed{\mathrm{G1a}\ \Longleftrightarrow\
 w_0>0\ \text{and}\ g(t)\ne0\ \text{for every }t<\lambda.}       \tag{3.3}
\]

Indeed, absence of zeros excludes every odd eigenvalue strictly below lambda. The positive residue excludes an odd eigenvalue at lambda. Conversely, strict parity ordering makes p_O(lambda)>0 and g positive throughout that exterior interval.

The “no zero” condition in (3.3) is equivalent to g>0 there, by continuity and the sign at −∞. **Odd-bottom simplicity is unnecessary.** Even-bottom simplicity, or an equivalent noncancellation certificate, is not optional. Under G1a, w₀>0 proves that the ground central coefficient is nonzero and has the same sign as its eta-pairing.

### 3.3 N4(c): the Abel implication and its precise strength

**[ABSTRACT | PAPER]** For strictly ordered even eigenvalues, put W_k=Σ_{i≤k}w_i and x_i(t)=1/(lambda_i−t). For t<lambda₀,

\[
 g(t)=\sum_{k=0}^{m-1}W_k\big(x_k(t)-x_{k+1}(t)\big)+W_mx_m(t).
                                                               \tag{3.4}
\]

Every displayed kernel is positive and W_m=1. Therefore the weaker hypotheses

\[
 W_0>0,\qquad W_k\ge0\ (1\le k<m)                              \tag{3.5}
\]

suffice for G1a, provided the lowest even eigenvalue is simple. The request’s strict inequalities imply these. With degeneracies, group weights by full eigenspaces, and still retain a simple lowest even eigenvalue. A projector onto “the lowest k+1 levels” is canonical only when its cutoff does not split a multiple eigenspace.

The condition is **sufficient, not necessary**. Section 5.2 gives a matrix satisfying the exact displacement identity, with G1a and W₁<0. Without the simple-bottom qualification, even W_k>0 for every k can coexist with a degenerate ground state; see §5.3.

### 3.4 N4(d): global interlacing

**[ABSTRACT | PAPER]** If all even eigenvalues are distinct and all w_i>0, then

\[
 g'(t)=\sum_i\frac{w_i}{(\lambda_i-t)^2}>0.                       \tag{3.6}
\]

On (lambda_i,lambda_{i+1}), g runs from −∞ to +∞ and has exactly one zero. It has no zero outside the extreme even eigenvalues. Since p_O has degree m, this proves the strict complete interlacing in N4(d), including simplicity of all odd eigenvalues.

If even eigenvalues repeat, this statement concerns only the distinct visible poles after cancellation; strict interlacing of the full spectra does not follow. Positive individual weights in a chosen basis do not repair that defect. For instance, E=cI₂, O=(c), with an even eigenbasis rotated through −π/6, has weights (3−√6)/4 and (1+√6)/4, both positive, but all three full eigenvalues equal c. This is the m=1 structured matrix K=cI₃.

### 3.5 Q1(b): an eigenvector-free endpoint sign

**[FINITE_CELL | PAPER]** At a simple lowest even eigenvalue,

\[
 \boxed{w_0=\frac{\chi(\lambda)}{\operatorname{tr}\operatorname{adj}(E-\lambda I)}.}
                                                               \tag{3.7}
\]

The denominator is the product of the positive remaining even gaps. Hence the exact source sign required for w₀>0 is

\[
 \boxed{h^T\operatorname{adj}(E-\lambda I)e
       =\det(O-\lambda I)>0.}                                  \tag{3.8}
\]

This is not a proof of (3.8) on the original tail. Its first unpaid input is an actual source lower envelope for this cofactor at the lowest even root. The dependence on lambda must be enclosed rather than replaced by a floating-point eigenvalue.

At a multiple lowest even eigenvalue the adjugate vanishes. Thus a positive lower bound in (3.8) would itself rule out that multiplicity, without assuming simplicity. But (3.8) **alone** does not rule out an even number of odd levels below lambda. Section 5.1 makes this obstruction exact.

## 4. Q1(c–d): an exact positive representation, without a hidden simple-bottom premise

### 4.1 Retain the polynomial, not only the reduced scalar function

**[FINITE_CELL | PAPER]** Put lambda=λ_min(E), without any simplicity assumption, and define

\[
 P(x)=\chi(\lambda-x)=\det(O-\lambda I+xI)
     =\sum_{k=0}^{m}c_kx^k,\qquad c_m=1.                         \tag{4.1}
\]

Every root of P is real, because O is symmetric. The following are equivalent:

\[
\begin{aligned}
 &\mathrm{G1a};\\
 &P(x)>0\quad\text{for every }x\ge0;\\
 &c_0>0\quad\text{and }c_k\ge0\quad(1\le k<m);\\
 &c_k>0\quad(0\le k\le m).
\end{aligned}                                                   \tag{4.2}
\]

**Proof.** If G1a holds, each d_j=mu_j−lambda is positive, and P(x)=∏_j(x+d_j) has strictly positive coefficients. Conversely, nonnegative coefficients and a positive constant imply P(x)>0 for x≥0. A nonpositive d_j would give a root x=−d_j≥0, impossible. Finally, positivity of P on the entire closed half-line excludes all such roots and gives mu>lambda, so (3.1) supplies simplicity and eta-normalization. This proves every direction, including the degenerate cases.

On x>0,

\[
 \boxed{g(\lambda-x)=
 \frac{\displaystyle\sum_{k=0}^{m}c_kx^k}
      {\displaystyle\det(E-\lambda I+xI)}.}                    \tag{4.3}
\]

The denominator is positive. Once the coefficient signs in (4.2) are supplied, (4.3) is literally a sum of positive/nonnegative terms, not a subtraction of nearly equal lowest-pole contributions. The endpoint c₀ is retained: discarding it would lose the common-ground-eigenvalue case.

This criterion is **exact**, whereas the Abel cone is only sufficient. It closes the logical continuum-to-finite-sign reduction at every size. It does **not** establish those signs for the literal family, and it does not claim that coefficient computation is automatically well-conditioned.

### 4.2 The coefficients are source quantities

**[FINITE_CELL | PAPER]** They have either of the exact descriptions

\[
 c_k=\frac{(-1)^k}{k!}\chi^{(k)}(\lambda)
     =e_{m-k}(O-\lambda I),                                    \tag{4.4}
\]

where e_r is the sum of all r-by-r principal minors, with e₀=1. Equivalently, if A=O−lambda I and e₀(A)=1,

\[
 r e_r(A)=\sum_{j=1}^{r}(-1)^{j-1}e_{r-j}(A)\operatorname{tr}(A^j).
                                                               \tag{4.5}
\]

Thus only the literal matrix entries and a certified lowest even root are needed; even eigenvectors and their phase choices are not. Formula (4.5) is an algebraic computation rule, **not** a positive-sign proof: its alternating terms can cancel. No numerical estimate obtained by subtracting unresolved near-equal quantities is accepted here.

The units are explicit: c_k has spectral-energy degree m−k. For a dimensionless ledger one may use c_k/s_m^(m−k), where s_m=1+||E_m||_F+||O_m||_F is source-defined and positive. This rescaling changes no sign and supplies no margin.

**First unpaid term:** on every sufficiently late original cell, prove lower envelopes for c₀ and c₁,…,c_{m−1} with the directions in (4.2), retaining all growing dimensions and the uncertainty in lambda. Neither the table’s w₀ nor its minimum cumulative weight supplies this theorem. In particular, c₀>0 is only the first sign, not the whole certificate.

### 4.3 A root-free sufficient certificate suitable for source bounds

**[COFINAL_FAMILY | CONDITIONAL]** One can avoid solving for lambda entirely by producing source-defined real tau_m such that

\[
 p_{E_m}(\tau_m)\le-\kappa_m<0,\qquad
 \det(O_m-\tau_mI+xI)=\sum_{k=0}^{m}d_{m,k}x^k,
                                                               \tag{4.6}
\]
\[
 d_{m,0}\ge\varepsilon_m>0,\qquad d_{m,k}\ge0\quad(1\le k<m).
                                                               \tag{4.7}
\]

The odd polynomial has no nonnegative root, so every odd eigenvalue exceeds tau_m. The negative even determinant guarantees at least one even eigenvalue below tau_m. Consequently lambda_min(E_m)<tau_m<lambda_min(O_m), and G1a follows. All margins may shrink; no polynomial or constant gap is assumed.

Conversely, if G1a holds, choose tau strictly between the even bottom and the smaller of the next even eigenvalue and the odd bottom. The bottom is simple by (3.1), so exactly one factor of p_E(tau) is negative, and (4.6)–(4.7) hold. Thus **existence** of such a certificate is an exact interface for G1a, although a particular proposed tau can fail.

A negative coefficient at a poorly chosen tau only rejects that proposed bracket. It does not refute G1a. At the exact lowest even root, however, (4.2) is an equivalence. In either setting, finite-cell certification would remain finite-cell certification.

### 4.4 What this does and does not improve

**[ABSTRACT | PAPER]** The change is from a reduced signed spectral measure to an **unreduced real-rooted cofactor polynomial**. It preserves common eigenvalues, replaces a continuum exterior-positivity test by finitely many coefficient signs, and removes the unnecessary demand that all spectral prefixes be positive. It does not remove the arithmetic sign difficulty. Calling the coefficients positive without a supplier would simply assume G1a in another notation.

This is the selected positive representation. The two alternative coordinates in §6 remain useful for locating a supplier or falsifying an overly strong one; neither is elevated to a theorem about the literal tail.

## 5. Exact adversarial plants: what the structural hypotheses do not imply

All matrices in this section are **synthetic members of the exact displacement class** (1.1)–(1.2), not replacements for the arithmetic CCM source. Their role is to refute structural shortcuts. No counterexample to the eventual literal G1a is asserted.

### 5.1 A positive lowest weight can coexist with two odd levels below the even bottom

**[ABSTRACT | PAPER]** Take m=2 and

\[
 A_0=4,\quad A_1=A_2=0,\quad b_1=b_2=1.
\]

Then

\[
 E=\begin{pmatrix}4&\sqrt2&1/\sqrt2\\
 \sqrt2&1&2/3\\1/\sqrt2&2/3&1/2\end{pmatrix},\qquad
 O=-C,\quad C=\begin{pmatrix}1&2/3\\2/3&1/2\end{pmatrix}.
                                                               \tag{5.1}
\]

C is positive definite because its leading entry is 1 and det C=1/18. With u=(√2,1/√2)ᵀ, uᵀC⁻¹u=3, so the Schur complement of C in E is 4−3=1>0. Therefore E≻0 and O≺0. The even characteristic polynomial is

\[
 p_E(t)=-t^3+\frac{11}{2}t^2-\frac{32}{9}t+\frac1{18},\qquad
 p_O(t)=t^2+\frac32t+\frac1{18}.                                \tag{5.2}
\]

Its discriminant is 269909/1458>0, so the even eigenvalues are distinct. At lambda=λ_min(E)>0, p_O(lambda)>0 and (3.2) gives w₀>0. Nevertheless both odd eigenvalues are below lambda, so G1a fails and g has two zeros on the exterior interval.

The coefficient certificate pinpoints the missing sign:

\[
 P(x)=x^2-(3/2+2\lambda)x+
       \big(\lambda^2+(3/2)\lambda+1/18\big).                   \tag{5.3}
\]

Its constant is positive but its linear coefficient is negative. This is an exact obstruction to a **w₀-only** or **endpoint-cofactor-only** inference.

### 5.2 G1a does not require positive cumulative weights

**[ABSTRACT | PAPER]** Keep A₁=A₂=0 and b₁=b₂=1, but set A₀=−2/3. Then

\[
 p_E(t)=-\frac{54t^3-45t^2-186t+11}{54},\qquad
 p_O(t)=\frac{18t^2+27t+1}{18}.                                \tag{5.4}
\]

Exact opposite signs at the rational endpoints isolate the three even roots respectively in

\[
 (-153/100,-151/100),\quad(1/20,3/50),\quad(229/100,23/10).
                                                               \tag{5.5}
\]

The cubic has exactly three roots, so these are exhaustive, distinct brackets. The odd bottom is

\[
 \mu_1=-3/4-\sqrt{73}/12>-3/2,
\]

whereas the even bottom is below −151/100. Thus G1a holds strictly.

For the top even root r, its residue is w₂=−p_O(r)/p_E′(r), and

\[
 -p_O(t)-p_E'(t)=\frac{(3t-7)(4t+3)}6.                          \tag{5.6}
\]

At r∈(229/100,23/10), the right side is negative because r<7/3, and p_E′(r)<0. Therefore w₂−1>0, giving

\[
 \boxed{W_1=1-w_2<0\quad\text{while G1a holds}.}                \tag{5.7}
\]

This refutes necessity of the Abel condition **within the same exact structured class**, not merely among arbitrary signed rational functions.

### 5.3 A reduced resolvent can hide a degenerate bottom

**[ABSTRACT | PAPER]** Take b₁=b₂=0 and A₀=A₁=0, A₂=1. Then

\[
 E=\operatorname{diag}(0,0,1),\qquad O=\operatorname{diag}(0,1),
 \qquad g(t)=-1/t.                                             \tag{5.8}
\]

In the displayed even eigenbasis, the weights are (1,0,0) and every cumulative weight is 1. The grouped lowest spectral weight is also 1, and g is positive on (−∞,0). Yet the full bottom is degenerate, so G1a is false. The polynomial cofactor is p_O(t)=(−t)(1−t), and c₀=0 correctly detects the failure.

This is the necessary qualification to N4(c), and to any extension of N4(a) that omits its stated simple-even-bottom assumption. It does not refute N4(a) with that assumption retained.

### 5.4 Scope and evidence of these refutations

| Refuted implication | KILL_SCOPE | Evidence kind / exact reference | Surviving statement |
|---|---|---|---|
| w₀>0 alone implies G1a | THEOREM_SHAPE | Exact structured matrix (5.1) | Add exterior zero exclusion and simple-bottom/noncancellation control |
| G1a requires all W_k>0 | THEOREM_SHAPE | Exact structured matrix (5.4)–(5.7) | Abel positivity is sufficient, not necessary |
| Positive cumulative weights prove G1a without a simple-bottom condition | THEOREM_SHAPE | Exact structured matrix (5.8) | Retain simplicity or use the unreduced criterion (4.2) |

For these implications the failure type is COUNTEREXAMPLE and their exact shapes are MATHEMATICALLY_DEAD. The literal arithmetic family and the larger route are **not** classified that way.

## 6. Moments, Lanczos, and the negative upper spectral mass

### 6.1 Source moments do not become positive merely because E is self-adjoint

**[ABSTRACT | PAPER]** Outside a sufficiently large spectral circle,

\[
 g(t)=-\sum_{j=0}^{\infty}\frac{h^TE^je}{t^{j+1}}.              \tag{6.1}
\]

The moments nu_j=hᵀEʲe are the correct moments. Replacing them by eᵀEʲe or hᵀEʲh changes the object to a diagonal resolvent, whose spectral weights are squares. That substitution discards precisely the cross sign under investigation.

Likewise, choose M≥λ_max(E). For t<lambda₀,

\[
 g(t)=\sum_{j=0}^{\infty}
 \frac{h^T(MI-E)^je}{(M-t)^{j+1}}.                              \tag{6.2}
\]

Nonnegativity of every numerator would be sufficient for exterior positivity, but it is a new signed-moment obligation, not a consequence of MI−E≽0. It also does not, by itself, restore a cancelled common bottom. The detector in §5.3 still applies.

### 6.2 The exact single-ended Lanczos formula retains a signed numerator

**[ABSTRACT | PAPER]** Run exact symmetric Lanczos from q₁=e on its cyclic subspace C=span{Eʲe}. Write Q=(q₁,…,q_r), T=QᵀEQ, with positive off-diagonal Lanczos coefficients beta_j until termination, and a=Qᵀh. Let D_j(t) be the determinant of the trailing principal submatrix T[j:r,j:r]−tI, with D_{r+1}=1. Then

\[
 \boxed{
 g(t)=\frac{\displaystyle\sum_{j=1}^{r}
 a_j(-1)^{j-1}\Big(\prod_{i=1}^{j-1}\beta_i\Big)D_{j+1}(t)}
 {D_1(t)}.}                                                    \tag{6.3}
\]

For t below the bottom of T, all D_j(t)>0. Thus the signed coefficients (−1)^(j−1)a_j matter. A positive continued fraction for the **diagonal** entry (T−t)⁻¹₁₁ is not a positive continued fraction for g. Starting at h instead does not remove this two-endpoint issue.

If C is proper, then

\[
 p_O(t)=\det(E|_{C^\perp}-tI)\,N(t),                            \tag{6.4}
\]

where N is the numerator in (6.3). The omitted factor is exactly an invisible even/odd common factor. Full cyclicity cannot be inferred from finitely many successful runs, and a visible-subspace certificate cannot ignore a lower eigenvalue in C-perp.

For a k-step truncation, with residual beta_k q_{k+1}e_kᵀ and Q_kᵀEQ_k=T_k,

\[
 |g(t)-h^TQ_k(T_k-tI)^{-1}e_1|
 \le\frac{\|h\|\beta_k
 |e_k^T(T_k-tI)^{-1}e_1|}{\lambda_0(E)-t}.                       \tag{6.5}
\]

This follows directly by applying (E−t)⁻¹ to the Lanczos residual equation. The denominator must be paid near the lowest even pole. A short continued fraction without this tail budget is not a sign certificate.

### 6.3 A small negative mass at high energies needs an actual inequality

**[ABSTRACT | PAPER]** Suppose a retained head has all remaining negative weights at eigenvalues at least b>lambda₀, and let nu_- be the total absolute negative tail mass. Then, for t<lambda₀,

\[
 g(t)\ge g_{\rm head}(t)-\frac{\nu_-}{b-t},                      \tag{6.6}
\]

where positive tail weights have only been omitted in a lower bound. A sufficient source budget is therefore

\[
 (b-t)g_{\rm head}(t)>\nu_-\quad\text{for every }t<\lambda_0.    \tag{6.7}
\]

The table supplies neither an eventual b nor an eventual bound for nu_-, and it does not pay (6.7). A negative mass such as 0.048 is not automatically negligible relative to a lowest weight as small as those listed.

There is an unconditional algebraic bound

\[
 \sum_i|w_i|\le\|h\|\|e\|=\sqrt{2m+1},\qquad
 \nu_-\le\frac{\sqrt{2m+1}-1}{2},                              \tag{6.8}
\]

by Cauchy–Schwarz. It grows with m and is not the empirically small-mass theorem the proposal would need.

### 6.4 A positive lowest weight controls the near-pole end, not the entire exterior interval

**[ABSTRACT | PAPER]** Assume a simple even bottom, w₀>0, and let d₁=lambda₁−lambda₀>0. Put A=E−lambda₀I and B₁=||h||·||Ae||. With x=lambda₀−t>0,

\[
 g(\lambda_0-x)\ge \frac{w_0}{x}-\frac{\nu_-}{d_1},             \tag{6.9}
\]
\[
 g(\lambda_0-x)\ge\frac1x-\frac{B_1}{x^2}.                    \tag{6.10}
\]

For (6.10), use (A+xI)⁻¹=x⁻¹I−x⁻¹A(A+xI)⁻¹ and ||(A+xI)⁻¹||≤1/x. Consequently g is positive for

\[
 0<x\le\frac{w_0d_1}{2\nu_-}\quad(\nu_->0),
 \qquad x\ge2B_1,                                             \tag{6.11}
\]

with the zero-negative-mass case immediate. Any remaining zeros must lie in the intervening compact interval. This is a useful discriminator, but the scales themselves need certified source bounds. The structured plant (5.1) shows why the middle interval cannot simply be discarded.

These representations answer the suggested moment, continued-fraction, and high-negative-mass branches without granting them an unpaid positivity theorem.

## 7. Q2: a conditional low-spectrum ladder, and the missing source estimate

### 7.1 A precise mechanism using the scalar function itself

**[ABSTRACT | PAPER]** Assume G1a has supplied the first rung and the even poles in a proposed low range are distinct. Consider two adjacent even poles lambda_i<lambda_{i+1} with w_i,w_{i+1}>0. Suppose all negative weights are supported at energies at least b>lambda_{i+1}, with total absolute mass nu_-. Then throughout that open gap,

\[
 g'(t)\ge
 \frac{w_i}{(t-\lambda_i)^2}
 +\frac{w_{i+1}}{(\lambda_{i+1}-t)^2}
 -\frac{\nu_-}{(b-t)^2}.                                      \tag{7.1}
\]

Minimizing the two positive terms and bounding the negative term gives the explicit sufficient budget

\[
 \boxed{
 \frac{(w_i^{1/3}+w_{i+1}^{1/3})^3}
      {(\lambda_{i+1}-\lambda_i)^2}
 >\frac{\nu_-}{(b-\lambda_{i+1})^2}.}                           \tag{7.2}
\]

Under (7.2), g′>0 in the gap. Its endpoint limits are −∞ and +∞, so it has exactly one, simple zero there, hence exactly one odd eigenvalue. Applying this to successive low gaps gives a strict **partial** parity ladder while allowing negative residues and nonalternation higher up.

This is the requested type of mechanism, with exact orders: positive low-residue mass divided by the square of a low even gap must dominate negative tail mass divided by the square of its distance from that gap. It is **not yet a theorem for the literal tail**. The source suppliers for the low weight signs, negative-support threshold b, mass nu_-, and the comparison (7.2) remain unpaid. The first rung, exterior positivity including the endpoint condition, is also not supplied by this derivative argument.

Positive adjacent residues alone guarantee at least one odd zero between them, not necessarily exactly one: other signed weights can add roots unless a derivative or counting budget is paid. Two odd eigenvalues below the first even pole are also compatible with w₀>0, as (5.1) showed.

**Q2 code: `ALTERNATION_PARTIAL`.** Equation (7.2) is the first explicit unpaid tail budget for this route. It answers how a top defect could be harmless, rather than assuming that it is harmless because it is high in the spectrum.

### 7.2 The prolate import does not identify the needed operator

**[FINITE_CELL | PAPER: source audit]** The pinned Lean statement `finiteFourierAction_intertwines_prolateWaveExpression` concerns the continuous finite-Fourier integral action and a prolate differential expression on globally C² test functions; its boundary cancellation uses the vanishing endpoint factor. It does not assert [J_m,K_m]=0 for the arithmetic finite Weil matrix [S8, lines 512–544]. No Lean execution is claimed.

The primary Connes text separately states the prolate spectral property in Fact 6.3 and leaves simple-evenness for the Weil operator as a remaining step in §6.6 [P2]. It supplies no missing finite-K intertwiner. These are different operators, not two names for the same spectral problem.

### 7.3 Even exact Jacobi commutation does not order the eigenvalues of K

**[ABSTRACT | PAPER]** In the full mode order −1,0,1, take

\[
 K=\begin{pmatrix}0&1&1\\1&4&1\\1&1&0\end{pmatrix},\qquad
 T=\begin{pmatrix}1&1&0\\1&4&1\\0&1&1\end{pmatrix}.              \tag{7.3}
\]

K has the exact structured data A₀=4, A₁=0, b₁=1. T is irreducible, real symmetric, centrosymmetric and tridiagonal. They commute exactly: K=T−2P_odd. The even block of K is

\[
 \begin{pmatrix}4&\sqrt2\\\sqrt2&1\end{pmatrix}\succ0,
\]

while its odd eigenvalue is −1. Thus the ground state of K is odd despite exact commutation with a genuine Jacobi matrix. In the common eigenbasis, the odd eigenvalue has been moved below the even ones.

**Refuted theorem shape:** exact Jacobi commutation plus the source displacement/parity structure implies G1a. `KILL_SCOPE: THEOREM_SHAPE`; `FAILURE_TYPE: COUNTEREXAMPLE`; exact evidence (7.3). A source-specific monotonicity law for K’s eigenvalues in that basis could still repair the route.

The failure of a commutation-only implication is not restricted to small dimension. For every m, let T be the path-graph Laplacian on 2m+1 vertices (diagonal entries 1 at the endpoints, 2 inside, nearest-neighbor entries −1). It is irreducible, centrosymmetric and Jacobi, and T eta=0. For c>0,

\[
 K=aI+c\eta\eta^T,\qquad A_n=a+c,\quad b_n=cn
\]

is in the exact displacement class and commutes with T, yet its bottom a has multiplicity 2m and contains the entire odd sector. This is a cofinal synthetic structured obstruction to the bare commutation implication, not an arithmetic CCM counterfamily.

For an approximate version, let a proposed symmetric J have simple eigenvalues theta_i and orthonormal eigenvectors v_i. Put k_i=v_iᵀKv_i, and let d_J=min_{i≠j}|theta_i−theta_j|. Then

\[
 \|K-\sum_i k_iv_iv_i^T\|
 \le\|K-\sum_i k_iv_iv_i^T\|_F
 \le\frac{\|[J,K]\|_F}{d_J}.                                  \tag{7.4}
\]

Thus a spectral-order margin must dominate twice this error. Small commutator norm alone is insufficient, even when the commutator is exactly zero. On shrinking CCM gaps, a merely polynomially small error is not automatically usable; no cofinal gap order is inferred from the table.

### 7.4 Window edges and sign-change counts

**[ABSTRACT | PAPER]** For a low/high decomposition,

\[
 K-tI=\begin{pmatrix}L-tI&B\\B^T&H-tI\end{pmatrix},\qquad
 H-tI\succeq\gamma I>0,
\]

elimination produces L−tI−B(H−tI)⁻¹Bᵀ, with correction norm at most ||B||²/gamma. A high-band defect can be ignored only after this correction, or the resolvent-tail alternative (7.2), is dominated by a source lower margin. The data do not establish such a bound or identify the failure as a window-edge effect.

Mode-coordinate sign changes are not invariant spectral data. The gauge x_n↦(−1)^n x_n preserves reflection parity and all eigenvalues; it cannot repair a parity ordering failure. It also leaves positive even-distance entries positive. For a matrix with a positive triangle of off-diagonal entries, no ±1 diagonal gauge can make all three edges negative, since the triangle product is gauge-invariant. The observed oscillation counts therefore do not by themselves identify a Sturm operator in these coordinates.

## 8. Q3: the exact Theta interface, and what is still missing

**[FINITE_CELL | PAPER]** The multiplicity-safe failure condition is

\[
 \boxed{\neg\mathrm{G1a}\ \Longleftrightarrow\
 \exists t\le\lambda_{\min}(E):\ \chi(t)=0.}                    \tag{8.1}
\]

This follows from chi=p_O and (3.1). With a simple even bottom, it can be rephrased by the corrected N4(a): nonpositive w₀ or a zero of g strictly below the even bottom. Without that simplicity condition, a common bottom may cancel while the grouped lowest residue remains positive; the request’s scalar alternative must then be augmented as in (8.1).

**[COFINAL_FAMILY | CONDITIONAL]** A Theta-witness for the literal family would require the following new implication, not a reformulation assumed as an input:

\[
 \zeta(1/2+\delta+i\gamma)=0,\quad\delta>0
 \ \Longrightarrow\
 \text{infinitely many original }m\text{ admit }t_m\le\lambda_m
 \text{ with }\chi_m(t_m)=0.                                   \tag{8.2}
\]

No derivation of (8.2) is obtained here. Nor is a zero-independent proof of the opposite eventual statement obtained. The first unpaid step is a zero-dependent control of this **parity-resolved characteristic cofactor**, or of the signed exterior resolvent with its noncancellation condition—not merely a bound for the full minimum of K.

### 8.1 Why negative-bottom growth does not supply it

**[ABSTRACT | PAPER]** Scalar shifts leave all relevant parity data unchanged:

\[
 K\mapsto K-MI,\quad g(t)\mapsto g(t+M),\quad
 \lambda\mapsto\lambda-M,\quad\mu\mapsto\mu-M,
\]

and leave all weights, reflection, and the displacement identity unchanged. More explicitly, for every carrier size take b_n=0, A₀=0, A_n=1 for n≠0, then subtract M_mI. The full ground is simple, central and even, with nonzero eta-pairing, while its eigenvalue is −M_m. One may choose M_m=m^delta/(log m)^(2delta).

This is a cofinal **synthetic structured counterfamily to the inference from negative-bottom growth to parity failure**. It is not the arithmetic CCM family and does not prove `G1A_NOT_THETA_GRADED`.

### 8.2 Pole and null-plane links: exact algebra, unpaid sign

**[FINITE_CELL | PAPER]** From the literal pole entry define

\[
 u_n=\frac{L}{L^2+16\pi^2n^2},\qquad
 v_n=\frac{4\pi n}{L^2+16\pi^2n^2},\qquad
 \kappa=32L\sinh^2(L/4).
\]

Then W₀,₂=kappa(uuᵀ−vvᵀ). On the even block E=H_E+kappa u_Eu_Eᵀ, where H_E is the retained archimedean-plus-prime contribution with its actual sign. Where the displayed inverses and denominator exist, Woodbury gives

\[
 g(t)=h^TR_He-
 \frac{\kappa\,(h^TR_Hu_E)(u_E^TR_He)}
      {1+\kappa u_E^TR_Hu_E},\qquad R_H=(H_E-tI)^{-1}.           \tag{8.3}
\]

This identity does not give a sign: the domain, denominator, and cross terms all remain to be controlled. The pole vector u is not eta.

The shelf’s null-plane construction concerns vectors annihilated by the global Weil form and their controlled finite projections [S2; the earlier analytic suppliers remain at their stated scope]. It gives no identity forcing the boundary-central resolvent cofactor to vanish, and no ordering of the deepest even and odd levels. I do not import its zero-location-independent smallness as a Theta witness.

**Q3 code: `THETA_UNDECIDED`.** A failure to derive (8.2) is RESEARCH_DEBT, not a proof that such a mechanism cannot exist.

## 9. Dependency audit, route choice, and predictions

### 9.1 Consumer-first contract

**[ABSTRACT | PAPER]**

```yaml
DOWNSTREAM_CONSUMER: G2_REAL_ZEROS_FOR_THE_SAME_GROUND_FAMILY
ACTUAL_CONSUMER_REQUIREMENT: SIMPLE_EVEN_BOTTOM_WITH_NONZERO_ETA_PAIRING
EXACT_SOURCE_INTERFACE: lambda_min(E_m) < lambda_min(O_m) EVENTUALLY
ORIGINAL_REQUESTED_OBJECT: POSITIVE_SPECTRAL_PREFIXES_W_k_FOR_ALL_k
ORIGINAL_OBJECT_IS: NOT_NECESSARY
KNOWN_WEAKER_INTERFACES:
  - SIMPLE_EVEN_BOTTOM_AND_POSITIVE_LOWEST_RESIDUE_AND_NO_EXTERIOR_ZERO
  - UNREDUCED_COFACTOR_POSITIVE_ON_CLOSED_EXTERIOR_HALF_LINE
  - SOURCE_BRACKET_4_6_4_7
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: UNREDUCED_COFACTOR_AND_REAL_ROOTED_COEFFICIENT_CONE
REOPEN_TRIGGER: COFINAL_ENTRY_LEVEL_LOWER_ENVELOPES_OR_AN_EXACT_SOURCE_FACTORIZATION
ORIGINAL_ROUTE_FAMILY_KILLED: false
```

The mathematical roof still additionally needs the same-family entire-transform and convergence obligations. G1a is not replaced by the selected-row floor G1b, and the latter is not reopened. The pinned ledger [S9] records these as distinct dependencies. Existing compiled wrappers are not claimed to have been modified.

### 9.2 Route map and two re-representations

| Route | Decisive object | Kill-power / cost | Main risk / status |
|---|---|---|---|
| **Chosen: unreduced cofactor** | Positive coefficients of (4.1), or source bracket (4.6)–(4.7) | High for an entire cell family / medium algebra, high cofinal analysis | Exact representation; source signs unpaid |
| Cross-Lanczos with full numerator | Signed numerator (6.3), invisible factor (6.4), paid remainder (6.5) | High for testing low-dimensional suppliers / medium | Positive diagonal continued fraction is the wrong object |
| Low-pole versus negative-tail comparison | Exterior budget (6.7), then derivative budget (7.2) | High for isolating harmless top defects / medium-to-high | Small negative mass alone does not pay the margin |

These are not authorizations for larger eigensolver scans. The bounded tests already decide which generic shortcuts fail.

The cross-domain checks are explicit. **Control/Krylov theory** gives an exact two-endpoint transfer function but exposes hidden modes rather than proving positivity. **Sturm/Jacobi theory** gives a possible ladder only with a source ordering law; (7.3) kills commutation-only transfer. **Real-rooted polynomial positivity** gives the exact finite coefficient cone (4.2). No vanishing residual identity closing the source sign was found. The collapse object is a cofinal positive factorization or coefficient lower-envelope family for the unreduced cofactor.

### 9.3 Strongest attack on the selected representation

The strongest objection is correct: (4.2) is an exact re-representation of the parity sign, not a new proof of that sign. It must not be scored as cofinal G1a progress. Its value is that it removes two unjustified strengthening steps—positivity of every spectral prefix and positivity of a scalar diagonal Stieltjes measure—and preserves common eigenvalues. If its coefficient bounds prove no easier to obtain from the entries, do not spend a third round just renaming them.

The most likely implementation failure is replacing lambda by a numerical root, or replacing the full cross numerator by a diagonal resolvent. The response is to reject that certificate, not to weaken the spectral statement. A rigorous sign change at a chosen tau rejects that bracket; only an argument with the correct quantifiers can reject the literal eventual claim.

### 9.4 Frozen observer predictions

| Prediction | Fate in this adjudication |
|---|---|
| P1a: N1, N3, N4(a–c) survive (0.80) | **Qualified confirmation.** Core identities and the simple-bottom implications survive. Shared factors and the missing simplicity condition in an unqualified N4(c) require explicit repair. |
| P1: Q1 code distribution | **G1A_REDUCED_TO_POSITIVE_SIGN** is the result; no cofinal sign is proved. |
| P1b: first unpaid term only concerns the bottom even level (0.50) | **Not confirmed.** A positive endpoint cofactor/weight alone is insufficient; the exact certificate also needs exterior/root exclusion. Plant (5.1) establishes this structural boundary. |
| P2: alternation distribution | **ALTERNATION_PARTIAL.** The exact conditional budget (7.2) has no supplied cofinal arithmetic estimate. |
| P3: Theta distribution | **THETA_UNDECIDED.** Neither direction is proved. |

No probability was retroactively changed. A qualified confirmation is not recorded as an unqualified hit.

### 9.5 This session’s registered predictions and their tests

Before the bounded symbolic tests I recorded: (A) the rational identities would survive but need cancellation qualifications; (B) the Abel cone would be stronger than exterior positivity; (C) the structured class would admit positive w₀ with two odd levels below the even bottom. **All three were confirmed** by §§2–5. The exact Jacobi counterexample is a subsequent result, not a retroactively preregistered prediction.

## 10. Research log

### 10.1 Source register: READ versus RELAY

For `[S2]`–`[S9]`, the immutable repository base is:

`https://github.com/Malaeu/chen_q3/blob/bac124388928b9e16fae3754ab80f294f5a993ed/`

Paths below are relative to that base. Sources outside `docs/routeB_bus` opened for this task were exactly the cited `docs/Codex/PAPER_CHAIN.md` excerpt and the two named Lean source files. No archive or queue scan selected another task.

| ID | Locator and read scope | Status / use |
|---|---|---|
| S0 | `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` on `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13` | READ; protocol, not a mathematical premise |
| S1 | `docs/routeB_bus/proshka/PROSHKA_REQUEST_STIELTJES_2026-10-29.txt` at request commit `87fb6133560e9521876e37fb4cb460b5c09acdd3` | READ IN FULL; 217 lines; independent complete hash verification |
| S2 | `docs/routeB_bus/proshka/PROSHKA_VERDICT_PARITYSPLIT_2026-10-28.md`, especially §4 and §6 | READ; local attachment matched to pinned blob and full SHA-256; algebra rederived rather than accepted on authority |
| S3 | `docs/routeB_bus/proshka/PARITYSPLIT_AUDIT_2026-10-28.md` | READ; prior audit and limits; not an independent supplier for a new sign |
| S4 | `docs/routeB_bus/thetagrade_2026-10-28/parity_residue_probe.py` | READ IN FULL; identifies the computed scalar and signed weights; no new execution of its CCM scan |
| S5 | `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean`, lines 35–105 | READ; exact kernel, pole, archimedean and prime-power definitions; no Lean execution |
| S6 | `docs/routeB_bus/thetagrade_2026-10-28/residue_dps170.jsonl`, rows m=9,10; full summary in S1 | READ rows; reported nonalternation and signed weights remain DIAGNOSTIC/RELAY for numerical truth, not certified source inequalities |
| S7 | `docs/routeB_bus/litreview/CONNES_RH2026_USAGE_CARDS.md`, relevant cards 1 and 4 | READ excerpts; checked the relevant claims against P2; did not import other quoted companion results |
| S8 | `q3.lean.aristotle/Q3/Proofs/RouteB/ProlateSourceCommutation.lean`, lines 480–555, especially theorem at 519 | READ; continuous finite-Fourier/prolate intertwining, not finite CCM commutation |
| S9 | `docs/Codex/PAPER_CHAIN.md`, lines 6–35 | READ; consumer and same-family boundary; historical proof statuses are repository reports, not rerun gates |
| P1 | `https://arxiv.org/html/2511.22755v1`, Lemmas 5.1–5.4, Theorem 5.10 and the stated missing-step discussion | READ PRIMARY HTML; structured matrix and conditional ground-state construction. No cofinal simple-even theorem imported. |
| P2 | `https://arxiv.org/html/2602.04022v1`, Fact 6.3 and §6.6 | READ PRIMARY HTML; prolate result and explicit remaining Weil step kept separate |

The primary articles were read as HTML, not as the shelf PDFs; no PDF checksum or screenshot inspection is claimed. The request’s table and the previous negative-bottom/null-plane analytic estimates are not silently promoted from reports to fresh proofs.

### 10.2 Rejected approaches and the first decisive obstruction

| Candidate | Exact obstruction / reason not used |
|---|---|
| Treat the reduced g as containing the complete two-sector spectrum | Shared factors cancel; (5.8) hides a degenerate bottom |
| Settle G1a from w₀>0 alone | Two exterior odd roots survive in (5.1) |
| Require all positive spectral prefixes as a necessary target | G1a with W₁<0 in (5.4)–(5.7) |
| Replace the cross resolvent by a positive diagonal Lanczos fraction | Signed numerator a_j and invisible factor remain in (6.3)–(6.4) |
| Ignore negative top residues because their total is numerically small | The exact unpaid comparison is (6.7), and near-pole/far-field positivity leaves a middle interval |
| Infer a K-ladder from a commuting Jacobi operator | Exact [T,K]=0 in (7.3), but K has an odd bottom |
| Call the upper-spectrum failure a harmless edge effect | Schur correction B(H−t)⁻¹Bᵀ has no paid low-margin bound |
| Infer Theta-dependence from a growing negative minimum | Scalar shifts preserve the full parity/cofactor interface, §8.1 |

### 10.3 Reusable intermediate identities

**[ABSTRACT | PAPER]** The useful identities retained for other questions are the multiplicity law (2.5), the endpoint cofactor ratio (3.7), the coefficient equivalence (4.2), the cross-Lanczos numerator and omitted factor (6.3)–(6.4), the exact truncation-error bound (6.5), the compact-middle-interval discriminator (6.9)–(6.11), and the low-gap derivative budget (7.2). None supplies its own source sign.

### 10.4 Exact tests actually executed

The local symbolic script used exact rationals and algebraic square roots. Floating-point exploratory eigenvalues were used only to locate convenient synthetic examples; the reported conclusions were then checked by exact Schur complements, polynomial identities, discriminants, and rational root brackets. No such exploratory value appears as a proof premise.

```text
GENERAL m=2 displacement/cofactor identities: PASS
PLANT A: E positive definite, O negative definite, E simple: PASS
PLANT B: G1a and W_1<0, exact rational root brackets: PASS
PLANT D: g=-1/t, W=(1,1,1), degenerate full ground: PASS
PLANT J: exact irreducible Jacobi commutation, but odd ground: PASS
PAYLOAD SHA256 / Git blob / bytes / lines / final LF: PASS
```

The script SHA-256 was

`ef400598c62f1fcb665215f9ba3696caf1ea7f1f25f317c7feb8a6d71b1f8330`.

These tests are algebraic sanity checks. The universal-size proofs are the written arguments above; no Lean or interval-certified literal CCM theorem is claimed.

## 11. Proshka’s own line

I choose the unreduced cofactor because the consumer cannot tolerate a hidden common eigenvalue.  
The scalar resolvent is useful, but its cancellations are not harmless bookkeeping.  
The first nearby alternative is Abel positivity.  
It is sufficient, yet the structured example proves it can demand more than G1a needs.  
The second nearby alternative is a Jacobi explanation of the numerical ladder.  
The exact commuting counterexample shows that this requires an ordering law as well as an operator.  
The first move beyond this batch is an entry-level sign factorization of the endpoint cofactor.  
It must retain uncertainty in the lowest even root.  
A rigorously negative endpoint value on an unbounded original family would kill that necessary sign.  
A failed auxiliary lower bound would only kill that particular estimate.  
The second move is a low-spectrum derivative estimate against the entire negative tail.  
Its budget is (7.2), rather than an assertion that the top third does not matter.  
An uncontrolled low/high Schur term would defeat that proposed transfer.  
The extra input I would ask for is a symbolic source expression for the cofactor coefficients with all prime powers retained.  
Another table of small positive prefixes would not answer that question.  
The most useful surprise is that the mixed cofactor is exactly the odd characteristic polynomial.  
That identity is stronger than a numerical reciprocal check.  
It also makes the cancellation defect visible without inventing another model.  
I distrust the step from a small total negative mass to a negligible resolvent contribution.  
The denominators, low weights, and the interval of the comparison are part of that assertion.  
I also distrust a Sturm label attached solely to coordinate sign-change counts.  
The source must supply the intertwiner and the ordering, not merely resemblance.  
The clean result here is a smaller class of legitimate sign certificates and several rejected shortcuts.  
The cofinal arithmetic sign itself remains unpaid.

## 12. One next directive and meta closeout

### CODEX DIRECTIVE — one read-only mathematical task

**Target:** obtain a source-specific supplier for the necessary endpoint sign

\[
 \chi_m(\lambda_m)=h_m^T\operatorname{adj}(E_m-\lambda_mI)e_0>0,
 \qquad \lambda_m=\lambda_{\min}(E_m),                          \tag{12.1}
\]

on every sufficiently late original cell. Use the exact entries at `bac124388928b9e16fae3754ab80f294f5a993ed`. Seek a factorization or a one-sided coefficient/interval bound whose constants do not assume G1a. Do not estimate the cancelled lowest-odd-pole difference. A certified interval for lambda_m must be proved to contain the **lowest** even root, not merely some even root. The proof must pay the interval width in chi_m and retain the entire source matrix.

**Consumer and limit:** (12.1) supplies the endpoint cofactor and excludes a shared/degenerate even bottom; it does **not** by itself supply exterior zero exclusion. A success must therefore be reported as `ENDPOINT_COFACTOR_SIGN_ONLY`, never as G1a. Equations (4.2) and plant (5.1) are mandatory guards against that promotion.

**Validation gate:** verify the payload hashes; reproduce the exact algebraic plants (5.1), (5.4), (5.8), and (7.3); check the proposed sign proof against each applicable structural counterexample. Return the actual inequality, domain, source constants, and first unpaid term. No repository write, Lean run, broad numerical scan, selected-row substitution, or larger finite table is authorized by this directive. On failure, return `ENDPOINT_COFACTOR_SIGN_UNPAID` with the first failed estimate and its direction; do not declare the route dead.

### Meta closeout

**What became smaller?** The admissible interface now retains multiplicities and reduces exterior positivity to the real-rooted cofactor’s coefficient cone. The roles of the endpoint sign and the remaining exterior-root exclusion are explicitly separated.

**What was killed?** Only the theorem shapes listed in §5.4 and the commutation-only transfer in §7.3. Their evidence is exact. The literal eventual G1a, the possibility of a stronger Sturm mechanism, and the overall route were not killed.

**What must not be repeated?** A positive lowest weight promoted to G1a; a positive scalar resolvent with cancelled bottom factors promoted to simplicity; a diagonal Stieltjes fraction substituted for a cross resolvent; and Jacobi commutation substituted for spectral ordering.

**Current smallest named gaps:** the source endpoint-cofactor sign (12.1), the remaining coefficient/exterior-root certificate (4.2), the low-negative-tail budget (7.2), and the zero-dependent implication (8.2). These are obligations, not new axioms or mandatory original interfaces.

**Discriminator for a zero-consistent outcome:** keep p_E and chi unreduced. At a candidate bottom, test its multiplicity and the cofactor value; when the value vanishes, compare the orders of the two polynomial zeros. When an interval straddles zero, obtain a one-sided source envelope or an exact common-factor certificate. A scalar g that stays finite is not a degeneracy discriminator.

**Next cheapest diagnosis-changing test:** a source factorization or lower-envelope audit for (12.1), checked against the exact structured plants before any numerical escalation.

```yaml
iteration:
  target: GOAL058_G1A_ODD_RESOLVENT_SIGN
  status: PROGRESS
  failed_strategy: POSITIVE_LOWEST_WEIGHT_OR_JACOBI_COMMUTATION_AS_SUFFICIENT
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SOURCE_UNREDUCED_COFACTOR_ENDPOINT_AND_EXTERIOR_POSITIVITY
  invariant_learned: CROSS_RESOLVENT_CANCELLATION_MUST_NOT_ERASE_SHARED_EIGENVALUES
  forbidden_future_move: PROMOTE_REDUCED_SCALAR_POSITIVITY_TO_SIMPLE_GROUND_WITHOUT_NONCANCELLATION
  next_decisive_test: ENTRY_LEVEL_ENDPOINT_COFACTOR_SIGN_SUPPLIER
  proof_progress_boundary: NO_COFINAL_LITERAL_G1A_SIGN_ESTABLISHED
```

RH remains OPEN. No RH-equivalent premise was used, no numerical observation replaced a quantifier, and no final RH claim is made.
