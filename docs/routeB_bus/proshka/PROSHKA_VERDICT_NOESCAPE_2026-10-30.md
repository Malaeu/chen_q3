# STATUS: TRY_NOESCAPE_SIGNED_LEAKAGE_WITH_SPECTRAL_COUNT_GUARD

```yaml
OPERATIVE_CLASS: TRY_NOESCAPE_SIGNED_LEAKAGE_WITH_SPECTRAL_COUNT_GUARD
REQUEST_ID: REQ-2026-10-30-NOESCAPE
BOUNDARY_ID: GOAL058_FIXED_JET_NO_ESCAPE_ON_LITERAL_CCM_BOTTOMS
REQUEST_COMMIT: 1a23edcd44d6e95bafa2929396188f47312a270b
REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_NOESCAPE_2026-10-30.txt
REQUEST_GIT_BLOB: 96d3527d0248d4f5022893d5a301f4987f1e3672
REQUEST_SHA256: b3e364b55c6ac82d4af228b35f986f6ba23892ee3ef3d99cea3ee8a0b0071978
REQUEST_BYTES: 8875
REQUEST_LINES: 148
REQUEST_FINAL_LF: true
REQUEST_HASH_CHECK: ALL_FOUR_SUPPLIED_VALUES_MATCH
SOURCE_BASE_COMMIT: bdea6ec1e117c04da9e72528695caa1cfd0dc0ca
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_SELECTED_FERRERS_FAMILY
Q1: PARTIAL_WITH_PRECISE_REMAINDER
Q2: PARTIAL_WITH_PRECISE_REMAINDER
Q3: PARTIAL_WITH_PRECISE_REMAINDER
Q3_SUBCLAIM_REFUTED: STRICT_RESIDUAL_BELOW_THRESHOLD_ALONE_DOES_NOT_GIVE_UNIFORM_FIXED_JET_OVERLAP
Q4: PARTIAL_WITH_PRECISE_REMAINDER
TARGET_T_PROVED: false
TARGET_T_REFUTED: false
BLIND_TAIL_BOUND_WITH_FIXED_C_LT_1: NOT_PROVED_OR_REFUTED_FOR_LITERAL_CCM
NEW_SOURCE_RESULTS:
  - RAW_PROJECTED_FIXED_JETS_HAVE_SUPERPOLYNOMIAL_RESIDUAL_DECAY
  - EVERY_POLYNOMIAL_ZERO_BAND_CONTAINS_UNBOUNDEDLY_MANY_EVEN_LEVELS
  - ZERO_EXTENDED_FINITE_OPERATORS_CONVERGE_STRONGLY_IN_RESOLVENT_TO_ZERO
NEW_ABSTRACT_RESULT: SATURATED_POSITIVE_THRESHOLD_COUNT_GIVES_LOWER_FLOOR_MINUS_RESIDUAL
RH_EQUIVALENCE_PROVED_HERE: COFINAL_VANISHING_LOWER_FLOOR_FOR_ONE_LITERAL_PARITY_SECTOR
TARGET_T_LOGICAL_STATUS: THIS_STEP_IMPLIES_RH_CONVERSE_NOT_ESTABLISHED
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: UNRESOLVED
KILL_SCOPE_FOR_SCOPED_REFUTATIONS: THEOREM_SHAPE
KILL_EVIDENCE_KIND: EXACT_COUNTEREXAMPLES_AND_COFINAL_MINMAX_COUNT
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: SPECTRAL_CLUSTER_AND_TRANSFER_LEMMAS_NOT_TARGET_CLOSURE
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 4
VERIFIER: PAPER
INDEPENDENT_REVIEW_OF_THIS_VERDICT: NOT_PERFORMED
EXACT_ALGEBRA_CONTROLS: EXECUTED
LITERAL_CCM_NUMERICAL_SCAN: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
REPOSITORY_WRITTEN: false
RH_PROVED: false
G1A_PROVED_COFINAL: false
G3_PROVED: false
ROUTE_PROMOTION: false
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## 0. Answer and proof boundary

**T implies RH. That is the intended conclusion, not a reason to stop.** I attempted the source-preserving proof through the actual leakage vector and through spectral counting. Neither attempt establishes T. The first unproved estimates are displayed in (4.9) and (5.9), with the exact additional conditions needed to spend them. I do not claim that the literal family violates either estimate.

There are three substantive results before that boundary.

* Every fixed jet has an arbitrarily small **absolute-energy** spectral return, but the number of levels near zero necessarily grows. In fact, every band `|lambda| < m^(-B)`, for fixed `B>0`, contains arbitrarily many even levels eventually. A bounded count at a polynomial threshold is therefore false for the literal family, independently of RH.
* An `r`-dimensional quasimode space with residual `delta < mu`, together with **at most r levels below the positive threshold mu**, forces `lambda_min >= -delta`. This works without isolating the bottom and even with growing `r`. If `delta -> 0`, its cofinal literal-source implementation proves RH. It is not proved here that the requisite upper count holds.
* That counted package does **not** automatically prove the requested fixed-jet T. Fixed rank needs a uniform ratio `delta/mu < 1`; growing rank needs an additional fixed-coordinate tightness estimate. Exact examples below separate these statements.

For Q2 I give the complete signed decomposition into the sampled whole-line Xi tail and its exterior/window correction. The exterior correction has an explicit exponentially small **absolute** envelope. It cannot be discarded after division by the small excited eigenvalues. The supplied measurements do not determine which term carries the `v_1` component.

The protocol and request were fetched through GitHub. The full request text was saved locally without altering its UTF-8 content; SHA-256 and Git-object hashing reproduce all supplied values. The locally mounted CONFINE artifact has SHA-256 `57088a914942b0dd1c3d1835edaca2f223a59831d78350c0a092356024852ddb` and Git blob `1879347b72d1aa55cf506f5387de37059f929122`, matching the pinned GitHub file. Its §§1–4 and §5.1 were read, not merely its prior chat summary. The Codex receipt reports one completed clean methodological pass and requests a formal second pass; it is a PAPER audit, not a Lean certificate. [S1–S3]

No asserted limit, decay fit, or numerical eigenvalue in the request is used as a cofinal premise. In particular, neither `exp(-4.6 m)` nor the observed first four spectral weights is promoted to a law.

### Claim ledger

| Claim | Scope | Verifier | Exact boundary |
|---|---|---|---|
| L1–L2 | COFINAL_FAMILY | PAPER | Raw fixed-jet residuals and conditioned finite-rank return |
| L3–L4 | COFINAL_FAMILY | PAPER | Spectral clustering and strong resolvent convergence, not ground selection |
| L5 | COFINAL_FAMILY | PAPER | A vanishing lower floor in either literal sector is equivalent to RH |
| L6 | COFINAL_FAMILY | PAPER | T implies RH; no converse asserted |
| L7–L9 | ABSTRACT | PAPER | Blind-tail identity, kernel guards, and failure plants |
| L10–L11 | COFINAL_FAMILY | PAPER | Exact Xi-tail/exterior decomposition and absolute exterior envelope |
| L12 | ABSTRACT | PAPER | Saturated count implies a lower floor and a quantitative subspace angle |
| L13–L15 | ABSTRACT | PAPER | Counterexamples and the extra budget required for a growing jet |
| L16–L18 | ABSTRACT | PAPER | Weak subsequential fingerprints and a compact-observable formulation |
| O1–O3 | COFINAL_FAMILY | CONDITIONAL | Actual blind-tail bound, saturated count, and fixed-coordinate tightness remain unproved |

Every lemma below begins with the requested honesty line. “THIS STEP IMPLIES RH” identifies an open sufficient target or a proved implication, not an assumed input. “THIS STEP IS RH” is used only where both directions are proved.

## 1. Source object and the usable suppliers

Work in the physical Hilbert space `H_E = L²_even(R)`; the odd version is identical with odd jets. Put

\[
 L=\log m,\quad b=L/2,\quad I_m=[-b,b],\quad
 \psi_{n,L}(x)=L^{-1/2}e^{2\pi i n(x+b)/L}\mathbf1_{I_m}(x),
 \qquad |n|\le m.                                      \tag{1.1}
\]

`P_m` is the orthogonal projection onto this literal carrier, restricted to the chosen parity when appropriate. `A_m=K_{m,E}` acts on `V_{m,E}`; its ordered eigenvalues are

\[
 \lambda_{m,0}\le\lambda_{m,1}\le\cdots\le\lambda_{m,m}.
\]

Choose orthonormal physical eigenfunctions `v_{m,i}`. T refers to a chosen unit bottom `f_m=v_{m,0}`. No simplicity is assumed silently. A statement for the entire bottom eigenspace will be identified separately.

The source convention is antilinear in the first variable. Define

\[
 H(t)=\widehat h(t)=4\xi(1/2-it),\quad
 \widehat f(t)=\int f(x)e^{-itx}\,dx,
 \quad \|f\|_2^2=(2\pi)^{-1}\int|\widehat f(t)|^2dt.       \tag{1.2}
\]

The explicit even positive theta function is

\[
 h(x)=e^{x/2}\sum_{n\ge1}
 (16\pi^2n^4e^{4x}-24\pi n^2e^{2x})e^{-\pi n^2e^{2x}}.
\]

For `r_j=h^(2j)`, set

\[
 J_r=\operatorname{span}\{r_0,\ldots,r_{r-1}\},\qquad
 J_{r,m}=P_mJ_r.                                       \tag{1.3}
\]

This notation uses `r` for the dimension, rather than the request's highest derivative index `k=r-1`.

For later exact tail calculations the source form is

\[
\begin{aligned}
\mathfrak k(f,g)={}&-c_*\langle f,g\rangle
 +\int_0^\infty j(s)\{2\langle f,g\rangle-Q_{f,g}(s)\}\,ds\\
 &-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}Q_{f,g}(\log n)
 +\langle f,p\rangle\langle p,g\rangle
 -\langle f,q\rangle\langle q,g\rangle,                  \tag{1.4}
\end{aligned}
\]

where

\[
 Q_{f,g}(s)=\int\overline{f(x)}[g(x+s)+g(x-s)]dx,\quad
 j(s)=\frac{e^{-s/2}}{1-e^{-2s}},
\]
\[
 c_*=\gamma+\log(8\pi)+\pi/2,\quad
 p(x)=\sqrt2\cosh(x/2),\quad q(x)=\sqrt2\sinh(x/2).
\]

All prime powers, both pole functionals, both endpoints and the identity Gram metric are retained. The direct matrix restriction of (1.4) agrees with CCM's v1 formulas (2.9)–(2.10), (3.13)–(3.20), (4.1)–(4.4). The v1 PDF was visually checked at the basis and explicit-formula pages; its fixed-window core theorem alone is **not** used to replace the diagonal `N=m` return. [S1 §1; P1]

The pinned CONFINE proof and its audit supply the following unconditional PAPER facts:

1. `k(r_j,g)=0` for every fixed derivative and the admissible mixed tests; the fixed even derivative span is dense in `H_E`.
2. For a fixed smooth cutoff `chi(x/b)` and any fixed derivative `r_j`, its finite projection `z_{j,m}=P_m(chi(x/b)r_j)` satisfies, for every fixed `A>0`,
   \[
   \|z_{j,m}-r_j\|+\|A_mz_{j,m}\|=O_{j,A}(m^{-A}).       \tag{1.5}
   \]
   This is (3.8)–(3.9), including the growing matrix and the exterior prime tail.
3. An off-critical zero gives, separately in each parity, a fixed compact smooth negative test. Its return (4.5) implies
   \[
   \lambda_{m,0}\le-\nu/2<0\qquad(m\ge m_0)             \tag{1.6}
   \]
   with a fixed `nu>0`. It does not result from splitting one negative vector by parity.

These are actual read mathematical suppliers [S1 §§1–4; S2], not imported numerical observations. The following arguments show exactly what they do and do not imply.

## 2. What the quasimode proves unconditionally

### L1. The raw projection in this request also has superpolynomial residual

THIS STEP IS PROVED HERE.

**[COFINAL_FAMILY | PAPER]** For every fixed `j` and every `A>0`,

\[
 \|P_mr_j-r_j\|+\|A_mP_mr_j\|=O_{j,A}(m^{-A}).           \tag{2.1}
\]

In particular, for `Z_m=||P_mh||` and `u_m=P_mh/Z_m`,

\[
 Z_m\to\|h\|>0,\quad u_m\to u:=h/\|h\|,
 \quad \delta_m:=\|A_mu_m\|=O_A(m^{-A}).                 \tag{2.2}
\]

**Proof.** We first give a sufficiently explicit polynomial norm bound, so that the change from the cutoff quasimode to the raw projection is paid. For any unit carrier function `v`,

\[
 \|v'\|_{L^2(I_m)}\le2\pi m/L,\quad
 \|v\|_\infty\le\sqrt{(2m+1)/L},\quad
 |v(-b)|+|v(b)|\le2\sqrt{(2m+1)/L}.
\]

Moving a correlation derivative onto the zero extension includes its two endpoint masses and gives

\[
 |2-Q_{v,v}(s)|\le
 2s\left(2\pi m/L+2(2m+1)/L\right).
\]

The archimedean integral is bounded using `int_0^infty s j(s) ds < 5`. The pole norm is at most `2 sqrt(m)`, and the complete prime part is at most `4 sqrt(m)L`, since `Lambda(n)<=log n`. Therefore

\[
 \|K_m\|\le\mathcal B_m:=c_*+(2+4L)\sqrt m
       +10\left(\frac{2\pi m}{L}+\frac{2(2m+1)}L\right). \tag{2.3}
\]

This is an absolute upper bound, not a sign assertion. The same bound applies to `A_m`.

Now `P_mr_j-z_{j,m}=P_m[(1-chi(x/b))r_j]`. The latter norm decreases faster than every power of `m`, because the tail starts at `|x|>=L/4` and the theta derivatives have double-exponential decay. Multiplying it by the polynomial bound (2.3) still gives superpolynomial decay. Combine with (1.5). Normalization gives (2.2). No spectral lower bound is used. ∎

### L2. Fixed-dimensional jets have an operator-norm residual, not merely columnwise residuals

THIS STEP IS PROVED HERE.

**[COFINAL_FAMILY | PAPER]** Let `B_{r,m}:C^r -> V_{m,E}` have columns `P_mr_j`, and let `M_{r,m}=B_{r,m}*B_{r,m}`. For fixed `r`, this matrix is positive definite eventually. With

\[
 Q_{r,m}=B_{r,m}M_{r,m}^{-1/2},\qquad
 \Delta_{r,m}=\|A_mQ_{r,m}\|,
\]

one has

\[
 \Delta_{r,m}^2
 =\lambda_{\max}\!\left(M_{r,m}^{-1/2}B_{r,m}^*A_m^2B_{r,m}M_{r,m}^{-1/2}\right)
 \le\frac{\sum_{j<r}\|A_mP_mr_j\|^2}{\lambda_{\min}(M_{r,m})},       \tag{2.4}
\]

and `Delta_{r,m}=O_{r,A}(m^{-A})` for every fixed `A`. Also

\[
 \eta_{r,m}:=\|P_{J_r}-P_{J_{r,m}}\|\longrightarrow0              \tag{2.5}
\]

at every fixed inverse-power rate.

**Proof.** The global Gram matrix of `r_0,...,r_{r-1}` is positive definite: a nonzero polynomial times the nonzero entire function `H(t)` cannot vanish almost everywhere. L1 gives convergence of the finite Gram matrix and of its inverse square root. The columns of `Q_{r,m}` are orthonormal, proving (2.4). The upper estimate follows from the Hilbert–Schmidt bound on `A_m B_{r,m}`. Convergence of these finite orthonormal frames gives (2.5); alternatively apply the elementary subspace-angle estimate to `B_{r,m}` and the global synthesis matrix. ∎

**Fixed-rank warning.** The constants in this proof depend on `r`. Substituting `r=r(m)` without paying the derivative norms and the smallest Gram eigenvalue is invalid.

### L3. Every polynomial-scale band around zero eventually contains arbitrarily many levels

THIS STEP IS PROVED HERE.

**[COFINAL_FAMILY | PAPER]** For every fixed `B>0` and integer `r>=1`,

\[
 \#\{i:|\lambda_{m,i}|<m^{-B}\}\ge r
 \quad\text{for all sufficiently large }m.                         \tag{2.6}
\]

Thus the count in this band tends to infinity. The same holds in the odd sector.

**Proof.** For every unit vector `x` in `J_{r,m}`, `||A_mx||²<=Delta_{r,m}²`. Min–max applied to the nonnegative matrix `A_m²` gives at least `r` eigenvalues of `A_m²` at most `Delta_{r,m}²`. These are exactly the squares of eigenvalues of `A_m`, counted with multiplicity. L2 makes `Delta_{r,m}<m^{-B}` eventually. ∎

This is a lower count, not the upper count requested in Q3. It proves that **a bounded upper count at any polynomial threshold cannot be the missing supplier**. It also explains why a more accurate residual need not isolate a single lowest level.

### L4. The entire embedded finite family converges strongly in resolvent to zero

THIS STEP IS PROVED HERE.

**[COFINAL_FAMILY | PAPER]** Extend `A_m` by zero on `V_{m,E}^perp` in `H_E`, obtaining the self-adjoint bounded operator `Atilde_m`. Then, for every nonreal `z`,

\[
 (\widetilde A_m-zI)^{-1}\longrightarrow-\frac1zI
 \quad\text{strongly on }H_E.                                      \tag{2.7}
\]

**Proof.** Write `R_m(z)=(Atilde_m-z)^{-1}`. Its norm is at most `1/|Im z|`. For a fixed derivative `r_j`, put `s_m=P_mr_j`. The resolvent identity on this vector gives

\[
 R_m(z)s_m+z^{-1}s_m=z^{-1}R_m(z)A_ms_m.
\]

Therefore

\[
 \|R_m(z)r_j+z^{-1}r_j\|
 \le\left(|\Im z|^{-1}+|z|^{-1}\right)\|r_j-s_m\|
   +\frac{\|A_ms_m\|}{|z||\Im z|}\to0.
\]

Finite linear combinations of the derivatives are dense, and the operators are uniformly bounded for fixed `z`. Approximation proves the assertion for every vector. ∎

This unconditional theorem does **not** say that the lowest eigenvalue tends to zero. Escaping eigenvectors can carry fixed negative eigenvalues while all fixed-vector resolvent tests converge. L9 supplies an exact counterexample. Strong resolvent convergence here is not a replacement global realization of the Weil form.

## 3. The intended RH bridge, with the logical directions explicit

### L5. A vanishing cofinal lower floor for one literal sector

THIS STEP IS RH.

**[COFINAL_FAMILY | PAPER]** The following statement is equivalent to RH:

\[
 \exists\text{ unbounded }\mathcal M\subset\mathbb N,
 \quad\exists\epsilon_m\ge0\ (m\in\mathcal M),\quad
 \epsilon_m\to0,\quad\lambda_{m,0}\ge-\epsilon_m.                    \tag{3.1}
\]

One may use either the even or the odd sector, separately.

**Proof.** Under RH all centered zeros are real, and the unconditional explicit formula becomes a sum of nonnegative squares. Hence every literal compression is nonnegative and (3.1) holds with zero error. This use of RH is only the forward half of an equivalence, not a premise in the attempted proof of T.

Conversely, an off-critical zero gives (1.6) on **every** sufficiently late original cell, by the separate parity test and the explicit `N=m` return. On any unbounded `M`, eventually `epsilon_m<nu/2`, a contradiction. No claim that the moving carriers are nested is required. ∎

L1 also gives `lambda_{m,0}<=<u_m,A_mu_m><=delta_m->0`. Thus (3.1) is equivalently convergence of the sector bottom to zero along an unbounded subsequence. The fixed-window result in CCM Corollary 3.8 has a related shape; the proof above additionally pays the selected diagonal schedule. [S1 §4; P1]

### L6. Fixed-jet no escape implies (3.1)

THIS STEP IMPLIES RH.

**[COFINAL_FAMILY | PAPER]** If T holds with a fixed `J_r` and `epsilon>0`, then on its unbounded set,

\[
 |\lambda_{m,0}|\le\frac{2\Delta_{r,m}}\epsilon
 \quad\text{eventually}.                                           \tag{3.2}
\]

Consequently T implies RH. Its converse is not established.

**Proof.** By (2.5), `||P_{J_{r,m}}f_m||>=epsilon/2` eventually. Self-adjointness gives

\[
 |\lambda_{m,0}|\|P_{J_{r,m}}f_m\|
 =\|P_{J_{r,m}}A_mf_m\|
 \le\|P_{J_{r,m}}A_m\|=\Delta_{r,m}.
\]

This proves (3.2), and L5 finishes the implication. ∎

**What still has to be proved, not renamed:** an actual source-dependent positive lower bound for that overlap on an unbounded set. L1–L4 give no such lower bound. The following two attempts expose the precise estimates that would provide it.

## 4. Q1–Q2: the signed leakage proof attempt

### L7. Exact blind-tail identity, including invisible zero modes

THIS STEP IS PROVED HERE.

**[FINITE_CELL | PAPER]** Let

\[
 u_m=P_mh/Z_m,\qquad e_m=(h-P_mh)/Z_m,
 \qquad a_{m,i}=\langle u_m,v_{m,i}\rangle.
\]

Then

\[
 \mathfrak k(e_m,v_{m,i})=-\lambda_{m,i}a_{m,i}.                     \tag{4.1}
\]

The order of the arguments matters for complex vectors; the displayed convention makes (4.1) exact. In particular,

\[
\begin{aligned}
 1-|a_{m,0}|^2={}&
 \sum_{\substack{i\ge1\\\lambda_{m,i}\ne0}}
       \frac{|\mathfrak k(e_m,v_{m,i})|^2}{\lambda_{m,i}^2}
 +z_m,\\
 z_m:={}&\sum_{\substack{i\ge1\\\lambda_{m,i}=0}}|a_{m,i}|^2.       \tag{4.2}
\end{aligned}
\]

**Proof.** Radicality gives `k(h/Z_m,v)=0`, so `k(e_m,v)=-k(u_m,v)`. On an eigenvector the latter is `-<u_m,A_mv>=-lambda_i a_i`. Parseval gives `sum_i |a_i|²=1`. Division is valid only for nonzero eigenvalues; the remaining terms are exactly `z_m`. ∎

If the bottom is multiple, (4.2) is still valid for the chosen orthonormal basis and chosen `v_0`. A basis-invariant alternative removes the **entire** bottom eigenspace. It proves overlap with some unit bottom, not with every arbitrarily chosen unit vector in that eigenspace.

The displayed sum in the request is therefore literally valid without amendment only when all its denominators are nonzero. A Moore–Penrose inverse alone does not remove the need for `z_m`.

### L8. The requested bound is a no-escape theorem, not a residual estimate

THIS STEP IMPLIES RH.

**[COFINAL_FAMILY | PAPER]** If the right side of (4.2) is at most a fixed `c<1` cofinally, then T holds with `J=span{h}`. Conversely T with this one-dimensional jet gives such a `c<1` eventually on a possibly smaller unbounded set.

**Proof.** Since `f_m` belongs to the carrier,

\[
 \left|\left\langle h/\|h\|,f_m\right\rangle\right|^2
       =\frac{Z_m^2}{\|h\|^2}|a_{m,0}|^2.                          \tag{4.3}
\]

The prefactor tends to one by L1. Use (4.2) in both directions. ∎

This equivalence to the **one-jet version of T** does not establish equivalence to RH. It identifies the exact statement we are trying to prove.

### L9. Why the unweighted residual cannot supply the blind-tail bound

THIS STEP IS PROVED HERE.

**[ABSTRACT | PAPER]** For any positive threshold `mu`,

\[
 \sum_{|\lambda_i|\ge\mu}|a_i|^2\le\delta_m^2/\mu^2.              \tag{4.4}
\]

The uncontrolled part is the excited mass with `|lambda_i|<mu`, including zero modes.

**Proof.** Expand `||A_mu_m||²=sum_i lambda_i² |a_i|²` and discard nonnegative terms. ∎

Here is a cofinal falsifier, not another CCM family. In `ell²(N_0)`, let `V_m=span{e_0,...,e_m}` and

\[
 A_m^-e_j=\varepsilon_me_j\quad(j<m),\qquad
 A_m^-e_m=-e_m,\qquad \varepsilon_m=2^{-m^2}.                      \tag{4.5}
\]

Every fixed coordinate jet has superpolynomial residual, and the zero-extended operators even converge strongly to zero. Nevertheless the simple bottom is `e_m`, weakly escaping, with eigenvalue `-1`. For `u=e_0` the complete excited blind-tail mass is **exactly one**. Thus neither small residual, near-zero spectral concentration, nor strong resolvent convergence proves T.

A positive sibling replaces `-1` by `1`. It has the same matrix action, Rayleigh values, and residual Gram matrix on every tested fixed jet once `m` is larger than that jet. The missing information concerns the competing complement.

The zero-mode falsifier is `A=diag(-1,0,2)`, `u=e_1`. Its residual is zero; a pseudoinverse-only sum is zero; its overlap with the negative bottom is zero. Formula (4.2) correctly restores `z=1` and rejects the proposed certificate.

**Repair of the failed inequality.** Choose `0<eta<c<1` and `mu_m=delta_m/sqrt(eta)` when `delta_m>0`. The high absolute-energy contribution is at most `eta`. A sufficient, still unproved, source estimate is

\[
 \boxed{
 \sum_{\substack{i\ge1\\0<|\lambda_{m,i}|<\mu_m}}
 \frac{|\mathfrak k(e_m,v_{m,i})|^2}{\lambda_{m,i}^2}
       +z_m\ \le\ c-\eta
 \quad(m\in\mathcal M),\qquad \mathcal M\text{ unbounded}.}        \tag{4.6}
\]

When `delta_m=0`, `u_m` lies in the kernel; its position relative to the bottom must be checked rather than divided by zero. Formula (4.2) remains the correct test.

The first inequality not supplied by the source is **(4.6)**. Its left side is nonnegative and dimensionless; its budget is a fixed number below one. Absolute tail control does not pay the eigenvalue denominators. The negative plant (4.5) makes the left side one and violates any proposed budget `c-eta<1`.

### L10. The exact Xi-tail formula has an exterior correction

THIS STEP IS PROVED HERE.

**[FINITE_CELL | PAPER]** Put `h_in=h 1_{I_m}`, `h_out=h 1_{I_m^c}` and `omega_n=2 pi n/L`. Use the same basis (1.1) for **all** integers `n` when expanding functions on the fixed window. Its coefficients are

\[
 c_{m,n}=\langle\psi_{n,L},h_{\rm in}\rangle
   =\frac{(-1)^n}{\sqrt L}
        \bigl[H(\omega_n)-\widehat h_{\rm out}(\omega_n)\bigr].     \tag{4.7}
\]

For a unit even carrier eigenfunction `v_i`, define

\[
\begin{aligned}
 F_{m,i}&=\sum_{|n|>m}\frac{(-1)^n}{\sqrt L}H(\omega_n)
                          \mathfrak k(\psi_{n,L},v_i),\\
 X_{m,i}&=\mathfrak k(h_{\rm out},v_i)
    -\sum_{|n|>m}\frac{(-1)^n}{\sqrt L}\widehat h_{\rm out}(\omega_n)
                          \mathfrak k(\psi_{n,L},v_i).
\end{aligned}
\]

Then the complete source equation is

\[
 \boxed{\mathfrak k(e_m,v_i)=\frac{F_{m,i}+X_{m,i}}{Z_m}.}          \tag{4.8}
\]

The blind-tail target, with no dropped sector, is consequently

\[
 \boxed{
 \sum_{\substack{i\ge1\\\lambda_{m,i}\ne0}}
 \frac{|F_{m,i}+X_{m,i}|^2}{Z_m^2\lambda_{m,i}^2}+z_m\le c<1
 \quad\text{on an unbounded original family}.}                    \tag{4.9}
\]

**Proof.** Formula (4.7) is the Fourier coefficient integral; `exp(-i omega_n b)=(-1)^n`. The functions `h`, `h_in` and `h_out` are real even, so all sampled coefficients in (4.7) are real. There is no missing conjugation in the displayed first-slot pairing.

Expand

\[
 h-P_mh=\sum_{|n|>m}c_{m,n}\psi_{n,L}+h_{\rm out}.
\]

The first window integration-by-parts boundary term vanishes because `h(-b)=h(b)` and the sampling frequencies are periodic. A second integration gives

\[
 |c_{m,n}|\le
 \frac{2|h'(b)|+\|h''\|_{L^1(I_m)}}{\sqrt L\,\omega_n^2}
 \quad(n\ne0).
\]

Thus the Fourier series converges in periodic `H¹` and uniformly. The mixed form is continuous for that convergence, retaining the endpoint traces: its archimedean part is controlled by the derivative and trace bound used in CONFINE (3.5), and its finite-window pole and prime parts are bounded. This justifies termwise pairing. The sampled `H` series converges faster; subtracting it gives the same validity for the exterior-coefficient series. Equation (4.8) follows. ∎

This corrects the approximation in `quasimode_xi_tail.py`: sampled whole-line `4 Xi` values are not exactly the coefficients of `h` restricted to the window. The phase is harmless in a squared norm but not in the signed pairing. Moreover, that script sums only `m<n<6m` at 30 decimal digits and supplies no certified remainder; it is a diagnostic model, not a source identity. [S5]

An entirely explicit matrix expression is available without any high-mode eigenvectors. If `v_i=sum_{|j|<=m}v_{i,j} psi_j`, then

\[
 \mathfrak k(\psi_n,v_i)=\sum_{|j|\le m}K_L(n,j)v_{i,j},            \tag{4.10}
\]

where `K_L(n,j)` uses the literal entry formula at the same `L` and prime cutoff. For `|n|>m`, all these entries are off-diagonal. There has been no change to the active carrier of the eigenproblem; the additional modes occur only in the exact leakage representation.

### L11. Exterior corrections are small absolutely, not automatically in the inverse spectral metric

THIS STEP IS PROVED HERE.

**[COFINAL_FAMILY | PAPER]** The functional `v -> X_m(v)` in L10 has a completely explicit envelope `mathcal X_m` on the unit finite carrier and satisfies

\[
 \sup_{\|v\|=1}|X_m(v)|\le\mathcal X_m
       \le C m^4(1+\log m)^2e^{-\pi m}                  \tag{4.11}
\]

for a fixed finite constant `C` and all sufficiently large `m`. This does not imply `X_{m,1}=o(lambda_{m,1})`.

**Proof with the envelope.** Define

\[
 W_m(x)=\sum_{\ell\in\mathbb Z\setminus\{0\}}h(x+\ell L),
 \quad x\in I_m,\qquad \beta_m=(I-P_m)W_m
\]

where window functions are extended by zero for the form. Periodization and (4.7) show that the coefficients of `W_m` are `(-1)^n hat h_out(omega_n)/sqrt L`. Hence

\[
 X_m(v)=\mathfrak k(h_{\rm out},v)-\mathfrak k(\beta_m,v).           \tag{4.12}
\]

Let `d_m=2m+1`, `S_Lambda=sum_{n>=2}(log n)n^(-3/2)`, and

\[
 A_{
m out}=\int_{|x|>b}e^{|x|/2}h(x)dx,\quad
 T_{
m out}=\|e^{|x|}h\mathbf1_{I_m^c}\|_2.
\]

A valid first envelope is

\[
\begin{aligned}
 B_{
m out}:={}&10\left(\|h'\mathbf1_{I_m^c}\|_2
                       +2h(b)\sqrt{d_m/L}\right)\\
 &+2m^{1/4}A_{
m out}+2\sqrt m\,S_\Lambda T_{
m out}.              \tag{4.13}
\end{aligned}
\]

Indeed `h_out` and `v` have disjoint supports in measure, so their inner product and the diagonal term vanish. The derivative of `h_out` is its interior derivative plus the two boundary masses of magnitude `h(b)`; differentiating the correlation and using `int s j(s)<5` gives the first line. The poles are bounded by the weighted `L¹` norm in the second line. For **every** prime power, including `n>m`,

\[
 |Q_{h_{\rm out},v}(\log n)|\le2\sqrt m\,n^{-1}T_{
m out}.
\]

This proves the complete prime envelope in (4.13).

The even function `W_m` has equal endpoint values, so its periodic weak derivative is in `L²`. Fourier projection is contractive on that derivative. Consequently

\[
 \|\beta_m\|\le\|W_m\|,\qquad
 \|\beta_m'\|\le\|W_m'\|,
\]
\[
 |\beta_m(-b)|+|\beta_m(b)|
 \le J_W:=2\|W_m\|_\infty+2\sqrt{d_m/L}\,\|W_m\|.
\]

Its exact orthogonality to the carrier permits the same mixed bound as CONFINE (3.5). We may therefore take

\[
 \boxed{\mathcal X_m=B_{
m out}
 +(2+4L)\sqrt m\,\|W_m\|+10\|W_m'\|
 +10J_W\sqrt{d_m/L}.}                                            \tag{4.14}
\]

All norms in this expression concern the explicit theta function, not an unknown eigenvector.

To obtain the simpler asymptotic envelope in (4.11), differentiate the theta series. For `x>=0`,

\[
 |h(x)|\le C_0e^{9x/2}e^{-\pi e^{2x}},\qquad
 |h'(x)|\le C_1e^{13x/2}e^{-\pi e^{2x}},                            \tag{4.15}
\]

where the constants are finite positive sums of Gaussian-weighted powers of `n`. For example `C_0=16 pi² sum_{n>=1}n^4 exp[-pi(n²-1)]` is admissible. Each differentiated term is a polynomial in `n²e^{2x}` times the same Gaussian, which proves the second estimate with an analogous explicit finite sum. Evenness gives the left tail.

At `x=b`, `e^{2b}=m`. Substitution `y=e^{2x}` in the tail integrals bounds them by a polynomial in `m` times `e^(-pi m)`. In the periodization, `|x+ell L| >= (2|ell|-1)b`; the first images have the same envelope and all further images form a smaller, uniformly convergent tail. Thus

\[
 \|W_m\|_\infty\le C m^{9/4}e^{-\pi m},\qquad
 \|W_m'\|_\infty\le C m^{13/4}e^{-\pi m}.
\]

Insert these bounds, `||W||_2<=sqrt L ||W||_infty`, and the tail integrals into (4.14). Enlarging one fixed constant gives (4.11). ∎

**Why this does not settle the prediction about `v_1`.** Let

\[
 g_m=\min_{\substack{i\ge1\\\lambda_{m,i}\ne0}}|\lambda_{m,i}|.
\]

The Riesz vector of `X_m` has norm at most `mathcal X_m`, so its nonzero excited inverse-weighted norm is at most

\[
 \left(\sum_{\substack{i\ge1\\\lambda_{m,i}\ne0}}
        \frac{|X_{m,i}|^2}{\lambda_{m,i}^2}\right)^{1/2}
 \le\mathcal X_m/g_m.                                             \tag{4.16}
\]

No lower bound on `g_m` at this scale has been proved. The absolute estimate therefore does not give a small dimensionless budget. Similarly, a large norm of the whole Xi-tail functional does not say that its pairing with `v_1` is large; it may be almost orthogonal to that level.

The decisive source quantities are the **signed** pair `(F_{m,1}, X_{m,1})` and their sum, or their complete inverse-weighted excited vectors. Triangle bounds may erase the very cancellation sought. The current data report only the sum `-Z_m lambda_1 a_1` and its global supremum. They do not identify its two contributions.

A falsifiable diagnostic is

\[
 D_m^{\rm ext}=\frac{|X_{m,1}|}{|F_{m,1}+X_{m,1}|},                \tag{4.17}
\]

with rigorous enclosures for numerator and denominator. A nonzero lower bound for the denominator is mandatory; a zero-consistent enclosure must be refined or resolved by an exact vanishing identity. A small value proves exterior negligibility only on that cell. Large `D_m^ext` detects an exterior contribution or cancellation hidden by the total. This diagnostic is **not** itself a proof of (4.9).

**Q1/Q2 closeout.** The one-jet target would be proved by (4.9), or by the repaired low-cluster budget (4.6) after reserving the high-energy cost. Those are the first unproved inequalities. The whole-line/window distinction is now exact and its absolute error is paid; the low-level inverse weighting is not. I neither prove nor refute a cofinal `c<1` for the literal CCM matrices.

## 5. Q3: what a threshold index theorem would really buy

### L12. Spectral saturation theorem

THIS STEP IS PROVED HERE.

**[ABSTRACT | PAPER]** Let `A=A*` act on a finite-dimensional Hilbert space. Let `J` have dimension `r>=1`, and suppose

\[
 \|A|_J\|\le\delta<\mu,\qquad\mu>0,
 \qquad N_A(\mu):=\#\{\lambda(A)<\mu\}\le r.                     \tag{5.1}
\]

Then exactly `r` eigenvalues lie below `mu`, all belong to `[-delta,delta]`, and

\[
 \boxed{A\succeq-\delta I.}                                      \tag{5.2}
\]

If `S=ran 1_{(-infty,mu)}(A)`, then for every unit `v in S`,

\[
 \boxed{\|P_Jv\|^2\ge1-(\delta/\mu)^2.}                          \tag{5.3}
\]

**Proof.** Min–max for `A²` supplies at least `r` eigenvalues with `|lambda|<=delta`. They all lie strictly below `mu`. The upper count leaves room for no others below `mu`, proving the spectral interval and (5.2), including all ties at `+/-delta`.

For `u in J`, the spectrum on `S^perp` lies in `[mu,infty)`, so

\[
 \|(I-P_S)u\|\le\mu^{-1}\|Au\|\le(\delta/\mu)\|u\|.
\]

Thus `P_S|_J` has smallest singular value at least `sqrt(1-(delta/mu)²)`. Both spaces have dimension `r`, so its adjoint `P_J|_S` has the same singular values. This proves (5.3). Eigenvalues equal to `mu` belong to the upper subspace and cause no problem. ∎

The conclusion is a **lower** envelope `-delta`, not positivity when `delta>0`. It is sharp: `A=diag(-delta,2mu)`, `J=span e_0` attains (5.2). A fixed negative eigenvalue cannot hide outside the jet while satisfying the count: it would consume an additional level below `mu`.

### L13. The literal counted package implies RH, even at growing rank

THIS STEP IMPLIES RH.

**[COFINAL_FAMILY | PAPER]** Suppose on an unbounded original family there are genuine `r_m`-dimensional carrier subspaces with

\[
 \Delta_m=\|A_m|_{J_m}\|\to0,\quad
 0\le\Delta_m<\mu_m,\quad N_{A_m}(\mu_m)\le r_m.                  \tag{5.4}
\]

Then RH follows, without requiring `r_m` bounded and without requiring a uniform ratio `Delta_m/mu_m`.

**Proof.** L12 gives `lambda_{m,0}>=-Delta_m`, so L5 applies. ∎

This is the useful repair when the immediate consumer is RH rather than the stronger geometric selection statement. It does not prove (5.4).

For the initial derivative jets in the request, the actual first source inequalities would be

\[
 \Delta_m^2\le
 \frac{\sum_{j<r_m}\|A_mP_mh^{(2j)}\|^2}
      {\lambda_{\min}(M_{r_m,m})}
 <\mu_m^2,\qquad N_{A_m}(\mu_m)\le r_m.                           \tag{5.5}
\]

The displayed quotient must tend to zero. At growing order neither the numerator constants nor the Gram denominator can be borrowed from a fixed-order asymptotic. The spectral count must count **all** negative levels, not only levels with small absolute value.

**Classification versus MARKOV (4.19).** The count alone, with unspecified `n(m)` and `mu_m`, has no definite logical strength: `n(m)=m+1` makes it automatic, and an upper count can allow negative levels. The complete vanishing-residual package (5.4) **implies RH**, and hence would imply the index conclusions classified in MARKOV. The converse for the prescribed initial derivative jets is not established. Calling that package “equivalent to RH” would add an unproved direction. The statement (3.1), by contrast, genuinely **is RH**. No MARKOV index bound is used as a premise in this proof.

### L14. Strict residual separation is insufficient for uniform fixed-jet no escape

THIS STEP IS PROVED HERE.

**[ABSTRACT | PAPER]** The assertion “(5.1) with fixed rank and `delta<mu` implies a uniform positive overlap along a family” is false unless a uniform margin or another argument is added.

**Exact counterexample.** In `ell²(N_0)`, let

\[
 h_* =\sum_{j\ge0}2^{-j}e_j,\quad V_m=\operatorname{span}\{e_0,\ldots,e_m\},
 \quad u_m=P_mh_*/\|P_mh_*\|,
\]
\[
 A_me_j=\varepsilon_me_j\ (j<m),\qquad
 A_me_m=\varepsilon_m^2e_m,\qquad\varepsilon_m=2^{-m^2}.
\]

The bottom `e_m` is simple, positive in eigenvalue, and weakly escapes. Its overlap

\[
 t_m^2=|\langle e_m,u_m\rangle|^2
    =\frac{4^{-m}}{\sum_{j=0}^m4^{-j}}\longrightarrow0.
\]

Nevertheless, with the projected fixed one-jet `J_m=span{u_m}` and `mu_m=epsilon_m`,

\[
 N_{A_m}(\mu_m)=1,\quad
 \Delta_m^2=\varepsilon_m^2(1-t_m^2)+\varepsilon_m^4t_m^2
             <\mu_m^2.                                           \tag{5.6}
\]

Thus all strict counted hypotheses hold, with residual tending to zero, but the uniform no-escape conclusion fails. The ratio `Delta_m/mu_m` tends to one. This example concerns the generic inference, not the theta function or literal arithmetic matrix.

**Repair for a fixed literal jet.** If `r` is fixed and there is a fixed `q<1` such that

\[
 N_{A_m}(\mu_m)\le r,\qquad \Delta_{r,m}\le q\mu_m                 \tag{5.7}
\]

cofinally, L12 and (2.5) give

\[
 \|P_{J_r}f_m\|\ge\sqrt{1-q^2}-\eta_{r,m}.
\]

This proves T. No simplicity is needed: the bound holds for every unit vector in the whole low subspace.

Trying `mu_m=m^(-B)` cannot supply (5.7) at fixed `r`, by L3. A successful fixed-rank count must use a smaller scale or a genuinely different spectral estimate. Merely increasing a finite fixed jet order does not evade that theorem.

### L15. Growing jets need both conditioning and fixed-coordinate tightness to prove T

THIS STEP IS PROVED HERE.

**[ABSTRACT | PAPER]** Even a uniformly separated counted package at growing rank does not imply persistence in a fixed jet.

For an exact plant take `r_m=floor(m/2)`, the coordinate jet `J_m=span{e_0,...,e_{r_m-1}}`, and let `A_m` have eigenvalue `epsilon_m²` on `e_{r_m-1}`, eigenvalue `epsilon_m` on the other jet coordinates, and eigenvalue `1` on the remaining carrier coordinates. With `mu=1/2` and small `epsilon_m`, the count is `r_m`, the Gram matrix is the identity, and `Delta_m/mu=2epsilon_m->0`. The unit bottom nevertheless escapes through the jet order. Every fixed coordinate projection tends to zero.

This plant is positive; it refutes **selection**, not the valid lower-floor conclusion of L13. It also shows that explicit order growth and excellent conditioning, by themselves, do not give T.

Here is a sufficient non-vacuous additional budget. Orthogonalize the fixed derivative sequence once in the global space, giving an orthonormal basis `chi_0,chi_1,...` with
`span{chi_0,...,chi_{r-1}}=J_r`. Suppose an unbounded family satisfies

\[
 \|P_{J_{r_m}}f_m\|^2\ge a>0,
 \qquad \sum_{j<r_m}\omega_j|\langle\chi_j,f_m\rangle|^2\le C,
 \quad \omega_j\uparrow\infty.                                   \tag{5.8}
\]

Choose a fixed `R` with `C/omega_R<a/2`. The mass in coordinates `R<=j<r_m` is at most `C/omega_R`, whence `||P_{J_R}f_m||²>=a/2`. This proves T. Passing from a finite projected jet to the global `J_{r_m}` additionally requires an explicit bound for their projector difference, paid using the growing Gram matrix.

For example, if `R_r` is global derivative synthesis, a usable rank/conditioning control is

\[
 \|(I-P_m)R_r(R_r^*R_r)^{-1/2}\|<1.
\]

It bounds the subspace angle and guarantees that projection has not lost rank. At growing `r` it must be established, not inferred from fixed-rank convergence.

The genuinely unproved source package for **T via counting** can now be written without ambiguity:

\[
 \boxed{\exists r<\infty,\ q<1,\ \mathcal M\text{ unbounded}:\quad
 N_{A_m}(\mu_m)\le r,
 \quad\Delta_{r,m}\le q\mu_m\quad(m\in\mathcal M).}               \tag{5.9}
\]

Alternatively, a growing-rank version needs (5.8). These are sufficient interfaces, not claims that T requires them.

**Q3 answer.** The original unqualified inference to T is refuted by L14, and the growing-rank variant is refuted by L15 without its tightness budget. The repaired counted package gives a valid direct proof route to the RH-equivalent vanishing floor. Its actual source upper count remains unproved. Thus the question's overall code is `PARTIAL_WITH_PRECISE_REMAINDER`, with a scoped `ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE` for the two generic selection shortcuts.

## 6. Q4: what can be said about the limiting ladder

### L16. T needs only one persistent scalar pairing, not a limiting ladder

THIS STEP IS PROVED HERE.

**[ABSTRACT | PAPER]** For a unit sequence `f_m` in the even sector, the following are equivalent:

1. T holds for some fixed finite derivative jet.
2. For some fixed `j`, `limsup_m |<h^(2j),f_m>| > 0`.
3. Some subsequence has a nonzero weak limit in `H_E`.

**Proof.** In a fixed jet, projection norm is the positive-definite Gram quadratic form of its finitely many pairings. Persistent projection therefore forces one of those pairings to persist on a subsequence. The converse is immediate from Cauchy–Schwarz on the jet.

For (2) to (3), take a weakly convergent subsequence of the bounded sequence, and a further subsequence along which the persistent complex scalar converges. Its limit is nonzero. Such weak subsequences exist because the Hilbert space is separable and its bounded balls are weakly sequentially compact.

For (3) to (2), a nonzero weak limit has a nonzero pairing with at least one fixed derivative, by density of their span. That pairing is the limit of the corresponding pairings of `f_m`. ∎

Thus the cheapest sufficient limit is a positive limsup of **one fixed pairing**. Even its limit need not exist. For the actual CCM bottoms this statement implies RH by L6, but it has not been proved here.

### L17. Subsequence fingerprints exist; the nonzero bottom fingerprint is the missing part

THIS STEP IS PROVED HERE.

**[ABSTRACT | PAPER]** From any sequence of orthonormal ordered eigenvectors one can extract a common subsequence on which

\[
 v_{m,i}\rightharpoonup\phi_i\qquad\text{for every fixed }i.
\]

On this subsequence,

\[
 w_i(m)=|\langle v_{m,i},u_m\rangle|^2
       \longrightarrow p_i:=|\langle\phi_i,u\rangle|^2,
 \qquad \sum_{i\ge0}p_i\le1.                                   \tag{6.1}
\]

The family `(phi_i)` is Bessel with bound one; it need not be orthonormal or complete.

**Proof.** Repeated weak subsequence extraction and a diagonal selection give all fixed-index limits. Since `u_m->u` strongly,

\[
 |\langle v_{m,i},u_m-u\rangle|\le\|u_m-u\|\to0,
\]

which proves the pointwise weight convergence. For finite coefficient vectors `(c_i)`, weak lower semicontinuity gives

\[
 \left\|\sum_i c_i\phi_i\right\|^2
 \le\liminf_m\left\|\sum_i c_iv_{m,i}\right\|^2
 =\sum_i|c_i|^2.
\]

The resulting synthesis contraction has an adjoint contraction; hence the Bessel inequality. Fatou applied to the original normalized weights gives the same bound for their sum. ∎

There is also an unconditional **energy-measure** limit which must not be confused with this indexed fingerprint. For

\[
 \nu_m=\sum_i w_i(m)\,\delta_{\lambda_{m,i}},
\]

one has `nu_m => delta_0`, since for every fixed `a>0`,
`nu_m({|lambda|>=a}) <= delta_m²/a² -> 0`. Its entire mass collapses to energy zero. This says nothing about the weight of the first ordered level inside that collapsing cluster. The negative plant (4.5) has this same energy-measure limit while its bottom weight is zero.

The defect `1-sum p_i` represents weight not retained at fixed eigenvalue indices. No theorem here makes it zero. A positive fixed-index weight at `i>0` cannot replace ground weight: it can coexist with an unseen lower negative level. Even weak limits of orthogonal vectors can coincide: `(e_0+e_m)/sqrt2` and `(e_0-e_m)/sqrt2` are orthogonal but have the same weak limit.

If T holds through `h` itself, a subsequence can be chosen with `p_0>0`. If T holds only through a different derivative, it still gives `phi_0!=0`, but it need not give `p_0>0` for the particular fingerprint of `h`. There is no established unique limiting ladder and no identification of `phi_0` with `h`, a heat evolution, or a plateau mixture.

For comparison only: under RH, L2 and min–max imply `0<=lambda_{m,i}->0` for every fixed `i`. Convergence of these eigenvalues does not prove convergence of their eigenvectors. Nor may an unweighted weak limit be inserted into the global Weil form: its zero constraints are not continuous in that topology.

### L18. A compact phase-space observable is an equivalent no-escape witness

THIS STEP IS PROVED HERE.

**[ABSTRACT | PAPER]** Let `P_T^freq` be orthogonal Fourier cutoff to `[-T,T]` in the physical Fourier convention, and put

\[
 C_{R,T}=\mathbf1_{[-R,R]}P_T^{\rm freq},\qquad R,T>0.
\]

For a bounded unit sequence, T is equivalent to the existence of fixed `R,T,epsilon>0` and an unbounded family with

\[
 \|C_{R,T}f_m\|\ge\epsilon.                                      \tag{6.2}
\]

**Proof.** The kernel of `C_{R,T}` is
`1_{[-R,R]}(x) sin(T(x-y))/(pi(x-y))`. Its Hilbert–Schmidt norm squared is `2RT/pi`, so it is compact. A weakly convergent subsequence with (6.2) must have a nonzero weak limit, since compact operators map bounded weakly convergent sequences to strongly convergent sequences.

Conversely, for a nonzero weak limit `phi`, suitable finite `R,T` have `C_{R,T}phi!=0`, because these cutoffs approximate the identity strongly. Compactness then gives (6.2) along that subsequence. Apply L16. ∎

**Attempt to pay this directly from the source.** The archimedean multiplier satisfies an elementary lower bound

\[
 a(t)\ge\tfrac12\log(2+|t|)-C_0.                                \tag{6.3}
\]

One can obtain it without a zero estimate from

\[
 a(t)+c_*=2\sum_{\ell\ge0}
 \frac{t^2}{(2\ell+1/2)((2\ell+1/2)^2+t^2)}:
\]

terms with `2ell+1/2<=|t|` each dominate `1/(2ell+1/2)`, whose partial harmonic sum gives (6.3), with the remaining bounded range absorbed in `C_0`.

For an even unit bottom the odd pole functional vanishes and the even pole square is nonnegative. Therefore the actual eigenrelation gives only

\[
 \langle f_m,A_{\rm arch}f_m\rangle
 \le\lambda_{m,0}+2S_L
 \le\delta_m+4\sqrt m L,
 \quad S_L=\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n}.                \tag{6.4}
\]

Here the final estimate uses only `Lambda(n)<=log n`; it is not a prime asymptotic. Combining (6.3)–(6.4),

\[
 \frac1{2\pi}\int\log(2+|t|)|\widehat f_m(t)|^2dt
       \le2(C_0+\delta_m+4\sqrt m L).                             \tag{6.5}
\]

This grows with `m`. It does not give uniform high-frequency tightness at fixed `T`, and it gives no positive local mass at fixed `R`. The desired compact-observable lower bound (6.2) is therefore still unproved. Replacing its fixed cutoffs by cutoffs escaping with `m` would remove precisely the compactness needed in the proof.

This identifies an additional honest repair path: a source-specific phase-space tightness inequality, not a global limit law. It is an alternative to the blind-tail route, not an extra mandatory premise.

**Q4 answer.** Full weak or strong convergence of the low ladder has not been proved or refuted for the literal source. Weak diagonal subsequences and the subprobability fingerprint (6.1) exist abstractly; their possibly zero ground profile is not a solution. A single persistent fixed pairing, or (6.2), is enough for T and requires much less than constructing the entire limiting ladder.

## 7. Adversarial review, preserved structure, and exact kill scopes

### 7.1 What survives every change of representation

**[ABSTRACT | PAPER]** All source implications use the original `m=N`, `L=log m`, full complex form with parity restriction, and unit physical `L²` normalization. Finite derivative jets are distinguished from their projected images. Growing jets explicitly carry rank and Gram-conditioning costs. Zero modes, spectral multiplicities, both endpoints, and all exterior prime powers remain present.

The move to `A_m²` preserves the magnitude of each eigenvalue but initially loses its sign. L12 restores the missing sign information through the **one-sided** count `lambda<mu`; an absolute-value count is not interchangeable with it. The negative plant (4.5) exposes that error immediately.

The move to whole-line Xi samples requires the correction (4.7). The move to weak limits loses form convergence and orthogonality of the limiting ladder. Neither lost property is silently restored.

### 7.2 The falsifier must test the claimed conclusion

**[ABSTRACT | PAPER]** No-escape and nonnegativity are different properties for general matrices. For example `diag(-epsilon_m,1)` has a nonescaping bottom with a small negative eigenvalue. It would be wrong to demand that a correct abstract test of no-escape reject that true statement. Our implication from T to RH uses the literal-source negative-witness theorem; it is not a general matrix positivity theorem.

Likewise (5.2) is an error-tolerant lower floor, so `-delta` is allowed. What it must reject is an eigenvalue **below** its claimed floor. A persistent hidden `-1` with `delta->0` fails the saturated count and the complete blind-tail bound. No arbitrary negative matrix is admitted as positive.

### 7.3 Scoped falsifications

| Inference rejected | Evidence | Kill scope |
|---|---|---|
| Fixed-jet small residual or near-zero spectral concentration implies T | (4.5), bottom `e_m`, blind-tail mass exactly 1 | THEOREM_SHAPE, generic inference only |
| A pseudoinverse-only blind-tail sum controls overlap at zero eigenvalues | `diag(-1,0,2)`, `u=e_1`; omitted kernel mass 1 | THEOREM_SHAPE |
| Fixed rank, strict `delta<mu`, and the upper count alone give a uniform positive overlap | (5.6), projected fixed `h_*`, ratio tends to 1 | THEOREM_SHAPE |
| Growing jet, excellent conditioning, vanishing residual and a uniform counted angle give T | L15's moving bottom inside a growing coordinate jet | THEOREM_SHAPE |
| A bounded count at a fixed polynomial zero threshold could hold eventually for the literal family | (2.6), for arbitrary fixed rank | THEOREM_SHAPE, literal cofinal count with those quantifiers |

For a claimed overlap floor `||P_J f||² >= epsilon²`, (4.5) gives the exact adjusted upper envelope `-epsilon²`; (5.6) gives at most `4^(-m)-epsilon²<0` eventually. For the bounded-count claim `N_m(mu)<=r`, L3 with rank `r+1` gives `r-N_m(mu)<=-1` eventually. Thus the refutations have negative upper witnesses for the statements actually being rejected, not merely failed sufficient bounds.

The counterexamples do not refute T, the literal low-level blind-tail inequality, or the possibility of a different counted proof. No route-family death is asserted. Every counterexample is exact and reproducible without a numerical spectrum.

### 7.4 Executed controls

Four controls were registered before their exact symbolic execution: persistent hidden negative direction; the sharp lower-floor/angle algebra; projected fixed-vector escape when the ratio tends to one; and invisible excited kernel mass. All four passed exact rational/symbolic checks. The first harness used structural equality between expanded and factored polynomials, which returned false; it was replaced by checking that their difference simplifies to zero. No mathematical prediction or test inequality was changed.

These executions validate finite algebra only. They are not an independent analytic review, an interval certificate, or a run on the literal CCM matrices. The infinite-family proofs above do not rely on a finite sample of the plants.

## 8. Dependency audit, route choice, and prediction closeout

### 8.1 Consumer-first contract

**DOWNSTREAM_CONSUMER:** exclude an actual off-critical zero using the original-cell negative witness; for the geometric route, establish T.

**ACTUAL_CONSUMER_REQUIREMENT:** either persistent fixed-profile overlap T, or the weaker sufficient lower-floor conclusion (3.1) proved directly without selecting a profile.

**ORIGINAL_REQUESTED_OBJECT:** T and, for the one-jet attempt, (4.9).

**ORIGINAL_OBJECT_IS:** `UNKNOWN` as a necessary condition for RH. T implies RH; RH implying T is not established. A full limiting ladder is `NOT_NECESSARY` for T.

**KNOWN_WEAKER_INTERFACES:** one fixed scalar pairing with positive limsup implies T by L16; a fixed compact observable with positive limsup implies T by L18. A saturated count plus a vanishing residual implies (3.1) directly by L12–L13, even when it does not imply T.

**FAILURE_TYPE:** `NO_DERIVATION` for the actual source estimates (4.6), (4.9), (5.5)/(5.9), and (6.2). `COUNTEREXAMPLE` only for the scoped generic shortcuts in §7.3.

**EPISTEMIC_STATUS:** `UNRESOLVED` for the source targets. In the protocol's bookkeeping vocabulary these are recheckable research obligations, not mathematical impossibility. This terminology does not replace the explicit statements “T implies RH” and “the vanishing lower floor is RH.”

**NOVELTY_AXIS:** signed Xi-tail/exterior separation; singular-value min–max with a one-sided counting guard; physical versus index-space compactness.

**REOPEN TRIGGERS:** a verified estimate of the complete inverse-weighted low leakage with margin below one; or a source upper count at a scale above the actual jet residual, including its conditioning; or a fixed phase-space lower bound. New precision, a larger finite plateau, or an unweighted tail envelope is not such a trigger.

### 8.2 Two viable representations, and why neither is declared a supplier yet

| Representation | Exact useful object | Potential decisive power / estimated cost | Principal failure risk |
|---|---|---|---|
| Signed leakage in the low spectral metric | `(F_i+X_i)/(Z_m lambda_i)`, with kernel guards | High: would prove the requested one-jet T; medium cost for the bounded discriminator, high for a cofinal proof | Termwise estimates destroy the cancellation, or the exterior correction is magnified by the low inverse |
| Saturated count / phase-space tightness | A rank-conditioned quasimode space plus the one-sided count; alternatively a fixed compact observable | High: can prove RH without a full ladder; high analytic cost | Polynomial thresholds contain too many levels; growing order hides escape rather than stopping it |

These are candidates with explicit tests, not authorization for a larger scan. The primary choice remains the first: determine the actual signed source contribution before attempting any new inverse-weighted estimate. The counted route is retained as a mathematically valid alternative, with its exact obstructions now visible.

Three bridge checks have been completed: finite-dimensional singular-value geometry gives L12; the radical identity gives (4.8) but does not make its remainder zero; compact-operator theory gives L18 but requires an actual source lower bound. No unproved external spectral theorem is used to jump between these domains.

### 8.3 Frozen predictions

| Prediction | Fate in this batch |
|---|---|
| P1: Q1 complete / partial / refuted | `PARTIAL_WITH_PRECISE_REMAINDER`. T itself is not refuted. |
| P2: `v_1` carried by the Xi tail rather than exterior primes | **Not decided.** L10–L11 separate the terms but do not give their relative sizes on `v_1`. |
| P2: a cofinal bound with fixed `c<1` | **Not established.** No retroactive positive score. |
| P3: the threshold index statement is equivalent to RH | **Not confirmed as stated.** The count lacks quantified scales and residual guards. The complete package implies RH; a vanishing lower floor is proved equivalent; necessity for the prescribed jets is not proved. |
| P4: a full limiting ladder with `phi_0 != h` exists | **Not decided.** Weak subsequential extraction is not that assertion. |

The four newly registered algebra controls in §7.4 were confirmed. They are distinct from the observer's scientific predictions.

### 8.4 What became smaller

The unknown is no longer “does a small residual select the bottom?” That implication is false. For the actual one-jet source it is exactly the **low excited inverse-weighted** budget (4.6), with the signed components (4.8) and zero-mode guard included. The absolute exterior error is now explicit. The alternative counting interface has a proved lower-floor consumer and precise restrictions on threshold scale, rank, ratio, and coefficient tightness.

No actual persistent overlap, limiting profile, or source upper count was supplied. Thus this is proof progress on family-level spectral structure and the correctness of the transfer, not completion of the requested RH-implying target.

```yaml
iteration:
  target: GOAL058_FIXED_JET_NO_ESCAPE_ON_LITERAL_CCM_BOTTOMS
  status: OPEN
  failed_strategy: UNWEIGHTED_RESIDUAL_NORM_AS_GROUND_SELECTION
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: MANY_NEAR_ZERO_LEVELS_DO_NOT_IDENTIFY_THE_BOTTOM
  forbidden_future_move: DROP_EXTERIOR_COEFFICIENT_CORRECTION_OR_EXCITED_KERNEL_MASS
  smallest_open_inequality: COMPLETE_LOW_EXCITED_INVERSE_WEIGHTED_SIGNED_LEAKAGE_LE_C_LT_1
  next_decisive_test: SOURCE_RESOLVED_V1_LEAKAGE_WITH_CERTIFIED_RELATIVE_REMAINDER
  actual_T_progress: NOT_CLOSED
  route_score: 4
```

## 9. Proshka's own line

I take the request literally: the objective is a proof of RH through no escape.
The equivalence or implication is not an objection to the objective.
The question is which independent estimate supplies the positive overlap.
The strongest unconditional geometry presently supplied is clustering near energy zero.
It is not selection of the lowest point in that cluster.
I chose the inverse-weighted leakage first because it measures exactly the missing mass.
I did not choose another residual-norm improvement because that loses the low spectral weights.
I did not choose a full limiting ladder because T needs much less.
The useful surprise is that singular-value min–max gives a lower floor from a saturated count.
That conclusion does not need an isolated ground state.
It may eventually be a shorter route to RH than proving T itself.
But the upper count is the difficult half, and a polynomial threshold cannot keep bounded rank.
The exterior calculation is also useful: the Xi samples have a precise correction.
An exponentially small absolute error can still be enormous after division by an excited level.
I distrust any claim about the v_1 component inferred from the norm of the whole residual.
I also distrust a growing jet unless both its conditioning and its coefficient tightness are visible.
My first move beyond this batch is to split the existing v_1 leakage into its signed terms.
A large exterior-to-total ratio would falsify the proposed tail-localization mechanism.
My second move is to seek a source upper count at the actual residual scale.
Extra clustered levels would kill that chosen threshold, not the mathematical route.
For that move I would ask for exact Gram and residual matrices, not just principal angles.
For the first move I would ask for the retained eigenpairs and the actual window Fourier coefficients.
A tiny measured angle is useful for choosing an object, not for spending a cofinal quantifier.
The lower-floor route and the geometric selection route should no longer be conflated.
A proof of either appropriate source estimate would be a real advance, not a cosmetic reformulation.
Until then, the complete proof of T is not present in this verdict.

## 10. Research log and source register

All repository sources below were read at `bdea6ec1e117c04da9e72528695caa1cfd0dc0ca`, except the request and bootstrap protocol as explicitly stated. Source locators are code-form URLs or repository paths so the artifact remains self-contained. The primary article was read as arXiv v1; binary byte identity with the shelf PDF was not independently hashed in this session. No later paper version is substituted for a quoted v1 statement.

| ID | Status and pinned locator | Exact use / limitation |
|---|---|---|
| S0 | READ: `Malaeu/chen_q3@1a23edcd44d6e95bafa2929396188f47312a270b:docs/routeB_bus/proshka/PROSHKA_REQUEST_NOESCAPE_2026-10-30.txt`; blob `96d3527d0248d4f5022893d5a301f4987f1e3672` | Complete authoritative request; SHA-256 and byte/line counts independently recomputed. |
| S1 | READ: `docs/routeB_bus/proshka/PROSHKA_VERDICT_CONFINE_2026-10-30.md`; blob `1879347b72d1aa55cf506f5387de37059f929122`; SHA-256 `57088a914942b0dd1c3d1835edaca2f223a59831d78350c0a092356024852ddb` | §§1–4 and §5.1: literal form, dense derivatives, cutoff quasimodes, separate negative tests and diagonal return, leakage Gram identity. |
| S2 | READ: `docs/routeB_bus/proshka/CODEX_AUDIT_CONFINE_2026-10-30.md`; blob `fd9561b57bc8fb505c095d567162a03e67e2deb6` | Eight analytic steps reported clean; one completed methodological pass, formal second pass requested. Not a kernel certificate and not a review of the present verdict. |
| S3 | READ: `docs/BATCH_PATTERNS.md`; blob `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | Proof-batch requirements; this is the only non-bus `docs/` source opened in this batch. |
| S4 | READ: `docs/routeB_bus/thetagrade_2026-10-28/overlap_gap_probe.py`; blob `fcac8440c2acda67c0e2d6005ba0e2b528841502` | Raw window projection and spectral-weight definitions; projection quadrature internally uses 50 dps. Script was not run. |
| S5 | READ: `docs/routeB_bus/thetagrade_2026-10-28/quasimode_xi_tail.py`; blob `feffed82b1bd96dc250b8e78cd64e7aab2f18649` | Diagnoses the sampled whole-line tail approximation, finite `6m` truncation and missing exterior correction. Script was not run. |
| S6 | READ: `docs/routeB_bus/thetagrade_2026-10-28/jet_cluster_probe.py`; blob `b766d87200a139560609c393a57ae5f03ba7f2be` | Confirms operator-norm residual and principal-angle objects; projection quadrature uses 60 dps. Script was not run. |
| P1 | READ: CCM, *Zeta Spectral Triples*, `https://arxiv.org/pdf/2511.22755v1` and v1 HTML; Lemma 2.3, §3 explicit formula, Proposition 3.4, Corollary 3.8 | Checked source normalization and the distinction between fixed-window core convergence and the required diagonal return. PDF pages 4–5 visually inspected; no new global convergence supplier is imported. |
| Protocol | READ: `Malaeu/chen_q3@rh_clean:docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`; blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13` | Bootstrap and adjudication format; read through the response-format end. |
| Numerical request table | RELAY / DIAGNOSTIC, not a theorem premise | No JSONL result was independently rerun or converted into an interval certificate. |

### Attempt branches rejected or left open

**[ABSTRACT | PAPER]** Unweighted residual to bottom overlap: rejected by the exact family (4.5). Weak/strong resolvent convergence to bottom convergence: rejected by the same family. Omitting zero-eigenspace mass: rejected by `diag(-1,0,2)`. Strict counted separation to a uniform fixed-jet overlap: rejected by (5.6). Growing rank plus conditioning to fixed-order persistence: rejected by L15. Polynomial threshold with a bounded source count: refuted by (2.6). Whole-line Xi samples as exact window coefficients: corrected by (4.7). Exterior absolute smallness as relative low-level smallness: estimate (4.16) leaves the denominator unpaid. Full limiting ladder construction: not attempted as a mandatory supplier because L16 shows it is unnecessary. The direct phase-space energy route yields (6.5), not a fixed compactness budget.

### Reusable intermediate results

**[ABSTRACT | PAPER]** The rank-saturation implication (5.2) is useful for any Hermitian family with a genuine low-residual subspace. The weak fingerprint (6.1) is useful when numerical weight profiles appear stable but indexed mass might escape. The periodization correction (4.12) is useful whenever a window Fourier tail is estimated from samples of a whole-line transform. The compact-observable equivalence (6.2) gives a physical alternative to coefficient-index tightness. None supplies its unproved source inequality automatically.

## 11. One next directive

**CODEX DIRECTIVE — source-resolved `v_1` leakage discriminator, read-only, on an already computed cell.**

Use the existing `m=16` or `m=20` even-sector eigenpair and the exact source normalization; do not launch a new range scan. Resolve the two terms `F_{m,1}` and `X_{m,1}` of (4.8), with the explicit periodization correction and all exterior prime powers. Enclose the complete Fourier-sum and quadrature remainders **relative to** `Z_m |lambda_{m,1} a_{m,1}|`, not relative to the unweighted residual norm. Independently check

\[
 F_{m,1}+X_{m,1}+Z_m\lambda_{m,1}a_{m,1}=0.
\]

The identity is a normalization/control test, not evidence for a cofinal inequality. If the retained eigenpair is only floating-point, its eigenvector and eigenvalue error must be included; merely increasing printed precision is not a certificate. If no cached eigenpair or certified relative budget is available, report that exact missing input rather than treating the comparison as complete.

**Discriminator:** certify either `D_m^ext < 1/4` or `D_m^ext >= 1` from (4.17); otherwise return an inconclusive enclosure with the missing error term. The first outcome supports a Fourier-tail-dominant mechanism on that cell; the second falsifies neglect of the exterior correction on that cell. Neither is a cofinal proof of T. Do not proceed to a proposed low-cluster estimate until this source attribution is resolved.

**Final boundary.** T and the fixed-`c<1` blind-tail inequality remain unproved and unrefuted on the literal family. The new results are PAPER proofs of spectral clustering, exact tail bookkeeping, and guarded implications/counterexamples. They are not independently reviewed or formally verified. RH, cofinal G1a and G3 remain open; no repository write, Lean execution, or literal CCM numerical scan was performed.
