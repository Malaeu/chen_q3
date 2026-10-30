# STATUS: TRY_MARKOV_BULK_WITH_INDEX_GUARD

```yaml
OPERATIVE_CLASS: TRY_MARKOV_BULK_WITH_INDEX_GUARD
REQUEST_ID: REQ-2026-10-29-MARKOV
BOUNDARY_ID: GOAL058_G1A_PF_BULK_AND_TWO_SECULAR_SCALARS
REQUEST_COMMIT: cfe490d950758d0a8b1e53d7a76a29d9ab671f0d
REQUEST_GIT_BLOB: 9f299b2a4f17802018a00790b3044ad4ab06d6c0
REQUEST_SHA256: f59076d74630a2656be28e0f8e2898636faa44f1a906e1a5cc9cb1825bb26548
REQUEST_BYTES: 10530
REQUEST_LINES: 171
REQUEST_FINAL_LF: true
REQUEST_HASH_VERIFIED: true
SOURCE_BASE_COMMIT: ab6394323c40ed2c1b0a720778f0fb09662dc0bb
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_SELECTED_FERRERS_FAMILY
Q1: MARKOV_PROVED
Q1_SCOPE: CONTINUUM_FULL_WINDOW_POLE_FREE_OPERATOR_ALL_L_POSITIVE
Q1_FINITE_FOURIER_COMPRESSION: MARKOV_PARTIAL
Q1_FINITE_FIRST_UNPAID: UNIFORM_FIXED_WINDOW_GALERKIN_RETURN_ON_THE_N_EQUALS_M_SCHEDULE
Q2a: REDUCTION_CORRECTED
Q2b: INDEX_RH_GRADED
Q2b_SCOPE: EACH_INDEX_BOUND_SEPARATELY_ON_AN_UNBOUNDED_ORIGINAL_N_EQUALS_M_FAMILY
Q2b_NEW_RESULT: OFFLINE_ZERO_FORCES_TWO_NEGATIVE_EVEN_BULK_DIRECTIONS_AND_ONE_NEGATIVE_ODD_BULK_DIRECTION_EVENTUALLY
Q2c: EXACT_SECULAR_DESCRIPTION_WITH_UNTOUCHED_EIGENVALUES_RETAINED
Q3: REDUCED_TO_FIRST_UNPAID
Q3_FIRST_UNPAID: POSITIVE_SECTOR_SUSCEPTIBILITY_BUDGETS_OR_EQUIVALENT_THETA_WEIGHTED_JUMP_INEQUALITY
G1A_FOR_K_PROVED: false
SECULAR_SIGNS_PROVED_COFINAL: false
INDEX_BOUNDS_PROVED_COFINAL: false
VERIFIER: PAPER
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: CONTINUUM_MARKOV_THEOREM_AND_SOURCE_SPECIFIC_INDEX_EQUIVALENCES
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
EXACT_SYMBOLIC_CONTROLS_EXECUTED: true
NEW_LITERAL_CCM_NUMERICAL_SCAN: false
ARB_INTERVAL_EXECUTED: false
LEAN_EXECUTED: false
REPOSITORY_WRITTEN: false
INDEPENDENT_REVIEW_CLAIMED: false
ROUTE_PROMOTION: false
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## 0. Decision

**Q1: `MARKOV_PROVED`, for the pole-free continuum operator on every bounded window.** The exact bulk is a killed symmetric jump Dirichlet form minus a finite constant. Its semigroup is positivity improving; it has compact resolvent and a simple, positive-a.e., reflection-even ground state. This is a theorem about the full window, **not automatically about its finite Fourier compression**. At integer `m >= 2`, its lowest eigenvalue is negative; “positive ground state” refers to the eigenfunction, not the eigenvalue.

**Q2(a): `REDUCTION_CORRECTED`.** The two advertised scalar signs are correct on the invertible, one-negative-even/positive-odd branch. Singular blocks require kernel-orthogonality and Moore–Penrose inverses. The nonnegative-even branch is a separate case. All these cases are classified below.

**Q2(b): `INDEX_RH_GRADED`, separately for each cofinal index bound.** This is stronger than saying that PF cannot prove an index. If an off-critical zero exists, an explicit construction gives, on **every sufficiently late original cell with `N=m`**,

\[
 n_-(G_{m,E})\ge2,\qquad n_-(G_{m,O})\ge1.                 \tag{0.1}
\]

The construction uses **two separately designed, pole-annihilating parity tests**, not the killed inference from one negative full-space vector to two negative parity vectors. The growing-window/Fourier-projection return is paid in §4. Thus either `n_-(G_{m,E}) <= 1` or `G_{m,O} >= 0` on an unbounded original family would already exclude off-critical zeros. Conversely RH implies both bounds; an elementary constant trial makes the even index exactly one for every `m >= 2`.

This does **not** show that the simple-even condition G1a for `K` is RH-equivalent. Bulk index control, positivity of `K`, and parity ordering of `K` are different statements.

**Q3: `REDUCED_TO_FIRST_UNPAID`.** A positive Feynman–Kac integral cannot be continued through the negative bulk ground-state pole while retaining its positive-measure meaning. Ground-pole subtraction gives exact, competing positive quantities, not their required ordering. An additional exact representation in §6 expresses the original Weil form as a positive theta-weighted jump energy minus explicit variance terms. The missing inequality is displayed with constant **8**, all prime powers, and the exterior contribution retained. It is not asserted proved.

### Source and verification boundary

The request was fetched through the GitHub connector at the owner-specified commit. The returned UTF-8 text was materialized locally and independently hashed: **10,530 bytes, 171 LF-terminated lines, both supplied hashes match**. A direct raw-network download was unavailable; it was not used as evidence. The matching SHA-256 and Git-blob computation establish the byte match of the connector-delivered payload.

Repository mathematical reads were pinned to `ab6394323c40ed2c1b0a720778f0fb09662dc0bb`; only the required bootstrap protocol was read from `rh_clean`. The preceding STIELTJES attachment was available locally and matched its full shelf SHA-256. Other repository source reads are identified by their pinned path and connector-reported blob; I do not claim independently to have recomputed every shelf hash. No repository edits, Lean execution, interval certification, or new literal CCM eigensolver scan occurred. All new universal mathematical claims here have **PAPER**, not LEAN, status.

### Claim ledger

| ID | Scope / verifier | Result established | Boundary |
|---|---|---|---|
| M1 | ABSTRACT / PAPER | Exact jump-form identity, domain and compactness, §2 | Full-window operator |
| M2 | ABSTRACT / PAPER | Positivity improvement and simple positive even bulk ground state, §2 | Not inherited by Fourier compression |
| M3 | FINITE_CELL / PAPER | The constant source mode has strictly negative bulk energy for every `m >= 2`, §3 | Proves at least one even negative eigenvalue, not at most one |
| M4 | ABSTRACT / PAPER | Complete rank-one inertia and singular-case classification, §3 | Scalar signs remain inputs |
| M5 | COFINAL_FAMILY / PAPER | Off-line-zero implication (0.1), including diagonal `N=m` return, §4 | Conditional branch inside an unconditional implication; no off-line zero is asserted |
| M6 | COFINAL_FAMILY / PAPER | Each cofinal index bound is equivalent to RH, §4 | Neither index bound is proved |
| M7 | ABSTRACT / PAPER | Secular characterization and a sufficient strict parity bracket, §5 | Requires signed arithmetic estimates and guards against untouched levels |
| M8 | ABSTRACT / PAPER | Exact susceptibility and theta-weighted jump identities, §6 | Their sharp domination inequalities remain open |
| M9 | ABSTRACT / PAPER | Explicit counterexamples to PF sign transfer and Fourier-compression inheritance, §§2, 7 | Synthetic plants are not alternative arithmetic CCM matrices |
| M10 | FINITE_CELL / PAPER | Full `K`, unlike `G`, fails positivity preservation at the continuum window `m=2`, §2.6 | Does not refute a simple positive ground state or G1a |

## 1. Source object and normalization

**[ABSTRACT / PAPER]** Work first in physical logarithmic coordinates

\[
 I_L=(-L/2,L/2),\quad L>0,\quad \widetilde f=0\ \text{outside }I_L,
 \quad \widehat f(z)=\int_{\mathbb R}f(x)e^{-izx}\,dx.
\]

Use the antilinear-first `L²(dx)` inner product. For quadratic expressions put

\[
 Q_f(s)=2\Re\int_{\mathbb R}\overline{\widetilde f(x)}\widetilde f(x+s)\,dx,
 \quad a_n=\log n,\quad c_n=\frac{\Lambda(n)}{\sqrt n},
 \quad j(s)=\frac{e^{-s/2}}{1-e^{-2s}}\quad(s>0).             \tag{1.1}
\]

The literal archimedean term has multiplier

\[
 a(\xi)=\Re\psi(1/4+i\xi/2)-\log\pi,
 \qquad a(0)=-c_*,
 \quad c_*=\gamma+\log(8\pi)+\pi/2.                         \tag{1.2}
\]

The pole-free bulk form is

\[
 \mathfrak g_L[f]=\frac1{2\pi}\int_{\mathbb R}a(\xi)|\widehat{\widetilde f}(\xi)|^2\,d\xi
       -\sum_{2\le n\le e^L}c_nQ_f(a_n).                   \tag{1.3}
\]

These are the archimedean and prime terms of the exact CCM form, not an asymptotic replacement [S2; P1, equations (3.8)–(3.20)]. An atom at `a_n=L` has zero correlation almost everywhere. Keeping that atom is harmless and preserves the literal endpoint convention.

Define the two **physical pole functions**

\[
 p(x)=\sqrt2\cosh(x/2),\qquad q(x)=\sqrt2\sinh(x/2).
\]

Then

\[
 \mathfrak k_L[f]=\mathfrak g_L[f]+|\langle p,f\rangle|^2-|\langle q,f\rangle|^2,
 \quad p(x)p(y)-q(x)q(y)=2\cosh((x-y)/2).                  \tag{1.4}
\]

Here `q` is the odd pole function, **not** the selected Ferrers trial row.

**[FINITE_CELL / PAPER]** On the source basis

\[
 \psi_{n,L}(x)=L^{-1/2}e^{2\pi in(x+L/2)/L},\qquad -N\le n\le N,
\]

let `P_{L,N}` be orthogonal projection and `G_{m,N}` the matrix of (1.3), with `L=log m`. Integration gives

\[
 \operatorname{coeff}(P_{L,N}p)=\sqrt\kappa\,u,
 \quad \operatorname{coeff}(P_{L,N}q)=i\sqrt\kappa\,v,
\]
\[
 \kappa=32L\sinh^2(L/4),\quad
 u_n=\frac{L}{L^2+16\pi^2n^2},\quad
 v_n=\frac{4\pi n}{L^2+16\pi^2n^2}.                        \tag{1.5}
\]

Consequently

\[
 K_{m,N}=G_{m,N}+\kappa(uu^T-vv^T).                        \tag{1.6}
\]

The `i` in the physical odd pole coefficients cancels in its Hermitian rank-one matrix. This is why a real odd coefficient vector synthesizes an imaginary odd function in this complex Fourier basis. It must not be “realified” by dropping the function's imaginary part.

All finite-family results below use **exactly `N=m`** unless explicitly described as fixed-window Galerkin facts. The original carrier, the identity Gram metric, all prime powers and the full archimedean diagonal are preserved.

## 2. Q1 — the full-window Markov theorem

### 2.1 Exact Dirichlet form, with the boundary retained

**[ABSTRACT / PAPER]** The integral representation of the digamma function gives

\[
 a(\xi)-a(0)=2\int_0^\infty j(s)(1-\cos(\xi s))\,ds.
\]

Thus, with `S_L=Σ_{2<=n<=e^L} c_n`,

\[
 \boxed{\mathfrak g_L[f]=\mathcal D_L[f]-(c_*+2S_L)\|f\|_2^2,}            \tag{2.1}
\]
\[
 \mathcal D_L[f]=\int_0^\infty j(s)\|\widetilde f(\cdot+s)-\widetilde f\|_2^2\,ds
       +\sum_{2\le n\le e^L}c_n\|\widetilde f(\cdot+a_n)-\widetilde f\|_2^2. \tag{2.2}
\]

The symmetric Lévy measure is

\[
 \nu_L(ds)=j(|s|)\,ds+
       \sum_{2\le n\le e^L}c_n(\delta_{a_n}+\delta_{-a_n})(ds).           \tag{2.3}
\]

Indeed, `j(s)~1/(2s)` at zero and `j(s)=O(e^{-s/2})` at infinity, so
`∫(1∧s²)ν_L(ds)<∞`. The extra potential in (2.1) is a bounded constant for each fixed window. It is **not uniformly bounded as `L→∞`**.

The form domain is the maximal finite-energy, zero-extension domain

\[
 \mathcal F_L=\{f\in L^2(I_L):\mathcal D_L[f]<\infty\}.
\]

It is not replaced by `H¹₀(I_L)`. In Fourier coordinates its norm is equivalent, for fixed `L`, to

\[
 \int_{\mathbb R}\bigl(1+\log(2+|\xi|)\bigr)
                 |\widehat{\widetilde f}(\xi)|^2\,d\xi.                 \tag{2.4}
\]

Closure follows either from the nonnegative translation-difference integral and Fatou's lemma, or from the complete weighted Fourier space with the closed support constraint. Smooth compactly supported functions form a core: an inward dilation followed by mollification stays within the window and converges in (2.4). The prime part is a bounded form perturbation.

For every normal contraction `C` with `C(0)=0` and Lipschitz constant at most one,
`|C(f(x))-C(f(y))|<=|f(x)-f(y)|`; therefore `D_L[C(f)]<=D_L[f]`. This proves the Dirichlet/Markov property of **`D_L`**. The shifted form `g_L` need not be nonnegative or generate a sub-Markov contraction semigroup.

**Boundary warning.** Writing (2.2) only over `I_L × I_L` produces an additional killing density

\[
 k_L(x)=\int_{\mathbb R}\mathbf1_{\{x+s\notin I_L\}}\,\nu_L(ds).
\]

Its archimedean part grows logarithmically near the endpoints. It is not a bounded potential. It belongs to the killed Dirichlet form itself. The phrase “Dirichlet form plus bounded potential” is correct in (2.1), **not** after discarding this exterior killing term.

### 2.2 Positivity improvement, without assuming an index

**[ABSTRACT / PAPER]** The continuous jump density is strictly positive between every two distinct points of the window. Here is a direct semigroup proof that avoids an unproved irreducibility assertion.

Since `j` is decreasing, choose `c=j(L)>0` and remove from `ν_L` the finite positive measure
`c 1_{|s|<L} ds`. Its killed generator on `I_L` is

\[
 2cL\,I-cJ,\qquad (Jf)(x)=\int_{I_L}f(y)\,dy.
\]

The remaining jump form has a nonnegative self-adjoint generator `A` whose semigroup is positivity preserving. Consequently

\[
 G_L=A+(2cL-c_*-2S_L)I-cJ.                                \tag{2.5}
\]

The Dyson expansion in the bounded positive operator `cJ` has positive terms. For nonzero nonnegative `f,g`, its first-order term has matrix element

\[
 c\int_0^t
  \langle e^{-(t-s)A}g,1\rangle\,
  \langle1,e^{-sA}f\rangle\,ds>0.                         \tag{2.6}
\]

Each factor is strictly positive: a positivity-preserving self-adjoint heat operator is injective, hence sends a nonzero nonnegative vector to a nonzero nonnegative vector. The scalar exponential in (2.5) does not affect the sign. Thus

\[
 \langle g,e^{-tG_L}f\rangle>0\qquad(t>0),
\]

equivalently `e^{-tG_L}f>0` almost everywhere.

The embedding `(F_L,form norm) → L²(I_L)` is compact. To see this directly, (2.4) uniformly suppresses Fourier mass above `R` by `O(1/log R)`; low-frequency translation differences tend uniformly to zero, and physical support is fixed. The `L²` compactness criterion applies. Hence `G_L` has compact resolvent and an attained lowest eigenvalue.

Positivity improvement makes that lowest eigenvalue simple, with a positive-a.e. eigenfunction `φ_L`. Reflection commutes with the operator. Reflection of `φ_L` is another positive normalized ground state, so simplicity forces it to be the same state. Therefore

\[
 \boxed{\phi_L>0\ \text{a.e.},\qquad \phi_L(-x)=\phi_L(x),
        \qquad\langle p,\phi_L\rangle>0.}                 \tag{2.7}
\]

The strict parity ordering `λ₀(G_{L,E})<λ₀(G_{L,O})` follows for the continuum operator. There is no asserted uniform gap in `L`.

Suzuki's §5.2 proves positivity improvement for his limiting small-window form. I read the primary PDF and checked the relevant pages visually [P2]. Equations (2.1)–(2.7) are a separate full-window calculation for the **pole-free** bulk, with the finite prime jumps retained; they do not misquote Suzuki as proving this claim for the full Weil form.

### 2.3 What survives Fourier compression

**[FINITE_CELL / PAPER]** On `V_{L,N}=span{ψ_n:|n|<=N}`, the restricted form remains closed, Hermitian, reflection invariant, and exactly the source compression. The identity (2.1) still holds on this subspace. What fails as an automatic argument is closure under normal contractions: `|f|`, `min(1,max(0,f))`, and positive parts need not lie in `V_{L,N}`. Fourier projection itself is not positivity preserving.

A **synthetic exact inheritance counterexample** is useful. On the circle let

\[
 A=M_{1+\cos x}+\tfrac14(I-\Pi_{\rm const}).
\]

This is a bounded potential plus a complete-graph jump generator. Its full semigroup is positivity improving. Compress it to Fourier degree one. For `f=1-cos x>=0`, `f(0)=0`, the even coefficient matrix in the basis `(1,cos x)` is

\[
 T=\begin{pmatrix}1&1/2\\1&5/4\end{pmatrix}.
\]

Direct exponentiation gives

\[
 (e^{-tT}f)(0)=
 -\frac2{\sqrt{33}}e^{-9t/8}\sinh(\sqrt{33}\,t/8)<0\qquad(t>0).          \tag{2.8}
\]

Continuity makes the output negative on an interval, not merely at one point. This refutes inheritance of physical-cone positivity under Fourier compression. It is **not** a counterexample to the literal `G_{m,m}`.

For **fixed `L`**, the Fourier spaces form a nested form core. Rayleigh–Ritz convergence and the isolated simple continuum ground state imply that, for sufficiently large `N=N₀(L)`, the compressed bottom is simple and even, and its pairing with `P_{L,N}p` is nonzero. This does not prove pointwise positivity of the compressed eigenfunction. More importantly, no uniform bound proving `m>=N₀(log m)` has been supplied. That is the first unpaid finite-schedule step.

### 2.4 A finite discretization that really preserves the cone

**[ABSTRACT / PAPER]** Use normalized indicators of a reflection-symmetric interval partition. They lie in the logarithmic form domain. Distinct basis functions have disjoint supports, so their off-diagonal bulk pairings are strictly negative from the archimedean kernel, with additional nonpositive prime contributions. The resulting irreducible symmetric matrix has a positivity-improving semigroup in its physical-cell cone. Its form is a weighted graph Dirichlet form plus killing and the same bounded scalar potential.

This is the correct finite **Markov** object. It is not the literal Fourier matrix. Replacing the source carrier by it without a controlled comparison would be an unauthorized family swap. It can serve as a comparison model only after a same-window form or spectral error bound pays the return.

### 2.5 Diagnostic source correction

**[FINITE_CELL / PAPER: code audit]** `pf_probe.py` synthesizes a real eigensolver vector in the complex exponential basis and then applies `mp.re` [S3]. A real odd vector synthesizes a purely imaginary odd function. An exact planted odd vector therefore produces zero after this operation. The function-sign diagnostic is not armed against an odd-bottom branch. Repair it by a common phase making the synthesized function real, or by using an explicit real cosine/sine basis. The reported even cases are not disproved by this finding, but the code cannot certify a parity-independent “no sign changes” claim. A finite interior grid, with a 2% boundary margin, is not a global function-sign certificate either.

### 2.6 The pole term is a genuine obstruction for full `K`

**[FINITE_CELL / PAPER]** This is a statement about `K`, not a refutation of (2.7). At `L=log 2`, take smooth nonnegative nonzero bumps `f,g` supported respectively in

\[
 (-1/4-1/100,-1/4+1/100),\qquad
 (1/4-1/100,1/4+1/100).
\]

Both supports lie in `I_L`; their separation is between `12/25` and `13/25`, below `log 2`. No prime shift contributes. Their full cross pairing is

\[
 \mathfrak k_L(f,g)=\iint[2\cosh((x-y)/2)-j(|x-y|)]f(x)g(y)\,dxdy.
\]

For the relevant separations,

\[
 j(s)<\frac1{1-e^{-24/25}}<\frac{1513}{888}<2,
\]

using `e^(24/25)>1+24/25+(24/25)^2/2=1513/625`. Therefore

\[
 \mathfrak k_L(f,g)>
 \frac{263}{888}\Bigl(\int f\Bigr)\Bigl(\int g\Bigr)>0.                \tag{2.9}
\]

Disjoint positive functions with positive cross pairing violate positivity preservation of the full `K` semigroup. This is a rigorous obstruction to applying the same Markov argument directly to `K`, **not** an obstruction to a simple even ground state of `K`.

**Q1 result and unpaid term:** `MARKOV_PROVED(CONTINUUM_FULL_WINDOW, ALL L>0)`; for the literal growing Fourier schedule, `MARKOV_PARTIAL(UNIFORM_GALERKIN_RETURN)`. No claim of `MARKOV_REFUTED` for the pole-free continuum bulk is made.

## 3. Q2(a) — the exact two-scalar classification

### 3.1 One negative even bulk direction is unconditional

**[FINITE_CELL / PAPER]** The constant source mode is available for every `N>=0`. Its prime contribution is nonpositive. From the literal archimedean diagonal [S2], for `L>=log 2`,

\[
 \mathfrak g_L[L^{-1/2}\mathbf1_{I_L}]
 \le 1-\gamma-\log\bigl(4\pi\tanh(L/2)\bigr)
 \le 1-\gamma-\log(4\pi/3)<0.                             \tag{3.1}
\]

For the first inequality, use
`e^(s/2)(1-s/L)-1 >= -s/L` in the integral and
`(1/L)∫_0^L s/sinh(s) ds <= 1`. Hence

\[
 n_-(G_{m,N,E})\ge1\qquad(m\ge2).
\]

This pays **at least one**, not **at most one**. The distinction is load bearing.

### 3.2 Positive rank-one lift: all cases

**[ABSTRACT / PAPER]** Let `A=A*`, `κ>0`, and `A⁺=A+κuu*`. The statements below apply to finite matrices, and also to the present compact-resolvent operators with the inverse taken on the orthogonal complement of the kernel.

If `A>=0`, then `A⁺>=0` automatically. There is no condition `1+κ<u,A^{-1}u><=0` in this branch. Its kernel is `ker A ∩ u⊥`.

If `n_-(A)>=2`, a rank-one lift cannot make `A⁺` nonnegative.

Suppose `n_-(A)=1`. Then

\[
 \boxed{A+\kappa uu^*\succeq0
 \iff u\perp\ker A\quad\text{and}\quad
             s_E:=1+\kappa\langle u,A^\dagger u\rangle\le0.}            \tag{3.2}
\]

Here `A†` is the Moore–Penrose inverse. Necessity of the kernel condition is not cosmetic: on a negative direction and a nonzero kernel component of `u`, the updated two-dimensional determinant is negative.

For a direct proof, write `A=-b|φ><φ| ⊕ A_+ ⊕0`, where `b>0`, `A_+>0`, and, after imposing `u⊥ker A`, write `u=aφ+u_+`. Set

\[
 R_E=\langle u_+,A_+^{-1}u_+\rangle\ge0.
\]

Minimizing the updated quadratic form over the positive subspace leaves

\[
 \left[-b+\frac{\kappa|a|^2}{1+\kappa R_E}\right]|x|^2.
\]

This is nonnegative exactly when

\[
 \kappa|a|^2\ge b(1+\kappa R_E),                           \tag{3.3}
\]

which is (3.2). In particular, orthogonality to the negative eigenvector makes repair impossible. Orthogonality to some positive eigenvector merely leaves that level untouched.

If `s_E<0`, the nonzero spectral subspace becomes positive and the old kernel remains. If `s_E=0`, one additional null direction is `A†u`; the old kernel remains as well. Thus equality is a genuine semidefinite case, not a strict-positive certificate.

### 3.3 Negative rank-one update: all cases

**[ABSTRACT / PAPER]** For `B=B*`,

\[
 \boxed{B-\kappa vv^*\succeq0
 \iff B\succeq0,\quad v\perp\ker B,\quad
             s_O:=1-\kappa\langle v,B^\dagger v\rangle\ge0.}            \tag{3.4}
\]

The necessity `B>=0` follows from `B=(B-κvv*)+κvv*`. On the positive subspace, Cauchy–Schwarz in the `B` metric proves sufficiency and necessity of the last inequality. If `s_O=0` and `v!=0`, `B†v` is an additional null direction. If `v=0`, the update does nothing.

### 3.4 Application to the literal source

**[FINITE_CELL / PAPER]** Take `A=G_{m,E}`, `B=G_{m,O}`, and the parity-coordinate versions of `u,v`. The two sectors are orthogonal and uncoupled. Since (3.1) supplies a negative even direction, at integer `m>=2`, positivity of `K_m` is equivalent to

\[
\begin{gathered}
 n_-(A)=1,\quad u\perp\ker A,\quad 1+\kappa\langle u,A^\dagger u\rangle\le0,\\
 B\succeq0,\quad v\perp\ker B,\quad1-\kappa\langle v,B^\dagger v\rangle\ge0.
\end{gathered}                                                        \tag{3.5}
\]

When both blocks are invertible, this is precisely the advertised pair of scalars, with the odd hypothesis strengthened from `B>=0` to `B>0` so the ordinary inverse exists. A full-matrix inverse is unnecessary; the sector inverses are the correct objects.

For arbitrary small real windows, the even bulk can be nonnegative, and the automatic-positive branch of §3.2 must be retained. Ties between even and odd eigenvalues of `K` are not ruled out by (3.5). Positivity and G1a are different consumers.

**Q2(a) code:** `REDUCTION_CORRECTED`. The first unpaid inputs are the actual source index/kernel facts and the signed margins in (3.5), not the rank-one algebra.

## 4. Q2(b) — both proposed cofinal index bounds are RH-graded

This section supplies the source-specific mechanism. It is not the generic parity-twin argument and does not infer sector information from the sign of the full minimum.

### 4.1 A legitimate global test class, not a global semibounded bulk operator

**[ABSTRACT / PAPER]** Let `S_exp` consist of smooth functions whose every derivative decays faster than every exponential. On this class define the global Weil form by the same archimedean, pole and **all-prime-power** expression. The prime series converges absolutely: for any fixed `r>1/2`,

\[
 \left|\int\overline{f(x)}g(x+\log n)\,dx\right|
 \le n^{-r}\|e^{r|x|}f\|_2\|e^{r|x|}g\|_2,
\]

and `Σ Λ(n)n^{-r-1/2}<∞`. The archimedean form is continuous in any positive-order Sobolev norm. These facts also show continuity under smooth expanding cutoffs.

The explicit formula, in the convention of §1, is

\[
 \mathfrak k(f,g)=\sum_{\rho}
       \overline{\widehat f(\overline{z_\rho})}\widehat g(z_\rho),
 \qquad z_\rho=i(\rho-1/2),                               \tag{4.1}
\]

with multiplicity. It applies to this class by cutoff approximation; Fourier transforms and their derivatives decay rapidly in every fixed horizontal strip, giving an absolutely summable zero-side majorant. This is the unconditional explicit formula [P1, §3], not Weil positivity.

Write

\[
 \mathfrak g(f,g)=\mathfrak k(f,g)
       -\overline{\langle p,f\rangle}\langle p,g\rangle
       +\overline{\langle q,f\rangle}\langle q,g\rangle.                \tag{4.2}
\]

No assertion of a lower-bounded global operator `G` on all of `L²(R)` is needed or made. Only these convergent form pairings are used.

### 4.2 An explicit zero-location-independent negative even direction

**[ABSTRACT / PAPER]** Define

\[
 h(x)=e^{x/2}\sum_{n\ge1}
       \left(16\pi^2n^4e^{4x}-24\pi n^2e^{2x}\right)e^{-\pi n^2e^{2x}}.
                                                                    \tag{4.3}
\]

The Gaussian polynomial `H(u)=(16π²u⁴-24πu²)e^{-πu²}` is Fourier self-dual, vanishes at zero, and has zero integral. Poisson summation therefore gives `h(-x)=h(x)`. For `x>=0`, every summand is strictly positive because `2πn²e^{2x}>3`; hence `h>0` on the whole line. The series and all derivatives decay super-exponentially at both ends, so `h∈S_exp`.

A Mellin calculation initially in `Re s>1` gives

\[
 \widehat h(z)=\zeta(s)\int_0^\infty H(u)u^{s-1}\,du
 =2s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)
 =4\xi(s),\qquad s=1/2-iz.                               \tag{4.4}
\]

Both sides are entire, so the identity holds everywhere. Thus `h` lies in the radical of the global Weil form on this test class, irrespective of zero location:

\[
 \mathfrak k(h,f)=0\qquad(f\in S_{\exp}).
\]

Also `hat h(±i/2)=4ξ(0)=4ξ(1)=2`, and therefore

\[
 \langle p,h\rangle=2\sqrt2,\qquad\langle q,h\rangle=0,
 \qquad\boxed{\mathfrak g(h,h)=-8.}                       \tag{4.5}
\]

This is an explicit negative bulk direction. It is not a negative direction of the Weil form.

### 4.3 Plant an off-line zero into each parity separately

**[ABSTRACT / PAPER: implication under an off-line-zero hypothesis]** Suppose an actual nontrivial zero `ρ=β+iγ` has `β>1/2`. Then

\[
 z_0=-\gamma+i(\beta-1/2),\quad z_0^2\notin\mathbb R.
\]

The zero quartet `z₀,-z₀,bar z₀,-bar z₀` is distinct and has a common multiplicity `r>=1`. Set

\[
 X(z)=4\xi(1/2-iz),\qquad
 P(z)=\bigl[(z^2-z_0^2)(z^2-\overline{z_0}^{\,2})\bigr]^r,
 \qquad H_0(z)=X(z)/P(z).                                \tag{4.6}
\]

`H₀` is entire, real-even in the sense `H₀(bar z)=overline{H₀(z)}`, and nonzero at the four selected points. It still vanishes at every other nontrivial zero.

Choose real constants `A_E,B_E,A_O,B_O` and define

\[
 F_E(z)=(z^2+1/4)(A_E+B_Ez^2)H_0(z),
\]
\[
 F_O(z)=iz(z^2+1/4)(A_O+B_Oz^2)H_0(z),                    \tag{4.7}
\]

so that

\[
 F_E(z_0)=i,\qquad F_O(z_0)=1.
\]

These are **explicit solvable two-real-variable equations**. If `Z=z₀²` and the needed value of `A+BZ` is `w`, use

\[
 B=\Im(w)/\Im(Z),\qquad A=\Re(w)-B\Re(Z).                 \tag{4.8}
\]

For the even equation take `w=i/[(Z+1/4)H₀(z₀)]`; for the odd equation take
`w=1/[iz₀(Z+1/4)H₀(z₀)]`. The denominators are nonzero.

Completed-zeta decay on every fixed horizontal strip, from its gamma factor and the standard polynomial strip bounds for zeta, implies that `F_E,F_O` and their horizontal derivatives decay exponentially there. Division by `P` introduces no pole because the zeros were canceled exactly. Contour shifting in Fourier inversion shows that the inverse transforms `f_E,f_O` lie in `S_exp`. The reality symmetries in (4.7) make `f_E` real even and `f_O` real odd.

The factor `z²+1/4` is essential:

\[
 \widehat f_E(\pm i/2)=\widehat f_O(\pm i/2)=0,
 \quad\langle p,f_E\rangle=\langle q,f_E\rangle
 =\langle p,f_O\rangle=\langle q,f_O\rangle=0.              \tag{4.9}
\]

It annihilates **both pole functionals**, rather than hoping a rank-one perturbation will leave a negative vector intact.

At the quartet, the even transform values are `(i,-i,i,-i)` in the order
`(z₀,bar z₀,-z₀,-bar z₀)`; the odd values are `(1,-1,-1,1)`. Each of the four summands in (4.1) is `-1`. Every other zero contributes zero. Therefore

\[
 \boxed{\mathfrak k(f_E,f_E)=\mathfrak g(f_E,f_E)=-4r,
        \qquad\mathfrak k(f_O,f_O)=\mathfrak g(f_O,f_O)=-4r.}            \tag{4.10}
\]

Moreover, (4.5), the radical identity and (4.9) give

\[
 \mathfrak g(h,f_E)=0.
\]

The bulk form on `span{h,f_E}` is thus exactly

\[
 \begin{pmatrix}-8&0\\0&-4r\end{pmatrix},                 \tag{4.11}
\]

and `f_O` is a negative odd direction. This is the promised **new parity mechanism**. The old parity-twin shortcut is not used: both Fourier targets were constructed and evaluated separately.

### 4.4 Return to the literal growing Fourier carrier

**[COFINAL_FAMILY / PAPER]** A noncompact test is not yet a witness for `N=m`. Here is the missing quantifier bridge, with its growing-prime cost paid.

For a fixed `f∈S_exp`, choose a fixed smooth even cutoff which is one on the central half of the window and zero before its endpoints; call the resulting cutoff `χ_L`. Put

\[
 f^{\rm cut}_m=\chi_{\log m}f,\qquad
 f_m=P_{\log m,m}f^{\rm cut}_m,\qquad L=\log m.             \tag{4.12}
\]

Cutoff errors tend to zero faster than any inverse power in exponentially weighted `L²` norms and in all fixed Sobolev norms. The derivatives through order four of `f_m^cut` have uniformly bounded `L¹` norms for sufficiently large `m`. Since the cutoff is zero near both endpoints, four integrations by parts give its periodic Fourier coefficients

\[
 |c_n|\le C_f L^{7/2}|n|^{-4}.
\]

For the projection error `e_m=f_m-f_m^cut`, Parseval gives

\[
 \|e_m\|_2\le C_fL^{7/2}m^{-7/2},\qquad
 \|e'_m\|_{L^2(I_L)}\le C_fL^{5/2}m^{-5/2}.               \tag{4.13}
\]

The derivative is an **interior derivative**. Zero extension is not claimed to be `H¹`. For any fixed `s<1/2`, zero extension from `H¹(I_L)` to `H^s(R)` is bounded uniformly for `L>=2`; a proof follows by splitting the fractional seminorm into interior pairs and the endpoint weight `dist(x,∂I_L)^{-2s}`, which is integrable and controlled by the local `H¹` trace estimate. In particular,

\[
 \|\widetilde e_m\|_{H^{1/4}}\le C_fL^{7/2}m^{-5/2}.       \tag{4.14}
\]

The archimedean multiplier is bounded in magnitude by a constant times
`(1+|ξ|²)^{1/4}`, so (4.14) pays its bilinear error. The **entire** finite prime operator satisfies

\[
 \left\|\sum_{2\le n\le m}c_n(S_{a_n}+S_{a_n}^*)\right\|
 \le2\sum_{2\le n\le m}c_n\le4\sqrt m\log m.              \tag{4.15}
\]

The pole operator norm is at most

\[
 \|p\|_{L^2(I_L)}^2+\|q\|_{L^2(I_L)}^2
   =4\sinh(L/2)=O(\sqrt m).                              \tag{4.16}
\]

Thus, for any two fixed tests in a finite list, their full matrix and form pairings differ by at most

\[
 \varepsilon_m\le C\left(
 L^{7/2}m^{-5/2}+L^{9/2}m^{-3}+m^{-2}\right)\longrightarrow0,           \tag{4.17}
\]

after enlarging a finite test-dependent constant `C`. The `m^{-2}` allowance pays the smooth cutoff in the weighted norms of §4.1; faster decay is available. The prime bound (4.15) deliberately uses only `Λ(n)<=log n`, not a zero-free estimate. All prime powers, endpoint effects, complex conjugations and the pole pairing are retained.

Apply this common return to the finite list `{h,f_E,f_O}`. Reflection commutes with both the even cutoff and the Fourier projection, so parity is exact. The coefficient Gram matrices converge to those of the original independent tests. The even two-by-two form matrix converges to (4.11), and the odd value converges to `-4r`.

For example, once the even entry errors are below `min(8,4r)/4`, its largest eigenvalue is at most `-min(8,4r)/2<0`; once the odd error is below `2r`, its value is at most `-2r<0`. These are **negative upper envelopes**, not failures of sufficient lower bounds. Hence, for every sufficiently large integer `m`,

\[
 \boxed{n_-(G_{m,m,E})\ge2,\qquad n_-(G_{m,m,O})\ge1.}      \tag{4.18}
\]

The threshold depends on the hypothesized zero, its multiplicity and the explicit test seminorms. No numerical threshold or actual off-line zero is asserted. The statement is cofinal on the original schedule, not on a separately chosen `N(L)`.

### 4.5 The exact index equivalences

**[COFINAL_FAMILY / PAPER]** Under RH, the explicit formula makes `K_{m,m}>=0` for every cell. Therefore

\[
 G_{m,m,E}=K_{m,m,E}-\kappa uu^*,\qquad
 G_{m,m,O}=K_{m,m,O}+\kappa vv^*
\]

give `n_-(G_E)<=1` and `G_O>=0`. Equation (3.1) makes the first index exactly one for `m>=2`.

Conversely, (4.18) excludes either bound on **any unbounded set of original integers** if an off-line zero exists. It follows that the following three assertions are equivalent:

\[
\begin{aligned}
 &\mathrm{RH};\\
 &\exists\ \text{unbounded }\mathcal M\subset\{2,3,\ldots\}:
       n_-(G_{m,m,E})\le1\quad(m\in\mathcal M);\\
 &\exists\ \text{unbounded }\mathcal M\subset\{2,3,\ldots\}:
       G_{m,m,O}\succeq0\quad(m\in\mathcal M).
\end{aligned}                                                        \tag{4.19}
\]

“One negative eigenvalue” can replace “at most one” in the middle line by (3.1). Requiring either bound on every sufficiently late cell gives the same equivalence. Analogous statements for an unbounded family of full continuum windows follow already from smooth cutoff approximation, without the Fourier step.

**Q2(b) code: `INDEX_RH_GRADED`.** PF proves simplicity/evenness of the **lowest** bulk state. It does not count the other negative states. The first missing index inequality is already a complete zero-exclusion obligation, as the explicit witness and return demonstrate. This classification is an unconditional theorem of implications; it does not use RH as an input to prove either missing bound.

There is no contradiction with the finite diagnostics: a finite table can satisfy both index bounds under either eventual scenario. Nor does (4.19) prove that negative spectrum forces failure of G1a for `K`. It does not compare the two lowest levels of `K` at all.

## 5. Q2(c) — what the Green functions really say about G1a

### 5.1 Secular equations, including invisible levels

**[ABSTRACT / PAPER]** Write `A=G_E`, `B=G_O`, and define, away from their spectra,

\[
 \Phi_E(t)=1+\kappa\langle u,(A-t)^{-1}u\rangle,
 \qquad
 \Phi_O(t)=1-\kappa\langle v,(B-t)^{-1}v\rangle.            \tag{5.1}
\]

For finite matrices,

\[
 \det(K_E-t)=\det(A-t)\Phi_E(t),\qquad
 \det(K_O-t)=\det(B-t)\Phi_O(t).                           \tag{5.2}
\]

These are identities of polynomials after multiplication, not licenses to erase common factors. An eigenvector orthogonal to the update vector remains an eigenvector at the original eigenvalue. A degenerate eigenspace loses at most one dimension under the rank-one update. Such untouched levels must be included when locating either bottom. The same spectral rule applies to the compact-resolvent continuum operators, without using an unregularized infinite determinant.

On pole-free real intervals,

\[
 \Phi'_E(t)=\kappa\|(A-t)^{-1}u\|^2>0\quad(u\ne0),
 \qquad
 \Phi'_O(t)=-\kappa\|(B-t)^{-1}v\|^2<0\quad(v\ne0).        \tag{5.3}
\]

Suppose, for the moment, that `A` has simple bottom `α₀` with nonzero `u` overlap. Its first lifted level is found from the increasing root of `Φ_E` above `α₀`, unless an earlier untouched level intervenes. For the odd block, a nonzero overlap of `v` with the bottom eigenspace of `B` gives a unique lowered root below `β₀=λ₀(B)`. If that overlap vanishes, the bottom may instead be an untouched `β₀`; one must inspect the limiting scalar and retained multiplicity.

### 5.2 An executable sign bracket, not a claim of its existence

**[ABSTRACT / PAPER]** A sufficient strict G1a bracket is a real `τ` satisfying

\[
 \begin{gathered}
 \alpha_0<\tau<\min(\alpha_1,\beta_0),\qquad
 \Phi_E(\tau)>0,\qquad \Phi_O(\tau)>0.                    \tag{5.4}
 \end{gathered}
\]

Here `α₁` is the second even bulk eigenvalue, counted with multiplicity; the interval requires a simple `α₀`. On this interval `A-τ` has exactly one negative direction. Equation (3.2), applied at `τ`, shows that `Φ_E(τ)>0` leaves exactly one negative direction in `K_E-τ`; meanwhile (3.4) makes `K_O-τ` positive. Thus

\[
 \lambda_0(K_E)<\tau<\lambda_0(K_O),                       \tag{5.5}
\]

and the bottom is simple even. In the literal structured CCM family the usual displacement identity supplies the nonzero eta pairing from this strict ordering; this is the previously proved algebraic interface, not a new PF inference [S8, §3 and S9]. For a standalone certificate avoiding that import, include the eta pairing as an explicit nonzero condition on the resulting one-dimensional bottom eigenspace.

Bracket (5.4) is sufficient, not necessary in cases where the lifted even level is an untouched bulk eigenvalue. The fully exact description is: retain the full products in (5.2), with multiplicities, and compare their lowest real roots. No new bound for these source scalars at a common `τ` is obtained here.

### 5.3 Which signs PF does and does not give

**[ABSTRACT / PAPER]** The continuum PF theorem proves `α₀<β₀` and `a=<φ₀,u>!=0`. It therefore fixes the singular behavior

\[
 \Phi_E(t)\to-\infty\quad\text{as }t\downarrow\alpha_0\text{ from above}.
\]

It does **not** determine how far the even root moves upward, how far the odd root moves downward, or their final order. It gives no positivity-preserving kernel on the odd half-line: the reflected-prime obstruction in the shelf remains intact [S6].

The observer's statement about the full resolvent can be sharpened. Below `γ₀=λ₀(G_L)`,

\[
 (G_L-t)^{-1}=\int_0^\infty e^{st}e^{-sG_L}\,ds
\]

is positivity improving. At any resolvent parameter `t>γ₀`, it cannot be positivity preserving, because it sends the positive ground state to `(γ₀-t)^{-1}φ₀<0`. Thus at `t=0` and `m>=2`, the physical positive-kernel argument is unavailable for a precise reason, not just lack of a theorem.

**Q2(c):** the Green-function secular description is exact; its source-specific root ordering and common-parameter margins are unpaid. This leaves G1a open.

## 6. Q3 — exact representations and the first unpaid sign

### 6.1 The Feynman–Kac continuation does not preserve a positive representation

**[ABSTRACT / PAPER]** On the invertible index branch, decompose

\[
 A=-b|\phi_0\rangle\langle\phi_0|\oplus A_+,\qquad
 u=a\phi_0+u_+,\qquad b>0,\quad A_+>0.
\]

Then exactly

\[
 s_E=1-\frac{\kappa|a|^2}{b}
       +\kappa\int_0^\infty\langle u_+,e^{-sA_+}u_+\rangle\,ds,
\]
\[
 s_O=1-\kappa\int_0^\infty\langle v,e^{-sB}v\rangle\,ds
       \qquad(B>0).                                      \tag{6.1}
\]

The integrands are nonnegative spectral quadratic expressions. The unsubtracted even integral diverges, since it contains `|a|²e^{bs}`. Removing that ground contribution is exactly the negative term in (6.1); it is not a positive expectation continued past the pole.

The precise unpaid inequalities are

\[
 \boxed{\kappa|a|^2\ge b(1+\kappa R_E),\qquad
        \kappa R_O\le1,}
 \quad R_E=\langle u_+,A_+^{-1}u_+\rangle,
 \quad R_O=\langle v,B^{-1}v\rangle.                       \tag{6.2}
\]

No sign is inferred by subtracting rounded nearly equal numbers. The formulas exhibit the competing quantities that a one-sided proof would have to compare. With kernels present, replace the inverses and add exactly the guards in §3.

One equivalent positive variational object for the odd side is

\[
 R_O=\sup_{f\ne0}\frac{|\langle v,f\rangle|^2}{\langle f,Bf\rangle},
 \qquad
 R_O^{-1}=\inf_{\langle v,f\rangle=1}\langle f,Bf\rangle.    \tag{6.3}
\]

This is a capacity/susceptibility problem. It does not prove that the infimum exceeds `κ`. The prime jump squares in (2.2) cannot supply that conclusion by themselves: their diagonal compensation is `2S_L`, and discarding it changes the operator.

### 6.2 A source-specific positive jump energy without a continued resolvent

**[ABSTRACT / PAPER]** The explicit positive theta function `h` of (4.3) gives a stronger change of representation than formal continuation of a Green function. It is useful even though it does not settle the remaining sign.

For a compactly supported `f`, put `F=f/h` and extend `F` by zero outside its support. Define the positive weighted jump energy

\[
\begin{aligned}
 \mathcal E_h[F]={}&\frac12\iint_{\mathbb R^2}
     j(|x-y|)h(x)h(y)|F(x)-F(y)|^2\,dxdy\\
 &+\sum_{n\ge2}c_n\int_{\mathbb R}
     h(x)h(x+a_n)|F(x+a_n)-F(x)|^2\,dx.                   \tag{6.4}
\end{aligned}
\]

Every displayed summand is nonnegative. The **infinite** prime-power sum converges because `h` decays faster than every exponential and `F` has compact support.

The elementary ground-transform identity is

\[
 (h_xF_x-h_yF_y)^2-h_xh_y(F_x-F_y)^2
   =(h_x-h_y)(h_xF_x^2-h_yF_y^2),                         \tag{6.5}
\]

with its sesquilinear/polarized analogue for complex functions. The distributional equation supplied by (4.1) and (4.4) is

\[
 \mathfrak k(h,\cdot)=0,\qquad Gh=-4\cosh(x/2),            \tag{6.6}
\]

where `Gh` denotes the convergent global distributional action on this rapidly decaying test, not an asserted global self-adjoint realization. Applying (6.5), first with finite jump cutoffs and then passing by absolute convergence, gives

\[
 \mathfrak g[hF]=\mathcal E_h[F]
          -4\int\cosh(x/2)h(x)|F(x)|^2\,dx.              \tag{6.7}
\]

Introduce the probability measure and bounded odd function

\[
 d\mu(x)=\tfrac12\cosh(x/2)h(x)\,dx,
 \qquad \tau(x)=\tanh(x/2).
\]

The measure has total mass one by (4.4). Restoring the two pole terms gives the exact identity

\[
 \boxed{\mathfrak k[hF]
   =\mathcal E_h[F]-8\left(
       \operatorname{Var}_{\mu}(F)+
       \left|\int\tau F\,d\mu\right|^2\right).}           \tag{6.8}
\]

Here `Var_μ(F)=∫|F|²dμ-|∫F dμ|²`. Therefore the remaining sign can be stated without an eigenvector or an inverse:

\[
 \boxed{\mathcal E_h[F]\ \ge\
    8\operatorname{Var}_{\mu}(F)+
    8\left|\int\tau F\,d\mu\right|^2.}                  \tag{6.9}
\]

For even `F`, the last term vanishes. For odd `F`, the mean in the variance vanishes. On a finite CCM carrier, take exactly `F=f/h` with `f` in that carrier and zero outside its window. A density/form argument extends the identity from smooth compact tests to these finite trigonometric window functions. No selected Ferrers row is substituted.

**What is paid:** the kernel, the constant `8`, the probability normalization, every prime power, the two parity terms, and the equality to the source form.

**What is unpaid:** the sharp weighted jump/Poincaré inequality (6.9), on the required family. Positivity of the jump kernel alone does not provide this spectral-gap constant.

**Exterior warning:** for a window-supported `F`, primes with `log n>L` can still contribute positive terms to (6.4), because one endpoint of a jump lies outside the support and `h` is nonzero there. Their compensating contribution is contained in the exact equation (6.6). Deleting these terms while retaining the fixed potential in (6.7) would break the identity. This is not a covert truncation of the prime comb.

### 6.3 Candidate assessment

**[ABSTRACT / PAPER]** A positive random-walk expectation below the bottom is legitimate; its continuation through the ground pole is not a positive-measure sign supplier. A sieve-square calculation would have to retain the source's diagonal compensation and establish (6.2) or (6.9), not merely rewrite the already positive jump energy. No such arithmetic inequality has been proved here.

The Zhu statement mentioned in the request is **RELAY, not an imported premise**. Nothing in this verdict depends on its wording or on a supposed new theorem in that manuscript.

**Q3 code: `REDUCED_TO_FIRST_UNPAID`.** Equations (6.2) are the exact sector susceptibility budgets; (6.9) is an alternative explicit, source-specific jump-energy formulation. Neither is represented as a proved nonnegative expansion of `-s_E` or `s_O`. A claim that no other sign representation can exist would be unjustified.

## 7. Adversarial controls and exact scope of the refutations

### 7.1 PF and the observed index pattern do not determine either scalar

**[ABSTRACT / PAPER]** Let `J` be the three-by-three all-ones matrix and

\[
 G=I-J,\quad e=(1,1,1)/\sqrt3,\quad o=(1,0,-1)/\sqrt2.
\]

Reflection exchanges coordinates one and three. The heat semigroup of `G` is strictly positive. Its eigenvalues are `-2,1,1`; its bottom is simple, positive and even. Its even block has one negative eigenvalue, and its odd block is positive.

Choose `κ=1`, `u=√P e`, `v=√Q o`, with `P,Q>0`. Then

\[
 s_E=1-P/2,\quad s_O=1-Q,
 \quad\lambda_0(K_E)=\min(-2+P,1),\quad\lambda_0(K_O)=1-Q.              \tag{7.1}
\]

Taking `P∈{1,3}` and `Q∈{1/2,2}` realizes all four scalar-sign combinations while leaving the bulk Markov structure and its index pattern unchanged. In addition, `P=9/4,Q=1/2` gives a simple even bottom of `K`, whereas `P=11/4,Q=1/2` gives an odd bottom; both updated matrices are positive.

Changing the bulk to `-I-J` leaves its strictly positive heat kernel and its simple positive even bottom, but gives two negative even eigenvalues and one negative odd eigenvalue. Thus PF alone does not establish either index bound.

These are exact synthetic controls. They refute a structural implication, not the arithmetic source's eventual signs.

### 7.2 Equality and tiny-margin discriminators

**[ABSTRACT / PAPER]** On the nonsingular branches,

\[
 K_EA^{-1}u=s_Eu,\qquad K_OB^{-1}v=s_Ov.                  \tag{7.2}
\]

With kernel guards, the corresponding pseudoinverse identities hold on the nonzero spectral subspaces. Therefore an exact zero scalar is tied to an explicit null-vector equation. The **DISCRIMINATOR** for a zero-consistent scalar computation is an exact factorization/null-vector proof, or a rigorous signed enclosure of the unreduced secular determinant and its remainder with the kernel case checked. Agreement at two floating precisions is not this discriminator.

For positivity certificates use the target margins `Δ_E=-s_E` and `Δ_O=s_O`. A PASS requires a **lower envelope** for the relevant margin that is nonnegative, together with the inertia/kernel premises. A negative upper envelope for a source Rayleigh witness refutes positivity; merely failing a sufficient scalar bound does not.

For G1a, a common zero or an untouched level must be detected with the full products (5.2), not with a canceled rational secular function. Strict parity separation, not positivity of each sector separately, is the target.

### 7.3 Scoped kill ledger

```yaml
SCOPED_KILLS:
  - CODE: KILL_PF_BULK_IMPLIES_SECULAR_SIGNS
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    KILL_EVIDENCE_KIND: EXACT_REFLECTION_INVARIANT_THREE_STATE_PLANT
    PINNED_EVIDENCE: this_verdict_section_7_1_equation_7_1
    SCOPE: ABSTRACT
    VERIFIER: PAPER
    LIMIT: NOT_A_COUNTEREXAMPLE_TO_THE_ARITHMETIC_CCM_FAMILY
  - CODE: KILL_AUTOMATIC_FOURIER_MARKOV_INHERITANCE
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    KILL_EVIDENCE_KIND: EXACT_NEGATIVE_SEMIGROUP_OUTPUT_ON_A_NONNEGATIVE_FOURIER_POLYNOMIAL
    PINNED_EVIDENCE: this_verdict_section_2_3_equation_2_8
    SCOPE: ABSTRACT
    VERIFIER: PAPER
    LIMIT: LITERAL_G_M_M_POSITIVITY_PRESERVATION_NOT_REFUTED
  - CODE: KILL_FULL_WEIL_K_POSITIVITY_PRESERVATION_FOR_ALL_WINDOWS
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    KILL_EVIDENCE_KIND: POSITIVE_DISJOINT_CROSS_PAIRING_AT_L_LOG_2
    PINNED_EVIDENCE: this_verdict_section_2_6_equation_2_9_and_source_S2
    SCOPE: FINITE_CELL
    VERIFIER: PAPER
    LIMIT: DOES_NOT_REFUTE_G1A_OR_A_POSITIVE_GROUND_EIGENFUNCTION
ROUTE_FAMILY_KILLED: false
```

For the last kill, the positivity-preservation target on disjoint nonnegative tests is `-k(f,g)>=0`; (2.9) supplies a strictly negative upper envelope for that target. No positivity failure of the quadratic form is inferred from this cross-pairing test.

## 8. Consumer-first dependency audit and route map

### 8.1 What the roof actually consumes

**[ABSTRACT / PAPER]** The downstream real-zero construction consumes a simple even bottom of the **same `K` family**, with its eta normalization. It does not consume the Markov property of `G`, nonnegativity of `K`, or a bulk index count merely because these are attractive intermediate objects. Transform-level G3 remains a separate obligation.

```yaml
DOWNSTREAM_CONSUMER: G2_REAL_ZEROS_OF_THE_SAME_CCM_GROUND_TRANSFORM
ACTUAL_CONSUMER_REQUIREMENT: SIMPLE_EVEN_BOTTOM_OF_K_WITH_NONZERO_ETA_PAIRING
ORIGINAL_REQUESTED_OBJECT: MARKOV_BULK_PLUS_INDEX_PATTERN_PLUS_TWO_SECULAR_SIGNS
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_IS_NOTE: NECESSITY_FOR_LITERAL_G1A_IS_NOT_ESTABLISHED; THE_PACKAGE_TARGETS_K_POSITIVITY_WHICH_IS_STRONGER_THAN_THE_STATED_G1A_INTERFACE
KNOWN_WEAKER_INTERFACES:
  - INTERFACE: STRICT_EVEN_BELOW_ODD_ORDERING_OF_K_ON_THE_ORIGINAL_TAIL
    IMPLICATION: SOURCE_DISPLACEMENT_ALGEBRA_GIVES_SIMPLE_EVEN_BOTTOM_AND_ETA_NONVANISHING
  - INTERFACE: GUARDED_SECULAR_BRACKET_5_4
    IMPLICATION: STRICT_PARITY_ORDERING_5_5
  - INTERFACE: DIRECT_G1A_AND_COMPACT_UNIFORM_TRANSFORM_TRACKING
    IMPLICATION: SAME_FAMILY_REAL_ZERO_AND_CONVERGENCE_ROOF_WITH_THE_OTHER_SOURCE_CROSSWALKS
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: FULL_WINDOW_DIRICHLET_FORM_PLUS_SOURCE_SPECIFIC_POLE_ANNIHILATING_INDEX_WITNESSES
REOPEN_TRIGGER: A_SOURCE_SPECIFIC_STRICT_PARITY_BRACKET_OR_A_PAID_FINITE_COMPRESSION_RETURN_NOT_USING_THE_RH_EQUIVALENT_INDEX_BOUNDS_AS_PREMISES
```

There is no claim that a missing proof makes G1a mathematically dead. The index conditions are classified by a proved implication, not by a literature-search failure. The arithmetic family has not been replaced by any of the synthetic controls.

### 8.2 Two remaining re-representations, with cost and decision power

| Candidate | Exact object and consumer | Decision power / cost | First risk or unpaid term |
|---|---|---|---|
| **Guarded sector secular bracket** | Equations (5.1)–(5.5), for G1a rather than all-window positivity | High if one common-parameter inequality closes the tail / moderate algebra, high arithmetic | Invisible levels, shrinking gaps and the common `τ` bounds; no index premise may be smuggled in |
| **Theta-weighted jump energy** | Equation (6.9), for actual Weil positivity | High, an explicit family-wide inequality / high analytic cost | Sharp constant `8` and the extra odd covariance; merely positive jump coefficients are insufficient |
| Lattice-preserving bulk discretization | Cell-indicator graph form, for continuum-bulk comparison | High for checking the Markov instrument / low-to-moderate | Does not replace the literal Fourier carrier; needs an explicit return |

The first two are genuine alternatives in representation, not authorizations for larger eigensolver scans. They have different consumers: the second is stronger than the first. Their costs are qualitative estimates, not runtime promises.

### 8.3 Three cross-domain checks

**Dirichlet-form / probability bridge:** an exact form identity and a rank-one Dyson argument close the continuum bulk theorem. This is a real bridge, not analogy.

**Finite-rank inertia bridge:** rank-one update theory completely classifies the two scalar branches, but exposes the index obligations. The source-specific zero interpolation proves those obligations are RH-graded on the original tail.

**Ground-transform / Poincaré bridge:** the explicit positive theta radical vector converts the source form into (6.8). The algebra and constants close; the sharp domination inequality does not.

The vanishing identity is `k(h,·)=0`; it removes a residual but does not manufacture positivity. A collapse object would be a proved lower envelope for the jump energy at the exact variance/covariance budget in (6.9), or, for the weaker G1a consumer, a strict common-parameter bracket (5.4). Both are explicit; neither is hidden behind an “unknown constant”.

### 8.4 Strongest attack on this verdict

The strongest objection to §4 is that an off-line-zero test on the whole line need not survive the actual finite schedule. That objection is valid against an unqualified form-core claim. Equations (4.12)–(4.17) explicitly pay the `O(sqrt(m) log m)` prime operator and the archimedean boundary norm, with `N=m`; they do not choose `N` after seeing the window. The construction also avoids relying on an unstable residual eigenvector or on the tiny observed scalar margins.

The strongest objection to §6 is also valid: a positive energy minus a variance is not yet a positive representation of the Weil form. It is presented as an **unpaid sharp inequality**, not a solution. No sign of `s_E`, `s_O`, or the lowest parity difference is promoted from it.

## 9. Frozen predictions and meta closeout

### 9.1 Observer predictions

| Frozen prediction | Outcome |
|---|---|
| P1: MARKOV_PROVED 0.55 / PARTIAL 0.30 / REFUTED 0.15 | **Qualified MARKOV_PROVED:** every continuum window, pole removed. The literal Fourier-compression part remains partial. No unqualified finite-schedule success is scored. |
| P1c: finite compression needs its own argument, 0.65 | **Confirmed.** A generic exact inheritance counterexample is supplied; the actual schedule still needs its own return. |
| P2: reduction confirmed/corrected with the same two scalars, 0.85 | **Confirmed with correction.** Inverse domains, zero modes, the nonnegative-even branch and equality cases are explicit. |
| P2b: even index UNCONDITIONAL 0.25 / RH_GRADED 0.20 / UNDECIDED 0.55 | **RH_GRADED.** The cofinal equivalence is proved by a pole-free even witness plus the negative theta direction, with diagonal projection return. The odd index is separately RH-graded by its independently constructed witness. |
| P3: SIGN_REPRESENTATION 0.07 / FIRST_UNPAID 0.63 / NONE 0.30 | **REDUCED_TO_FIRST_UNPAID.** The susceptibility and theta-jump identities are exact; the domination signs are not proved. |

No probability has been changed. The classification `RH_GRADED` is not scored as an RH proof.

### 9.2 This session's registered expectations

Before the main tests I stated two expectations: the pole-free full-window Markov theorem should survive while finite Fourier transfer needs a separate argument; PF alone should not determine the secular signs. Both are confirmed at the scopes stated in §§2 and 7.

The pole-annihilating index construction was subsequently pursued as an exploratory test and produced §4. I do **not** retroactively score it as a preregistered successful prediction. The exact symbolic controls checked the pole split, singular-case plants, quartet signs, theta Mellin factor and ground-transform algebra; they are algebra checks, not independent verification of the analytic proof.

### 9.3 What changed

**Smaller:** the full-window bulk question is closed, including domain, boundary, irreducibility, compactness and parity. The two-scalar reduction now has complete guards. The index hypotheses are no longer free-looking missing inputs: their exact cofinal zero content is identified by explicit source witnesses.

**Killed:** automatic Fourier Markov inheritance; PF-to-secular-sign transfer; positivity preservation of full `K` on every window. The literal G1a claim is not killed.

**Do not repeat:** discard the pole, prove PF for the easier bulk, and then quietly restore the pole as though PF controlled a resolvent above its negative ground state. Do not use a finite index table as a supplier for either line of (4.19). Do not drop the odd imaginary phase in a physical sign probe.

**Smallest open targets:** for G1a, the guarded same-parameter secular parity sign; for full positivity, the susceptibility budgets (6.2) or the exact weighted inequality (6.9). The bulk Markov theorem is not one of the remaining targets.

```yaml
iteration:
  target: GOAL058_G1A_PF_BULK_AND_TWO_SECULAR_SCALARS
  status: PROGRESS
  failed_strategy: POSITIVE_KERNEL_CONTINUATION_THROUGH_THE_NEGATIVE_BULK_POLE
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: GUARDED_SOURCE_SECULAR_PARITY_BRACKET_WITHOUT_RH_EQUIVALENT_INDEX_PREMISES
  invariant_learned: POSITIVITY_IMPROVING_BULK_SEMIGROUP_CONTROLS_ITS_GROUND_STATE_NOT_ITS_NEGATIVE_INDEX_OR_THE_UPDATED_PARITY_ORDER
  forbidden_future_move: TREAT_N_MINUS_G_E_LE_1_OR_G_O_PSD_ON_A_COFINAL_N_EQUALS_M_FAMILY_AS_AN_UNPAID_UNCONDITIONAL_INPUT
  next_decisive_test: INDEPENDENT_PAPER_AUDIT_OF_POLE_ANNIHILATING_PARITY_WITNESS_AND_DIAGONAL_PROJECTION_RETURN
```

## 10. Proshka's own line

I chose the physical jump form because the coefficient signs were obscuring the operator's cone.
It closes the continuum bulk question without estimating a tiny eigenvalue.
The nearest alternative was to manipulate the two inverse scalars directly.
That would have put a positive-kernel argument on the wrong side of a negative pole.
The other alternative was a larger finite PF scan.
It could not supply the missing quantifier or repair the Fourier cone.
The pole split is useful, but it moves the arithmetic difficulty into the index and susceptibility.
The index pattern is therefore not an innocent background observation.
The off-line-zero construction makes that statement precise on the actual schedule.
Its key move is to annihilate the pole functionals before testing either parity.
That is different from symmetrizing one negative witness and hoping both halves stay negative.
The first move beyond this batch is an independent audit of that witness and its finite return.
A lost prime-power term or an unpaid growing projection error would kill the asserted equivalence.
The second move is to test the theta-weighted jump formulation as a source inequality.
A bound that merely loses the constant eight would not reach its consumer.
For G1a alone, I would prefer the weaker guarded secular bracket over full positivity.
I would ask for a source comparison that controls the two updated roots at one common parameter.
I would not ask for another ground-angle table.
The most useful surprise is that the bulk Markov theorem really does hold for every window.
The more consequential surprise is that both proposed cofinal index restrictions already exclude off-line zeros.
I distrust the unqualified word “positive” when it might mean an eigenfunction, a kernel, or a quadratic form.
Those three meanings lead to different conclusions here.
I also distrust sign grids that erase the odd phase or omit the boundary without a return budget.
The right next step is to verify the new mechanism, then spend it only on the consumer it actually reaches.

## 11. Research log and sources

### 11.1 Source register

Repository paths below are relative to `Malaeu/chen_q3`. Unless separately stated, their read pin is **`ab6394323c40ed2c1b0a720778f0fb09662dc0bb`**. Repository sources are provenance for the requested object, not substitute proofs of the new analytic results.

- **[S0] READ, complete request.** `docs/routeB_bus/proshka/PROSHKA_REQUEST_MARKOV_2026-10-29.txt`, request commit `cfe490d950758d0a8b1e53d7a76a29d9ab671f0d`, blob `9f299b2a4f17802018a00790b3044ad4ab06d6c0`. Both hashes and byte/line counts recomputed. Taken: exact task, restrictions, predictions and output name.
- **[S1] READ, bootstrap protocol.** `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` at `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`, including the continuation ranges. Taken: source-lock and verdict discipline, not mathematical premises.
- **[S2] READ, lines 1–43.** `docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py`, blob `5cbd156db9be84caa938cdbabd4e9ec0b5a6d2f3`. Taken: exact `W02-WR-Prime` entry formulas, endpoint branch and full prime-power sum. No numerical output generated from it.
- **[S3] READ, complete.** `docs/routeB_bus/thetagrade_2026-10-28/pf_probe.py`, blob `71bf4f919f5d66b09427281e10ec7edc87f8c200`. Taken: physical synthesis, omitted boundary margin and the real-part operation; the odd-phase defect is an independent code finding.
- **[S4] READ, complete.** `docs/routeB_bus/thetagrade_2026-10-28/pf_secular_probe.py`, blob `bdadb4144524e9c2a71b722e2586ef864625634e`. Taken: the actual sector count and inverse scalar definitions; singular cases are not covered by that diagnostic script.
- **[S5] READ, eight records.** `docs/routeB_bus/thetagrade_2026-10-28/pf_secular_dps120.jsonl`, blob `f310027f2e59eb338e136a1480e158bd543b796d`. Taken only as the reported finite diagnostic, not as proof of any sign or index quantifier.
- **[S6] READ, main audit and the displayed beginning of the reflected-prime appendix.** `docs/routeB_bus/CONTACT_INDEPENDENT_CHECK_2026-09-10.md`, blob at the stated base. Taken: domain caution and distinction between the full-window cone and the odd half-line cone. Its historical independent-review claims are reported provenance, not a review performed in this session. The present bulk proof is rederived in §2.
- **[S7] READ, displayed source-identity and scope ledger.** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDOW_WEIL_IDENTITY_AND_LEAKAGE_MECHANISM_2026-09-04.md`, at the stated base. Taken: warning against claiming selected diagonal exhaustion without a proof. The present return (4.12)–(4.17) supplies its own argument; the earlier ledger is not used to assert it.
- **[S8] READ, local retained STIELTJES attachment, §3, §8.2 and the displayed dependency/closeout sections.** `docs/routeB_bus/proshka/PROSHKA_VERDICT_STIELTJES_2026-10-29.md`; local bytes **58,592**, SHA-256 **`0055688df2c9e18220f6ca297391562fa7b6fab381930942972217cd510de367`**, matching the pinned audit [S9]. Taken: earlier pole split, source parity interface and the previous unresolved sign; no newly proved global sign was imported.
- **[S9] READ, complete.** `docs/routeB_bus/proshka/STIELTJES_AUDIT_2026-10-29.md`, blob `640e3726e55e1c417e23ef2b08b4767216fc5e2a`. Taken: previous exact algebraic interfaces and the scope of the finite checks. Its computational PASS reports remain external diagnostic reports.
- **[P1] READ, primary CCM text.** Connes–Consani–Moscovici, *Zeta Spectral Triples*, **arXiv:2511.22755v1**, §§2–3, particularly (2.6), (3.2), (3.8)–(3.20): `https://arxiv.org/html/2511.22755v1`. Taken: basis, Fourier convention, unconditional explicit formula and the literal pole/archimedean/prime form. All later estimates and witness constructions are derived in this verdict.
- **[P2] READ and visually checked, primary Suzuki PDF.** Masatoshi Suzuki, *Weil's quadratic form via the screw function*, **arXiv:2606.09096**, the retrieved 30-page PDF, Theorem 1.4, (4.4) and §§5.1–5.3: `https://arxiv.org/pdf/2606.09096`. Screenshots checked PDF pages 5, 16, 19 and 20. Taken: the small-window limiting-form Markov argument and its scope. Not taken: an all-window PF theorem for the full Weil form, or a finite Fourier-compression theorem.
- **RELAY, NOT IMPORTED.** Zhu, **arXiv:2608.24827**, the cancellation phrase quoted in the request. No claim in this verdict rests on it.

The broad retrospective `WALL_ONE_FORMULA_2026-10-29.md` was not needed as a premise and was not opened. Search results unrelated to the two primary analytic sources were not used. No private repository content was replaced by public web search.

### 11.2 Branches tested and stopped

**Automatic Fourier transfer:** stopped by (2.8), an exact negative output from a nonnegative finite Fourier polynomial.

**PF directly for full `K`:** stopped by (2.9), the source-specific positive disjoint cross pairing at `m=2`. This kills the semigroup shortcut, not the spectral target.

**Index from a simple positive bulk ground state:** stopped as a generic inference by `-I-J`, and classified for the source by the stronger witness theorem (4.18).

**Positive expectation at `t=0`:** stopped by the divergent even ground contribution `|a|²e^{bs}`. Removing it produces the signed term in (6.1).

**Prime squares with no diagonal compensation:** stopped by the exact `-2S_L||f||²` term in (2.1). Omitting it changes the object.

**Purely noncompact zero witness:** not accepted on its own; repaired by the explicit cutoff and `N=m` projection estimates (4.12)–(4.17).

**A generic parity-twin argument:** not reused. The two targets (4.7) were constructed separately and the zero-side signs checked separately.

### 11.3 Intermediate identities retained for reuse

The original source pole matrix is exactly (1.6), with the physical odd phase specified in (1.5).

The shifted Dirichlet identity (2.1) holds for every bounded window, including endpoint prime atoms and exterior killing.

The singular rank-one criterion (3.2) requires orthogonality to the old kernel; a nonzero kernel component makes the two-dimensional determinant negative.

The separately interpolated zero tests satisfy (4.9)–(4.11), with exact energies `-4r` and `-8`, not a fitted negative scale.

The finite return (4.17) is available for any fixed finite family in `S_exp`, not just these witnesses.

The weighted identity (6.8) is exact even when its sign is unknown. Its missing ingredient is a sharp jump inequality, not an absent normalization or boundary term.

### 11.4 Executed algebra controls

The following were checked with exact symbolic arithmetic in the local runtime: pole factorization; the three-state PF plant; the negative determinant caused by a kernel component; the quartet signs; the Gaussian Mellin factor `4ξ`; and the ground-transform identity (6.5). They are controls on signs and factors only. Neither SymPy nor floating arithmetic proved a continuum or cofinal theorem.

A compact reproducible subset is:

```bash
uv run --with sympy python - <<'PY'
import sympy as s

# A synthetic PF bulk, not an arithmetic CCM matrix.
G = s.eye(3) - s.ones(3)
e = s.ones(3, 1) / s.sqrt(3)
o = s.Matrix([1, 0, -1]) / s.sqrt(2)
assert G * e == -2 * e
assert G * o == o

# A rank-one lift cannot cure a negative direction and a coupled zero mode.
k = s.symbols('k', positive=True)
u = s.Matrix([1, 1])
assert s.expand((s.diag(-1, 0) + k*u*u.T).det()) == -k

# Exact Fourier-compression obstruction, degree one.
T = s.Matrix([[1, s.Rational(1, 2)], [1, s.Rational(5, 4)]])
C = T - s.Rational(9, 8) * s.eye(2)
assert C*C == s.Rational(33, 64)*s.eye(2)
assert (s.Matrix([[1, 1]]) * T * s.Matrix([1, -1]))[0] == s.Rational(1, 4)

# Pair selected conjugate zeros in the antilinear-first Weil formula.
for F in ([s.I, -s.I, s.I, -s.I], [1, -1, -1, 1]):
    Q = sum(F[i]*s.conjugate(F[j]) for i, j in [(0, 1), (1, 0), (2, 3), (3, 2)])
    assert s.simplify(Q) == -4

# Pointwise ground-transform identity, real case; polarization gives complex case.
a, b, x, y = s.symbols('a b x y', real=True)
assert s.expand((a*x-b*y)**2-a*b*(x-y)**2-(a-b)*(a*x*x-b*y*y)) == 0
print('PASS: exact algebra controls only; no CCM scan, no analytic certification.')
PY
```

There are no user-specific placeholders in this command. It does not access or write the repository.

## 12. One next directive and final boundary

**CODEX DIRECTIVE — read-only independent PAPER audit of §4.**

Audit exactly the theorem

> An off-critical zeta zero forces `n_-(G_{m,m,E})>=2` and `n_-(G_{m,m,O})>=1` on every sufficiently late original cell.

Use the pinned literal source entries, the unconditional explicit formula, the explicit Fourier targets (4.6)–(4.8), and the original `L=log m, N=m` schedule. First check the pole annihilation and the even/odd reality symmetries. Then independently verify the zero-side value `-4r`, the bulk cross-pairing with `h`, and every growing-window error term in (4.13)–(4.17). Preserve both endpoints and all prime powers. The displayed exact-algebra command is a sign/factor check only; the analytic return must be checked on paper.

**Success condition:** both negative subspaces survive with strict negative upper envelopes for all sufficiently large original `m`, without assuming RH, a cofinal index bound, ground-state tracking, or a freely chosen larger Fourier cutoff. Return either `INDEX_WITNESS_DIAGONAL_RETURN_CONFIRMED_PAPER` or `INDEX_WITNESS_FIRST_UNPAID_TERM` with the first incorrect or unproved estimate and a repaired statement. No Lean, repository edit, broad numerical scan or new route promotion is authorized.

This audit is the cheapest decisive check because the classification of both index hypotheses rests on that one source-specific return. It should be settled before anyone spends the index pattern as an unconditional supplier.

**Final boundary:** the continuum pole-free Markov theorem and the index implications are PAPER results in this verdict. The finite-schedule PF statement for the literal compression, G1a for `K`, the cofinal scalar signs, and the sharp theta-weighted inequality remain open. RH is not claimed proved, and the final claim remains with the owner.
