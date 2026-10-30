# STATUS: TRY_CONFINE_FIXED_JET_OVERLAP_AUDIT

```yaml
OPERATIVE_CLASS: TRY_CONFINE_FIXED_JET_OVERLAP_AUDIT
REQUEST_ID: REQ-2026-10-30-CONFINE
BOUNDARY_ID: GOAL058_WINDOW_BOTTOM_AS_CONFINED_XI_RADICAL_VECTOR
REQUEST_COMMIT: 339fcb4cd9a0c947398ece7b712ca3e4291841f2
REQUEST_GIT_BLOB: f7c13308bb3febf5f32337a39410c6861900a7f8
REQUEST_SHA256: 7db169026511e0f7184814ee1e19e33f2403ce427a0507d4865fae2446689731
REQUEST_BYTES: 11398
REQUEST_LINES: 172
REQUEST_FINAL_LF: true
REQUEST_HASH_CHECK: ALL_FOUR_SUPPLIED_VALUES_MATCH
SOURCE_BASE_COMMIT: f89683aee0e7137e1e1f4e0567418c838ded29d3
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_SELECTED_FERRERS_FAMILY
Q1: SELECTION_RH_GRADED
Q1_ACTUAL_FIXED_LIMIT: NOT_PROVED_OR_REFUTED
Q1_PRECISE_DIRECTION: NONZERO_WEAK_SUBSEQUENTIAL_LIMIT_OF_EITHER_SECTOR_BOTTOM_IMPLIES_RH
Q1_HEAT_TIME_IDENTIFIED: false
Q2_COMMUTATOR: COMMUTATOR_EXACT
Q2_GAP: GAP_REDUCED
Q3_FIXED_FINITE_JET: PROXIMITY_RH_GRADED
Q3_UNRESTRICTED_L2_CLOSED_SPAN: PROXIMITY_ZERO_FREE_VACUOUS
Q4A: EXACT_IMPLICIT_AUTOCORRELATION_EQUATION_NOT_AN_EXPLICIT_ROOT_FORMULA
Q4B: FIT_NOT_LAW
Q4C: NO_VERIFIED_RKHS_TO_WINDOW_HEAT_TIME_CROSSWALK
NEW_COFINAL_RESULT: FIXED_RADICAL_JET_QUASIMODES_AND_OFFLINE_ZERO_WEAK_ESCAPE
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: PAPER_IMPLICATIONS_AND_SOURCE_PRESERVING_QUASIMODE_ESTIMATES
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
VERIFIER: PAPER
INDEPENDENT_REVIEW_OF_THIS_VERDICT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
REPOSITORY_WRITTEN: false
LITERAL_CCM_NUMERICAL_SCAN: NOT_PERFORMED
SYMBOLIC_CONTROLS: PASSED_EXACT_ALGEBRA_ONLY
G1A_PROVED_COFINAL: false
G3_PROVED: false
RH_PROVED: false
ROUTE_PROMOTION: false
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## 0. Verdict: distinguish a fixed small family from its unrestricted closure

**Q1 — `SELECTION_RH_GRADED`, in a precise one-way sense.** No plateau limit or heat time is identified. Instead, I prove below that, for the literal original schedule, an off-critical zero would force **every normalized even-sector bottom and every normalized odd-sector bottom to converge weakly to zero in physical `L²(ℝ)`**. Consequently, a nonzero strong limit of either sector, or even a nonzero weak subsequential limit, would imply RH. No G1a hypothesis is needed for this implication. The converse—RH selects a fixed profile—is not established.

**Q3 has two genuinely different answers.** The `L²`-closed span of all derivatives of `h` is the entire Hilbert space, separately in each parity. Proximity to that unrestricted closed span is identically zero and feeds **neither G1a nor G3**. In contrast, persistent nonzero overlap with a **fixed finite jet**, such as `span{h,h'',h''''}`, would already imply RH. Under an off-critical zero, the distance of a unit sector bottom to each such fixed jet tends to **one**, not zero. This is the useful distinction concealed by the phrase “the xi-radical family.”

**Q2 — `COMMUTATOR_EXACT` plus `GAP_REDUCED`.** The exact finite commutator is rank two. The pole term is translation-invariant on the line, just like the other components; its finite commutator is a boundary effect. The derivative trial has an explicit residual, but its Rayleigh value is still an **upper**, not lower, bound for the odd bottom. A precise complement/Schur inequality remains unpaid.

**Q4.** The threshold has an exact autocorrelation equation, not a proved explicit value for the unknown limit. The `4.6` decay exponent remains a fit. The archived Part I does not prove the quoted Part II RKHS bound or identify its parameter with the fitted heat time.

The new PAPER work is §§2–4, especially the original-`N=m` residual estimate (3.8) and the resulting fixed-jet escape theorem (4.8). These arguments are written out rather than imported from the still-unverified portions of MARKOV §4. They require an independent mathematical audit before being treated as accepted project suppliers. They do not prove RH, G1a, G3, or the existence of the observed plateau.

### 0.1 Source lock and verification

The current protocol was fetched through the GitHub connector from `rh_clean`. The request was fetched at the owner-specified commit, transcribed without changing its UTF-8 contents, and checked locally:

```text
bytes    11398
lines    172
final LF true
SHA-256  7db169026511e0f7184814ee1e19e33f2403ce427a0507d4865fae2446689731
Git blob f7c13308bb3febf5f32337a39410c6861900a7f8
```

All mathematical repository reads used `f89683aee0e7137e1e1f4e0567418c838ded29d3`, not current HEAD. Source references `[S…]` are listed in §12. In addition, the primary CCM v1 HTML was read for the exact form and displacement identities. No PDF was used. No repository mutation, Lean run, interval certification, or new literal CCM eigenvalue scan was performed.

### 0.2 Claim ledger

| Claim | Scope / verifier | What is proved | Boundary |
|---|---|---|---|
| C1 | ABSTRACT / PAPER | All finite derivatives and translates of `h` are global radical tests | Not a statement about the `L²` closure of the form's kernel |
| C2 | ABSTRACT / PAPER | Derivative jets have dense `L²` span, separately by parity | Unrestricted proximity is nonselective |
| C3 | COFINAL_FAMILY / PAPER | Every fixed derivative has superalgebraically accurate finite near-null rows on `N=m` | No positive floor or bottom tracking follows |
| C4 | COFINAL_FAMILY / PAPER | An off-critical zero gives a fixed negative test in each parity and negative late-cell upper envelopes | Two separate tests; not the rejected parity-twin inference |
| C5 | COFINAL_FAMILY / PAPER | Under that zero hypothesis, sector bottoms converge weakly to zero and lose every fixed finite-jet overlap | No actual off-critical zero is asserted |
| C6 | ABSTRACT / PAPER | A nonzero weak/strong limiting profile of either sector would imply RH | Not an equivalence and not a proof of a profile |
| C7 | FINITE_CELL / PAPER | Exact commutator, derivative residual, and guarded Schur lower-gap criterion | Its source-specific positive margin is unpaid |
| C8 | ABSTRACT / PAPER | Exact leakage Ritz identity and compact-transform error bound | No limiting leakage matrix or rate is supplied |
| C9 | ABSTRACT / PAPER | Exact atom-speed/autocorrelation equation and heat-family degeneracy | No certified threshold, asymptotic eigenvalue exponent, or selected heat time |

## 1. Literal object, conventions, and what “radical” means

**[ABSTRACT / PAPER]** Use the Fourier convention

\[
\widehat f(z)=\int_{\mathbb R}f(x)e^{-izx}\,dx,
\qquad \|f\|_2^2=\frac1{2\pi}\int_{\mathbb R}|\widehat f(t)|^2dt.
\tag{1.1}
\]

Let `𝒮_exp` denote smooth functions whose derivatives have every exponentially weighted `L²` norm finite. The theta function in the request is

\[
h(x)=e^{x/2}\sum_{n\ge1}
 (16\pi^2n^4e^{4x}-24\pi n^2e^{2x})e^{-\pi n^2e^{2x}},
\qquad H(z):=\widehat h(z)=4\xi(1/2-iz).
\tag{1.2}
\]

For clarity, put `H_phys(u)=(16π²u⁴-24πu²)e^{-πu²}`. Gaussian Fourier differentiation gives `F_{2π} H_phys=H_phys`, while `H_phys(0)=0` and its integral is zero. Poisson summation then gives `h(-x)=h(x)`. Its derivatives decay faster than every exponential. The normalization is checked directly by

\[
 \int_0^\infty H_{\rm phys}(u)u^{s-1}du
 =\pi^{-s/2}\{8\Gamma(s/2+2)-12\Gamma(s/2+1)\}
 =2s(s-1)\pi^{-s/2}\Gamma(s/2).
\]

Multiplication by `ζ(s)` first in a Mellin half-plane, followed by analytic continuation, gives (1.2). These are the same normalization and function as MARKOV (4.3)–(4.4), not a new trial row [S3].

For antilinear-first pairings put

\[
 C_{f,g}(s)=\int\overline{f(x)}g(x+s)\,dx,
 \qquad Q_{f,g}(s)=C_{f,g}(s)+C_{f,g}(-s),
\]
\[
 j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad
 c_* =\gamma+\log(8\pi)+\pi/2,\quad
 c_n=\frac{\Lambda(n)}{\sqrt n},\quad a_n=\log n,
\]
\[
 p(x)=\sqrt2\cosh(x/2),\qquad q(x)=\sqrt2\sinh(x/2).
\]

The exact global form on these tests and on the mixed tests used below is

\[
\begin{aligned}
\mathfrak k(f,g)={}&-c_*\langle f,g\rangle
 +\int_0^\infty j(s)\{2\langle f,g\rangle-Q_{f,g}(s)\}\,ds\\
 &-\sum_{n\ge2}c_nQ_{f,g}(a_n)
 +\langle f,p\rangle\langle p,g\rangle
 -\langle f,q\rangle\langle q,g\rangle .
\end{aligned}
\tag{1.3}
\]

The archimedean rewrite agrees with [S2, S3] and the primary CCM form [P1]. It retains the constant, both poles, and all prime powers. For two functions supported in a length-`L` window the prime correlations vanish for `log n>L`, and also at the endpoint `log n=L` in the integral sense.

The unconditional explicit formula reads

\[
 \mathfrak k(f,g)=\sum_\rho
      \overline{\widehat f(\overline{z_\rho})}\,
      \widehat g(z_\rho),\qquad
 z_\rho=i(\rho-1/2),
\tag{1.4}
\]

with multiplicity. No zero location is assumed. For `𝒮_exp` the formula follows from smooth cutoff approximation of the classical formula: weighted derivative convergence gives rapid uniform Fourier decay in the closed critical strip; the usual unconditional zero-count growth makes the zero sum absolutely convergent. The arithmetic side also converges absolutely, since

\[
 |C_{f,g}(s)|\le e^{-A|s|}
    \|e^{A|x|}f\|_2\|e^{A|x|}g\|_2,
 \qquad
 \sum_{n\ge2}(\log n)n^{-A-1/2}<\infty\quad(A>1/2).
\tag{1.5}
\]

Mixed pairing of a fixed derivative of `h` with a compact trigonometric window function is covered as well: its correlation is smooth and rapidly decreasing, despite the jumps of the window function itself.

Consequently, for every fixed integer `k>=0`, every real translation `a`, and every admissible partner,

\[
 \mathfrak k(h^{(k)}(\cdot-a),g)=0.
\tag{1.6}
\]

This verifies the request's algebraic radical assertion on the stated test class. It does **not** extend (1.6) to an arbitrary `L²` limit. The global form is not a bounded `L²` bilinear functional, and a fixed-window closed-form theorem is not a global `L²`-continuity theorem.

For the matrices, throughout

\[
 L=\log m,\quad b=L/2,\quad I_m=[-b,b],\quad N=m,
\]
\[
 \psi_{n,L}(x)=L^{-1/2}e^{2\pi in(x+b)/L}\mathbf1_{I_m}(x),
 \quad -m\le n\le m,
 \quad V_m=\operatorname{span}\{\psi_{n,L}\},
\tag{1.7}
\]

and `P_m` is orthogonal projection onto `V_m` in `L²(ℝ)`. The matrix `K_m` is exactly the restriction of (1.3) to this basis. Real even coefficient vectors synthesize real even functions; real odd coefficient vectors synthesize imaginary odd functions, which may be made real by one common phase. No imaginary part is discarded.

## 2. First discriminator: the unrestricted radical span is dense

### 2.1 Density even without translations

**[ABSTRACT / PAPER]** Define

\[
 \mathcal J_{E,r}=\operatorname{span}\{h,h'',\ldots,h^{(2r)}\},
 \qquad
 \mathcal J_{O,r}=\operatorname{span}\{h',h''',\ldots,h^{(2r+1)}\}.
\]

Then

\[
 \boxed{\overline{\bigcup_r\mathcal J_{E,r}}^{\,L^2}=L^2_E(\mathbb R),
 \qquad
 \overline{\bigcup_r\mathcal J_{O,r}}^{\,L^2}=L^2_O(\mathbb R).}
\tag{2.1}
\]

**Proof.** The theta series extends holomorphically to `|Im x|<π/4`: there `Re(e^{2x})>0`. On the right half of any smaller strip its defining series and derivatives are dominated by double-exponential decay. Evenness, extended by the identity theorem, gives the same bound on the left half. Shifting the Fourier contour therefore gives, for each `0<a<π/4`,

\[
 |H(t)|\le C_a e^{-a|t|}\quad(t\in\mathbb R).
\tag{2.2}
\]

Also `H` is a nonzero entire function, so its real zeros are discrete and have measure zero. This statement does not require RH.

Suppose `g` is even and orthogonal to all even derivatives. The integrable function
`M(t)=overline(g-hat(t)) H(t)` has an exponential moment by Cauchy–Schwarz and (2.2), using a smaller exponent than the one in that bound. Its Fourier transform is analytic on a strip about the real axis. All even derivatives of that transform at zero vanish by the assumed orthogonality; all odd derivatives vanish by parity. The identity theorem and Fourier uniqueness give `M=0` almost everywhere, hence `g=0`. For odd `g`, odd derivative orthogonality supplies the odd moments and parity supplies the even ones. This proves (2.1).

The same nonvanishing-a.e. argument also proves density of the translates of `h`, but translations are not needed for the conclusion.

### 2.2 Finite-carrier consequence

**[FINITE_CELL / PAPER]** For every individual `m`,

\[
 \operatorname{span}\{P_mh^{(2j)}:j\ge0\}=V_{m,E},
 \qquad
 \operatorname{span}\{P_mh^{(2j+1)}:j\ge0\}=V_{m,O}.
\tag{2.3}
\]

Indeed, the image is dense by (2.1), and a linear subspace of a finite-dimensional space is closed. Thus a finite collection of projected derivatives spans the entire sector, although the required order and conditioning may depend arbitrarily badly on `m`.

**Every finite sector vector—not just its bottom—can therefore be described as a confined radical combination if the derivative order is unrestricted.** This remains true after perturbing the prime positions, because (2.3) is a statement about the carrier and the fixed function `h`, not about `K_m`.

This refutes the *selectivity* of unrestricted `L²` radical proximity. It does not refute the observed proximity to the particular **three-dimensional** spaces in the request.

### 2.3 What topology would retain the zero constraints?

**[ABSTRACT / PAPER]** In a norm with exponential weight, Fourier evaluation can be continuous. For example, if `A>|Im z|`,

\[
 |\widehat f(z)|\le
 \|e^{A|x|}f\|_2
 \left(\int e^{-2A|x|+2(\Im z)x}\,dx\right)^{1/2}.
\tag{2.4}
\]

In such a topology the closure of radical tests still vanishes at the relevant zeros and is a proper subspace. The density theorem is specifically about **unweighted physical `L²`**, the norm named in Q1. It must not be transported to an analytic or form topology without its norm map.

## 3. A source-specific bridge: every fixed jet has a strong near-null return on `N=m`

This section supplies the norm estimate needed for the grading statement, rather than assuming that a global null vector remains null after compression.

### 3.1 Fourier return with endpoint jumps paid

**[COFINAL_FAMILY / PAPER]** Fix one derivative `r=h^(k)`. Choose once and for all a real even smooth cutoff `χ` equal to one on `[-1/2,1/2]` and zero outside `(-3/4,3/4)`. For `b>=1`, set

\[
 z_m(x)=\chi(x/b)r(x),\quad u_m=P_m z_m,\quad
 e_m=u_m-z_m,\quad w_m=r-z_m.
\tag{3.1}
\]

Here `u_m` is a function in the literal carrier, not a changed matrix. All functions have the parity of `r`. For every integer `p>=2`, there is a fixed finite

\[
 A_{r,p}:=\sup_{b\ge1}\|[\chi(\cdot/b)r]^{(p)}\|_2<\infty.
\]

Periodic Fourier Parseval, with the zero boundary jets of `z_m`, gives

\[
 \epsilon_0:=\|e_m\|_2
 \le A_{r,p}\left(\frac{L}{2\pi m}\right)^p,
 \qquad
 \epsilon_1:=\|e_m'\|_{L^2(I_m)}
 \le A_{r,p}\left(\frac{L}{2\pi m}\right)^{p-1},
\tag{3.2}
\]
\[
 J_m:=|e_m(-b)|+|e_m(b)|
 \le \frac{2A_{r,p}}{\sqrt L}
       \left(\frac{L}{2\pi}\right)^p
       \sqrt{\frac2{2p-1}}\,m^{1/2-p}.
\tag{3.3}
\]

For (3.3), apply Cauchy–Schwarz to the two Fourier tails and use
`Σ_{|n|>m}|n|^{-2p} <= 2 m^{1-2p}/(2p-1)`. The derivative in (3.2) is the **interior** derivative; the endpoint jumps of its zero extension have not been declared zero.

Let `v∈V_m` have norm one. Then

\[
 \|v\|_\infty\le\sqrt{(2m+1)/L}\le\sqrt{3m/L},
 \qquad \langle e_m,v\rangle=0.
\]

Moving a correlation derivative onto the zero extension of `e_m`, including both endpoint masses, yields

\[
 |Q_{e_m,v}(s)|\le
 2s\left(\epsilon_1+J_m\sqrt{3m/L}\right).
\tag{3.4}
\]

Since

\[
 J_1:=\int_0^\infty s j(s)\,ds
 =\sum_{\ell\ge0}(2\ell+1/2)^{-2}<5,
\]

the archimedean contribution is at most
`10(ε1+J_m sqrt(3m/L))`. The diagonal constant vanishes in this mixed pairing by the proved orthogonality, not by deleting it from `K_m`.

The two pole terms cost at most `2 sqrt(m) ε0`, because
`||p||²_{I_m}+||q||²_{I_m}=4 sinh(b) <= 2 sqrt(m)`. The prime terms cost at most `4 sqrt(m)L ε0`, using only `Λ(n)<=log n`. Therefore

\[
 \boxed{|\mathfrak k(e_m,v)|\le
 (2+4L)\sqrt m\,\epsilon_0
 +10\epsilon_1+10J_m\sqrt{3m/L}.}
\tag{3.5}
\]

This is a bound for **every** unit vector in the growing carrier, not just a fixed test direction.

### 3.2 Exterior tail, including prime powers larger than the window

**[COFINAL_FAMILY / PAPER]** Define

\[
 A(w)=\int e^{|x|/2}|w(x)|dx,\qquad
 T(w)=\|e^{|x|}w\|_2,\qquad
 S_\Lambda=\sum_{n\ge2}\frac{\log n}{n^{3/2}}<\infty.
\]

For every unit `v∈V_m`, the full global mixed tail obeys

\[
 |\mathfrak k(w_m,v)|\le\tau_m,
\]
\[
 \tau_m:=c_*\|w_m\|_2+10\|w_m'\|_2
 +2m^{1/4}A(w_m)+2\sqrt m S_\Lambda T(w_m).
\tag{3.6}
\]

The last bound follows from

\[
 |Q_{w_m,v}(\log n)|\le 2\sqrt m\,n^{-1}T(w_m).
\tag{3.7}
\]

The prime sum in (3.6) is **infinite**: it is part of the comparison with a global radical vector. No prime power has been discarded. The archimedean bound follows by translation differences of the globally smooth `w_m`; the pole bound uses weighted `L¹` and the exact window pole norms.

The support of `w_m` starts at `|x|>=b/2`. Double-exponential decay of every derivative of `r` implies that `τ_m`, and the weighted norms defining it, decrease faster than every inverse power of `m`. A factor polynomial in `m` cannot overcome the decay beginning at `exp(2|x|)>=sqrt(m)`.

### 3.3 The near-null statement

**[COFINAL_FAMILY / PAPER]** By the exact radical identity,

\[
 \mathfrak k(u_m,v)=\mathfrak k(e_m-w_m,v).
\]

Taking the supremum over unit carrier vectors in (3.5)–(3.6) proves

\[
 \boxed{\|K_m\operatorname{coeff}(u_m)\|_2\le
 (2+4L)\sqrt m\,\epsilon_0+10\epsilon_1
       +10J_m\sqrt{3m/L}+\tau_m.}
\tag{3.8}
\]

The explicit right side is

\[
 O_{r,p}\!\left(L^{p+1}m^{1/2-p}+L^{p-1}m^{1-p}\right)+\tau_m.
\]

Since `p` is arbitrary, the **same** `u_m=P_m(χ(x/b)r)` satisfies, for every fixed `A>0`,

\[
 \boxed{\|u_m-r\|_2+\|K_m\operatorname{coeff}(u_m)\|_2
       =O_{r,A}(m^{-A}).}
\tag{3.9}
\]

No larger Fourier cutoff is chosen. No lower spectral bound, positivity, G1a, G3, or zero-free region was used.

## 4. What a fixed plateau would imply: nonzero overlap forces RH

### 4.1 An off-critical zero supplies a negative test in each parity

**[ABSTRACT / PAPER: implication under an off-critical-zero hypothesis]** Suppose `ρ` is a nontrivial zero with `Re ρ>1/2`, and put `z0=i(ρ-1/2)`. Its real and imaginary parts are nonzero. The quartet

\[
 z_0,-z_0,\overline{z_0},-\overline{z_0}
\]

consists of distinct zeros of `H` of the same multiplicity `r>=1`. Set

\[
 P(z)=(z^2-z_0^2)(z^2-\overline{z_0}^{\,2}),\qquad
 B(z)=(z^2+1/4)e^{-z^2}\frac{H(z)}{P(z)^r}.
\tag{4.1}
\]

The quotient is entire. `B` is even, is of real type, and is nonzero at the selected quartet. It vanishes at every other zeta zero and at both pole points `±i/2`.

Because `z0²` is nonreal, a real linear polynomial can take any prescribed complex value there. Choose real linear polynomials `p_E,p_O` satisfying

\[
 p_E(z_0^2)=i/B(z_0),\qquad
 p_O(z_0^2)=1/[iz_0B(z_0)].
\]

Explicitly, for prescribed value `u` at `w=z0²`, take
`p(X)=a+bX`, `b=Im(u)/Im(w)`, `a=Re(u)-b Re(w)`. Define Fourier targets

\[
 F_E(z)=B(z)p_E(z^2),\qquad
 F_O(z)=izB(z)p_O(z^2).
\tag{4.2}
\]

Their inverse Fourier transforms are respectively real even and real odd. On every horizontal strip the Gaussian factor gives rapid decay; division by `P^r` creates no poles after removal. Contour shifting, also after differentiation, shows that both inverse transforms belong to `𝒮_exp`.

For the even target, the quartet values are `i,i,-i,-i`, and
`overline(F_E(bar z))=F_E(z)`. For the odd target they are `1,-1,-1,1`, and
`overline(F_O(bar z))=-F_O(z)`. Formula (1.4) gives **separately**

\[
 \boxed{\mathfrak k(f_E,f_E)=-4r,
        \qquad \mathfrak k(f_O,f_O)=-4r.}
\tag{4.3}
\]

The pole factors are also annihilated, although this stronger property is not needed for the present `K` argument. This is not symmetrization of one negative vector into two witnesses: the two Fourier interpolations have different prescribed signs and are constructed independently.

Smooth even cutoffs converge in every weighted norm needed for (1.3). Hence each parity has a **fixed compactly supported smooth** unit test `φ_σ`, `σ=E,O`, with

\[
 \mathfrak k(\varphi_\sigma,\varphi_\sigma)=-\nu_\sigma<0.
\tag{4.4}
\]

The continuity used here follows from (1.5), the bounded pole functionals on exponentially weighted spaces, and the translation-difference expression for the archimedean term. It does not assume the desired positivity statement.

### 4.2 The negative tests survive on the original diagonal schedule

**[COFINAL_FAMILY / PAPER]** For late `m`, the support of a fixed `φ=φ_σ` lies strictly inside `I_m`. Put `v_m=P_m φ`, `e=v_m-φ`. The Fourier estimates (3.2)–(3.3) apply with `A_p=||φ^(p)||₂`, without the cutoff tail.

For completeness, let `A_arch` be the archimedean operator in (1.3). Its action on a fixed smooth compact test is in `L²`, with the elementary bound

\[
 \|A_{\rm arch}\varphi\|_2\le c_*\|\varphi\|_2
 +\|\varphi''\|_2\int_0^1s^2j(s)ds
 +4\|\varphi\|_2\int_1^\infty j(s)ds=:C_\varphi.
\]

Use (3.5) for `k(e,v_m)` and the last bound for `k(φ,e)`. The pole/prime bound for the latter is
`(2+4L)sqrt(m)||φ||₂ ||e||₂`. Thus

\[
\begin{aligned}
 |\mathfrak k(v_m,v_m)-\mathfrak k(\varphi,\varphi)|
 \le{}&\bigl[(2+4L)\sqrt m\,\epsilon_0
       +10\epsilon_1+10J_m\sqrt{3m/L}\bigr]\|v_m\|_2\\
 &+\bigl[C_\varphi+(2+4L)\sqrt m\|\varphi\|_2\bigr]\epsilon_0
 \longrightarrow0.
\end{aligned}
\tag{4.5}
\]

The identity behind this estimate is
`k(v_m,v_m)-k(φ,φ)=k(e,v_m)+k(φ,e)`. Every term has the original support convention. For late `m`, `v_m` is nonzero and has norm at most one. Therefore min–max supplies strict **negative upper envelopes**

\[
 \boxed{\lambda_{\min}(K_{m,\sigma})\le-\nu_\sigma/2<0,
       \qquad\sigma=E,O,\quad m\ge m_0(\rho).}
\tag{4.6}
\]

This independently proves precisely the negative-witness return needed here. It does not claim a new independent review of all the stronger bulk-index assertions in MARKOV §4.

### 4.3 Weak escape and collapse of every fixed jet

**[COFINAL_FAMILY / PAPER]** Let `f_{m,σ}` be **any** unit eigenfunction for the bottom of the indicated sector, synthesized and extended by zero as in (1.7). Simplicity is not assumed. For any fixed radical derivative `r` of that parity, choose `u_m` from (3.1). Hermiticity gives

\[
 |\lambda_{m,\sigma}|\,|\langle f_{m,\sigma},u_m\rangle|
 \le\|K_m\operatorname{coeff}(u_m)\|_2.
\]

Combining (3.9) and (4.6), for every `A>0`,

\[
 \boxed{|\langle f_{m,\sigma},r\rangle|
 \le\frac{\|K_m\operatorname{coeff}(u_m)\|_2}{\nu_\sigma/2}
       +\|u_m-r\|_2=O_{r,A}(m^{-A}).}
\tag{4.7}
\]

More generally, the same argument says that any eigenvector sequence whose eigenvalues stay a fixed distance from zero converges weakly to zero. Conversely, if a subsequence has a nonzero weak limit, some fixed derivative has a nonzero limiting pairing; (3.9) and the eigenrelation force its eigenvalues to tend to zero on that subsequence. The off-critical-zero hypothesis is used to contradict that conclusion through (4.6).

Density (2.1) and boundedness `||f_m||=1` now imply

\[
 \boxed{\text{an off-critical zero exists}
 \quad\Longrightarrow\quad
 f_{m,E}\rightharpoonup0,\qquad f_{m,O}\rightharpoonup0.}
\tag{4.8}
\]

For a fixed finite jet `𝒥`, its Gram matrix is positive definite: a nontrivial polynomial times `H(t)` cannot vanish almost everywhere. Consequently (4.7) also implies

\[
 \|P_{\mathcal J}f_{m,\sigma}\|_2=O_{\mathcal J,A}(m^{-A}),
 \qquad \operatorname{dist}_{L^2}(f_{m,\sigma},\mathcal J)\longrightarrow1.
\tag{4.9}
\]

The same conclusion holds for least-squares fitting by the restrictions of these **fixed** derivatives to `I_m`: their Gram matrices tend to the global Gram matrix, and the fitted inner products are exactly the global inner products with the zero-extended `f_m`. This addresses the meaningful, finite-dimensional version of the actual experiment.

### 4.4 Exact classification of Q1 and Q3

**[COFINAL_FAMILY / PAPER]** Any of the following would exclude an off-critical zero:

- a nonzero weak subsequential limit of either sector bottom;
- strong `L²` convergence of unit sector bottoms to a fixed profile;
- for some fixed derivative jet `𝒥`, some `ε>0`, and an unbounded set of original `m`, `||P_𝒥 f_{m,σ}||₂>=ε`.

The third condition is weaker than identifying a plateau and requires no convergence rate. It is nevertheless **RH-implying**, not a free geometric supplier.

**Q1 code: `SELECTION_RH_GRADED`.** Direction proved: persistence of a nonzero physical profile implies RH. No fixed profile, derivative relation between limits, or rate has been obtained. RH is not claimed sufficient for such selection. The first unpaid input is an actual cofinal lower bound for fixed-profile overlap or another no-escape statement on the literal family.

**Q3 code for the measured fixed three-jet family: `PROXIMITY_RH_GRADED`.** A cofinal extension of the small residual would imply RH by (4.9), without G1a. This is not a proof from the finite table.

**Q3 code for the unrestricted `L²`-closed family: `PROXIMITY_ZERO_FREE`, but vacuous.** Its distance is zero for every vector by (2.1)–(2.3), including vectors for perturbed prime matrices. It supplies neither G1a nor G3. A statement about growing derivative order needs an explicit complexity/conditioning budget; (4.9) does not give a bound uniform in that order.

## 5. Selection, heat, and the actual G3 consumer

### 5.1 The exact selection functional is leakage, not ordinary tail mass

**[FINITE_CELL / PAPER]** Fix finitely many radical tests `r_i` of one parity and put

\[
 s_{i,m}=P_mr_i,\qquad e_{i,m}=r_i-s_{i,m},
\]
\[
 M_m(i,j)=\langle s_{i,m},s_{j,m}\rangle,
 \qquad H_m(i,j)=\mathfrak k(s_{i,m},s_{j,m}).
\]

Radicality gives the exact identity

\[
 \boxed{H_m(i,j)=\mathfrak k(e_{i,m},e_{j,m}).}
\tag{5.1}
\]

It includes the exterior pieces, the omitted Fourier modes, their mutual terms, the poles and all prime powers. The right side is **not** `||e||²` and is not known to be nonnegative without further information. Calling an ordinary `L²` tail “the confinement energy” changes the functional.

Within this fixed span, the Ritz-selected coefficients minimize

\[
 \frac{c^*H_mc}{c^*M_mc},\qquad H_mc=\ell_m M_mc.
\tag{5.2}
\]

That is an exact finite-dimensional selection principle, not a determination of its asymptotic minimizer. Nor is the Ritz minimum automatically the full sector minimum. If `U_m` is an orthonormalization of these rows and `Q_m=I-U_mU_m^*` in the sector, the exact effective matrix at an admissible spectral parameter `t` is

\[
 U_m^*K_mU_m-tI
 -U_m^*K_mQ_m
 [Q_m(K_m-tI)Q_m]^{-1}
 Q_mK_mU_m.
\tag{5.3}
\]

Its inverse requires the stated complementary spectral domain; there is no assumed fixed floor. Ignoring the last term is not a confinement theorem.

A genuinely identifying asymptotic argument would need a scale `r_m>0`, convergence of the **full effective** matrix divided by `r_m`, a simple minimizing limiting direction, and errors smaller than its scaled separation. The first unpaid objects are this leakage asymptotic and its complementary return. Neither is supplied by the plateau coefficients or by ordinary tail ratios. If the derivative order is allowed to grow without a budget, (5.2) simply recovers the original problem by (2.3).

### 5.2 Least-squares coefficients are not heat Taylor coefficients

**[ABSTRACT / PAPER]** For `s>=0`, physical heat smoothing means

\[
 h_s=e^{s\partial_x^2}h,
 \qquad \widehat h_s(z)=e^{-sz^2}H(z).
\tag{5.4}
\]

Thus `h+s h''` is a first-order heat approximation, **not** exact evolution at time `s`. A usable finite-order bound is

\[
 \|h_s-h-sh''-\tfrac12s^2h''''\|_2
 \le\frac{s^3}{6}\|h^{(6)}\|_2.
\tag{5.5}
\]

It follows from the real-frequency Taylor remainder for `e^{-s t²}`. No convergence of the infinite heat Taylor series in this topology is assumed.

Suppose the target really is `h_s`, and it is least-squares projected onto the three nonorthogonal functions `r=(h,h'',h'''')` on a chosen window/grid. With Gram matrix `M`, its fitted coefficients obey

\[
 c_{\rm fit}=(1,s,s^2/2)^T
 +M^{-1}\bigl(\langle r_i,R_3(s)\rangle\bigr)_i,
\tag{5.6}
\]

where `R_3` is the omitted remainder. Higher derivatives project onto the lower ones. An overall normalization of the target multiplies all coefficients, without removing this bias. Therefore the measured ratio `0.75–0.81` is not, by itself, a theorem refuting an exact heat-profile limit. It is not evidence proving such a limit either.

In particular, the `weights_normalised` field of `pingeom_fit.py` normalizes `c_i||r_i||` by their Euclidean sum of squares. The functions are not orthogonal, so these numbers are not orthogonal spectral masses. The Gram matrix is indispensable [S5, S8]. The two fitted values of `s` are close but not equal, and there is no certified limiting remainder.

If one eventually proved an **exact fixed finite-jet limit** with nonconstant polynomial multiplier, that limit could not equal a positive-time Gaussian heat profile: a finite polynomial cannot equal `e^{-s z²}` on an open set for `s>0`. That conditional observation does not apply to the present finite fit residuals.

**What fixes `s`?** Globally, nothing in the null condition does. Every `h_s` lies in the same global radical. For the finite heat trial family only, a necessary stationary equation is

\[
 \frac{d}{ds}\frac{\langle P_mh_s,K_mP_mh_s\rangle}{\|P_mh_s\|_2^2}
 =\frac{2\Re\langle P_mh_s'',(K_m-\ell_m(s))P_mh_s\rangle}
        {\|P_mh_s\|_2^2}=0.
\tag{5.7}
\]

This is a source-specific leakage equation. It has not been solved cofinally, and a full bottom need not belong to the heat subfamily at all. There is no identified `s=0.0031` theorem.

### 5.3 `L²` convergence and G3 are not the same assertion

**[ABSTRACT / PAPER]** If a window-supported function `f_m` is compared with a fixed rapidly decreasing `F`, then on `|Im z|<=H`,

\[
 \sup|\widehat f_m(z)-\widehat F(z)|
 \le B_H(L)\|f_m-F\|_{L^2(I_m)}
       +\int_{I_m^c}e^{H|x|}|F(x)|dx,
\tag{5.8}
\]
\[
 B_H(L)=\left(\frac{\sinh(HL)}{H}\right)^{1/2}\ (H>0),
 \qquad B_0(L)=\sqrt L.
\]

Thus an unweighted error tending to zero at no specified rate does not supply compact holomorphic convergence. For positive strip height, a sufficient polynomial rate is `O(m^{-a}(log m)^A)` with `H<2a`; all fixed heights require a stronger return. A direct exponentially weighted `L¹` error is another sufficient interface.

A simple topology control is a bump of amplitude `m^{-H/2}` placed near the right window edge: its `L²` norm tends to zero but its transform at `z=iH` can remain of constant size. Conversely, smooth fixed-window functions multiplied by increasingly high-frequency oscillations have nonvanishing `L²` norm while their transforms tend to zero on every compact complex set. Adding a fixed component and applying the chosen anchor normalization gives the analogous nonzero-limit example. These are topology counterexamples, not claims that actual CCM bottoms behave that way.

Even after a weighted return is proved, the target matters. With a nonzero center normalization and
`hat F(z)=M(z) H(z)`, the limiting normalized transform is

\[
 \Xi(z)\frac{M(z)}{M(0)},
\tag{5.9}
\]

not necessarily `Xi(z)`. A fixed heat time would give `e^{-s z²}Xi(z)`, so `s>0` is not literal G3-to-Xi. Nonetheless, if the approximating transforms have only real zeros and the limit is nonzero, an **entire** multiplier cannot cancel a nonreal zero of Xi. Such a weaker zero-containing limit would still suffice for the Hurwitz consumer. It is a different interface with its own normalization and compact-convergence obligations.

There is also a separate regularity gap in the proposed odd limit: `f_{m,E}->F_E` in `L²` does not imply convergence of the interior derivatives. A claim that the odd limit is `F_E'` needs derivative control and normalization to `F_E'/||F_E'||₂`, including the endpoint issue below.

The implication in §4 is stronger in a different direction: **for these actual sector minima**, merely obtaining a nonzero physical weak limit already has RH content, without first invoking G3 or Hurwitz. That is why the plateau is not an inexpensive replacement for G3.

## 6. Q2 — exact derivative commutator, with the pole and the boundary separated correctly

### 6.1 The full line form is translation invariant, including its poles

**[ABSTRACT / PAPER]** The request's explanation “cosh is not translation invariant” is incorrect for the actual kernel. The pole pair is

\[
 p(x)p(y)-q(x)q(y)=2\cosh((x-y)/2).
\tag{6.1}
\]

It depends on the difference. In fact, simultaneous translation preserves every correlation in (1.3), and hence the entire form. On suitable global tests the distributional convolution action commutes with `∂_x`. This is also the translation identity in CCM Lemma 2.2 [P1].

What breaks translation is **confinement and the periodic finite derivative**, not a non-invariant global pole kernel. Individual rank-one pole pieces mix under translation; their difference is invariant.

### 6.2 Source formula for the rank-two commutator

**[FINITE_CELL / PAPER, every `m>=2`]** Let

\[
 X=\operatorname{diag}(-m,\ldots,m),\qquad
 D=i\omega X,\quad\omega=2\pi/L,\qquad
 \eta=(1,\ldots,1)^T.
\]

Write `β_n=n K_m(n,0)` and `β_0=0`. The literal entries [S2] give

\[
\begin{aligned}
 \beta_n={}&\frac{\kappa n}{L^2+16\pi^2n^2}
 +\frac1\pi\int_0^L j(s)\sin(2\pi ns/L)\,ds\\
 &+\frac1\pi\sum_{2\le k\le m}\frac{\Lambda(k)}{\sqrt k}
                       \sin(2\pi n\log k/L),
 \qquad \kappa=32L\sinh^2(L/4).
\end{aligned}
\tag{6.2}
\]

Here `β` is the `b_n` vector of the request, not the endpoint `b=L/2`. The integral is convergent at zero. The endpoint prime `k=m` contributes zero to this sine moment, as required; it has not been deleted.

For distinct indices,

\[
 K_m(n,k)=\frac{\beta_n-\beta_k}{n-k}.
\]

Thus

\[
 [X,K_m]=\beta\eta^T-\eta\beta^T,
\]
\[
 \boxed{[K_m,D]=i\omega(\eta\beta^T-\beta\eta^T).}
\tag{6.3}
\]

This is the CCM displacement identity with the physical derivative factor and its sign retained, cf. Lemma 5.2 [P1]. All diagonal terms commute with `D`; they remain in the operator and in every Rayleigh value.

For the pole split, define the same `u,v` as the request:

\[
 u_n=\frac{L}{L^2+16\pi^2n^2},\qquad
 v_n=\frac{4\pi n}{L^2+16\pi^2n^2},\qquad
 W=\kappa(uu^T-vv^T).
\]

Since `Xu=L v/(4π)` and `Xv=(η-Lu)/(4π)`,

\[
 \boxed{[W,D]=\frac{i\kappa}{2L}(\eta v^T-v\eta^T).}
\tag{6.4}
\]

Equivalently `β_pole=κv/(4π)` in (6.3). The archimedean and prime boundary contributions are the other two terms of (6.2).

### 6.3 Where the endpoint enters

**[FINITE_CELL / PAPER]** For `f=Σ ξ_n ψ_n` the common endpoint trace is

\[
 f(-b)=f(b)=L^{-1/2}\eta^T\xi.
\]

Its zero-extended distributional derivative is

\[
 \partial_x\widetilde f
 =\widetilde{Df}+f(-b)\delta_{-b}-f(b)\delta_b.
\tag{6.5}
\]

The last two terms are not carrier vectors and are not silently assigned zero. `D` in the probe differentiates the interior trigonometric function. Formula (6.3), which uses only finite entries, is the well-defined boundary return and needs no pointwise trace of the singular archimedean kernel.

For a regular convolution kernel `k(x-y)`, integration by parts on `[0,L]` gives the same structure: if `a(x)=k(x-L)-k(x)` and `t` is its coefficient row, the finite commutator is
`(t η^T+η t*)/sqrt(L)`. For the actual distributional kernel this is interpreted through its finite moments (6.2), not through undefined endpoint values of `j(0)`.

The global translation mode and the interior derivative are therefore related but not identical objects after confinement.

### 6.4 Exact derivative trial and its unpaid complementary coupling

**[FINITE_CELL / PAPER]** Choose a real unit even-sector bottom vector `ξ`, with eigenvalue `λ_E`. Set

\[
 \alpha=\eta^T\xi,\qquad z=X\xi,\qquad d=\|z\|_2.
\]

If `d=0`, then `ξ` is the central mode and the derivative trial is zero; the proposed test is unavailable. Suppose `d>0` and put `v=z/d` in the odd block. By parity `β^T ξ=0`, so (6.3) gives

\[
 \boxed{(K_O-\lambda_E I)v=-\frac\alpha d\beta.}
\tag{6.6}
\]

Consequently

\[
 a:=v^T(K_O-\lambda_E I)v
   =-\frac{\alpha\,\beta^T X\xi}{d^2},
\tag{6.7}
\]
\[
 r:=(I-vv^T)(K_O-\lambda_E I)v
   =-\frac\alpha d(I-vv^T)\beta.
\tag{6.8}
\]

The request's identity is correct with `D` as defined:

\[
 \langle D\xi,K_mD\xi\rangle-\lambda_E\|D\xi\|^2
 =\langle D\xi,[K_m,D]\xi\rangle
 =-\omega^2\alpha\,\beta^T X\xi.
\tag{6.9}
\]

But min–max says only

\[
 \lambda_{\min}(K_O)-\lambda_E\le a.
\tag{6.10}
\]

Let `Q=I-vv^T` in the odd sector and `C=Q(K_O-λ_E I)Q|_{v⊥}`. When the complement is nontrivial, the exact strict positivity criterion is

\[
 \boxed{K_O-\lambda_E I>0
 \quad\Longleftrightarrow\quad
 C>0\ \text{and}\ a-r^*C^{-1}r>0.}
\tag{6.11}
\]

Thus the first unpaid term is explicitly the **source-weighted complementary response** of `Qβ`, together with the positive complementary domain. It is not another unknown derivative angle. For example, if a proved `γ_m>0` satisfies `C>=γ_m I` and
`a>||r||²/γ_m`, then

\[
 \lambda_{\min}(K_O)-\lambda_E
 \ge\frac{a+\gamma_m-\sqrt{(a-\gamma_m)^2+4\|r\|^2}}2>0.
\tag{6.12}
\]

No such lower envelope is supplied here. `γ_m` is allowed to depend on the cell; the previously rejected fixed-floor premise is not reintroduced. In a one-dimensional odd sector the complement is absent and the exact condition is simply `a>0`.

Once strict even-below-odd ordering is proved, simplicity and nonzero `η` pairing follow from the same displacement identity: a multiple even bottom would contain a nonzero eigenvector with `η` pairing zero; its image by `X` would be an odd eigenvector at the same eigenvalue unless it were the central mode, which is incompatible with zero `η` pairing. This is a conditional algebraic consequence, not a supplied ordering.

### 6.5 Why the proposed positive-commutator shortcut does not close the sign

**[ABSTRACT / PAPER]** Since `η⊥β`, the nonzero eigenvalues of (6.3), when `β≠0`, are

\[
 \pm\omega\|\eta\|_2\|\beta\|_2.
\tag{6.13}
\]

The whole commutator is indefinite and has trace zero. A nontrivial globally positive commutator cannot be extracted from this exact finite identity. A localized Mourre-type argument would need a new, explicitly controlled spectral restriction; it does not follow from the rank-two formula.

The angle is also less accurate than the request's wording suggests. For aligned unit vectors,

\[
 \|u-v\|_2^2=2(1-|\langle u,v\rangle|).
\]

Thus `1-cos=1.5e-6` corresponds to a vector error about `1.73e-3`, not `1.5e-6`. In `odd_is_derivative.py`, the uniform 300-point full-period quadrature actually integrates the trigonometric products exactly when `2m<300`; this is not the main obstruction. The obstruction is spectral weighting and the missing lower bound [S7].

An exact negative control is

\[
 O=\operatorname{diag}(-1,10^6),\qquad
 v=(\sqrt{999999}/1000,1/1000).
\]

Its trial value is `10^{-6}>0`, its angle to the true bottom is very small, but its actual bottom is `-1`. This is a generic counterexample to the lower-bound inference, not a counterfeit arithmetic CCM example.

**Q2 codes:** `COMMUTATOR_EXACT` and `GAP_REDUCED`. No source parity-gap lower bound or Theta classification of G1a is inferred.

## 7. Q4 — threshold, decay, and the old heat-RKHS proposal

### 7.1 Exact threshold equation; no automatic arithmetic rigidity

**[ABSTRACT / PAPER]** For a real unit function `f`, let

\[
 R_f(a)=\int f(x)f(x+a)dx.
\]

A single atom of fixed weight `c` contributes `-2c R_f(a)`. Along a simple eigenvalue branch, at an **interior** shift and with the weight held fixed, Hellmann–Feynman gives

\[
 \frac{d\lambda}{da}=-2cR_f'(a).
\tag{7.1}
\]

For an alleged smooth global profile with `hat F_E(t)=4M(t)Xi(t)` and odd profile `F_E'/||F_E'||₂`, the threshold equation is

\[
 R_O'(a)=-\frac{16}{\pi\|F_E'\|_2^2}
  \int_0^\infty t^3|M(t)|^2\Xi(t)^2\sin(ta)\,dt=0.
\tag{7.2}
\]

For pure unnormalized `h'`, omit the norm denominator and put `M=1`. This is an exact implicit formula through Xi. It does not prove existence, uniqueness, the minimum character of a particular root, or a numerical value for the unknown `F_E`.

`pingeom_limit.py` uses `8/π` instead of `16/π` for the unnormalized autocorrelation. The factor-two discrepancy is already acknowledged in the pinned RESULT log [S9, S11]. It does not move a root of `R'`, but it does change amplitudes and cannot be reused in an energy identity. Both displayed quadratures have finite integration ranges and no interval tail certificate; their reported root agreement remains diagnostic.

“All prime shifts lie beyond `a*`” supplies a local speed pattern only after one has proved that `R_O'` has the required sign on the **whole** relevant region. A plotted first crossing does not prove that. A Beurling first prime with `log p_1<a*` would simply fall on the other side of the same profile's speed pattern; this is not a theorem about that Beurling system's eigenfunction or zeta function.

There is an additional source distinction. The probe moves `j log p` while freezing `Λ(p^j)/sqrt(p^j)`. For a coherent change `p=e^a`, the weight is instead `c_j(a)=a e^{-ja/2}`. Away from support thresholds the derivative is

\[
 -2\sum_j\left[c_j'(a)R_f(ja)+j c_j(a)R_f'(ja)\right],
 \qquad c_j'(a)=e^{-ja/2}(1-ja/2).
\tag{7.3}
\]

The first term is absent in the position-only probe. At `ja=L`, the true correlation is clipped to zero outside the window; one must use one-sided derivatives rather than continue the interior formula past `L`. These guards preserve the diagnostic's legitimate interior meaning but prevent its promotion to a global Beurling law [S6, S10].

### 7.2 What sets `exp(-4.6m)`?

**[COFINAL_FAMILY / CONDITIONAL: no asymptotic law supplied]** Nothing read or proved here establishes this exponent. The measured slopes are finite-range fits. Formula (5.1) shows the relevant object: the signed Weil form of the **combined spatial and Fourier leakage**, followed by the complementary response (5.3). The spatial tail `∫_{|x|>L/2}|F|²` does not determine it.

The original carrier has a separate frequency cutoff `Ω_m=2πm/log m`; the diagnostics retain both a growing window and a growing bandwidth. Neither source scale may be replaced by the other. Strong `L²` shape agreement is not an energy-error estimate for this growing family.

The quasimode result gives a rigorous, but nonsharp, statement:

\[
 \lambda_{\min}(K_{m,\sigma})\le C_A m^{-A}
 \quad\text{for every fixed }A>0
\tag{7.4}
\]

by a nonzero parity-correct `u_m`. It is an **upper** bound, compatible with negative eigenvalues. It gives neither a positive lower envelope nor the exponent `4.6`.

Also, the tail used by `confine_probe.py` belongs to a rounded, fitted three-term profile, and its integral stops at `L/2+2`; an infinite-tail remainder is not certified. The observed mismatch is a valid reason not to spend that simple tail model. It is not a proof of an alternative asymptotic rate [S12].

### 7.3 Heat time is not supplied by an RKHS norm cap

**[ABSTRACT / PAPER: source audit and exact heat observation]** The cited archive is **Paper I**. Its Discussion announces a Part II RKHS bound, but the Part II theorem and proof are not present in the supplied file. That bound remains **RELAY / unverified**, not an input [S13].

Three maps are missing before it could constrain `s`: the exact variable/metric map, the identification of its sampling operator with the full CCM form (including the diagonal compensation and poles), and a variational equation selecting the same window bottom. A Gaussian in the test-function construction is not automatically evolution of the physical theta profile by `e^{s∂²}`.

There is a more direct objection to the proposed global “balance point.” For every `s>=0`, `h_s` belongs to `𝒮_exp` and its transform is `e^{-s z²}H(z)`. Therefore

\[
 \boxed{\mathfrak k(h_s,g)=0\quad\text{for every }s\ge0.}
\tag{7.5}
\]

The global arithmetic balance already holds for **all** these heat times. It cannot select `s≈0.0031`. Only confinement/projection and their actual leakage functional could distinguish them. In addition,
`∂_s R_{h_s}(a)=2R_{h_s}''(a)`, whose sign need not be uniform in `a`; heating is not a termwise monotone damping of every source prime correlation.

Two exact checks also prevent treating the archive's summary as a ready positivity supplier. In its Gaussian-tail argument the substitution `x=e^y` must give

\[
 \int_N^\infty\frac{\log x}{\sqrt x}e^{-t(\log x)^2}\,dx
 =\int_{\log N}^\infty y e^{y/2-ty^2}\,dy,
\tag{7.6}
\]

not the displayed integrand without `e^{y/2}`. And its claim of extending a linear expression
`∫a_* Φ-Σ w_n Φ(ξ_n)` to nonnegativity on **all** even nonnegative continuous compact tests cannot be correct: an even narrow bump equal to one at an isolated prime node has integral `O(ε)` and prime contribution `-w_n`, hence negative value for small `ε`. This refutes that unrestricted-cone promotion, not an unspecified Part II operator theorem or the properly restricted Weil autocorrelation criterion.

Thus no selected heat time is imported from the archived claim. This is a source mismatch and an unpaid proof, not a theorem that no useful connection can ever exist.

## 8. Source audit of the observations: what the diagnostics actually establish

**[FINITE_CELL / PAPER: code and log inspection, not a numerical certification]**

1. **Finite plateau versus limit.** The pinned log says that a fixed limiting mixture has been found. Its evidence is a short finite sequence of least-squares fits. This does not prove convergence, rule out a later drift, or prove that either bottom lies exactly in the three-dimensional family. The claim “does NOT converge to h” is likewise not established asymptotically [S5, S11].
2. **Norm and phase.** The fits omit the common `L^{-1/2}` synthesis factor, which cancels in their relative residuals, but must be restored for unit physical profiles. Their basis Gram matrix is not the identity. The derivative-angle code uses a common phase rather than discarding an odd imaginary function; that part is appropriate [S5, S7].
3. **Perturbation provenance.** `break_sign_keep_shape.py` directly computes the old/new bottom angle and eigenvalues; the extra radical-fit residuals are recorded in RESULT, not produced by that script. None was independently recomputed here. The comparison is a finite sensitivity experiment with position-only atom changes, not a theorem about every Beurling system [S10, S11].
4. **Extent of rejected fits.** `confine_probe.py` searches a bounded interval of the parameter in `e^{t x²}h`, and the log says the best fit reaches the search edge. This rejects that tested fitting regime; it is not a mathematical proof against all parameters or all asymptotic versions. No new search of the rejected regime is proposed [S12].
5. **Prior proof status.** The MARKOV audit explicitly leaves its entire Fourier targets and the full diagonal return without an independent analytic verification. This verdict does not quietly relabel those statements as audited. Sections 3–4 give a separate complete proof of the narrower facts used in the present grading argument [S4].

The exact sign/shape claim of Q3 must consequently name its complexity and topology before it is tested. “Within the radical family” without those qualifiers is not an observable with the claimed discriminating power.

## 9. Adversarial controls, scope of refutations, and route map

### 9.1 Strongest attacks on the new result

**[ABSTRACT / PAPER]** The strongest objection is that global radicality does not survive a moving finite projection, while the prime operator grows. That objection would be fatal to a proof using only `k(r,.)=0`. It is why (3.8) is a **norm** bound uniform over every unit carrier vector: the `sqrt(m) log m` prime cost, endpoint jumps, and infinite exterior prime tail all appear before limits are taken.

The second objection is a hidden change from fixed-window `N→∞` to the prescribed diagonal `N=m`. Equations (3.2)–(3.8) and (4.5) are explicit on that diagonal and do not invoke a free Fourier-cutoff choice.

The third objection is the forbidden parity-twin inference. It is avoided by the two different target interpolations (4.2), their separate reality symmetries, and the separately negative values (4.3).

The fourth objection is that density of a radical should force the whole form to vanish. It would do so for a bounded `L²` form, which this global arithmetic form is not. No `L²` continuity is asserted. Only the explicit finite near-null estimates are used to transfer overlap information.

The fifth objection is that a fit on a bounded grid proves the needed fixed-jet overlap. It does not. The theorem explains the content of a future **cofinal, source-certified** overlap statement; it does not supply that statement from the samples.

### 9.2 Exact theorem shapes refuted, not a route-family death

| Refuted shape | Scope / verifier | Evidence and repaired statement |
|---|---|---|
| Unrestricted `L²` radical proximity distinguishes the arithmetic bottom | ABSTRACT / PAPER | Equations (2.1)–(2.3): it holds for every vector. Repair: fix the derivative order or an appropriate compactness/analytic budget. |
| The global pole pair breaks translation invariance | ABSTRACT / PAPER | Equation (6.1) is a difference kernel. Repair: account for confinement and both endpoint masses. |
| A small derivative angle and a positive trial Rayleigh gap imply a positive odd bottom gap | ABSTRACT / PAPER | Exact plant in §6.5 has an actual negative upper envelope `U=-1`. Repair: a complementary lower bound and the Schur correction. |
| A nonzero finite commutator (6.3) is globally positive | FINITE_CELL / PAPER | Its two nonzero eigenvalues have opposite signs (6.13). Repair: any restricted commutator estimate needs an independently supplied spectral restriction. |
| The archive's linear prime-sampling expression is nonnegative on every even nonnegative compact test | ABSTRACT / PAPER | Narrow prime-node bump in §7.3 gives `U=-w_n+O(ε)<0`. Repair: retain the actual autocorrelation/test-class restrictions and prove the missing operator map. |

For each row: `KILL_SCOPE=THEOREM_SHAPE`, `FAILURE_TYPE=COUNTEREXAMPLE` (or exact incompatible identity), `KILL_EVIDENCE_KIND=EXPLICIT_PAPER_IDENTITY_OR_PLANT`, and `EPISTEMIC_STATUS=MATHEMATICALLY_DEAD_FOR_THAT_SHAPE_ONLY`. The pinned source locations are [S1–S3, S5–S13] as applicable; the exact mathematical witnesses are the numbered formulas above. No `ROUTE_FAMILY` kill is asserted. Neither the actual fixed limit nor the actual heat-profile possibility is refuted.

### 9.3 Two admissible re-representations before any escalated computation

**[ABSTRACT / CONDITIONAL: research proposals, subjective cost estimates]**

| Candidate | Exact object and implication | Kill-power / cost | First risk |
|---|---|---|---|
| **Fixed-jet overlap / weak escape** | The Gram-corrected quantity `c_m* G^{-1} c_m`, `c_m=(<h^(k),f_m>)` for fixed parity indices. A positive cofinal lower bound excludes the weak escape of §4. | 9/10 / 4/10 for an independent proof audit; proving the lower bound is much harder | An error in the source-preserving norm return would invalidate the classification. Finite positive measurements do not supply the lower bound. |
| **Scaled leakage with complementary return** | The full effective form (5.3), not ordinary spatial tail mass. A controlled scaled limit could select a profile and identify whether a heat subfamily is relevant. | 8/10 / 9/10 | The complementary response may be of the same order as the apparent leading leakage, or the minimizing direction may drift with complexity. |

A third representation is available for G1a alone: the rank-one complementary response of `Qβ` in (6.11). It is more explicit than an angle, but no positive lower bound has been supplied. It is not the selected next task.

The cross-domain checks are concrete. **Translation/Fourier cyclicity** supplies the exact density theorem, not a sign. **Confinement/Feshbach elimination** supplies the leakage selection functional, with its complement retained. **Analytic interpolation at a zero quartet** supplies the two negative witnesses and thereby the no-escape obstruction. These bridges change the mathematical question; no generic PF or approximate-prime argument is being recycled.

### 9.4 Discriminators

**[ABSTRACT / CONDITIONAL]** For the geometry claim, fix the jet dimension **before** testing and use its actual Gram matrix. A proof of

\[
 \exists r,\epsilon>0\ \exists\text{ unbounded original }\mathcal M:
 \quad\|P_{\mathcal J_{\sigma,r}}f_{m,\sigma}\|_2\ge\epsilon
 \quad(m\in\mathcal M)
\tag{9.1}
\]

is the decisive no-escape functional. Increasing `r` after looking at each vector defeats the test by (2.3). A finite table or an interval consistent with zero is not (9.1).

For the derivative-gap claim, first certify the domain `C>0` and then enclose

\[
 \Delta_m=a-r^*C^{-1}r.
\tag{9.2}
\]

A strictly positive lower envelope for `Δ_m` proves the gap on its certified scope. A strictly negative upper envelope refutes that scope. A zero-straddling interval is inconclusive; the missing item is the signed complementary response, not another scalar subtraction at the same uncertified precision.

## 10. Consumer-first dependency contract

**[ABSTRACT / PAPER for the implications; CONDITIONAL for the unpaid suppliers]**

```yaml
SELECTION_CONTRACT:
  DOWNSTREAM_CONSUMER: LITERAL_GROUND_PROFILE_SELECTION_OR_SAME_FAMILY_G3
  ACTUAL_CONSUMER_REQUIREMENT: >-
    For literal G3, correctly normalized compact-uniform transform tracking.
    For the separate implication in this verdict, one nonzero fixed physical
    overlap on an unbounded original family already excludes an off-critical zero.
  ORIGINAL_REQUESTED_OBJECT: FIXED_EVEN_PROFILE_AND_ITS_NORMALIZED_DERIVATIVE_WITH_RATE
  ORIGINAL_OBJECT_IS: UNKNOWN
  NECESSITY_QUALIFICATION: >-
    Neither this exact limiting profile nor a fixed positive heat time is proved
    necessary for the original mathematical roof. It is not made mandatory.
  KNOWN_WEAKER_INTERFACES:
    - FIXED_JET_OVERLAP_LOWER_BOUND_IMPLIES_RH_BY_4_7_TO_4_9
    - WEIGHTED_TRANSFORM_ERROR_PLUS_REAL_ZERO_FAMILY_REACHES_HURWITZ
    - ENTIRE_MULTIPLIER_LIMIT_CONTAINING_XI_ZEROS_CAN_REPLACE_EXACT_XI_LIMIT
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: FIXED_COMPLEXITY_NO_ESCAPE_VERSUS_DENSE_L2_CLOSURE
  FIRST_UNPAID_TERM: COFINAL_FIXED_JET_OVERLAP_LOWER_BOUND_OR_ACTUAL_SELECTION_ASYMPTOTIC
  REOPEN_TRIGGER: >-
    A source-derived no-escape inequality, or a scaled effective leakage limit
    with a controlled complementary return, not another finite plateau.
G1A_CONTRACT:
  DOWNSTREAM_CONSUMER: SIMPLE_EVEN_BOTTOM_WITH_NONZERO_ETA_PAIRING
  ACTUAL_CONSUMER_REQUIREMENT: STRICT_EVEN_BELOW_ODD_ORDERING
  ORIGINAL_REQUESTED_OBJECT: DERIVATIVE_MODE_COMMUTATOR_LOWER_GAP
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - ANY_VALID_SOURCE_PARITY_COMPARISON_REACHES_G1A
    - C_POSITIVE_AND_A_MINUS_R_CINV_R_POSITIVE_REACHES_G1A
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: EXACT_BOUNDARY_VECTOR_RESIDUAL
  FIRST_UNPAID_TERM: POSITIVE_COMPLEMENT_DOMAIN_AND_SIGNED_QBETA_RESPONSE
  REOPEN_TRIGGER: >-
    A lower envelope for the source Schur margin with all modes and boundary
    contributions retained, or a genuinely different parity supplier.
ARCHIVE_IMPORT_CONTRACT:
  DOWNSTREAM_CONSUMER: SOURCE_SPECIFIC_WINDOW_HEAT_SELECTION_OR_CCM_SIGN
  ACTUAL_CONSUMER_REQUIREMENT: EXACT_OPERATOR_METRIC_TEST_CLASS_AND_VARIATIONAL_CROSSWALK
  ORIGINAL_REQUESTED_OBJECT: PART_II_RKHS_PRIME_CAP_AS_SELECTION_BALANCE
  ORIGINAL_OBJECT_IS: UNKNOWN
  FAILURE_TYPE: NO_SOURCE
  EPISTEMIC_STATUS: RESEARCH_DEBT
  FIRST_UNPAID_TERM: ACTUAL_PART_II_THEOREM_AND_CORRECT_SOURCE_CROSSWALK
  REOPEN_TRIGGER: >-
    A pinned theorem with a complete proof and a map preserving the full CCM
    form and its norm; Paper I's announcement is insufficient.
```

There is no hidden claim that one of these unresolved suppliers is impossible. The exact kills in §9.2 concern only the displayed false interfaces. The actual source geometry, the limiting selection problem and G1a remain unresolved.

## 11. Predictions, proof controls, and closeout

### 11.1 Frozen observer predictions

These outcomes refer to this PAPER verdict; its new analytic proof has not been independently checked.

| Frozen prediction | Fate in this batch |
|---|---|
| P1: identified .25 / reduced .45 / no fixed limit .10 / RH-graded .20 | **RH-graded implication established**, not an identification and not an equivalence. The modal “reduced” guess understates the new obstruction, although the actual selection is still unpaid. |
| P1b: exact physical heat profile, .30 | **Unresolved.** The reported least-squares coefficient ratio is not a valid exact heat-Taylor test without the projection remainder. No heat parameter is proved. |
| P2: exact commutator, .70 | **Confirmed**, with correction of the pole-translation explanation. |
| P2: zero-free lower gap, .12 | **Not obtained.** The complementary source response remains unpaid; this does not refute G1a. |
| P3: RH-graded .55 / zero-free .20 / undecided .25 | **Scope split:** fixed finite-jet persistence is RH-implying; unrestricted `L²` closure proximity is zero-free but vacuous. These meanings cannot be merged into one probability outcome. |
| P4: closed form for `a*`, .45 | **Partial only:** exact implicit Fourier/autocorrelation equation, not an explicit root, uniqueness proof or certified limiting value. |

The two initial qualitative checks registered in the progress messages were the possible nonselectivity of the `L²` closure and the claimed failure of pole translation symmetry. Both resolved decisively in (2.1) and (6.1). The weak-escape theorem was developed during the work; it is not retroactively reported as a pre-registered forecast. No previous probability is changed.

### 11.2 Exact algebra controls executed

A small SymPy control, not a literal CCM scan, checked the displacement and derivative formulas on a symbolic five-mode structured matrix, the pole divided difference, the separate quartet signs, the planted Rayleigh failure, and the Jacobian in (7.6). The output was:

```text
PASS: displacement, derivative commutator, even-to-odd residual identity, energy sign
PASS: pole divided difference; separate even/odd zero-pair signs
PASS: planted Rayleigh test has q=1e-6 but actual lower envelope U=-1
PASS: prime-tail density substitution retains exp(y/2) Jacobian
```

A reproducible core of the check is:

```python
import sympy as s

# modes are the five source labels; these are symbolic structural controls,
# not a substitution for the literal arithmetic matrix.
modes = [-2, -1, 0, 1, 2]
a0, a1, a2, b1, b2, omega, lam = s.symbols(
    "a0 a1 a2 b1 b2 omega lam", real=True
)
beta = s.Matrix([-b2, -b1, 0, b1, b2])
eta = s.ones(5, 1)
diagonal = {0: a0, 1: a1, 2: a2}
K = s.Matrix(5, 5, lambda i, j:
    diagonal[abs(modes[i])] if i == j
    else (beta[i] - beta[j]) / s.Integer(modes[i] - modes[j]))
X = s.diag(*modes)
D = s.I * omega * X
assert s.simplify(X*K - K*X - (beta*eta.T - eta*beta.T)) == s.zeros(5)
assert s.simplify(K*D - D*K - s.I*omega*(eta*beta.T - beta*eta.T)) == s.zeros(5)
x0, x1, x2 = s.symbols("x0 x1 x2", real=True)
x = s.Matrix([x2, x1, x0, x1, x2])  # an arbitrary even vector
alpha = (eta.T*x)[0]
assert s.simplify(
    (K-lam*s.eye(5))*X*x + alpha*beta - X*(K-lam*s.eye(5))*x
) == s.zeros(5, 1)
assert sum(z*z for z in [s.I, s.I, -s.I, -s.I]) == -4
assert -sum(z*z for z in [1, -1, -1, 1]) == -4
v = s.Matrix([s.sqrt(999999)/1000, s.Rational(1, 1000)])
O = s.diag(-1, 10**6)
assert (v.T*v)[0] == 1
assert (v.T*O*v)[0] == s.Rational(1, 10**6)
assert min(O.eigenvals()) == -1
```

The continuum tail bounds, analytic interpolation, density argument and limiting quantifiers are **PAPER**, not consequences of these symbolic checks.

### 11.3 Meta closeout

**What became smaller?** The geometric hypothesis now has an exact dividing line: unrestricted closure gives no information, while a fixed finite-jet overlap is already a load-bearing RH-implying assertion. The derivative-mode calculation has one explicit source residual and one complementary response, rather than an unquantified analogy with a translation mode.

**What was killed?** Selectivity of unrestricted `L²` radical proximity; global pole non-invariance; the unguarded derivative-Rayleigh lower-gap inference; and the archived unrestricted-positive-cone promotion. None kills the literal fixed-profile conjecture or the route family.

**What must not be tried again?** Increasing the jet dimension until a fit succeeds and then treating the fit as arithmetic evidence; reading finite plateaus as limits; substituting a trial upper bound for an odd lower bound; or identifying two heat parameters without the operator/norm map.

**Smallest named gap.** For selection: a source-proved cofinal no-escape/fixed-jet lower-overlap statement. For G1a: the signed `Qβ` complementary response in (6.11). For heat: the actual scaled leakage selection equation, not a global radical condition.

**Next cheapest decisive check.** Independently audit (3.8), (4.5), and the separate quartet interpolation. Those are the nontrivial source-preserving bridges supporting the new classification.

```yaml
iteration:
  target: GOAL058_WINDOW_BOTTOM_AS_CONFINED_XI_RADICAL_VECTOR
  status: PROGRESS
  failed_strategy: UNRESTRICTED_L2_RADICAL_MEMBERSHIP_AS_A_SELECTIVE_GEOMETRIC_CERTIFICATE
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: COFINAL_FIXED_JET_NO_ESCAPE_ON_LITERAL_CCM_BOTTOMS
  invariant_learned: >-
    Fixed complexity and topology must be retained. A dense radical span is
    not a closed kernel of a bounded L2 form. Original N=m returns require
    uniform mixed-form estimates, including endpoint and exterior-prime costs.
  forbidden_future_move: FIT_WITH_UNBOUNDED_JET_ORDER_THEN_PROMOTE_TO_G1A_OR_G3
  next_decisive_test: INDEPENDENT_PAPER_AUDIT_OF_3_8_4_5_AND_4_8
```

## 12. Research log and source register

All repository source locators below use
`Malaeu/chen_q3@f89683aee0e7137e1e1f4e0567418c838ded29d3`, except the explicitly stated request and bootstrap. Read scopes are given so that no excerpt is passed off as a complete dependency audit. Request bytes were hash-verified; the other files were fetched at the pin with GitHub blob metadata, not independently SHA-256-verified in this batch.

| ID | Locator and read scope | Status / use |
|---|---|---|
| S0 | `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`; protocol plus response-format continuation | READ; judging discipline, no mathematical premise |
| S1 | `docs/routeB_bus/proshka/PROSHKA_REQUEST_CONFINE_2026-10-30.txt` at `339fcb4cd9a0c947398ece7b712ca3e4291841f2`, all 172 lines | READ, all supplied byte/hash values verified; authoritative task |
| S2 | `docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py`, lines 1–45, blob `5cbd156db9be84caa938cdbabd4e9ec0b5a6d2f3` | READ; literal entry construction and sine-moment signs; no quadrature output imported as proof |
| S3 | `docs/routeB_bus/proshka/PROSHKA_VERDICT_MARKOV_2026-10-29.md`, lines 100–215, plus the exact theta identities reproduced in S1/S4; blob `ac4661568b9279935a9d868f5e85c8b4c6392610` | READ at the stated scope; form, normalization and pole crosswalk rederived/checked here; disputed §4 not used as an accepted supplier |
| S4 | `docs/routeB_bus/proshka/MARKOV_AUDIT_2026-10-30.md`, complete returned content, blob `7d5525360bcfd727e2b9c16f6672e73b754133ec` | READ; explicitly records the remaining independent analytic audit; numerical checks remain RELAY |
| S5 | `docs/routeB_bus/thetagrade_2026-10-28/pingeom_fit.py`, complete, blob `8d34ba3c7453fb44e7295df64e0391a6d46eda9f` | READ; fixed 3-jet least squares, grid and nonorthogonal coefficient normalization |
| S6 | `docs/routeB_bus/thetagrade_2026-10-28/shake_probe.py`, complete, blob `36c9af1fc61eabbf18a2a94660ca7dfacfffbd52` | READ; fixed-weight shift derivative and endpoint guards |
| S7 | `docs/routeB_bus/thetagrade_2026-10-28/odd_is_derivative.py`, complete, blob `8cfff76cce30ac5dad74704eaef6e90d8cc2e6f1` | READ; interior derivative, phase convention and cosine statistic |
| S8 | `docs/routeB_bus/thetagrade_2026-10-28/heatsmooth_check.py`, complete, blob `5814c3ed82dcb49c61c8015caa62c76adac4d100` | READ; coefficient-ratio diagnostic; no remainder or exact heat identification |
| S9 | `docs/routeB_bus/thetagrade_2026-10-28/pingeom_limit.py`, complete, blob `ba48945773e01817ecdbe97014223aca0f1a82aa` | READ; autocorrelation root equation and factor-two amplitude issue |
| S10 | `docs/routeB_bus/thetagrade_2026-10-28/break_sign_keep_shape.py`, complete, blob `d9940cc1c31691dbf333aa617076e7ef27f3dca6` | READ; finite perturbation and old/new eigenvector angle, not a general Beurling theorem |
| S11 | `docs/routeB_bus/thetagrade_2026-10-28/RESULT.md`, lines 180–end, blob `951296f2997e2b7c59a42c3d80f2821ced9373a8` | READ; last diagnostic sections and observer interpretations; all numerical values RELAY, not rerun |
| S12 | `docs/routeB_bus/thetagrade_2026-10-28/confine_probe.py`, complete, blob `848c2697479786b49c555cdf1ba377bb7f493f5e` | READ; fitted tail, finite quadrature range, bounded heat-deformation search |
| S13 | `full/archive_latex_2026_01_29/paper1_fejer_heat/main.tex`, opening sections and lines 400–end excerpts | READ outside the bus because explicitly requested; Part II is announced, not proved here; tail and cone mismatches identified |
| P1 | Connes–Consani–Moscovici, `arXiv:2511.22755v1`, primary HTML: Lemma 2.2; §3 equations (3.2)–(3.20); §5 equations (5.2)–(5.3), Lemmas 5.1–5.4; real-zero theorem statement | READ; source normalization, translation invariance, unconditional explicit formula, and structured commutator. The new dense-jet/weak-escape derivation is this verdict's own PAPER proof. |

Primary public locator: `https://arxiv.org/html/2511.22755v1`.

The raw `pingeom_fit_dps100.jsonl` and `confine_probe_dps100.jsonl`, the remaining ancillary scripts, the ONO review, and the wall atlas were not newly read in full. Their relevant descriptions in the authoritative payload and pinned audit/log were not promoted into proof premises. No outside Part II, new arithmetic theorem, or new numeric law was assumed.

### 12.1 Candidate tests that did not survive, or did not close the consumer

**[ABSTRACT / PAPER unless marked CONDITIONAL]**

| Candidate | First failing fact or unpaid inequality |
|---|---|
| Radical membership as selection | Its unrestricted `L²` closure is the entire parity space, (2.1). |
| A fixed plateau from finite fitted coefficients | No cofinal convergence/tightness statement; fixed-jet persistence would already imply RH, (4.9). |
| Coefficient ratio as an exact heat test | Omitted higher terms project onto the same nonorthogonal three-jet basis, (5.6). |
| Ordinary spatial tail as confinement energy | Exact energy is `k(e_i,e_j)`, not the `L²` tail, (5.1). |
| Positive derivative Rayleigh gap as lower parity gap | Variational direction is (6.10); the complementary response is unpaid. |
| Global positivity of the finite commutator | Its nonzero eigenvalues are opposite, (6.13). |
| Threshold sign as exact-prime rigidity | The same autocorrelation sign applies to fake atoms; coherent weight and cutoff derivatives add (7.3). |
| Global heat “balance point” | Every heat-smoothed `h_s` is already radical, (7.5), so global balance cannot select one time. |
| Archived RKHS cap as a current source theorem | Part II proof and full operator/metric map are absent; Part I also has the explicit issues in §7.3. |

### 12.2 Reusable intermediate formulas

The norm return (3.8), negative-test return (4.5), Gram-corrected overlap consequence (4.9), leakage identity (5.1), compact-transform budget (5.8), derivative residual (6.8), and atom derivative with moving weights (7.3) remain available for other questions at exactly their stated scopes. None is an unpaid sign disguised as a theorem.

## 13. Proshka's own line

I would keep the geometric observation, but narrow its meaning before building on it.
A three-dimensional fit is informative; membership in a dense infinite-dimensional family is not.
The distinction changes the route more than another decimal place in the fit.
I chose the fixed-jet overlap question because it admits a source-preserving test of its arithmetic content.
I did not choose a heat-time fit as the main route because the existing coefficients are projections, not Taylor data.
I did not choose another secular bracket because the request already identifies that cancellation problem.
The useful surprise is that persistent overlap is enough; a complete limiting profile is stronger than necessary.
The unpleasant part is that this weak-looking overlap already excludes an off-critical zero.
That is a real mathematical implication, not a reason to stop investigating it.
The first move beyond this batch is an independent audit of the diagonal near-null return.
A missing endpoint term or an unpaid growing-prime factor would kill that proof as written.
The second move is a controlled leading leakage form on a fixed jet with its complement retained.
A complementary response of the same size would kill the naive three-by-three selection model.
I would ask for the actual Gram matrices and residual vectors, not more rounded normalized weights.
I would also ask for the precise phase and continuous-norm normalization used in any proposed limiting profile.
The pole correction matters because an apparent symmetry-breaking mechanism was assigned to the wrong place.
The window really does break translation; the global pole pair does not.
The derivative relation is useful because its residual is explicit in one boundary vector.
It is not useful as an odd lower bound until the orthogonal complement is controlled.
The threshold is a property of autocorrelation, not a fingerprint proving that the atoms are primes.
The old RKHS announcement is not a substitute for that control in another norm.
I distrust the words fixed, limit, and refuted when they are attached to finite diagnostic fits.
I do not distrust the observation itself; the fixed-jet version is precise enough to deserve a theorem.
The next result should verify that theorem's arithmetic content before anyone spends the geometry as an unconditional supplier.

## 14. One next directive and final boundary

**CODEX DIRECTIVE — read-only independent PAPER audit of the fixed-jet escape theorem.**

Audit §§1–4 of this attachment against the literal entries [S2] at the pinned source commit. The exact target is:

> If an actual off-critical zeta zero exists, then on the original `N=m`, `L=log m` schedule, every normalized even-sector and odd-sector bottom loses its overlap with each fixed derivative of `h`, and hence converges weakly to zero. In particular, persistent mass in a fixed finite derivative jet would imply RH.

First verify the signed explicit formula and the separate even/odd targets (4.1)–(4.3). Then check the **uniform mixed-form** estimate (3.5), both endpoint terms (3.3), the infinite exterior-prime estimate (3.7), and the compact negative-test return (4.5). Finally verify the exponential-strip density proof and the fixed-Gram projection step. Do not assume any MARKOV index equivalence, G1a, G3, a positive floor, or a freely chosen larger Fourier cutoff.

The algebra control in §11.2 is only a sign/factor test; the analytic estimates and quantifiers require a paper audit. No Lean, repository edit, broad numerical scan, source-family substitution, or route promotion is authorized.

**Success condition:** return `FIXED_JET_ESCAPE_CONFIRMED_PAPER`, with all the above returns justified on the original schedule. Otherwise return `FIXED_JET_ESCAPE_FIRST_UNPAID_TERM`, identifying the first incorrect or insufficient estimate and its weakest repaired statement. An error should repair or kill this exact proof, not be turned into route-family death.

**Final boundary:** no actual cofinal fixed-jet lower bound, fixed limit, heat time, parity-gap lower bound, or G3 estimate has been obtained. The new result is a PAPER classification of what those geometric claims would entail, together with exact source algebra and explicit return budgets. RH remains open; no RH claim or repository-state change is made.
