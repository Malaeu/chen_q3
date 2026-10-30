# STATUS: TRY_VARIATIONAL_SOURCE_CUT_COMPARISON

```yaml
OPERATIVE_CLASS: TRY_VARIATIONAL_SOURCE_CUT_COMPARISON
REQUEST_ID: REQ-2026-10-30-VARIATIONAL
BOUNDARY_ID: GOAL058_FIXED_JET_NO_ESCAPE_ON_LITERAL_CCM_BOTTOMS
REQUEST_SHA256: d2e14cbbc2e0827b6bf4867c010337e3adb10c5ba1943de85a6bf3b033af4c1f
REQUEST_BYTES: 11328
REQUEST_LINES: 219
REQUEST_FINAL_LF: true
REQUEST_COMPUTED_GIT_BLOB: c34bf7b387edcbe2dd72ff531b8a1e72e93f6a83
REQUEST_HASH_CHECK: MATCH
SOURCE_BASE_COMMIT: 805ed24718155280ef563316ea5798d354b35cc7
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_SELECTED_FERRERS_FAMILY
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
ACTUAL_ESCAPING_BOTTOM_STRICT_COMPETITOR: NOT_PRODUCED
NOESCAPE_T: OPEN
RH: OPEN
G1_G3: NOT_CLOSED
NEW_SOURCE_THEOREM: NONNEGATIVE_ESCAPING_SUPERPOLYNOMIAL_QUASIMODES_IN_THE_LITERAL_EVEN_CARRIER
NEW_VARIATIONAL_REPRESENTATION: EXACT_NORM_PRESERVING_EVEN_COEFFICIENT_CUTS
ADDITIONAL_SOURCE_PROPERTY_REQUIRED: SIGNED_CROSS_CUT_BINDING_WITH_SEPARATELY_PROVED_ONE_SIDED_BUDGETS
FIRST_UNPAID_ESTIMATE: EQUATION_7_6_NOT_PROVED_FOR_AN_ESCAPING_EXACT_BOTTOM
MODULUS_LOW_ENERGY_SURROGATE: INSUFFICIENT_BY_AN_ACTUAL_SOURCE_SEQUENCE
VARIATIONAL_NOESCAPE_REFUTED: false
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: COFINAL_SOURCE_COUNTERTEST_AND_EXACT_FINITE_VARIATION_ONLY
NOESCAPE_PROOF_PROGRESS: NO_COFINAL_BOTTOM_OVERLAP_OR_LOWER_FLOOR_ESTABLISHED
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 3
VERIFIER: PAPER
INDEPENDENT_REVIEW_OF_THIS_VERDICT: NOT_PERFORMED
SYMBOLIC_CONTROLS: EXACT_ALGEBRA_PASSED
LITERAL_CCM_NUMERICAL_SCAN: NOT_PERFORMED
M16_FX_RERUN: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
REPOSITORY_WRITTEN: false
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## 0. Answer to the single question

**I do not obtain the strict competitor for an actual escaping bottom.** The additional source property needed by the supplied modulus argument is not a consequence of small energy, small residual, or fixed-jet escape. The stronger obstruction proved here is source-specific: there exist **nonnegative, real, even, unit vectors in the original `N=m` carrier** which escape every fixed jet, have residual smaller than every fixed inverse power of `m`, and are left **exactly unchanged** by the projected-modulus transformation. This is not a synthetic replacement of the CCM matrix. It rules out repairing that argument merely by adding an arbitrarily accurate quasimode hypothesis to the proposed low-energy class. It does **not** show that these vectors are exact bottoms.

I then use exact bottom minimality in a different way: **flip signs of blocks of the even Fourier coefficients**. These competitors remain in the carrier and preserve the norm exactly. Their full energy difference is a signed cross-block pairing with no Fourier-return error and no unknown eigenvalue in the comparison. Minimality, beyond stationarity, forces every such pairing to be nonpositive. A contradiction would follow from an independently proved positive lower envelope for one of them under escape. I derive the exact source kernel and the separate positive/negative budgets for that test. **The required source comparison is not proved.**

The precise remaining work is (7.6), not a new name for a compact-flux identity or an assumed tightness theorem. The restriction to specified coefficient cuts makes it a transformation-specific sufficient mechanism, not an equivalent formulation of T. Its failure would not refute variational NOESCAPE.

The objective remains a proved RH. The inherited implication **T implies RH** is used only as a downstream consumer; neither T, RH, positivity of the bottoms, nor a cofinal lower floor is used as an input to the new lemmas.

### 0.1 Intake and scope

The entire attached TXT was read. Direct computation on its mounted UTF-8 bytes gave the byte count, LF count, SHA-256, and Git blob recorded above. The last LF is present. The current protocol was fetched from `rh_clean`; mathematical source reads were pinned to `805ed24718155280ef563316ea5798d354b35cc7`.

The attachment's V1–V6 are retained as the reviewed own attempt, not rewritten into a different operator. The m16 result is not promoted: the attachment expressly leaves independent physical-X quadrature certification open. No finite F/X computation was repeated. The reported ENTROPY replay, reviews, and stronger translated-entropy result are **owner-supplied status**, not new checks claimed in this batch. None is needed to prove the new construction below. [S0]

### 0.2 Claim ledger

| ID | Scope / verifier | Result established here | Boundary |
|---|---|---|---|
| V-A | ABSTRACT / PAPER | An escaping complex bottom sequence can be reduced to real even bottoms without assuming simplicity | Does not make bottoms nonnegative |
| V-B | FINITE_CELL / PAPER | An explicit polynomial norm envelope for the full literal matrix | No lower floor |
| V-C | COFINAL_FAMILY / PAPER | Moving symmetric translates of the theta radical survive the original Fourier return with superpolynomial residual | They are trial vectors, not selected eigenvectors |
| V-D | COFINAL_FAMILY / PAPER | Those trials can be made exactly nonnegative inside the original carrier with the same residual order | Does not prove or refute T |
| V-E | COFINAL_FAMILY / PAPER | Fixed-prime autocorrelations need not vanish under fixed-jet escape, even for these source quasimodes | No passage of an infinite prime sum through a weak limit |
| V-F | FINITE_CELL / PAPER | Exact coefficient-cut energy formula and bottom stability inequalities | No positive cut for actual escaping bottoms is obtained |
| V-G | FINITE_CELL / PAPER | Source-explicit pole/archimedean/prime cut decomposition and finite one-sided budgets | The decisive strict separation remains unproved |
| V-H | COFINAL_FAMILY / CONDITIONAL | A source separation as in (7.6) would contradict an escaping bottom and hence prove T | This is a receiver, not a supplied theorem |

## 1. Literal source and the use of minimality

Throughout,
\[
L=\log m,\quad b=L/2,\quad I_m=[-b,b],\quad N=m,
\]
\[
\psi_{n,L}(x)=L^{-1/2}e^{2\pi in(x+b)/L}\mathbf1_{I_m}(x),
\qquad |n|\le m.
\]
Let `V_m^E` be the even carrier. `P_m` denotes the orthogonal Fourier projection, with the even restriction understood when appropriate. Write `A_m` for the literal even CCM matrix. All vector norms are the Hilbert norms induced by this orthonormal basis.

The inherited source form, antilinear in its first argument, is [S2, §1]
\[
\begin{aligned}
\mathfrak k(f,g)={}&-c_*\langle f,g\rangle
 +\int_0^\infty j(s)\{2\langle f,g\rangle-Q_{f,g}(s)\}\,ds\\
 &-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}Q_{f,g}(\log n)
 +\langle f,p\rangle\langle p,g\rangle
 -\langle f,q\rangle\langle q,g\rangle,                 \tag{1.1}
\end{aligned}
\]
where
\[
Q_{f,g}(s)=\int\overline{f(x)}g(x+s)\,dx+
                \int\overline{f(x)}g(x-s)\,dx,
\]
\[
j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad
c_*=\gamma+\log(8\pi)+\pi/2,\quad
p=\sqrt2\cosh(x/2),\quad q=\sqrt2\sinh(x/2).
\]
For two window-supported functions the prime sum truncates at `n<=m` by support; the endpoint correlation at `n=m` is zero almost everywhere. For comparison with a global theta function the sum is infinite and will be bounded as such. The odd pole disappears only when both arguments really are even. The archimedean tail and constant remain in (1.1).

The inherited theta facts used below are
\[
h>0,\quad h(-x)=h(x),\quad
\widehat h(z)=4\xi(1/2-iz),\quad
\mathfrak k(h(\cdot-a),v)=0\quad(a\in\mathbb R),             \tag{1.2}
\]
for the admissible mixed tests, and
\[
\|e^{t|x|}h^{(j)}\|_2<\infty\quad(t\ge0,\ j\ge0).
                                                               \tag{1.3}
\]
These are the source identities re-read in CONFINE §1, not a claim that the radical identity extends continuously to every `L²` limit. [S2] They do not assume RH.

### Lemma 1. Realification preserves an escaping bottom problem

**THIS STEP IS PROVED HERE.**

**[ABSTRACT | PAPER]** Suppose complex unit even vectors `f_m` are exact bottoms and escape every fixed real theta jet. There exists a sequence of real even unit bottoms with the same eigenvalues and the same escape property.

**Proof.** The even source matrix is real symmetric. Write `f_m=x_m+i y_m`. Both real parts satisfy `A_m x_m=lambda_m x_m` and `A_m y_m=lambda_m y_m`. At least one has norm at least `1/sqrt(2)`. Normalize that part. Projection on a real jet commutes with realification, so each fixed-jet norm increases by at most `sqrt(2)`. The eigenvalue remains the bottom eigenvalue. No simple-eigenvalue assumption, phase convention, or positivity assumption is introduced. ∎

Thus the subsequent real-coordinate cut construction is sufficient for a contradiction to the proposed complex escape sequence.

### Lemma 2. What exact minimality supplies, and what it does not

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** For an exact unit bottom `f` with eigenvalue `lambda`,
\[
A_m-\lambda I\succeq0,
\qquad
\mathfrak k[g]-\lambda\|g\|^2\ge0\quad(g\in V_m^E).       \tag{1.4}
\]
Stationarity alone is only the eigenrelation. The positive-semidefinite assertion in (1.4) is the additional global variational fact.

Applied to the attachment's explicit candidate `P_m|f|/||P_m|f|||`, it yields exactly
\[
G(f)\le R(f).                                             \tag{1.5}
\]
It does **not** yield an upper bound for the return error small enough to reverse (1.5).

**Proof.** Diagonalize the finite Hermitian matrix. Every eigenvalue is at least its minimum. Equation (1.5) follows by inserting the accepted identity V2, whose denominator is positive. ∎

The attempted contradiction therefore needs a genuinely new source implication from escape to an inequality incompatible with (1.4). In particular, the first proposed bound `A(f)+P(f)>=eta_m>0` cannot follow just from escape and low energy. The next section gives a source-level, cofinal countertest to precisely that inference.

## 2. A uniform envelope needed for a lawful positivity repair

### Lemma 3. A polynomial upper bound for the full matrix norm

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** For `L>=2`, set
\[
\Omega_m=\frac{2\pi m}{L},
\]
\[
M_m=c_*+8+\frac34\Omega_m^2+
          \frac{3(2m+1)}L+(2+4L)\sqrt m.
                                                               \tag{2.1}
\]
Then the full literal compression, and hence its even restriction, satisfies
\[
\|K_m\|\le M_m.                                          \tag{2.2}
\]

**Proof.** Let `v` be a unit carrier vector, extended by zero. On the window,
\[
\|v'\|_2\le\Omega_m,\qquad
\|v\|_\infty^2\le(2m+1)/L.
\]
For `0<s<=1`, integration over the overlap and over the two endpoint strips gives
\[
\|\widetilde v(\cdot+s)-\widetilde v\|_2^2
 \le s^2\Omega_m^2+2s(2m+1)/L.                            \tag{2.3}
\]
This explicitly retains the zero-extension jumps. Since `j(s)<=3/(2s)` for `s<=1`, their archimedean contribution is at most
`3 Omega_m²/4+3(2m+1)/L`. For `s>=1`, the squared difference is at most four and
\[
\int_1^\infty j(s)ds
 \le\frac{2e^{-1/2}}{1-e^{-2}}<2.
\]
This accounts for the `8` in (2.1), including the tail beyond `L`.

The finite prime form has absolute value at most
\[
2\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n}
 \le4\sqrt m\,L.
\]
The two pole operators together have norm at most
\[
\|p\|_{L^2(I_m)}^2+\|q\|_{L^2(I_m)}^2
 =4\sinh b\le2\sqrt m.
\]
Adding the absolute diagonal constant gives (2.1). Taking the supremum of the absolute Rayleigh value of the finite Hermitian matrix proves (2.2). No sign of that matrix was assumed. ∎

The bound is deliberately coarse. Its role is to show that an independently superpolynomially small positivity correction remains superpolynomially small after applying the **actual** matrix. It is not a proposed spectral floor.

## 3. Nonnegative escaping quasimodes of the actual source

This construction addresses the precise objection to the top-mode example V6: those top modes were not low-energy quasimodes. The sequence here is.

### Lemma 4. Moving even radical packets have a uniform original-carrier return

**THIS STEP IS PROVED HERE.**

**[COFINAL_FAMILY | PAPER]** Put
\[
a_m=L/8,
\qquad
r_m(x)=\frac{h(x-a_m)+h(x+a_m)}{\nu_m},
\quad
\nu_m=\|h(\cdot-a_m)+h(\cdot+a_m)\|_2.                    \tag{3.1}
\]
Choose one fixed real even smooth `chi`, with `0<=chi<=1`, equal to one on `[-1/2,1/2]`, and supported in `(-3/4,3/4)`. Define
\[
z_m(x)=\chi(x/b)r_m(x),\qquad q_m=P_mz_m.
                                                               \tag{3.2}
\]
For every fixed `A>0`,
\[
\|q_m-r_m\|_2+\|K_m\operatorname{coeff}(q_m)\|_2
       =O_A(m^{-A}).                                      \tag{3.3}
\]
The same sequences (3.1)–(3.2) work for every `A`. The cutoff and `N=m` are not adjusted with the desired error order.

**Proof.** The profiles `r_m` are real, positive, even, unit normalized, and are global radical vectors by linearity of (1.2). This argument is in the physical Weil test class; it does not assert that `r_m/h` belongs to a global entropy or weighted jump-energy domain. Since `h>0`,
\[
\sqrt2\|h\|_2\le\nu_m\le2\|h\|_2.
                                                               \tag{3.4}
\]
For every fixed derivative order `p`, translation invariance of the `L²` norm and bounded cutoff derivatives give
\[
C_p:=\sup_{m:\,b\ge1}\|z_m^{(p)}\|_2<\infty.              \tag{3.5}
\]
All endpoint jets of `z_m` vanish.

Let `e_m=q_m-z_m`. Periodic Parseval and the Fourier-tail Cauchy–Schwarz bound give, for every integer `p>=2`,
\[
\epsilon_{0,m}:=\|e_m\|_2
       \le C_p(L/(2\pi m))^p,
\quad
\epsilon_{1,m}:=\|e_m'\|_{L^2(I_m)}
       \le C_p(L/(2\pi m))^{p-1},                         \tag{3.6}
\]
\[
J_m:=|e_m(-b)|+|e_m(b)|
 \le\frac{2C_p}{\sqrt L}(L/(2\pi))^p
                   \sqrt{\frac2{2p-1}}m^{1/2-p}.          \tag{3.7}
\]
The derivative in (3.6) is the interior derivative, not an assertion that the zero extension lies in global `H¹`.

For a unit `v` in the original carrier, `e_m` is orthogonal to `v`. Differentiating the correlation in the first argument includes the two boundary masses and gives
\[
|Q_{e_m,v}(s)|\le
  2s\left(\epsilon_{1,m}+J_m\sqrt{3m/L}\right).
\]
As `int_0^infty s j(s)ds<5`, the full mixed form consequently obeys
\[
|\mathfrak k(e_m,v)|
 \le (2+4L)\sqrt m\,\epsilon_{0,m}
       +10\epsilon_{1,m}+10J_m\sqrt{3m/L}.                \tag{3.8}
\]
This is the CONFINE mixed estimate with its constants checked directly: the diagonal and archimedean constant cancel only by `e_m perpendicular v`, the poles cost `2 sqrt(m) epsilon_0`, and all prime powers through `m` cost `4 sqrt(m)L epsilon_0`. [S2, §3]

It remains to make that estimate uniform for the **moving** translates. Let `w_m=r_m-z_m`. On its support, `|x|>=L/4` and
\[
|x\pm a_m|\ge L/8.
\]
For fixed `q,t>=0`, a change of variables and (1.3) give, for either translated theta derivative,
\[
\left\|e^{q|x|}\mathbf1_{\{|x|\ge L/4\}}
              h^{(j)}(x\pm a_m)\right\|_2
 \le m^{q/8-t/8}
             \|e^{(q+t)|y|}h^{(j)}(y)\|_2.              \tag{3.9}
\]
The factors from differentiating `chi(x/b)` are bounded. Since `t` is arbitrary, every weighted tail norm of `w_m` and `w_m'` needed below is smaller than every fixed inverse power of `m`.

For completeness define
\[
A(w)=\int e^{|x|/2}|w(x)|dx,
\quad T(w)=\|e^{|x|}w\|_2,
\quad S_\Lambda=\sum_{n\ge2}(\log n)n^{-3/2}<\infty.
\]
The exterior comparison has the explicit envelope
\[
\begin{aligned}
|\mathfrak k(w_m,v)|\le\tau_m:={}&c_*\|w_m\|_2+10\|w_m'\|_2\\
 &+2m^{1/4}A(w_m)+2\sqrt m\,S_\Lambda T(w_m).
                                                               \tag{3.10}
\end{aligned}
\]
Here the prime sum is **infinite**. Indeed, on the translated support of a window vector,
\[
|Q_{w_m,v}(\log n)|\le2\sqrt m\,n^{-1}T(w_m).
\]
The two pole integrals are bounded by their exponential weighted `L¹` norms. The archimedean expression is bounded by the global translation difference of `w_m'`. Thus no exterior prime, endpoint term, or pole is discarded. Weighted `L¹` follows from weighted `L²` with one additional exponential weight. Equation (3.9) proves `tau_m=O_A(m^{-A})` for every `A`.

Finally radicality yields
\[
\mathfrak k(q_m,v)=\mathfrak k(e_m-w_m,v).
\]
Taking the unit-carrier supremum in (3.8)–(3.10), and then choosing a fixed sufficiently large `p` for any prescribed `A`, proves the residual in (3.3). The norm approximation follows from (3.6) and the tail estimate. ∎

**Why this is not a uniform-in-translation assumption:** (3.9) pays the growing shift `a_m=L/8` explicitly. A fixed-translate theorem was not silently applied with an unbounded parameter.

### Lemma 5. The returned vectors can be made exactly nonnegative without leaving the carrier

**THIS STEP IS PROVED HERE.**

**[COFINAL_FAMILY | PAPER]** There exist real even `g_m in V_m^E` such that
\[
\boxed{\|g_m\|_2=1,\qquad g_m(x)\ge0\text{ on }I_m,}
                                                               \tag{3.11}
\]
and, for every fixed `A>0` and fixed finite theta jet `J_r`,
\[
\boxed{
\|A_m\operatorname{coeff}(g_m)\|_2+
\|P_{J_r}g_m\|_2=O_{r,A}(m^{-A}).}                       \tag{3.12}
\]
In particular `g_m` converges weakly to zero and
`|k[g_m]|=O_A(m^{-A})`. No eigenvector assertion is made.

**Proof.** Expand the smooth periodic function `z_m` from Lemma 4 in the full window Fourier series,
\[
z_m=\sum_{n\in\mathbb Z}d_{m,n}\psi_{n,L},
\]
and define the nonnegative scalar
\[
t_m=\frac1{\sqrt L}\sum_{|n|>m}|d_{m,n}|.
                                                               \tag{3.13}
\]
This is an exact definition, not a numerical truncation. For every fixed `p>=2`,
\[
t_m\le\frac{C_p}{\sqrt L}(L/(2\pi))^p
                 \sqrt{\frac2{2p-1}}m^{1/2-p}.           \tag{3.14}
\]
Thus `t_m` and `sqrt(L)t_m` are superpolynomially small. Uniform convergence gives
\[
|q_m(x)-z_m(x)|\le t_m\quad(x\in I_m).
\]
Set
\[
v_m=q_m+t_m\mathbf1_{I_m},\qquad g_m=v_m/\|v_m\|_2.
                                                               \tag{3.15}
\]
The correction is **only the zero Fourier mode**, not an enlarged carrier. It makes `v_m>=z_m>=0` pointwise. By (3.3), `||v_m||_2 ->1`, hence is at least `1/2` eventually. Lemma 3 gives
\[
\|A_m\operatorname{coeff}(v_m)\|_2
 \le\|A_m\operatorname{coeff}(q_m)\|_2+
            t_m\sqrt L\,M_m.                             \tag{3.16}
\]
The second term remains superpolynomially small because `M_m` is polynomially bounded. Normalization preserves that conclusion.

For any fixed derivative `h^(j)`, weighted Cauchy–Schwarz and
`|x-a|+|x|>=a` yield, for every `t>0`,
\[
|\langle h(\cdot\pm a_m),h^{(j)}\rangle|
 \le e^{-t a_m}
      \|e^{t|x|}h\|_2\|e^{t|x|}h^{(j)}\|_2
 =C_{j,t}m^{-t/8}.                                      \tag{3.17}
\]
The norm difference between `g_m` and `r_m` has every inverse-power bound by (3.3)–(3.16). The fixed theta-jet Gram matrix is positive definite: a linear dependence of its derivatives would give a polynomial times `H(t)=hat h(t)` equal to zero almost everywhere; `H` is continuous and nonzero on an interval around zero, so that polynomial is zero. Equation (3.17) and this fixed Gram inverse give the projection estimate in (3.12).

Alternatively weak convergence follows directly because `a_m -> infinity`, translates of a fixed `L²` function tend weakly to zero, and `g_m-r_m ->0` in norm. The energy bound follows from Cauchy–Schwarz and the residual. ∎

This is a uniform statement over the original cofinal schedule, not a finite sample. It has exact support, norm, parity and carrier, and pays the zero mode explicitly.

### Lemma 6. Escape does not erase the prime correlations of these source vectors

**THIS STEP IS PROVED HERE.**

**[COFINAL_FAMILY | PAPER]** Let
\[
C_h(s)=\int h(x)h(x+s)\,dx,\qquad H_0=\|h\|_2.
\]
For every fixed real `s`, the sequence of Lemma 5 satisfies
\[
\boxed{C_{g_m,g_m}(s)\longrightarrow C_h(s)/H_0^2.}        \tag{3.18}
\]
For each fixed prime-power shift this limit is positive. Nevertheless every fixed-jet projection of `g_m` vanishes.

**Proof.** Directly from (3.1),
\[
C_{r_m,r_m}(s)=
 \frac{2C_h(s)+C_h(s+2a_m)+C_h(s-2a_m)}{
                   2H_0^2+2C_h(2a_m)}.
\]
The displaced correlations tend to zero. The difference between the autocorrelations of two unit functions is bounded uniformly in `s` by twice their `L²` distance. Lemma 5 therefore proves (3.18). Positivity follows from `h>0`. ∎

This is a concrete source obstacle to the step “weak escape makes the jump correlations disappear.” Quadratic correlations are not compact linear observables. The pole growth is explicit:
\[
 \langle p,r_m\rangle=
 \frac{2\cosh(a_m/2)}{\nu_m}\langle p,h\rangle,
 \qquad\langle q,r_m\rangle=0.
\]
The first quantity tends to infinity; the window/projection corrections for `g_m` remain superpolynomially small after the window pole norm is paid. One may not interchange (3.18) with the growing prime sum: its total absolute weight grows. The exact radical identity supplies cancellation, not a dominated-convergence bound for that sum.

### Consequence for the supplied modulus attempt

For every `g_m` in Lemma 5,
\[
|g_m|=g_m,\qquad P_m|g_m|=g_m.
\]
Thus the attachment's quantities satisfy **exactly**
\[
 d_{g_m}(s)=0,\quad A(g_m)=P(g_m)=H(g_m)=G(g_m)=0,
\quad e=0,\quad R(g_m)=E(g_m)=0.                          \tag{3.19}
\]
There is no gain even though the return error is now zero, the residual has every inverse-power bound, and escape holds with the same strength.

This refutes a **uniform strict-modulus-gain supplier on that broader low-energy/quasimode class**. It does not refute a supplier that genuinely uses exact bottom minimality in an additional way. The distinction is essential: I have not proved
\[
\mathfrak k[g_m]-\lambda_m=o(1)
\]
without a lower bound on `lambda_m`, much less exact bottomness. The actual minimum could lie well below these packets.

## 4. The first failed inference and its repair

The attempted chain was:

1. The exact bottom is no higher than a fixed radical trial, so `lambda_m` has a superpolynomially small **upper** bound.
2. Under negation of T the bottom escapes all fixed jets.
3. Try to infer a jump phase-defect margin from low energy plus escape.
4. Use V3 to pay the pole cost and return and contradict minimality.

**Step 3 is false on the proposed low-energy/quasimode surrogate class.** Equations (3.11)–(3.19) are an exact source counterexample family, not merely the high-frequency V6 vector. Nothing in exact minimality by itself repairs the false implication: applied to V2 it gives the opposite inequality (1.5).

**The lawful repair is not to weaken the RH goal.** It is to use a variation that can change amplitude/sign structure **inside the carrier**, avoiding the particular modulus-return obstruction, and to seek a separate source estimate for its gain. The next section does that. It still leaves an arithmetic comparison open.

A related binding shortcut also fails: the positive global radical contains the translated pairs (3.1), and (3.12) returns them to the original carrier at every polynomial accuracy. Therefore a fixed, strictly positive energy separation between the centered radical family and all escaping near-null profiles cannot be obtained at that accuracy. This does not exclude a much smaller, source-specific separation that selects exact minima.

## 5. Exact carrier-preserving competitors

Use the real orthonormal even basis
\[
e_0=\psi_0,\qquad e_i=(\psi_i+\psi_{-i})/\sqrt2,
\quad1\le i\le m.
\]
Let `c=(c_0,...,c_m)` be a real unit even bottom coefficient vector, with eigenvalue `lambda`. Lemma 1 explains why this restriction loses no escaping-bottom contradiction.

### Lemma 7. Coefficient cuts use full minimality and incur no return error

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** For `0<=q<m`, let `S_q` multiply coefficients `0,...,q` by `-1` and leave the remaining coefficients unchanged. Define
\[
\mathcal C_q(c)=\sum_{i=0}^{q}\sum_{j=q+1}^{m}
                         (A_m)_{ij}c_ic_j.                \tag{5.1}
\]
Then
\[
\boxed{
\|S_qc\|=1,\qquad
(S_qc)^TA_m(S_qc)-c^TA_mc=-4\mathcal C_q(c).}             \tag{5.2}
\]
For an exact bottom,
\[
\boxed{\mathcal C_q(c)\le0\quad(0\le q<m).}               \tag{5.3}
\]

**Proof.** The diagonal and within-block products do not change. Each cross-block product changes sign; the symmetric quadratic form counts it twice. This gives (5.2). The sign flip is a unitary operation inside the original even coefficient space, so no projection, normalization correction, endpoint enlargement, or frequency enlargement is involved. Applying the global variational inequality (1.4) gives (5.3). ∎

The physical function can change sign and shape; that is permitted. Both odd pole pairings remain zero by its actual evenness. No hypothesis that a bottom has a particular phase pattern is used.

### Lemma 8. The complete multiplier stability identity

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** For any real multiplier vector `a=(a_i)`, put `y_i=a_i c_i`. The exact eigenrelation gives
\[
\boxed{
 y^T(A_m-\lambda I)y
 =-\sum_{i<j}(A_m)_{ij}c_ic_j(a_i-a_j)^2.}                \tag{5.4}
\]
The right-hand side must be nonnegative for a bottom. The equality alone holds for any eigenvector; the inequality is where **minimality beyond stationarity** enters.

**Proof.** Multiply row `i` of `(A_m-lambda)c=0` by `a_i² c_i` and sum. Subtract the resulting diagonal elimination from the quadratic form in `y`. For each pair `i<j`, the coefficient is
`2a_i a_j-a_i²-a_j²=-(a_i-a_j)²`. ∎

For the step multiplier in Lemma 7 this becomes `-4 C_q`. Full positivity of (5.4), when all `c_i` are nonzero and all multipliers are admitted, is simply another expression of the shifted matrix's positivity. It is **not** offered as a new supplier. The deliberately restricted prefix cuts in (5.3) are only necessary tests, and remain useful because their source expression is explicit and has no return error.

## 6. The exact arithmetic content of a cut

### Lemma 9. Source formula, including all supported prime powers

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** Define
\[
\omega_i=2\pi i/L,\quad d_0=1,\quad d_i=\sqrt2\ (i\ge1),
\]
\[
\kappa=32L\sinh^2(L/4),\qquad
U_i=\frac{d_iL}{L^2+16\pi^2i^2}.
\]
The literal source displacement row is
\[
\beta_i=\frac{\kappa i}{L^2+16\pi^2i^2}
 +\frac1\pi\int_0^L j(s)\sin(\omega_i s)ds
 +\frac1\pi\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}
                         \sin(\omega_i\log n),
\qquad \beta_0=0.                                       \tag{6.1}
\]
For distinct even-basis indices,
\[
(A_m)_{ij}=d_i d_j\frac{i\beta_i-j\beta_j}{i^2-j^2}.
                                                               \tag{6.2}
\]
For a fixed prefix cut set
\[
U_-=\sum_{i\le q}U_ic_i,\qquad U_+=\sum_{j>q}U_jc_j,
\]
\[
\mathcal T_q(s;c)=\sum_{i\le q<j}d_id_jc_ic_j
       \frac{i\sin(\omega_i s)-j\sin(\omega_j s)}{i^2-j^2}.
                                                               \tag{6.3}
\]
Then
\[
\boxed{
\mathcal C_q(c)=\kappa U_-U_+
 +\frac1\pi\int_0^L j(s)\mathcal T_q(s;c)ds
 +\frac1\pi\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}
                         \mathcal T_q(\log n;c).}         \tag{6.4}
\]

**Proof.** The raw entries in [S4] give, for distinct full indices,
`K(i,j)=(beta_i-beta_j)/(i-j)`, with `beta_i=i K(i,0)` and odd `beta`. Reflection into the orthonormal even basis gives, for positive distinct `i,j`,
\[
K(i,j)+K(i,-j)=2\frac{i\beta_i-j\beta_j}{i^2-j^2}.
\]
The central row gives `sqrt(2) beta_j/j`, which is also (6.2). The signs and constants of (6.1) follow directly from `W02-WR-Prime`; the off-diagonal minus signs in `WR` and `Prime` combine with the sine difference as displayed. The same source identity was independently derived in CONFINE (6.2). [S2, §6]

The pole divided difference reduces exactly to
\[
\frac{\kappa}{i^2-j^2}
 \left(\frac{i^2}{L^2+16\pi^2i^2}-
       \frac{j^2}{L^2+16\pi^2j^2}\right)
 =\frac{\kappa L^2}{(L^2+16\pi^2i^2)(L^2+16\pi^2j^2)}.
\]
This gives the first term in (6.4). The other two contributions are linear, giving (6.3).

At zero, `T_q(s)=O(s)`, so the archimedean integral is convergent. At `s=L`, every sine is zero. Thus a prime-power endpoint is retained and contributes zero exactly. Both arguments of the cross form are supported in the same window, so primes beyond `m` vanish by support. The archimedean constant and diagonal tail cancel between the orthogonal coefficient blocks, not from the original source operator. No signed cross term is omitted. ∎

### Lemma 10. Explicit coarse bounds show exactly where absolute estimates lose the sign

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** Put
\[
D_q(c)=\left(\sum_{i\le q}d_i|c_i|\right)
        \left(\sum_{j>q}d_j|c_j|\right),
\]
\[
B_q(c)=\sum_{i\le q<j}\frac{d_id_j|c_ic_j|}{j-i},
\qquad S_m=\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}.
\]
Then
\[
|\mathcal T_q(s;c)|\le B_q(c),\qquad
|\mathcal T_q(s;c)|\le\frac{2\pi s}{L}D_q(c),             \tag{6.5}
\]
\[
\left|\frac1\pi\int_0^L j(s)\mathcal T_q(s;c)ds\right|
 \le\frac{10}{L}D_q(c),
\]
\[
\left|\frac1\pi\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n}
                    \mathcal T_q(\log n;c)\right|
 \le\frac{S_m}{\pi}B_q(c)
 \le\frac{2\sqrt m L}{\pi}B_q(c).                        \tag{6.6}
\]

**Proof.** For the first bound in (6.5), bound the numerator of each divided difference by `i+j`. For the second, the derivative of
`x -> sqrt(x) sin((2 pi s/L) sqrt(x))` has absolute value at most `2 pi s/L`, including its limiting value at zero. The mean value theorem applies at `i²,j²`. The integral uses `int s j(s)ds<5`; the sum uses `Lambda(n)<=log n` and `sum_{n<=m}n^(-1/2)<=2 sqrt(m)`. ∎

In particular, the directly paid lower envelope is only
\[
\mathcal C_q(c)\ge\kappa U_-U_+
           -\frac{10D_q(c)}L-\frac{S_m B_q(c)}\pi.        \tag{6.7}
\]
No positivity of this expression for an escaping bottom has been derived. Neither the pole product nor the oscillatory arithmetic pairing is controlled in the required direction by weak fixed-jet escape. Lemma 6 shows why weak convergence is not a way to discard the prime correlations. The failure of (6.7) to furnish a positive lower bound is a failure of that sufficient envelope, not a claim about the sign of an unevaluated source cut.

## 7. Precise remainder: a source comparison, not assumed descent

For a real number `x` write `x_+=max(x,0)` and `x_-=max(-x,0)`. Define the following nonnegative, source-explicit quantities:
\[
\begin{aligned}
\mathcal P_q(c)={}&\kappa(U_-U_+)_+
 +\frac1\pi\int_0^L j(s)(\mathcal T_q(s;c))_+ds\\
 &+\frac1\pi\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}
                     (\mathcal T_q(\log n;c))_+,          \tag{7.1}
\mathcal N_q(c)={}&\kappa(U_-U_+)_-
 +\frac1\pi\int_0^L j(s)(\mathcal T_q(s;c))_-ds\\
 &+\frac1\pi\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}
                     (\mathcal T_q(\log n;c))_-.          \tag{7.2}
\end{aligned}
\]
These are finite. Equations (6.4) and (5.2) say
\[
\mathcal C_q=\mathcal P_q-\mathcal N_q,
\qquad
\mathfrak k[S_qf]-\lambda=-4(\mathcal P_q-\mathcal N_q).
                                                               \tag{7.3}
\]
Writing (7.3) by itself is **not progress on the sign**. An admissible supplier must produce independent bounds
\[
\mathcal P_q(c_m)\ge\ell_m,
\qquad \mathcal N_q(c_m)\le u_m,
\qquad \ell_m-u_m\ge\eta_m>0,                            \tag{7.4}
\]
for some specified prefix cut, using actual source structure and the hypothetical escape, on at least one sufficiently late cell of that sequence. The margin may shrink with `m`; no positive constant is demanded. Bounds obtained by defining `ell_m=P_q`, `u_m=N_q` and then assuming their separation would not be a supplier.

Here is an explicit **larger test class** on which such an independent source supplier could be sought. It is not defined by global minimality. Fix the centered, cutoff theta trial
\[
 u_m^0=\frac{P_m(\chi(\cdot/b)h)}{\|P_m(\chi(\cdot/b)h)\|},
 \qquad t_m^0=\mathfrak k[u_m^0],
\]
and let
\[
 \mathcal S_m=\{c\in\mathbb R^{m+1}:\|c\|=1,\quad
 A_mc=\theta c\text{ for some }\theta\le t_m^0\}.
                                                               \tag{7.4a}
\]
Every real bottom belongs to this class, by comparison with the explicit trial. The class also permits excited eigenvectors. One strictly sufficient, but not mandatory, source package would give fixed `r, epsilon>0`, a positive budget `eta_m`, and independent bounds (7.4) for some specified cut whenever
\[
 c\in\mathcal S_m,\qquad
 \|P_{J_r}f_c\|\le\epsilon,\qquad m\ge m_0.             \tag{7.4b}
\]
This is a quantitative **cut-instability theorem for all low-energy stationary vectors with the indicated geometry**, not an assumed theorem about compactness of bottoms. Neither (7.4b) nor a weaker sequence-level version has been proved here. In particular, the ground relation and the matrix entries have not yielded a positive `eta_m`. Lemma 13 below shows concretely why this larger-class package is stronger than merely having T.

### Lemma 11. Conditional completion of this variational attempt

**THIS STEP IS PROVED HERE — conditional implication only.**

**[COFINAL_FAMILY | CONDITIONAL]** Suppose an independent source argument establishes (7.4) under negation of T for actual unit bottoms. Then the original carrier contains a unit competitor with
\[
\mathfrak k[S_qf_m]\le\lambda_m-4\eta_m<\lambda_m,         \tag{7.5}
\]
a contradiction. Hence T holds, and the inherited NOESCAPE implication gives RH.

**Proof.** Equation (7.3) gives (7.5). The competitor uses the same `m`, `N=m`, window, raw matrix, norm and parity. It contradicts (1.4). Negation of T has therefore been excluded. The final RH implication is the previously established one, not a new hidden premise. ∎

**The exact first unproved inequality in this repaired route is**
\[
\boxed{\ell_m-u_m>0\quad\text{for the independently bounded
source quantities (7.1)–(7.2), on an escaping exact-bottom sequence}.}
                                                               \tag{7.6}
\]
I have not proved (7.6), or a theorem that escape selects a cut for which it can be proved. The coarse bounds (6.6) do not do so. All claims in (7.4) are **requested estimates**, not admitted assumptions in a completed proof.

### Why this is different from T, and what it buys

T asks for one persistent fixed finite observable of true bottoms. It contains no statement about coefficient signs, prefix cuts, prime sine moments, or the relation between (7.1) and (7.2). This route restricts the competitor to a specified, norm-preserving finite family. Proving a source estimate on a larger independently described low-energy/stationary class that forces (7.4) would be a **stronger and more specialized mechanism**, not a converse of T. Other transformations might prove T while all of these cuts remain unhelpful.

The gain over V3 is specific: **the Fourier-return error is identically absent**. The diagonal cancellations are exact. There is also no comparison of two nearly equal eigenvalues. The remaining arithmetic is not gone: it is the signed oscillatory correlation (6.3) sampled at every actual prime power and integrated against the exact archimedean kernel. The absence of a one-sided estimate for that expression is the obstacle. Minimality gives the inequality (5.3); it does not evaluate the source sums in the contradictory direction.

Thus (7.6) is the sharpest specific unpaid estimate obtained in this batch, not an alleged proof of it. The construction in §3 additionally shows why returning to a universal low-energy modulus assertion cannot supply that missing step.

## 8. Adversarial controls and proof checks

### Lemma 12. Stationarity and genuine bottom stability are distinguished by the cut test

**THIS STEP IS PROVED HERE.**

**[ABSTRACT | PAPER]** Consider
\[
B=\begin{pmatrix}2&-1\\-1&2\end{pmatrix}.
\]
For `c_+=(1,1)/sqrt(2)`, the eigenvalue is `1`, the cut pairing is `-1/2`, and the sign-flip energy change is `+2`. For the stationary but nonbottom vector `c_-=(1,-1)/sqrt(2)`, the eigenvalue is `3`, the pairing is `+1/2`, and the change is `-2`.

Replacing `B` by `B-5I` changes the bottom eigenvalue to `-4` but leaves both cut calculations unchanged. Therefore satisfying the cut stability test is not a positivity certificate.

**Proof.** Direct multiplication gives the stated eigenpairs and values of (5.1)–(5.2). ∎

### Lemma 13. Dense fixed quasimodes plus exact escaping minima do not imply no escape abstractly

**THIS STEP IS PROVED HERE.**

**[ABSTRACT | PAPER]** On `span{e_0,...,e_m}` take
\[
B_m=-|e_m\rangle\langle e_m|.
                                                               \tag{8.1}
\]
Every fixed coordinate vector is eventually an exact zero mode; the exact unique bottom is `e_m`, with energy `-1`, and it escapes every fixed finite coordinate span. Every diagonal sign cut leaves its energy unchanged.

**Proof.** All statements follow from the displayed diagonal spectrum. ∎

This is not a CCM counterexample. It verifies that the proposed logic does not promote quasimode abundance, stationarity, or cut stability into T. The actual-source sequence of §3 is a different, stronger test of the modulus surrogate, but likewise is not asserted to be the actual bottom sequence.

The distinction between T and the larger-class source package (7.4a)–(7.4b) also has an exact control. Replace (8.1) by
\[
 \widetilde B_m=-2|e_0\rangle\langle e_0|-|e_m\rangle\langle e_m|,
 \qquad m\ge2.                                         \tag{8.2}
\]
The bottom is the fixed vector `e_0`, so its no-escape statement holds. The explicit trial `e_1` has energy zero. Nevertheless `e_m` is an escaping stationary vector below that trial energy, and every coefficient sign cut leaves its energy unchanged. Thus no-escape of bottoms does not, by generic variational logic, imply a strict cut-instability theorem for all stationary vectors below an explicit trial. A literal-source proof of that stronger theorem would require its own arithmetic content; no such proof is assumed here.

### Exact controls executed

A small SymPy script checked, with symbolic or rational entries only:

- reflection of a five-mode displacement matrix into the three-dimensional even block, including the central `sqrt(2)` factors in (6.2);
- the coefficient-cut identity (5.2);
- the multiplier identity (5.4) on a symbolically exact eigenrelation;
- the four bottom/excited and shifted/unshifted cases of Lemma 12.

Every assertion passed. No literal CCM eigenproblem, broad scan, interval computation, or Lean invocation was run. These checks validate algebraic factors only; the cofinal estimates in §3 are the written PAPER argument, not a numerical certificate. The formatted script in Appendix A was also executed successfully; it records the exact structural controls, not an analytic verification of the source estimates.

## 9. Dependency epistemics and route choice

**DOWNSTREAM_CONSUMER:** fixed-jet no escape T, then the inherited implication T ⇒ RH.

**ACTUAL_CONSUMER_REQUIREMENT:** a single fixed finite jet with a strictly positive overlap on an unbounded original sequence. Neither a full limiting ladder nor global entropy tightness is required.

**ORIGINAL_REQUESTED_OBJECT:** a strict same-carrier energy-lowering competitor derived from hypothetical escape and exact bottom minimality.

**ORIGINAL_OBJECT_IS:** UNKNOWN as a necessary proof interface; it is sufficient for the requested contradiction. A particular modulus or sign-cut competitor is not asserted necessary.

**KNOWN_WEAKER/ALTERNATIVE INTERFACES:** the inherited one nonzero weak fingerprint would suffice for T, but is not assumed or substituted for the requested variational proof. Exact source-cut budgets (7.4) supply a different sufficient mechanism with a completely paid carrier return.

**FAILURE_TYPE:** NO_DERIVATION for the strict source comparison; exact countertest for a broader modulus supplier that omits true bottom information.

**EPISTEMIC_STATUS:** UNRESOLVED for T and RH. No route-family death is claimed. The absence of a source sign proof is not a proof of impossibility.

**NOVELTY_AXIS:** an original-carrier nonnegative escaping quasimode family, followed by a return-free finite variational test.

**REOPEN TRIGGER:** a new estimate separating (7.1) from (7.2) on an independently specified source class, or a different exact-carrier transformation with a complete, positive source gain. Another residual norm, another smooth trial near zero, or another finite overlap table does not meet this trigger.

### Two candidate re-representations

| Candidate | New object / decisive test | Estimated kill-power / cost | Main risk |
|---|---|---|---|
| A — selected here | Signed coefficient-cut graph; independently compare (7.1) and (7.2) | High if a source sign is found / low algebraic cost, high analytic cost | Escape need not force a cut instability; source sine moments retain the arithmetic |
| B — retained, not escalated | Keep the **signed** modulus return `R`, rather than the absolute budget `E`, and compare actual source pieces | High for that transformation / medium algebraic cost, high analytic cost | Nonnegative escape in §3 is completely invisible to modulus; a separate bottom-specific exclusion is indispensable |

Three bridges were tested at the level relevant to the request. Dirichlet/Perron modulus contraction is blocked by V4–V5 and now by the low-energy fixed points in §3. Concentration-compactness through a fixed binding margin is blocked by translated source near-null packets, not by a lack of terminology. Finite signed-graph stability supplies the exact carrier-preserving test in §§5–7, but no cofinal arithmetic separation. None is imported as a theorem proving T.

### Zero-consistent discriminator

For a proposed cut certificate, the discriminator is a certified **strict lower envelope** for `C_q`, obtained from independent bounds on (7.1)–(7.2). Equivalently the competitor must have a strict **negative upper envelope** for its energy difference in (5.2). A zero-containing enclosure is inconclusive. Exact equality (3.19) is instead a complete no-gain result for the specified trial family and specified transformation.

No claimed positivity/refutation is inferred from the failure of a sufficient bound.

## 10. Predictions and closeout

There were no new numerical predictions in the authoritative VARIATIONAL TXT. The checks registered in this run were confined to the chosen constructions: test whether a nonnegative escaping source quasimode can survive the literal return, and test whether coefficient cuts avoid a return error. Both survived the explicit proofs and exact algebra controls. No forecast of T or RH was registered and retroactively scored as a success. The source construction and the cofinal analytic estimates have not received an independent review in this batch.

**What became more precise:** the missing use of exact minimality cannot be replaced even by all polynomial orders of quasimode accuracy, nonnegativity, and exact carrier membership. A second transformation now has no Fourier-return debt at all.

**What was ruled out:** a uniform strict-modulus-gain inference from that enlarged low-energy/escape class. Not the bottom-specific estimate, not all variational arguments, not T, and not RH.

**What remains:** a source-specific signed binding estimate such as (7.4), or a genuinely different transformation with a paid gain. No actual bottom competitor was produced.

**What must not be repeated:** treating quadratic prime correlations as compact observables; treating `A_m f_m=lambda_m f_m` as full minimality; importing a positive-semigroup modulus inequality for the full signed Weil form; treating an all-orders residual as a discriminator for an exact bottom.

```yaml
iteration:
  target: VARIATIONAL_NOESCAPE_ON_LITERAL_EVEN_BOTTOMS
  status: OPEN
  failed_strategy: LOW_ENERGY_PLUS_ESCAPE_FORCES_STRICT_MODULUS_GAIN
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: EXACT_MINIMALITY_IS_STRONGER_THAN_EVERY_FIXED_POLYNOMIAL_QUASIMODE_ACCURACY
  current_source_remainder: INDEPENDENT_POSITIVE_CROSS_CUT_BUDGET
  forbidden_future_move: REPLACE_BOTTOM_SELECTION_BY_LOW_ENERGY_OR_WEAK_CORRELATION_VANISHING
  next_decisive_test: INDEPENDENT_AUDIT_OF_THE_ACTUAL_SOURCE_POSITIVE_ESCAPING_QUASIMODES
```

## 11. Proshka's own line

The useful distinction is now between an exact minimum and an excellent near-null vector.
The new construction makes that distinction on the real source, not on a substitute matrix.
A positive packet can move away from the centre while remaining near-null to every polynomial order.
That is why a small energy cannot serve as a hidden confinement theorem.
The source's global translation symmetry is doing real work here.
The finite window breaks it, but the resulting preference is not supplied by the rough error budget.
I chose coefficient cuts because they remove the Fourier-return obstacle completely.
They are not a claim that Fourier coordinates are the preferred physical geometry.
They are an admissible finite variational operation whose energy difference is exact.
The nearest alternative was another bound on the modulus projection error.
That would not touch the positive escaping fixed points of the modulus map.
The other alternative was to demand compactness of all the bottoms.
That would replace the task by a stronger premise without proving the source mechanism.
The first next mathematical move would be a signed source comparison for a selected cut.
It would fail if escaping low-energy stationary profiles can remain stable under every selected cut.
The second would be a signed, rather than absolute, treatment of the modulus return.
It would still need an independent treatment of nonnegative spatial escape.
The data I would ask for are not another small-cell overlap number.
I would ask for a source-derived sign relation linking the prime sine moments to a coefficient cut.
That relation must survive the exact scalar and phase conventions in (6.1).
The most important surprise is that positivity of a trial and escape are compatible here at arbitrarily high polynomial accuracy.
What I distrust is any attempt to spend that accuracy as bottom identification.
The RH implication is not the obstruction to proceeding.
The obstruction is the still-unproved strict inequality for a fully specified admissible variation.
A proof of that inequality would be a genuine step to the owner's goal.
Until it is proved, the variational contradiction is incomplete for a concrete mathematical reason.

## 12. Research log and source register

**[S0 — READ, authoritative attachment]** `PROSHKA_REQUEST_VARIATIONAL_2026-10-30.txt`, 11,328 bytes, 219 LF-terminated lines, SHA-256 `d2e14cbbc2e0827b6bf4867c010337e3adb10c5ba1943de85a6bf3b033af4c1f`. Entire text read. It selects the sole task, fixes the source pin and supplies V1–V6. Its processing/review reports are accepted as reports, not claimed as newly replayed here.

**[S1 — READ, protocol]** `Malaeu/chen_q3`, `rh_clean`, `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, Git blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Bootstrap and remainder read through the connector. Used for scope, envelope direction, source lock and verdict format.

**[S2 — READ, pinned mathematical source]** At `805ed24718155280ef563316ea5798d354b35cc7`, `docs/routeB_bus/proshka/PROSHKA_VERDICT_CONFINE_2026-10-30.md`, Git blob `1879347b72d1aa55cf506f5387de37059f929122`, SHA-256 `57088a914942b0dd1c3d1835edaca2f223a59831d78350c0a092356024852ddb`. Re-read §1, §3, and §6 via the connector; the mounted copy has the same computed Git blob and SHA-256. Used for the literal form, theta radical, mixed projection/tail estimates and displacement row. The extension to moving translates and positivity repair is proved here, not relayed from that file.

**[S3 — READ, pinned downstream bridge]** Same pin, `docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md`, Git blob `453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc`, SHA-256 `fdfd384345b69d7565100b93ef57348eb6944bdbaf014a01c001df007129aded`. Re-read L5–L6; mounted hashes match. Used only for T ⇒ RH and the distinction from its unproved converse. No blind-tail estimate is assumed.

**[S4 — READ, pinned entry constructor]** Same pin, `docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py`, lines 1–40, Git blob `5cbd156db9be84caa938cdbabd4e9ec0b5a6d2f3`. Read as a source-entry transcription, not run as a certificate. It retains the literal pole, archimedean diagonal, off-diagonal sine moments and all prime powers.

**[P1 — READ, primary external cross-check]** Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv `2511.22755v1`, HTML version, Lemma 2.2, Lemma 2.3 and equations (3.10), (3.13)–(3.20). Cross-check of translation invariance, the zero-extended Fourier carrier and source-form conventions. No PDF was analyzed in this batch, and no theorem in the primary paper is asserted to prove the new no-escape target.

**[RELAY, not used as mathematical premises]** The attachment's new global-LSI rejection, m16 identity-derived exterior ratio, independent-review statuses and incomplete direct-X certificate. Their status is preserved; their proofs were not independently rerun here.

### Abandoned or incomplete branches

- **Modulus plus better generic residual:** strict gain fails identically on (3.11)–(3.19), despite the strongest polynomial-scale quasimode bounds.
- **Weak escape kills prime correlations:** contradicted by the exact autocorrelation limit (3.18).
- **Fixed positive energy-at-infinity gap:** cannot be obtained from the rough near-null comparison, because the source admits the moving packets (3.1) and their return (3.12).
- **Stationarity as stability:** the excited eigenvector in Lemma 12 has a strict cut descent; the eigenrelation alone does not prohibit it.
- **Absolute cut bounds as a sign supplier:** (6.7) is paid but its required positivity is not. It is not treated as a lower-sign proof.
- **Cut stability as positivity:** `B-5I` in Lemma 12 has a strictly negative bottom while passing its bottom cut tests.

### Reusable exact results

The uniform moving-translate return (3.9)–(3.16); the zero-mode positivity repair; the autocorrelation limit (3.18); the norm-preserving cut identity (5.2); the multiplier stability identity (5.4); and the complete source cut kernel (6.3)–(6.4).

## 13. One next directive

**CODEX DIRECTIVE — one read-only PAPER audit of Lemmas 3–6.**

Audit the theorem that the literal even carrier contains nonnegative unit vectors `g_m` with both `||A_m g_m||` and every fixed-jet projection bounded by `O_{r,A}(m^{-A})` for each fixed `A`. Use the pinned source form and verify the growing shift `a_m=L/8`, the constants in the Fourier and endpoint estimates, the full infinite exterior-prime sum, the exact zero-mode positivity repair, and the polynomial matrix-norm budget. Then verify the nonvanishing fixed-shift autocorrelation limit.

Return either `POSITIVE_ESCAPING_LITERAL_QUASIMODES_CONFIRMED_PAPER` or the first invalid estimate with its repaired statement. Do not call these vectors exact bottoms or certify T from this audit. No Lean, repository edit, m16 F/X rerun, or numerical range scan is requested.

This audit establishes the scope of the new obstruction before it is used to reject a proposed low-energy modulus supplier. It does not replace the still-required source sign argument (7.6).

## Appendix A. Exact algebra control script

```python
import sympy as s

A0, A1, A2, b1, b2 = s.symbols('A0 A1 A2 b1 b2', real=True)
modes = [-2, -1, 0, 1, 2]
a = {0: A0, 1: A1, 2: A2, -1: A1, -2: A2}
b = {0: s.Integer(0), 1: b1, 2: b2, -1: -b1, -2: -b2}
K = s.Matrix([
    [a[i] if i == j else (b[i] - b[j]) / s.Integer(i - j)
     for j in modes] for i in modes
])
E = s.zeros(5, 3)
E[2, 0] = 1
for n in (1, 2):
    E[2 + n, n] = E[2 - n, n] = 1 / s.sqrt(2)
A = s.simplify(E.T * K * E)
d = [1, s.sqrt(2), s.sqrt(2)]
z = [0, b1, 2 * b2]
for i in range(3):
    for j in range(i + 1, 3):
        assert s.simplify(
            A[i, j] - d[i] * d[j] * (z[i] - z[j]) /
            s.Integer(i * i - j * j)
        ) == 0
c = s.Matrix(s.symbols('c0:3', real=True))
mask = s.diag(-1, -1, 1)
C = sum(A[i, 2] * c[i] * c[2] for i in (0, 1))
assert s.simplify(
    ((mask * c).T * A * (mask * c) - c.T * A * c)[0] + 4 * C
) == 0

# An exactly stationary vector, constructed rationally; no bottom claim.
v = s.Matrix([s.Rational(2), s.Rational(-3), s.Rational(5)])
lam = s.Rational(-2)
B = s.Matrix([
    [0, s.Rational(2, 3), s.Rational(-4, 5)],
    [s.Rational(2, 3), 0, s.Rational(3, 7)],
    [s.Rational(-4, 5), s.Rational(3, 7), 0],
])
for i in range(3):
    B[i, i] = lam - sum(B[i, j] * v[j]
                        for j in range(3) if j != i) / v[i]
t = s.symbols('t0:3', real=True)
y = s.diag(*t) * v
left = (y.T * (B - lam * s.eye(3)) * y)[0]
right = -sum(B[i, j] * v[i] * v[j] * (t[i] - t[j]) ** 2
             for i in range(3) for j in range(i + 1, 3))
assert s.simplify(left - right) == 0

base = s.Matrix([[2, -1], [-1, 2]])
for shift in (0, -5):
    for v, value in (
        (s.Matrix([1, 1]) / s.sqrt(2), 1 + shift),
        (s.Matrix([1, -1]) / s.sqrt(2), 3 + shift),
    ):
        matrix = base + shift * s.eye(2)
        reflected = s.diag(-1, 1) * v
        difference = s.simplify(
            (reflected.T * matrix * reflected)[0] - value
        )
        print(shift, value, difference)
print('Exact structural controls passed; no literal CCM numeric scan.')
```

**Final boundary:** the requested variational proof of T is incomplete at the explicit source comparison (7.6). The full RH goal is retained. Neither the source countertest to the modulus surrogate nor the absence of a paid cut comparison is a refutation of T, RH, or the larger variational program.
