# STATUS: TRY_DIAGONAL_CORRELATED_SOURCE_COMPARISON

```yaml
OPERATIVE_CLASS: TRY_DIAGONAL_CORRELATED_SOURCE_COMPARISON
REQUEST_ID: REQ-2026-10-30-DIAGONAL
BOUNDARY_ID: GOAL058_FIXED_JET_NO_ESCAPE_ON_LITERAL_CCM_BOTTOMS
SOURCE_BASE_COMMIT: 4c32496c04bd591d22974cf52dd0c74d4cca10c3
REQUEST_SHA256: 7938daaaa4a0aa8e79bf4eb8113abc3df7eea5d47f37ec33947bcf0604bda4d8
REQUEST_GIT_BLOB_COMPUTED: ac5f4412be543d57bfde0598c8b4001af2120ce4
REQUEST_BYTES: 6683
REQUEST_LINES: 109
REQUEST_FINAL_LF: true
REQUEST_HASH_CHECK: MATCH
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
ACTUAL_DIAGONAL_IDENTITY: CONFIRMED
NEW_SOURCE_BOUND: STRICT_CORRELATED_SECOND_DIFFERENCE_DISK
NEW_VARIATION: COORDINATE_PLUS_RESOLVENT_WITH_FULL_DIAGONAL
ESCAPE_USED: CENTERED_LAPLACE_RESOLVENT_MOMENTS_VANISH
STRICT_GAIN_ON_LITERAL_ESCAPING_BOTTOM: NOT_PROVED
SOURCE_CLASS_CONTROL: POSITIVE_RECIPROCAL_ATOMS_CAN_CREATE_EXACT_ESCAPING_BOTTOMS
CONTROL_IS_LITERAL_CCM: false
CONTROL_PRESERVES_THETA_RADICALITY: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ADDITIONAL_PROGRESS_SCOPE: SOURCE_MOMENT_BOUND_AND_SCOPED_COUNTEREXAMPLE_PROVED
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 3
VERIFIER: PAPER
SYMBOLIC_VALIDATION: EXECUTED_EXACTLY
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
LITERAL_CCM_NUMERICAL_SCAN: false
INDEPENDENT_REVIEW_OF_THIS_VERDICT: NOT_PERFORMED
REMOTE_DELIVERY: SEE_ACCOMPANYING_RESPONSE_FOR_ACTUAL_COMMIT_OR_FAILURE
AUTHORIZED_REMOTE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_DIAGONAL_2026-10-30.md
RH_PROVED: false
T_PROVED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 0. Decision and source lock

**No strict competitor for a literal escaping CCM bottom is proved here.** The new diagonal identity is correct. It supplies a genuine, strictly quantified constraint on the *source* sine/cosine moments, proved in Lemma 2. That constraint is not yet a constraint of the required sign on the *signed eigenvector-weighted* moments.

The diagonal is used explicitly in a coordinate-plus-resolvent competitor, rather than canceled through a multiplier identity. Its full normalization and trial corrections are paid in Lemmas 7–8. Complete fixed-jet escape is converted into an exact centered resolvent moment condition in Lemma 6. The unproved transition is from that condition and the actual source eigen-equations to the independent lower/upper bounds in (8.4).

There is also a precise limitation. Positive reciprocal pairs of jumps change the diagonal while leaving every sampled off-diagonal source moment unchanged. A fully specified **nonliteral** positive-source deformation has simple, exact, escaping bottoms and satisfies the whole diagonal/off-diagonal relation and the moment bound. This is not arbitrary diagonal completion. It is also **not** a CCM counterexample: its additional atoms and weights are not the primes, and it destroys the exact theta-radical identity. An argument that uses those additional arithmetic identities is not excluded.

The attached UTF-8 request was read in full and checked locally: 6683 bytes, 109 LF characters, final LF, SHA-256 as above. The current protocol was fetched from `rh_clean`; mathematical reads were pinned to the stated base. The requested own attempt [S2] was read completely. Only the verdict path is authorized for remote delivery. Storage provenance is reported separately from mathematical status.

For the following calculations, the falsifiers registered before exact replay were: incorrect pole cancellation; a missing endpoint cosine; an incorrect sign in the coordinate/resolvent mixed entry; and a synthetic stationary vector on which a purported complete positivity detector falsely passes. No probability forecasts were supplied in this request. No numerical CCM scan was used.

## 1. The actual diagonal, including its analytic extension

### Lemma 1. Full-source diagonal audit

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]**

Fix an integer m>=2, L=log m, omega=2*pi/L, x_i=i^2, d_0=1 and d_i=sqrt(2) for i>0. The even basis is e_0=psi_0 and e_i=(psi_i+psi_-i)/sqrt(2). A denotes the literal even compression, not its bulk or an arbitrary diagonal completion.

Write
\[
 j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad c_n=\frac{\Lambda(n)}{\sqrt n},\quad
 \kappa=32L\sinh^2(L/4),\quad C_L=\gamma+\log(4\pi\tanh(L/2)),
\]
\[
 \beta(t)=\frac{\kappa t}{L^2+16\pi^2t^2}
 +\frac1\pi\int_0^Lj(s)\sin(\omega ts)ds
 +\frac1\pi\sum_{2\le n\le m}c_n\sin(\omega t\log n),
 \qquad F(x)=\sqrt x\,\beta(\sqrt x).
\tag{1.1}
\]
The jump part of F extends analytically across zero; the pole part is the explicit rational function kappa*x/(L^2+16*pi^2*x). In particular, F is not asserted entire: it has the prescribed negative pole.

Let L_F have off-diagonal divided differences and diagonal F'(x_i). Then
\[
 A=D L_F D+\operatorname{diag}(\delta_i),\qquad D=\operatorname{diag}(d_i),
\tag{1.2}
\]
\[
 \delta(t)=-C_L-\int_0^L\left(2j(s)\cos(\omega ts)-\frac1{\sinh s}\right)ds
           -2\sum_{2\le n\le m}c_n\cos(\omega t\log n),\quad \delta_i=\delta(i).
\tag{1.3}
\]

**Proof.** The pole diagonal is exactly the derivative of kappa*t/(L^2+16*pi^2*t^2). For one jump of weight c at a, the raw diagonal is -2c(1-a/L)cos(omega*i*a), whereas its contribution to beta'(i) is 2ca/L*cos(omega*i*a). Their difference is -2c*cos(omega*i*a). The same subtraction inside the archimedean integral gives (1.3), keeping its subtracted diagonal term. Its integrand tends to 1/2 at zero, so it is integrated as one convergent expression.

For i>0, even compression adds beta(i)/i to the raw diagonal and
\[
 2F'(i^2)=\beta'(i)+\beta(i)/i.
\]
At zero, F'(0)=beta'(0). The off-diagonal even entries are d_i*d_j*(F_i-F_j)/(x_i-x_j), directly from the raw sine difference and reflection. These observations prove (1.2). They agree with the exact source definitions [S3] and CCM (2.9)–(2.10), (4.2)–(4.4), Lemma 5.1 [P1]. No eigen-equation or positivity is used. ∎

At n=m, the sine value is zero but its derivative is not. Its contribution to D L_F D is +2c_m on every diagonal and to diag(delta) is -2c_m. Thus its total matrix contribution is zero, as support requires. **Dropping it from only one part is incorrect.** All other supported prime powers remain as well.

## 2. A genuine source inequality, not shifted-minimum stability

### Lemma 2. Correlated moment disk, with a strict explicit margin

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]**

Remove only the explicit pole from beta and denote the result beta_J. Introduce the positive measure
\[
 d\nu(s)=j(s)ds+\sum_{2\le n\le m}c_n\delta_{\log n}(ds),\qquad 0<s\le L.
\]
Its mass at zero is infinite, but all integrals below converge. Define
\[
 D(t)=\delta(t)-\delta(0)=2\int(1-\cos(\omega ts))d\nu(s),
 \qquad \Delta_r^2 a(t)=a(t+r)+a(t-r)-2a(t).
\]
Then D(t)>=0 and, for all real r,t,
\[
 \boxed{[\Delta_r^2\delta(t)]^2+4\pi^2[\Delta_r^2\beta_J(t)]^2\le4D(r)^2.}
\tag{2.1}
\]
For the actual archimedean-plus-prime source and r=t=1 there is the strict bound
\[
 \boxed{4D(1)^2-[\delta(2)+\delta(0)-2\delta(1)]^2
       -4\pi^2[\beta_J(2)-2\beta_J(1)]^2
       \ge\frac{L^2m^{-3/8}}{288}>0.}
\tag{2.2}
\]

**Proof.** The damped measure (1-cos(omega*r*s))*nu is finite, since its density is O(s) at zero. Set
\[
 Z_r(t)=\int e^{i\omega ts}(1-\cos(\omega rs))d\nu(s).
\]
Elementary trigonometry gives
\[
 \Delta_r^2\delta(t)=4\Re Z_r(t),\quad
 \Delta_r^2\beta_J(t)=-\frac2\pi\Im Z_r(t),\quad Z_r(0)=D(r)/2.
\]
The triangle inequality |Z_r(t)|<=Z_r(0) proves (2.1). More generally the matrix (Z_r(t_a-t_b)) is positive semidefinite, by integrating the squared modulus of a finite exponential sum. This is a source-measure fact, not PSD of A or A-lambda.

For the strict bound, put r=t=1. Exactly,
\[
 Z_1(0)^2-|Z_1(1)|^2
 =\iint(1-\cos(\omega(s-u)))(1-\cos(\omega s))(1-\cos(\omega u))d\nu(s)d\nu(u).
\]
Every integrand is nonnegative. Restrict to s in [L/8,L/6] and u in [L/3,3L/8]. The three factors are respectively at least 1/2, 1/4 and 1. Both archimedean densities are at least exp(-3L/16). Each interval has length L/24. Hence the double integral is at least L^2*exp(-3L/8)/4608. The difference on the left of (2.2) is sixteen times that integral. ∎

This is a nontrivial restriction that arbitrary prescribed diagonal slopes and sine data need not satisfy. It has explicit constants and holds for every original m>=2. **It is not the desired eigenvector moment estimate.** In particular, beta_J is not the rational eigenvector quotient U/V. Transferring (2.1) to that quotient without a separate argument would replace a positive measure by signed coefficient weights.

Also delta(0)<0: C_L>0 for m>=2, the integral (exp(s/2)-1)/sinh(s) is positive, and all c_n are nonnegative. A standalone nonnegative-defect claim is already false. Its cancellation with the Loewner part is essential.

## 3. What part of the prime data the diagonal adds

### Lemma 3. Reciprocal splitting and exact invisible-endpoint cancellation

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]**

For a finite jump measure eta on [0,L], let eta^R be its reflection under s->L-s and eta_+=(eta+eta^R)/2, eta_-=(eta-eta^R)/2. At integer modes,
\[
 \beta_\eta(i)=\frac1\pi\int\sin(\omega is)d\eta_-(s),\qquad
 \delta_{\eta,i}=-2\int\cos(\omega is)d\eta_+(s).
\tag{3.1}
\]
The raw jump diagonal is
\[
 K_{\eta}(i,i)=-\int\cos(\omega is)d\eta_+(s)
 -2\int(1/2-s/L)\cos(\omega is)d\eta_-(s).
\tag{3.2}
\]
These equations keep endpoints and use finite measures only; they do not split the divergent archimedean mass without its renormalization.

In particular, add two positive atoms of equal weight w at a and L-a, with 0<a<L. Then
\[
 \Delta\beta(i)=0,\quad \Delta\beta'(i)=2w\cos(\omega ia),\quad
 \Delta\delta_i=-4w\cos(\omega ia),
\]
\[
 \boxed{\Delta A=-2w\operatorname{diag}(\cos(\omega ia))_{i=0}^m.}
\tag{3.3}
\]
All sampled off-diagonal entries are unchanged, but the full diagonal changes. For a single atom at L, the two diagonal changes instead cancel exactly and Delta A=0.

**Proof.** Sine is antisymmetric and cosine symmetric under reflection at the integer frequencies. Split (1-s/L) into 1/2+(1/2-s/L) for (3.2). For (3.3), the two sine values cancel, the two cosine values coincide, and differentiating the sine terms weights them by a and L-a. Their derivative weights add to L. Insert the resulting derivative and delta changes in (1.2), including i=0. For the atom at L, differentiation gives +2w in the Loewner diagonal and the defect gives -2w. ∎

For the actual prime measure the reflected nodes are L-log n=log(m/n). They are not silently replaced by primes. This shows exactly what was absent from multiplier-only tests: the reciprocal-*symmetric* cosine channel, in addition to the sine channel. It does not show that those two channels have a favorable comparison on an escaping eigenprofile.

### Lemma 4. A cofinal exact-minimum control satisfying the whole correlated relation

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER; NONLITERAL CONTROL]**

There exists a family obtained from the original CCM source by adding just four positive jumps per cell, with the same m=N, window, pole and archimedean terms, such that:

* all original sampled off-diagonal entries are unchanged;
* the whole relation (1.1)–(1.3) and the strict source inequality (2.2) remain valid for the enlarged jump measure;
* its ground state is simple, even, negative in energy, and escapes every fixed theta jet.

**This family is not the arithmetic CCM family. It does not retain the global theta-radical identity.** It is a falsifier of a structural inference that uses only the correlated relation, jump positivity, exact minimality and fixed-jet escape.

**Proof.** First, the original full source satisfies
\[
 \|A_m\|\le100m^2\qquad(m\ge3).
\tag{3.4}
\]
Here is a direct budget. For a unit carrier function, its zero-extension translation square is at most s^2*(2*pi*m/L)^2+2s*(2m+1)/L for 0<s<=1. The two boundary strips are included. Since j(s)<=4/(3s) there and int_1^infinity j(s)ds<2, the archimedean form is bounded in modulus by
\[
 c_*+8+(2\pi m/L)^2+3(2m+1)/L,\qquad c_*=\gamma+\log(8\pi)+\pi/2<7.
\]
The prime norm costs at most 4*sqrt(m)*L and both pole norms together at most 2*sqrt(m). Using L>=1, L<=m and pi<4 gives (3.4). This is a coarse bound, not a proposed lower floor.

For m>=16 set w=m^8 and add reciprocal pairs at
\[
 a=L/4,\quad L-a;\qquad b=L/4+L/(4m),\quad L-b.
\]
All four shifts lie in [log 2,L-log 2]. By (3.3), the even matrix becomes A+Q with
\[
 Q_{ii}=-2w\{\cos(\pi i/2)+\cos(\pi i/2+\pi i/(2m))\},\quad Q_{00}=-4w.
\]
If i is not divisible by four, the first cosine is at most zero and Q_ii-Q_00>=2w. If 4 divides i>0, use 1-cos t>=2t^2/pi^2 on [0,pi/2] to get Q_ii-Q_00>=w*i^2/m^2. Thus every other diagonal is separated from Q_00 by at least g=m^6.

For any unit bottom c of A+Q, let p=1-|c_0|^2. Comparing its energy with the central basis vector, and applying (3.4), gives
\[
 -4w+gp-100m^2\le\lambda_{\min}(A+Q)\le-4w+100m^2.
\]
Therefore p<=200m^{-4}, and after an overall sign
\[
 \|c-e_0\|\le20m^{-2},\qquad \lambda_{\min}(A+Q)<0.
\tag{3.5}
\]
The next eigenvalue is at least -4w+g-100m^2, by the elementary min-max bound for a perturbation of a diagonal matrix. Since g>200m^2, the bottom is simple.

In physical space e_0=L^{-1/2}1_{[-L/2,L/2]}. For each fixed derivative h^(2j), its pairing with e_0 is bounded by L^{-1/2}||h^(2j)||_1. The fixed jet Gram matrix is nonsingular. Thus (3.5) implies complete fixed-jet escape of these exact bottoms. Positivity of the added measure preserves (2.2), and no diagonal was completed by solving an eigen-equation. ∎

The four weights m^8 are deliberately nonarithmetic. A proposed proof using the exact weights Lambda(n)/sqrt(n), quantitative prime bounds, or exact theta-radicality may reject this control, and is not refuted. This is a limitation at the stated enlarged-class scope, not impossibility of the literal task.

## 4. The actual stationary restriction is a Hermite condition

### Lemma 5. Division-free source compatibility, including zero coordinates

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]**

For real c, define
\[
 V(z)=\sum_i\frac{d_ic_i}{x_i-z},\quad U(z)=\sum_i\frac{d_iF_ic_i}{x_i-z},\quad
 P(z)=\prod_i(z-x_i),\quad p(z)=P(z)V(z),\quad q(z)=P(z)U(z).
\]
Then p and q have degree at most m, and q(x_i)=F_i p(x_i). Moreover
\[
 Ac=\lambda c\quad\Longleftrightarrow\quad
 d_i^2\{q'(x_i)-F_i p'(x_i)\}-(A_{ii}-\lambda)p(x_i)=0
 \quad\text{for every }i.
\tag{4.1}
\]
Using the *actual* diagonal, this is
\[
 d_i^2(q-Fp)'(x_i)+(\lambda-\delta_i)p(x_i)=0.
\tag{4.2}
\]
Where c_i!=0, H=U/V is regular at x_i and
\[
 H(x_i)=F_i,\qquad H'(x_i)=F'(x_i)+\frac{\delta_i-\lambda}{d_i^2}.
\tag{4.3}
\]
If c_i=0, (4.1), not a divided slope formula, is retained.

**Proof.** The residues give p(x_i)=-d_i*c_i*P'(x_i). Write U_i,V_i for the regular parts of U,V at x_i. Then
\[
 q'(x_i)-F_i p'(x_i)=P'(x_i)(U_i-F_iV_i)
 =P'(x_i)\sum_{j\ne i}\frac{(F_i-F_j)d_jc_j}{x_i-x_j}.
\]
The left side of (4.1) is therefore d_i*P'(x_i)*((A-lambda)c)_i. That factor is nonzero. This proves both directions, including zero coordinates. Equation (4.2) follows from (1.2), and (4.3) by division only when p(x_i)!=0. ∎

For a trial rho=c^T A c and r=(A-rho)c, the defect in (4.1) is exactly d_i*P'(x_i)*r_i. **This is stationarity, not minimality.** It is useful for checking candidate interpolation arguments, but no root-separation or positive-measure representation for H is imported from it. Full positivity of its complete rational Gram would be the already identified congruence, not a new supplier.

## 5. What escape actually says about rational moments

### Lemma 6. Centered Laplace moments, with the correct phase and scale

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER, using the accepted jet-density lemma]**

For alpha>0 put z_m=-(alpha*L/(2*pi))^2 and
\[
 V_{\rm ctr}(z)=\sum_i\frac{(-1)^i d_i c_i}{x_i-z}.
\]
For the literal synthesized real even f_c,
\[
 \boxed{\langle e^{-\alpha|x|},f_c\rangle
 =\frac{\alpha L^{3/2}}{2\pi^2}
       \{V_{\rm ctr}(z_m)-m^{-\alpha/2}V(z_m)\}.}
\tag{5.1}
\]
Complete fixed-jet escape consequently implies
\[
 \boxed{L^{3/2}V_{\rm ctr}(z_m)\longrightarrow0\quad\text{for every fixed }\alpha>0.}
\tag{5.2}
\]
No decay rate follows from qualitative escape alone.

**Proof.** Direct integration gives
\[
 \int_{-L/2}^{L/2}e^{-\alpha|x|}\cos(\omega_i x)dx
 =\frac{2\alpha(1-(-1)^i e^{-\alpha L/2})}{\alpha^2+\omega_i^2}.
\]
The physical even basis contains the phase (-1)^i, giving (5.1), including i=0. If Q=alpha*L/(2*pi), Cauchy–Schwarz and a decreasing-integral bound give
\[
 |V(-Q^2)|\le\left(Q^{-4}+\frac{\pi}{2Q^3}\right)^{1/2}.
\]
Thus L^{3/2}m^{-alpha/2}V(z_m)->0 for every alpha>0.

By the density of the fixed even theta derivatives [S5], complete jet escape of unit vectors implies weak convergence to zero in physical L². Apply it to the fixed function exp(-alpha*|x|). Equations (5.1) and the preceding bound prove (5.2). ∎

The centered moment has an alternating phase. The U,V in the boundary displacement formula do not. Dropping that phase would turn a fixed central observation into a moving boundary observation. **Neither a sign for U nor a lower bound on |F_i V-U| follows from (5.2).** This is the specific point at which escape has been used, rather than being attached to an unchanged stability identity.

## 6. A variation that actually retains the diagonal

### Lemma 7. Coordinate-plus-resolvent descent certificate

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]**

Let c be a real unit exact eigenvector, Ac=lambda*c. Choose any coordinate k and any real z off the nodes. No nonzero-coordinate assumption is imposed. Put y=R_z c and
\[
 a=A_{kk}-\lambda=d_k^2F'(x_k)+\delta_k-\lambda,
\]
\[
 b=\frac{d_k}{x_k-z}(F_kV(z)-U(z)),\qquad
 q_0=V(z)U'(z)-U(z)V'(z).
\tag{6.1}
\]
Then the shifted-energy Gram on (e_k,y) is exactly
\[
 \begin{pmatrix}a&b\\b&q_0\end{pmatrix}.
\]
If a>0 and a*q_0-b^2<0, the explicitly normalized same-cell competitor is
\[
 w=b e_k-aR_zc,\qquad g=\frac{f_w}{\|w\|},\qquad
 \boxed{\mathfrak k[g]-\lambda
       =\frac{a(aq_0-b^2)}{\|w\|^2}<0.}
\tag{6.2}
\]
If a<0, e_k itself is a strict competitor. If a=0 and b!=0, y-t*sgn(b)*e_k has negative shifted energy for t>(max(q_0,0))/(2|b|). If a=b=0, this plane gives descent precisely when q_0<0.

**Proof.** The displacement identity gives
\[
 (A-\lambda)R_zc=R_z(uV(z)-vU(z)),\quad u_i=d_iF_i,\ v_i=d_i.
\]
Its k-th entry is b. Pairing with y gives q_0. The other diagonal is the actual A_kk-lambda. Evaluating the quadratic form on (b,-a) gives a*(a*q_0-b^2). A negative numerator proves w!=0, so normalization is legitimate. The other cases follow by evaluating the indicated two-dimensional quadratic. ∎

**Here exact minimality is used:** for a true bottom, every such shifted Gram must be PSD. A source proof of the opposite strict sign from escape would contradict minimality. The identity itself holds for every eigenvector and is not such a proof. Unlike a multiplier-only family, e_k also probes a coordinate outside supp(c); this does not dispense with any other off-support Schur couplings.

### Lemma 8. Complete trial correction and an independently payable source budget

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER / CONDITIONAL for the final sign certificate]**

For any real unit trial c, put rho=c^T A c, r=(A-rho)c, epsilon=||r|| and eta=min_i|x_i-z|>0. Compute a=A_kk-rho and b_0,q_0 from (6.1), replacing lambda by rho only in a. The actual mixed and resolvent entries are
\[
 b=b_0+\frac{r_k}{x_k-z},\qquad
 q=q_0+\sum_i\frac{c_i r_i}{(x_i-z)^2},
\]
\[
 |b-b_0|\le\epsilon/\eta,\qquad |q-q_0|\le\epsilon/\eta^2.
\tag{6.3}
\]
Suppose independently established source enclosures give
\[
 0<a\le A^+,\qquad |b_0|\ge B^-,\qquad q_0\le Q^+.
\]
Set B_*=B^--epsilon/eta and Q_*=max(0,Q^++epsilon/eta^2). If
\[
 \boxed{B_*>0,\qquad B_*^2>A^+Q_*,}
\tag{6.4}
\]
then the actual Gram determinant is strictly negative and (6.2), using actual a,b,y, gives a strict normalized competitor. Exact eigenvectors have epsilon=0.

**Proof.** Add R_z r to the displayed displacement equation. The mixed correction follows immediately; the diagonal correction follows by pairing with R_zc. Cauchy–Schwarz bounds sum |c_i*r_i| by epsilon. Therefore a*q-b^2<=A^+Q_*-B_*^2<0, with the max ensuring that multiplying upper bounds does not reverse the sign. Lemma 7 supplies the competitor. ∎

All three quantities to be enclosed are explicit source objects:
\[
 a=d_k^2F'(x_k)+\delta_k-\rho,
\]
\[
 b_0=\frac{d_k}{x_k-z}\sum_i\frac{d_i c_i(F_k-F_i)}{x_i-z},
 \qquad q_0=VU'-UV'.
\tag{6.5}
\]
There is no difference of close eigenvalues in (6.5), but there can still be cancellation inside the source sums. That cancellation is not presumed favorable.

A completely paid but coarse upper bound is a<=2M_m, with M_m=100m² for m>=3. Similarly
\[
 q_0\le\frac{2\|u\|\|v\|}{\eta^3}.
\tag{6.6}
\]
The latter follows by bounding V,U,V',U' separately. These estimates provide **no positive lower bound B^-**; using B^-=0 cannot pass (6.4). Sharper signed primitive bounds may replace (6.6), but are not claimed obtained.

For actual primitive evaluation, the pole part is rational, the prime sums are finite with every power retained, and the two archimedean integrands in (1.1),(1.3) are integrated in their paired nonsingular forms. In particular the diagonal integrand is not split into divergent terms. Numerical enclosures must carry their quadrature and input errors into A^+,B^-,Q^+. No such literal-source certificate has been executed here.

### Lemma 9. Exact negative control and the flat-trial test

**THIS STEP IS PROVED HERE. [ABSTRACT / FINITE_CELL | PAPER]**

On the supplied synthetic control [S2], with its unnormalized c, choose k=0 and z=-1. Exact algebra gives
\[
 a=2,\quad b=3/100,\quad q_0=1/2500,\quad aq_0-b^2=-1/10000.
\]
The witness in Lemma 7 has squared norm 391/33750 and energy -1/5000, hence
\[
 \boxed{\text{Rayleigh}(w)=-27/1564<0.}
\tag{6.7}
\]
Scaling c to unit norm leaves the normalized competitor unchanged. Thus the mixed test rejects this stationary nonminimum even though every single real resolvent in that example has positive shifted energy. This is an exact algebra control, not a literal CCM certificate.

For the accepted BOUNDARY flat escaping trials, let epsilon_m be their residual after subtracting their Rayleigh value. It decreases faster than every inverse power. Formula (6.3) is the full correction: if eta_m>=m^{-p} for a fixed p, both corrections remain superpolynomially small, **only absolutely**. If poles approach nodes faster, that assertion is unavailable.

For any fixed, independently specified finite list of shifts, BOUNDARY's finite-record construction may additionally null U(z),V(z) and any selected derivatives exactly. Then b_0=q_0=0 for those shifts, even though the actual diagonal relation is satisfied. Only the residual terms remain. Such nulling does not cover shifts selected adaptively after seeing the vector, a growing list, or exact minima. No impossibility statement about those alternatives follows.

**Proof.** The rational calculation is reproduced in Appendix A. For the trials, (6.3) and their accepted residual bound prove the cost statement. The source-dependent U,V evaluations are linear functionals, so the finite-record theorem [S4, Lemma 6] applies to a preassigned finite list. It makes neither the trials exact minima nor their residual corrections zero. ∎

## 7. The actual proof attempt and the first failed comparison

The attempted chain is now explicit:

1. Assume complete fixed-jet escape of selected literal even bottoms. A real escaping bottom sequence can be chosen: take the real or imaginary part of larger norm in each cell and renormalize. No simplicity is needed.
2. The exact diagonal enforces (4.1)–(4.3), not an arbitrary completion. The actual sine/cosine data satisfy the strict source moment bound (2.2).
3. Escape gives the centered, correctly scaled condition (5.2).
4. Seek k_m and z_m, and bounds on the primitive expressions (6.5), that satisfy (6.4) with epsilon=0 on one sufficiently late cell. Lemma 7 would then contradict exact minimum stability.

**Step 4 is not proved.** The first missing estimate is the following specific source response separation, not an assumed overlap:
\[
 \boxed{\text{For the actual prime measure and an escaping exact stationary profile,
 construct }k,z\text{ and independently bounded }A^+,B^-,Q^+
 \text{ with }0<a\le A^+,\ |b_0|\ge B^->0,\ q_0\le Q^+,
 \quad (B^-)^2>A^+\max(0,Q^+).}
\tag{7.1}
\]
The estimates must be derived using the actual cosine channel, actual weights and theta identities, together with (5.2); they cannot be defined by assuming the determinant's sign. Bounds (6.6) do not establish the required separation. The positive-measure proof of (2.2) does not transfer to the signed sums in (6.5). The Hermite equations do not make H equal to F off the nodes. These are the exact failures of the attempted shortcut.

This is a **restricted sufficient mechanism**, not a characterization of T. It allows all coordinates without requiring a central mandatory node, and can use a shrinking margin. It may fail because its two-dimensional planes miss a descent, or because its one-sided enclosures lose cancellation. Other competitors, higher-dimensional combinations, or quantitative moment arguments remain open. Even an actual negative determinant may fail conservative bounds: a=q=1,b²=2 gives determinant -1, while the valid upper bounds A^+=Q^+=10 do not certify it.

An independent proof of (7.1) under negation of T would give a same-cell strict competitor, hence T and the accepted implication to RH. **THIS COMPLETION WOULD IMPLY RH.** Neither this implication nor any RH-equivalent lower floor is used to prove (7.1). No such completion is claimed.

The meaningful added source information to use next is the **actual reciprocal-symmetric prime/cosine data constrained simultaneously by exact theta radicality**. The old multiplier drift sees only sine data after the diagonal is eliminated. Lemma 4 demonstrates why that missing cosine channel cannot be replaced by arbitrary positive source mass; it also explicitly leaves theta-based arguments untouched.

## 8. Consumer contract, alternatives, and closeout

**DOWNSTREAM_CONSUMER:** fixed-jet NOESCAPE T, then the accepted T=>RH implication. The old selected-Ferrers G1/G3 chain is not promoted.

**ACTUAL_CONSUMER_REQUIREMENT:** one nonzero fixed finite observable retained on an unbounded original family, or a valid contradiction to complete escape of exact selected bottoms.

**ORIGINAL_REQUESTED_OBJECT:** source-derived strict same-cell descent using the correlated diagonal/off-diagonal relation. **ORIGINAL_OBJECT_IS: UNKNOWN** as a necessary interface. The mixed two-dimensional test is only a sufficient implementation.

**KNOWN_WEAKER_INTERFACES:** any independently proved same-carrier negative shifted quadratic, with all errors dominated, suffices. A cofinal vanishing lower floor is another known RH-equivalent entrance, not an assumption here.

**FAILURE_TYPE:** NO_DERIVATION of (7.1). **EPISTEMIC_STATUS:** RESEARCH_DEBT for this attempted comparison, not mathematical death of T. **REOPEN_TRIGGER:** a signed lower bound for the actual mixed source response that survives the residual/input budgets and distinguishes the exact primes from Lemma 4's deformation.

**NOVELTY_AXIS:** correlated source moment disk; reciprocal symmetric diagonal channel; zero-coordinate-safe mixed variation; centered versus endpoint rational observations.

Two alternatives remain:

| Representation | Decisive supplier | Kill-power / cost | Limit |
|---|---|---|---|
| Coordinate plus resolvent | Primitive bounds (7.1) | High / moderate finite algebra, high source-estimate cost | Two-dimensional detection is not declared complete |
| Centered physical Laplace observations | An actual-source eigen-equation comparison between (5.2) and boundary/source response | High / high analytic cost | Escape supplies vanishing, not a rate or sign |

The strict source inequality (2.2) is proved, but it is not a sign of A. The perturbed-source control has a strict negative upper energy bound, but is not literal CCM. The mixed synthetic witness has exact negative energy, but is not a cofinal statement. These three evidence categories are kept separate.

The source-class claim refuted is exactly: “the correlated representation plus positive jump weights, exact minimality and fixed-jet escape are incompatible for every such source.” Its counterexample is Lemma 4; **scope: enlarged source family, PAPER**, not the exact-prime family and not the class additionally satisfying theta radicality. No other theorem shape or route family is declared killed.

Registered control fates: pole/endpoint factors passed; the mixed-entry sign passed; the stationary negative control was rejected by the mixed test. The hoped-for literal escape-to-sign implication was not established. No observer forecast has been retrospectively invented.

**What became smaller:** the missing transfer is between a positive source-measure inequality and a signed, eigenvector-weighted source response, with a concrete diagonal-containing competitor and complete correction. **What must not be repeated:** spending a standalone delta sign; deleting the endpoint cosine; replacing centered moments by boundary moments; or treating complete rational-Gram positivity as a source theorem.

**DISCRIMINATOR for a zero-consistent result:** a strict upper enclosure for a*q-b², with a positive lower enclosure for a and all input/residual errors. A floating determinant compatible with zero earns no sign. If a<=0 is encountered, use the exact branches of Lemma 7 rather than dividing by it.

**Memory:** `DIAGONAL: source moment disk proved with explicit strict margin; reciprocal positive atoms preserve sampled off-diagonals while changing the diagonal. Actual theta/primes remain essential. Mixed coordinate-resolvent descent is exact, but its source separation under centered escape is unpaid.`

## 9. Proshka's own line

The diagonal has not disappeared from the mathematics; it had disappeared from the chosen multiplier test.
The mixed coordinate direction puts it back without enlarging the carrier.
It also avoids assuming that every coefficient of a bottom is nonzero.
The strict moment disk is a real source theorem, with a visible positive margin.
It is not a theorem about the sign of the Weil form.
The distinction between those two statements matters more than the size of that margin.
The source measure is positive; the eigenvector coefficients are signed.
No operation here turns the latter into the former for free.
The reciprocal-pair construction is the strongest control in this batch.
It changes a whole cofinal sequence through an actual positive jump measure, not an arbitrary diagonal recipe.
Its exact bottoms escape, so the structural positivity route must reject it somewhere.
The exact theta-radical identity is one legitimate place to reject it.
The literal prime weights and support are another.
I would first seek a source comparison using both channels at once, rather than a smaller matrix determinant.
The nearest alternative is a centered resolvent equation with controlled transfer to the boundary.
A proof that only sees the antisymmetric sine measure would miss the new diagonal information again.
A proof that only sees positivity of the jump measure would pass the deformation again.
An adaptive choice of shifts may still succeed; no fixed-list control rules it out.
A quantitative growing-moment estimate may also succeed; no such estimate was refuted here.
The source datum I would request is a proposed signed estimate for the mixed response, not another finite spectrum.
Its falsifier should keep the actual diagonal and distinguish an excited state from a bottom.
The next mathematical gain must be that estimate or a different genuine descent, not the name of an interpolation class.

## 10. Research log and delivery boundary

**READ [S0]:** attached `PROSHKA_REQUEST_DIAGONAL_2026-10-30.txt`, all bytes; hash and metadata in the header.

**READ [S1]:** `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` at `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`; intake, proof discipline and delivery requirements.

**READ [S2]:** `docs/routeB_bus/proshka/NOESCAPE_ADAPTIVE_RESOLVENT_ATTEMPT_2026-10-30.md`, full file at the base commit, blob `8716b9a177264a11abfdd080e4e93d12b576bc7e`; exact rational identity, zero-support guard, supplied stationary control, actual diagonal extension. Its floating literal examples remain reported diagnostics, not premises.

**READ [S3]:** `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean`, lines 1–115 at the base, blob `960f1de9d00e9ca4b309a99fe98be48db40cdb31`; literal kernel and all three source contributions. No Lean execution.

**READ [S4]:** `docs/routeB_bus/proshka/PROSHKA_VERDICT_BOUNDARY_2026-10-30.md`, sections 3–4 and 6–7 at the base, blob `60909fcc71d86778404290704cd641223e210467`; accepted flat-trial cost and finite-record scope; reciprocal discrepancy approach not promoted to a sign.

**READ [S5]:** `docs/routeB_bus/proshka/PROSHKA_VERDICT_CONFINE_2026-10-30.md`, section 2 at the base, blob `1879347b72d1aa55cf506f5387de37059f929122`; fixed-jet density used in Lemma 6.

**READ [P1]:** Connes–Consani–Moscovici, `arXiv:2511.22755v1`, primary HTML, equations (2.9)–(2.10), (4.2)–(4.4), Lemmas 5.1–5.2. Only the source form and displacement comparison are used; no new spectral assertion is imported. No PDF was analyzed in this batch.

**Not imported:** the shelf's conditional real-zero theorem as an escape supplier; reported finite pair tests as a cofinal result; any RH-equivalent premise. A direct container raw-download attempt failed DNS resolution; connector reads succeeded. This failure is not evidence about GitHub write permissions.

**Branches restricted:** standalone delta positivity fails at i=0; diagonal-part arguments fail the exact endpoint cancellation; positive source-measure bounds do not control signed eigenvector moments; the Hermite system is stationarity rather than a strict variation; the perturbed positive-source family fails exact theta radicality and cannot refute the literal task.

**Reusable results:** (2.2) gives an explicit three-node source restriction; (3.3) isolates diagonal-only reciprocal perturbations; (4.1) is safe at zero coordinates; (5.1) preserves the central phase; (6.2) and (6.3) give the normalized competitor and its full trial cost.

**One next directive:** seek an independently proved comparison for the *actual reciprocal-symmetric cosine channel and signed sine response* in (6.5), under (4.1) and the centered escape condition (5.2), that pays (7.1) or yields a different same-carrier strict descent. Keep the true prime weights, exact theta identities, zero coordinates and both source endpoints. Return the proved one-sided bounds, or the first failed inequality with its falsifier; do not report complete-Gram congruence as progress. No broad numerical scan or Lean source change is part of this directive.

**Verification boundary:** Appendix A was executed with SymPy and passed exactly. It checks algebra, not analytic cofinal estimates or an interval CCM eigenpair. Lemmas 2, 4 and 6 and the proposed supplier require independent PAPER review. The mathematical verdict remains partial. Remote creation, if successful, writes this verdict only; its actual commit is reported with the download. No axiom profile or kernel-green status is claimed.

## Appendix A. Exact validation code

Execute with a Python environment containing SymPy. It performs no network access and no literal CCM numerical scan. The script's SHA-256 is `ecddacbb8d4cf027b5a97c1a45229e550b8c8b3934a8e4f5cfa1c5448d21110f`.

```python
#!/usr/bin/env python3
"""Exact algebra controls for DIAGONAL; no literal CCM numerical scan."""
import sympy as s

# Pole contribution has zero diagonal defect.
t, L, kap = s.symbols('t L kap', positive=True)
bp = kap*t/(L**2+16*s.pi**2*t**2)
wp = kap*(L**2-16*s.pi**2*t**2)/(L**2+16*s.pi**2*t**2)**2
assert s.simplify(s.diff(bp,t)-wp) == 0

# One jump: full even diagonal equals derivative part plus the cosine defect.
a, w = s.symbols('a w', positive=True)
bj = w/s.pi*s.sin(2*s.pi*t*a/L)
defect = -2*w*s.cos(2*s.pi*t*a/L)
actual_even = -2*w*(1-a/L)*s.cos(2*s.pi*t*a/L) + bj/t
assert s.simplify(s.diff(bj,t)+bj/t+defect-actual_even) == 0
assert s.simplify(s.limit(s.diff(bj,t)+defect,t,0)+2*w*(1-a/L)) == 0

# Reciprocal positive pair: beta values cancel, derivative and defect do not.
for n in range(6):
    theta = s.symbols('theta', real=True)
    cs = s.cos(2*s.pi*n-theta)
    assert s.trigsimp(s.sin(theta)+s.sin(2*s.pi*n-theta)) == 0
    assert s.trigsimp((2*w/L)*(a*s.cos(theta)+(L-a)*cs)-2*w*s.cos(theta)) == 0
    assert s.trigsimp(-2*w*(s.cos(theta)+cs)+4*w*s.cos(theta)) == 0

# Moment-disk identity for a finite positive-atom control (not the CCM measure).
r = s.Integer(1)
ats = [(s.pi/3,s.Integer(2)),(s.pi/2,s.Integer(3))]
beta = lambda x: sum(v*s.sin(x*q)/s.pi for q,v in ats)
delta = lambda x: 2*sum(v*(1-s.cos(x*q)) for q,v in ats)
dd = s.simplify(delta(2)+delta(0)-2*delta(1))
db = s.simplify(beta(2)+beta(0)-2*beta(1))
Z = s.simplify(sum(v*(1-s.cos(q))*(s.cos(q)+s.I*s.sin(q)) for q,v in ats))
Z0 = sum(v*(1-s.cos(q)) for q,v in ats)
assert s.simplify(dd-4*s.re(Z)) == 0
assert s.simplify(db+2*s.im(Z)/s.pi) == 0
assert s.simplify(4*delta(1)**2-dd**2-4*s.pi**2*db**2-16*(Z0**2-s.expand_complex(Z*s.conjugate(Z)))) == 0

# Supplied synthetic stationary control; all calculations are exact.
z = s.symbols('z')
xs = [s.Integer(x) for x in (0,1,4,9)]
ds = [s.Integer(1),s.sqrt(2),s.sqrt(2),s.sqrt(2)]
P = s.prod(z-x for x in xs)
F = z+z/(z*z+1)
fs = [F.subs(z,x) for x in xs]
c = s.Matrix([-(x*x+1)/(d*s.diff(P,z).subs(z,x)) for x,d in zip(xs,ds)])
A = s.zeros(4)
for i in range(4):
    for j in range(4):
        if i != j:
            A[i,j] = ds[i]*ds[j]*(fs[i]-fs[j])/(xs[i]-xs[j])
for i in range(4):
    A[i,i] = -sum(A[i,j]*c[j] for j in range(4) if j != i)/c[i]
assert A*c == s.zeros(4,1)
V = s.factor(sum(ds[i]*c[i]/(xs[i]-z) for i in range(4)))
U = s.factor(sum(ds[i]*fs[i]*c[i]/(xs[i]-z) for i in range(4)))
assert s.factor(U/V-F) == 0
p = s.cancel(P*V); q = s.cancel(P*U)
for i,x in enumerate(xs):
    assert s.simplify(q.subs(z,x)-fs[i]*p.subs(z,x)) == 0
    assert s.simplify(ds[i]**2*(s.diff(q,z).subs(z,x)-fs[i]*s.diff(p,z).subs(z,x))-A[i,i]*p.subs(z,x)) == 0
R = s.diag(*[1/(x+1) for x in xs])
y = R*c; e = s.eye(4)[:,0]
aa = A[0,0]; bb = (A*y)[0]; qq = (y.T*A*y)[0]
assert (aa,bb,qq) == (2,s.Rational(3,100),s.Rational(1,2500))
det = s.factor(aa*qq-bb**2)
assert det == -s.Rational(1,10000)
g0 = bb*e-aa*y
assert s.factor((g0.T*A*g0)[0]) == -s.Rational(1,5000)
assert s.factor((g0.T*g0)[0]) == s.Rational(391,33750)
assert s.factor((g0.T*A*g0)[0]/(g0.T*g0)[0]) == -s.Rational(27,1564)

# Trial corrections checked on an unrelated rational symmetric matrix.
T = s.Matrix([[2,1,-1],[1,-2,3],[-1,3,4]])
ct = s.Matrix([s.Rational(2,3),s.Rational(1,3),s.Rational(2,3)])
assert (ct.T*ct)[0] == 1
rho = (ct.T*T*ct)[0]; residual = T*ct-rho*ct
amp = s.diag(1,s.Rational(-2,3),s.Rational(3,5))
W = -sum(T[i,j]*ct[i]*ct[j]*(amp[i,i]-amp[j,j])**2 for i in range(3) for j in range(i+1,3))
assert s.simplify(((amp*ct).T*(T-rho*s.eye(3))*(amp*ct))[0]-W-sum(amp[i,i]**2*ct[i]*residual[i] for i in range(3))) == 0
print('PASS: pole, jump diagonal, reciprocal pair, moment disk, Hermite, mixed-node negative witness, trial correction')
```

Observed output:

```text
PASS: pole, jump diagonal, reciprocal pair, moment disk, Hermite, mixed-node negative witness, trial correction
```

**Final boundary:** no literal-source strict gain, T, G1a, G3, or RH is claimed proved. The exact CCM family and RH goal are unchanged.
