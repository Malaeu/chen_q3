# STATUS: TRY_LOCALIZE_SELECTED_COMPENSATED_EXTERIOR_RESPONSE
```yaml
OPERATIVE_CLASS: TRY_LOCALIZE_SELECTED_COMPENSATED_EXTERIOR_RESPONSE
REQUEST_ID: LOCALIZE_2026-10-31
BOUNDARY_ID: GOAL058_FIXED_JET_NO_ESCAPE_ON_LITERAL_CCM_BOTTOMS
SOURCE_BASE_COMMIT: 5575dc7b29f4f96c9d9d35e486e3a968cc8556d3
REQUEST_SHA256: f380d5b774022c76814d68c3eb9c3eac3662cd046aee5dc72caba5afafb4fb79
REQUEST_GIT_BLOB_COMPUTED: 05d1b1d5e1ca2c62fa280fd5c0d5b69d91045bef
REQUEST_BYTES: 5828
REQUEST_LINES: 98
REQUEST_FINAL_LF: true
REQUEST_HASH_CHECK: MATCH
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
NEW_SOURCE_BUDGET: NARROW_EDGE_RETURN_PLUS_COMPENSATED_FAR_COUPLING_WITH_UNIFORM_NEAR_COST
NEW_LITERAL_CONTROL: SPATIALLY_TIGHT_OSCILLATORY_RADICAL_QUASIMODES
CONTROL_RESIDUAL: SMALLER_THAN_EVERY_FIXED_INVERSE_POWER_ON_ORIGINAL_SCHEDULE
CONTROL_FIXED_JET_OVERLAP: SMALLER_THAN_EVERY_FIXED_INVERSE_POWER
CONTROL_UPPER_FOURIER_EDGE: SMALLER_THAN_EVERY_FIXED_INVERSE_POWER
CONTROL_PROJECTION_SOURCE_COST: SMALLER_THAN_EVERY_FIXED_INVERSE_POWER
CONTROL_LOCAL_ARCH_ENERGY: TENDS_TO_INFINITY
CONTROL_JOINT_EXPRESSION_STAR: TENDS_TO_PLUS_INFINITY
CONTROL_COMPENSATED_FAR_SOURCE_PAIRING: TENDS_TO_PLUS_INFINITY
CONTROL_IS_LITERAL_CCM: true
CONTROL_IS_EXACT_BOTTOM: NOT_ASSERTED
SELECTED_BOTTOM_UNIFORM_LOCAL_REGULARITY: NOT_PROVED_OR_REFUTED
STRICT_SAME_CARRIER_DESCENT: NOT_PROVED
PROGRESS_CLASS: FALSIFICATION_PROGRESS
ADDITIONAL_PROGRESS: SOURCE_BUDGET_AND_COFINAL_CONTROL_PROVED
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4
VERIFIER: PAPER
EXACT_ALGEBRA_REPLAY: PASSED
INDEPENDENT_REVIEW_OF_THIS_VERDICT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
LITERAL_CCM_NUMERICAL_SCAN: false
AUTHORIZED_REMOTE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_LOCALIZE_2026-10-31.md
REMOTE_DELIVERY: ACTUAL_COMMIT_AND_BYTE_READBACK_REPORTED_AFTER_WRITE
RH_PROVED: false
T_PROVED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 0. Decision

**The selected-bottom bound (*) and a strictly improving competitor remain unproved.** I do not infer their failure from the controls below. The new result is a sharper, literal-source obstruction to the proposed regularity mechanism, together with an explicit reduction of its quantitative costs.

There exist unit real-even vectors in the ORIGINAL CCM carriers, on the ORIGINAL schedule, which simultaneously:

1. escape every fixed theta jet, with superpolynomial accuracy;
2. have superpolynomially small full operator residual;
3. keep asymptotically all their physical mass in one fixed compact interval;
4. have superpolynomially small mass in the top `ceil(sqrt(m))` Fourier modes and superpolynomially small cutoff-return costs;
5. have local archimedean energy, the joint expression (*), and the compensated far-prime pairing tending to **plus infinity**.

These are **quasimodes, not asserted exact bottoms**. Their increasing derivative order is not given a uniform conditioning estimate; a justified diagonal construction chooses sufficiently large original cells for each fixed order. No quantitative rate for that increasing order is claimed. This construction therefore refutes a regularity supplier based only on escape, small residual, physical tightness and an upper-edge estimate. It does not refute a supplier that genuinely uses exact spectral minimality at its required scale.

The quantitative source reduction is also new: outside a spectral guard band of width `ceil(sqrt(m))`, the *full mixed-form* projection contribution has an explicit superpolynomial bound. The short-shift discrepancy costs a fixed constant. What remains is the **signed sum of a narrow spectral-edge return and a compact-to-exterior compensated prime coupling**. On the new controls the first term tends to zero and the second diverges. Thus paying only a selected upper-edge bound cannot, by itself, pay local regularity.

The request's own L1-L9 are used at their stated scope, not counted as new results. The complete own-attempt file was read at the pin. The current protocol was fetched through GitHub. The attached bytes were checked directly; the short source pin was resolved through the branch ref to the full hash above. No primary-source theorem outside this pinned shelf is imported in the new proofs.

### Claim ledger

| Claim | Scope / verifier | What is established |
|---|---|---|
| L1 | FINITE_CELL / PAPER | Nonzero cutoff return; exact trial excess and residual ledger |
| L2 | FINITE_CELL / PAPER | A full-source form majorant, including endpoint jumps |
| L3 | COFINAL_FAMILY / PAPER | Uniform superpolynomial return budget outside a narrow Fourier edge |
| L4 | FINITE_CELL / PAPER | Uniform short-shift cost; exact far compensated source formula |
| L5 | ABSTRACT / PAPER | Theta derivatives are dense in every fixed unweighted Sobolev space |
| L6 | ABSTRACT / PAPER | Normalized radical seeds with fixed compact mass and high local energy |
| L7-L8 | COFINAL_FAMILY / PAPER | Source-faithful diagonal return and oscillatory escaping controls |
| L9 | COFINAL_FAMILY / PAPER | Joint/far-source divergence on those controls, not on exact minima |
| L10 | ABSTRACT / PAPER | Local regularity plus surviving local mass implies T; regularity alone does not |

## 1. Conventions and the precise role of minimality

Keep `L=log m`, `b=L/2`, `I_m=[-b,b]`, `N=m`, and
\[
 \psi_{n,L}(x)=L^{-1/2}e^{2\pi in(x+b)/L}\mathbf1_{I_m}(x),\qquad |n|\le m.
\]
`P=P_m` is the original Fourier projection, restricted to even functions when appropriate. `A_m` is the full even matrix. Throughout this verdict all constructed vectors and cutoffs are real and even. The full source form is the one in CONFINE (1.3), with
\[
 j(a)=\frac{e^{-a/2}}{1-e^{-2a}},\quad c_n=\frac{\Lambda(n)}{\sqrt n},\quad
 c_*=\gamma+\log(8\pi)+\pi/2,
\]
\[
 p(x)=\sqrt2\cosh(x/2),\qquad q(x)=\sqrt2\sinh(x/2).
\]
The odd pole vanishes only because both partners are even. Every supported prime power, the entire archimedean tail, and the positive even pole remain. Pairings involving a global radical function retain the infinite prime-power tail.

Fix nonzero `chi` in `C_c^infinity`, even, `0<=chi<=1`, supported in `[-R,R]`. Only cells with `b>R` are used. Put
\[
 z=\chi f,\quad e=(I-P)z,\quad s=(I-P)(\chi^2f),\quad v=Pz.
\]
Denote the request's joint expression by
\[
 \mathscr B_{m,\chi}(f)=\Re\mathfrak k(f,s)-\int_0^L D(a)C_f'(a)\,da,
 \tag{1.1}
\]
where `D,C_f` are exactly those in the request. Define
\[
 I_\chi(f)=\int_0^L j_+(a)C_f(a)\,da,\qquad
 B_\chi=\int_0^\infty j_+(a)\min(\|\chi'\|_\infty^2a^2,1)\,da<\infty.
 \tag{1.2}
\]
For unit f, `|I_chi(f)|<=B_chi`. No sign for `C_f` is assumed.

### L1. The cutoff competitor is nonzero, but its denominator need not be uniform

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]**

For every nonzero carrier f, `P(chi f)!=0`. In fact,
\[
 \|P(\chi f)\|_2\ge\int\chi|f|^2>0\qquad(\|f\|_2=1).
 \tag{1.3}
\]
For a unit trial f set
\[
 \rho=\mathfrak k[f],\quad r=(A_m-\rho)f,\quad
 \varepsilon=\rho-\lambda_{\min}(A_m)\ge0.
\]
Then
\[
 \mathfrak k[\chi f]=\rho\|\chi f\|^2+
 \Re\langle r,P(\chi^2f)\rangle+\mathscr B_{m,\chi}(f)+I_\chi(f),
 \tag{1.4}
\]
\[
 \begin{split}
 N_\rho(f)&:=\mathfrak k[v]-\rho\|v\|^2\\
 &=\mathscr B_{m,\chi}(f)+I_\chi(f)+\Re\langle r,P(\chi^2f)\rangle
       -2\Re\mathfrak k(z,e)+\mathfrak k[e]+\rho\|e\|^2.
 \end{split}
 \tag{1.5}
\]
The actual minimality consequence for a trial is
\[
 N_\rho(f)\ge-\varepsilon\|v\|^2,
 \qquad
 \mathfrak k[v/\|v\|]-\lambda_{\min}
       =N_\rho(f)/\|v\|^2+\varepsilon.
 \tag{1.6}
\]
For an exact bottom, `r=0`, `epsilon=0`, and this becomes `N_lambda>=0`.

**Proof.** A nonzero finite trigonometric polynomial cannot vanish on an open interval. Since chi is positive on some open interval, its integral against `|f|^2` is strictly positive. Orthogonality and Cauchy-Schwarz give (1.3). Equation (1.4) is the supplied stationarity/pole-cancellation identity with its trial residual retained. Orthogonality gives `||v||^2=||z||^2-||e||^2`; expand the full form at `v=z-e` to obtain (1.5). The Rayleigh principle applied to v gives (1.6). The residual term is at most `||r||`, but no such absolute residual bound controls epsilon. This proof needs no simple eigenvalue. End of proof.

The source note's possible `v=0` branch is therefore unnecessary for a nonzero nonnegative smooth cutoff and a nonzero finite carrier vector. This correction supplies **no** cofinal denominator lower bound and is not itself progress on T.

## 2. A paid full-source projection budget, not an unsigned carrier-wide repair

### L2. A convenient majorant with both endpoints retained

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]**

For window-supported functions in the form domain put
\[
 d_m=c_*+(2+4L)\sqrt m,\qquad
 \mathcal B_m(w)^2=\mathcal H[w]+d_m\|w\|_2^2,
 \quad \mathcal H[w]=\int_0^\infty j(a)\|w-T_aw\|_2^2\,da.
\]
Then
\[
 |\mathfrak k(w,u)|\le\mathcal B_m(w)\mathcal B_m(u).
 \tag{2.1}
\]
If w is `H^1` inside the window, with endpoint sum
`J(w)=|w(-b)|+|w(b)|`, then
\[
 \mathcal H[w]\le10\|w'\|_{L^2(I_m)}^2+10J(w)^2+20\|w\|_2^2.
 \tag{2.2}
\]
In particular a cutoff-return error e has the valid full quadratic budget
\[
 |\mathfrak k[z-e]-\mathfrak k[z]|
 \le2\mathcal B_m(z)\mathcal B_m(e)+\mathcal B_m(e)^2.
 \tag{2.3}
\]

**Proof.** Archimedean polarization obeys Cauchy-Schwarz in its positive translation-difference energy. The prime part has norm at most
`2 sum_(n<=m) c_n <=4 sqrt(m)L`; the sum of the two pole norms squared is `4 sinh b<=2 sqrt(m)`. Include the scalar `c_*` and combine the two Cauchy-Schwarz inequalities to get (2.1). The zero-extended distributional derivative is
\[
 w'_{\rm int}\mathbf1_I+w(-b)\delta_{-b}-w(b)\delta_b.
\]
Consequently, for `0<a<=1`,
`||T_aw-w||_2<=a||w'||_2+sqrt(a)J(w)`.
Use the square bound with factor two and `int_0^infinity a j(a) da<5`; for `a>1`, use `||T_aw-w||<=2||w||` and `int_1^infinity j<=5`. This proves (2.2). Polarization proves (2.3). Nothing is inferred from an undefined whole-line H1 derivative. End of proof.

### L3. Only a narrow spectral edge is unpaid in the projection pairing

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]**

Let `kappa` be a fixed smooth function supported in `[-R,R]`. For an integer `1<=w<m`, split a unit carrier vector into
\[
 f=f^{\rm in}+f^{\rm ed},\quad
 f^{\rm in}=P_{m-w}f,\quad f^{\rm ed}=(P_m-P_{m-w})f.
\]
All projectors use the SAME window; the source operator still has cutoff m. Put
\[
 r^{\rm in}=(I-P_m)(\kappa f^{\rm in}).
\]
For integer `p>2` define
\[
 a_p=\frac{\|\kappa^{(p)}\|_1L^{p-1}}{(2\pi)^p},\quad
 t_p=\frac{2a_p}{p-1}w^{1-p},\quad
 u_p=\frac{2a_p}{p-2}w^{2-p}.
\]
Then, uniformly for every unit carrier f,
\[
 |\mathfrak k(f,r^{\rm in})|\le\mathfrak e_{m,w,p}:=
 \left[(2+4L)\sqrt m+\frac{(20\pi+60)m}{L}\right]t_p
       +\frac{20\pi}{L}u_p.
 \tag{2.4}
\]
With `w=ceil(sqrt(m))`, this is `O_{kappa,B}(m^{-B})` for every fixed B, by choosing fixed `p>2B+4` in the estimate. In particular, with `kappa=chi^2`,
\[
 \Re\mathfrak k(f,(I-P_m)\chi^2f)
 =E_{m,\chi}(f)+\epsilon_{m,\chi}(f),
\]
\[
 E_{m,\chi}(f)=\Re\mathfrak k(f,(I-P_m)\chi^2 f^{\rm ed}),
 \qquad |\epsilon_{m,\chi}(f)|\le\mathfrak e_{m,w,p}.
 \tag{2.5}
\]
No bound on the selected bottom's `f^ed` has been assumed.

**Proof.** Write
\[
 a_k(\kappa)=L^{-1}\int_I\kappa(x)e^{-2\pi ik(x+b)/L}\,dx.
\]
For `k!=0`, integration by parts p times gives `|a_k|<=a_p|k|^{-p}` with no boundary terms. Multiplication is convolution by `a_k`. If `|n|>m` and `|j|<=m-w`, then `|n-j|>w`. Young's inequality gives
\[
 \|r^{\rm in}\|_2\le t_p,\qquad
 \|(r^{\rm in})'\|_{L^2(I)}\le\frac{2\pi}{L}(mt_p+u_p).
 \tag{2.6}
\]
The second estimate uses `|n|<=|j|+|n-j|`. Absolute convergence of the Fourier tails, and the coefficient l1 bound of the input, give
\[
 J(r^{\rm in})\le2\sqrt{(2m+1)/L}\,t_p.
 \tag{2.7}
\]
Because `r^in` is orthogonal to the entire active carrier, the full mixed estimate CONFINE (3.5) applies:
\[
 |\mathfrak k(f,r^{\rm in})|
 \le(2+4L)\sqrt m\|r^{\rm in}\|+10\|(r^{\rm in})'\|
             +10J(r^{\rm in})\sqrt{3m/L}.
\]
Substitute (2.6)-(2.7) and `2m+1<=3m` to obtain (2.4). This estimate retains the archimedean tail, endpoint traces and all supported primes and poles. For the stated w, its largest powers are
`O(L^p m^{(2-p)/2}+L^{p-2}m^{(3-p)/2})`; the asserted choice of p pays any fixed B. End of proof.

This is not the killed uniform repair. The edge term remains signed and unbounded by this lemma. The improvement over a half-carrier split is explicit: only an `O(sqrt(m))`-wide edge remains in the projection source term, while its complement costs less than every fixed inverse power.

## 3. The remaining arithmetic can be made derivative-free

### L4. Uniform short-shift budget and exact compensated exterior coupling

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]**

Fix `a0>2R`, and take `L>a0`. Define
\[
 K_{a_0}=\sum_{2\le n\le e^{a_0}}c_n+2(e^{a_0/2}-1).
 \tag{3.1}
\]
For zero-extended f set
\[
 \begin{split}
 \mathcal V_{m,a_0}f={}&
 \sum_{\substack{2\le n\le m\\\log n>a_0}}c_n(T_{\log n}+T_{-\log n})f\\
 &-\int_{a_0}^L e^{a/2}(T_a+T_{-a})f\,da,
 \end{split}
\]
\[
 F_{m,\chi}^{\rm far}(f)=\langle\chi^2f,\mathcal V_{m,a_0}f\rangle.
 \tag{3.2}
\]
The integral is an ordinary finite-interval L2-valued integral. Then
\[
 \boxed{\left|\mathscr B_{m,\chi}(f)-E_{m,\chi}(f)
                    -F_{m,\chi}^{\rm far}(f)\right|
       \le K_{a_0}+\mathfrak e_{m,w,p}.}
 \tag{3.3}
\]
In particular this is a proper one-sided upper bound with an explicit, m-independent near cost and a superpolynomial return remainder.

**Proof.** The request's absolutely continuous `C_f` obeys `C_f(0)=C_f(L)=0`. Stieltjes integration by parts, INCLUDING the moving-endpoint derivative in its justification, yields
\[
 -\int_0^L D(a)C_f'(a)\,da
 =\sum_{2\le n\le m}c_n C_f(\log n)-\int_0^L e^{a/2}C_f(a)\,da.
 \tag{3.4}
\]
The atom at n=m is retained and has zero correlation. Since `|C_f(a)|<=1`, the part with `a<=a0` has absolute value at most (3.1). If `a>a0>2R`, the two cutoff supports do not overlap, so
\[
 C_f(a)=\langle\chi^2f,(T_a+T_{-a})f\rangle.
 \tag{3.5}
\]
This follows by expanding the cutoff square and changing variables in its second term. It does not use a reciprocal symmetry. The remaining part of (3.4) is exactly (3.2). Add (2.5). End of proof.

Only values of f with `|x|>a0-R` can enter the second factor of (3.2) where chi is nonzero. Also the pairing vanishes for shifts exceeding `b+R`. These are support consequences, not prime omissions. Primes and the subtracted continuum are kept together in (3.2); the subtraction is the exact pole cancellation already paid in the source note.

The outstanding source quantity is now
\[
 \boxed{E_{m,\chi}(f_m)+F_{m,\chi}^{\rm far}(f_m).}
 \tag{3.6}
\]
A uniform upper bound for (3.6) on exact bottoms would suffice for (*). No such bound is proved below. Equation (3.3) earns only its stated quantitative reduction; it does not turn an equality into a signed supplier.

## 4. A new literal negative control: tightness, tiny residual and negligible edge do not supply regularity

The following construction uses actual theta radicality. Unlike the earlier translated-packet control, it retains spatial mass in a fixed compact set. Its escape is oscillatory. This section is the principal new obstruction.

### L5. Sobolev density with exact fixed-jet annihilation

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]**

Let
\[
 \mathcal R_E=\operatorname{span}_{\rm finite}\{h,h'',h^{(4)},\ldots\},
 \qquad J_j=\operatorname{span}\{h,h'',\ldots,h^{(2j-2)}\}.
\]
For every fixed nonnegative integer s, `R_E` is dense in the real-even unweighted `H^s(R)`. Moreover
\[
 \mathcal R_E\cap J_j^\perp
 \text{ is dense in }H^s_E(\mathbb R)\cap J_j^\perp,
 \tag{4.1}
\]
where the orthogonality in (4.1) is the physical L2 orthogonality.

**Proof.** From the pinned theta representation, `H(t)=hat h(t)` satisfies `|H(t)|<=C_a exp(-a|t|)` for each `0<a<pi/4`, and is nonzero almost everywhere on the real line. Suppose g is Hs-orthogonal to all even derivatives. Set
\[
 M(t)=(1+t^2)^s\overline{\widehat g(t)}H(t).
\]
Cauchy-Schwarz shows that M has an exponential L1 moment of every smaller exponent. Its Fourier transform is analytic on a strip. All its even moments vanish by orthogonality; its odd moments vanish by parity. The identity theorem and Fourier uniqueness give `M=0`, hence `g=0`. This proves density; real coefficients suffice by taking real parts.

The L2 projector onto fixed J_j is bounded on Hs: choose an L2-orthonormal basis in J_j and bound each coefficient by the L2 norm. It maps R_E into R_E. Approximate a vector orthogonal to J_j by elements of R_E, and subtract their J_j projections. This proves (4.1). No statement is made for exponential spatial weights, global Weil-form convergence, or a derivative order growing uniformly with m. End of proof.

### L6. Radical seeds can have almost all their mass in a fixed interval and arbitrarily large local energy

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]**

For the control choose one admissible chi with `chi=1` on `[-1,1]`, supported in `[-2,2]`; let R=2. Choose a nonzero real even smooth bump `phi` supported in `(-1/2,1/2)`. There are unit `r_j in R_E cap J_j^perp` such that
\[
 \|\mathbf1_{[-1,1]}r_j\|_2^2\longrightarrow1,
 \qquad \mathcal H[\chi r_j]\longrightarrow\infty,
 \qquad \mathfrak k[\chi r_j]\ge 4j+B_\chi+10.
 \tag{4.2}
\]
Each `r_j` is a global Weil radical vector, but `chi r_j` need not be.

**Proof.** Consider unit bumps
\[
 g_T=\frac{\phi(x)\cos(Tx)}{\|\phi\cos(T\cdot)\|_2}.
\]
Their denominator tends to `||phi||/sqrt(2)`. They converge weakly to zero. Their Fourier L2 mass on `|t|>=T/2` tends to one, since their transforms are translates of the Schwartz function `hat phi`. The source lower bound
\[
 a(t)\ge e^{-1/2}(\log|t|-2)\quad(|t|\ge1)
\]
therefore gives `H[g_T]->infinity`. This is also genuine logarithmic-frequency divergence: splitting its defining integral at `min(1,1/|t|)`, using `j(a)<=4/a` for `0<a<=1` and `int_1^infinity j<5`, gives `a(t)<=64 log(2+|t|)`. Thus divergent arch energy forces divergent logarithmic Fourier energy. For fixed j, every coefficient of `P_Jj g_T` tends to zero faster than any inverse power of T, by integration by parts against the compact smooth bump times a fixed derivative of h. Thus `||P_Jj g_T||_H1->0`. Normalize `g_T-P_Jj g_T`; for T sufficiently large this vector has almost all its mass in `[-1,1]` and arbitrarily large local arch energy.

Now use (4.1), with s=1, and normalize a sufficiently accurate approximant in `R_E cap J_j^perp`. Multiplication by chi is bounded on H1. On functions supported in `[-2,2]`, the source form is H1-continuous, and
\[
 \mathfrak k[u]\ge\mathcal H[u]-K_R\|u\|^2,
 \quad K_R=c_*+2\sum_{n\le e^{2R}}c_n.
 \tag{4.3}
\]
For completeness, `H[u]<=5||u'||^2+20||u||^2`; the finite prime part costs at most `2 sum c_n`, and the two pole norms squared at most `4 sinh R`. These give explicit continuity constants. Choose the modulation first so that the desired inequalities have a strict margin, and then make the H1 approximation and normalization errors small enough to retain that margin and L2 error less than `1/j`. This gives (4.2). All choices are finite for each j. There is no uniform estimate on the jet order or coefficients as j grows. End of proof.

### L7. Return of each fixed seed, with the source, localization and residual budgets paid

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]**

Fix j temporarily. Choose once a real even smooth cutoff `vartheta`, equal to one on `[-1/2,1/2]`, supported in `(-3/4,3/4)`, with values in `[0,1]`. Set
\[
 z_{m,j}=\vartheta(x/b)r_j,\quad
 u_{m,j}=P_mz_{m,j},\quad q_{m,j}=u_{m,j}/\|u_{m,j}\|_2.
 \tag{4.4}
\]
For this fixed seed and every fixed B,
\[
 \|q_{m,j}-r_j\|_2+\|A_mq_{m,j}\|_2
       +\|\chi(q_{m,j}-r_j)\|_{H^1}=O_{j,B}(m^{-B}).
 \tag{4.5}
\]
The same holds for the top `ceil(sqrt(m))` coefficient norm. Also, with `s=(I-P)chi^2 q` and `e=(I-P)chi q`,
\[
 |\mathfrak k(q_{m,j},s)|=O_{j,B}(m^{-B}),
 \quad
 2\mathcal B_m(\chi q_{m,j})\mathcal B_m(e)+\mathcal B_m(e)^2
                   =O_{j,B}(m^{-B}).
 \tag{4.6}
\]
No m-dependent source operator or larger Fourier carrier is used.

**Proof and budgets.** The inherited CONFINE estimate applies by finite linearity to r_j. Write `e0=u-z`, `w0=r_j-z`,
`epsilon0=||e0||`, `epsilon1=||e0'||`, and `J0=|e0(-b)|+|e0(b)|`. For every fixed p the paid estimates are
\[
 \epsilon_0\le A_{j,p}(L/(2\pi m))^p,\qquad
 \epsilon_1\le A_{j,p}(L/(2\pi m))^{p-1},
\]
\[
 J_0\le\frac{2A_{j,p}}{\sqrt L}(L/(2\pi))^p
                    \sqrt{2/(2p-1)}m^{1/2-p},
 \tag{4.7}
\]
where `A_jp=sup_(b>=1)||[vartheta(x/b)r_j]^(p)||_2<infinity`. Radicality gives
\[
 \|A_mu_{m,j}\|\le(2+4L)\sqrt m\,\epsilon_0+10\epsilon_1
                         +10J_0\sqrt{3m/L}+\tau_{m,j},
 \tag{4.8}
\]
\[
 \begin{split}
 \tau_{m,j}={}&c_*\|w_0\|+10\|w_0'\|
 +2m^{1/4}\int e^{|x|/2}|w_0(x)|dx\\
 &+2\sqrt m\left(\sum_{n\ge2}\frac{\log n}{n^{3/2}}\right)
                          \|e^{|x|}w_0\|_2.
 \end{split}
 \tag{4.9}
\]
The prime sum in (4.9) is infinite. Super-exponential theta decay makes the weighted norms, whose support begins at `|x|>=L/4`, smaller than every fixed inverse power. Thus (4.7)-(4.9) give global L2 convergence and the full residual. The norm of u tends to one, so it is at least 1/2 eventually and normalization is paid. On the fixed support of chi, `vartheta(x/b)=1` eventually; (4.7) gives the local H1 convergence.

For any fixed derivative order p, the interior H^p norm of q is uniformly bounded in m for this fixed j: Fourier projection contracts the corresponding periodic derivative norm of z. Therefore the derivatives of `chi q` and `chi^2 q`, of any fixed order, are bounded uniformly in m and vanish at the endpoints. Apply the same Fourier-tail and endpoint estimates (4.7) to those products. Their return errors have arbitrarily high polynomial decay. The mixed estimate used in L3 gives the first bound in (4.6). Equations (2.1)-(2.3) give the second; their growing factors are only polynomial in m. The high-edge bound follows from the ordinary tail estimate beyond `m-ceil(sqrt(m))>=m/2` eventually. This proves all claims for each fixed j. End of proof.

### L8. One original-cell sequence has all the claimed controls simultaneously

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]**

There is a sequence of unit real-even `q_m in V_m,E` such that, for every fixed B and every fixed r,
\[
 \|A_mq_m\|+\|P_{J_r}q_m\|+\|q_m^{\rm ed}\|
 +|\mathfrak k(q_m,(I-P_m)\chi^2q_m)|=O_{r,B}(m^{-B}),
 \tag{4.10}
\]
and the full return budget in (4.6) has the same property. Nevertheless,
\[
 \|\mathbf1_{[-1,1]}q_m\|^2\to1,\quad q_m\rightharpoonup0,
 \quad\mathcal H[\chi q_m]\to\infty,
 \quad\mathfrak k[\chi q_m]\to\infty.
 \tag{4.11}
\]
Also `||P_m chi q_m||->1`.

**Proof.** Choose strictly increasing integers M_j tending to infinity. For each j, L7 allows M_j so large that on **every** `m>=M_j` all terms in (4.5)-(4.6), the edge norm, and the local source-form error needed to preserve (4.2), obey the desired bounds with right side `m^{-j}` (the local energy error may instead be bounded by 1). To obtain `m^{-j}`, apply the fixed-j estimates first with exponent `j+1`, then increase the threshold to absorb their finite constants. Require `M_j>=j` and `L>max(2R,a0)` as well.

Put `j(m)=max{j:M_j<=m}` and `q_m=q_{m,j(m)}`. For any fixed r and B, eventually `j(m)>=max(r,B)`. Since `r_j` is exactly orthogonal to J_j,
`||P_Jr q_m||<=||q_m-r_j||<=m^{-j}`. The other estimates follow from the same thresholds. The fixed local mass follows from L6 and L2 approximation. Density of the fixed jets and the unit norm imply weak convergence to zero. Local energy divergence follows by preserving (4.2); local H1 convergence for each seed and (4.3) also show the arch energy diverges. Since `chi=1` on the target bumps and their L2 approximation errors tend to zero, `||chi q_m||->1`. Its Fourier return error tends to zero, so `||P_m chi q_m||->1`.

This is a diagonal existence proof, not an effective rate for growing-order jets. Constants depending on j were absorbed only AFTER fixing j. It does not use any unproved uniform estimate in derivative order, and it never replaces N=m. End of proof.

The construction is compatible with the pinned source and theta identities. It is not a finite numerical extrapolation. Its small global L2 tails can carry large source-weighted interactions; no convergence in an exponentially weighted norm was asserted.

### L9. The compensated far-source term diverges even when projection and edge costs vanish

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]**

For the q_m of L8, let `rho_m=k[q_m]`, `r_m=(A_m-rho_m)q_m`. Then
\[
 |\rho_m|\le\|A_mq_m\|,
 \qquad \|r_m\|\le2\|A_mq_m\|.
\]
Consequently
\[
 \boxed{\mathscr B_{m,\chi}(q_m)\to+\infty,\qquad
       -\int_0^L D(a)C_{q_m}'(a)da\to+\infty,\qquad
       F_{m,\chi}^{\rm far}(q_m)\to+\infty.}
 \tag{4.12}
\]
Moreover the normalized cutoff candidate has
\[
 N_{\rho_m}(q_m)\to+\infty,
 \qquad \mathfrak k[P_m\chi q_m/\|P_m\chi q_m\|]-\rho_m\to+\infty.
 \tag{4.13}
\]

**Proof.** Use the exact trial identity (1.4). Its local energy tends to infinity; `rho_m` and its explicitly retained residual term tend to zero, while `|I_chi|<=B_chi`. This proves the first assertion of (4.12). Its projection pairing tends to zero by (4.10), proving the second. The short-shift part is bounded by (3.1), so (3.4)-(3.5) prove the third. Finally (2.3) and (4.6) show that returning chi q changes its source energy by a quantity tending to zero. Its norm tends to one. Equation (1.5) now gives (4.13). End of proof.

This refutes the following exact theorem shape:

> Escape, a full residual smaller than every inverse power, tight physical mass, and a superpolynomially small upper spectral edge imply an m-independent upper bound on (*), or on its compensated far-source part.

For any proposed constant C, (4.12) gives the strict **upper** envelope `C-B(q_m)<-1` eventually; this is a genuine counterexample to that shape. **KILL_SCOPE: THEOREM_SHAPE. KILL_EVIDENCE_KIND: LITERAL_SOURCE_COFINAL_QUASIMODE_CONSTRUCTION, L5-L9.** It does not kill a theorem restricted to exact bottoms.

Indeed, the exact energy excess of these controls is
\[
 \varepsilon_m=\rho_m-\lambda_{\min}(A_m).
 \tag{4.14}
\]
It has not been bounded by their residual. The only legitimate minimum comparison is (1.6), with this epsilon. The cutoff moves them upward, not downward. Nothing contradicts a source estimate which uses exact minimum selection at a scale not controlled by (4.10). The construction does not establish that any actual bottom realizes these profiles.

A further precise consequence is that the compact-to-exterior compensated operators in (3.2) have no uniform unweighted L2 bound on arbitrary window inputs. Choose `a0>2R` so `a0-R>1`. Only the exterior part `1_(|x|>a0-R)q_m`, whose norm tends to zero, contributes to (3.2), while that pairing diverges. Hence those operator norms are unbounded. This is an obstruction to a carrier-independent exterior Green estimate, not to a selected response estimate.

## 5. What exact minimality has and has not supplied

The main question is not closed. Here is the attempted chain and its precise first failure.

* Use the exact bottom equation to obtain (1.4) with no residual. This is stationarity.
* Pay the off-edge projection term by (2.4), and the short-shift discrepancy by (3.1). These are unconditional source/carrier estimates.
* The remaining sufficient upper estimate is
\[
 \boxed{E_{m,\chi}(f_m)+F_{m,\chi}^{\rm far}(f_m)\le C_\chi
       \quad\text{for the selected exact bottoms}.}
 \tag{5.1}
\]
Neither (5.1) nor a weaker joint upper bound feeding (*) has been proved. Small edge mass by itself is insufficient: L8-L9 make even the entire mixed projection term negligible and still violate (5.1) on trials. An exterior L2-smallness argument also fails at precisely the source-weighted pairing (3.2).

Exact MINIMALITY beyond stationarity enters at (1.6), and only there in this attempted localization argument: `epsilon=0` yields a lower bound for the returned local numerator. It does not supply an upper bound for (5.1). Nor does it give a negative numerator under escape. The full strict-descent obligation is still
\[
 E_{m,\chi}(f_m)+F_{m,\chi}^{\rm far}(f_m)
 +I_\chi(f_m)+\text{near term}+\text{off-edge term}
 -2\Re\mathfrak k(z,e)+\mathfrak k[e]+\lambda_m\|e\|^2<0,
 \tag{5.2}
\]
with each source term as defined above. The near and off-edge terms have the paid bounds (3.1), (2.4); the full return terms have (2.1)-(2.3). Those sufficient absolute budgets may be too lossy for a shrinking signed margin and are not made mandatory. No strict sign in (5.2) is asserted.

The uncontrolled pair (5.1) is not a substitute for T or full shifted PSD. It is a specific sufficient regularity interface on a fixed cutoff, and it need not be necessary for T. The new information is the paid removal of the rest and the literal obstruction to promoting residual, edge or unweighted tail information into its missing upper bound.

### An exact abstract check of the direction of minimality

Let `A=diag(-1,M)`, `M>0`, `f=(1,0)`, and
\[
 B=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix}.
\]
B is a positive contraction, f is a simple exact bottom, and
\[
 \langle Bf,(A+I)Bf\rangle=(M+1)/16\ge0,
 \quad\langle Bf,ABf\rangle=-1/4+M/16.
 \tag{5.3}
\]
The latter is arbitrarily large. This is **not CCM**; it checks only that minimum stability plus a positive localization contraction does not give an upper local-energy estimate. The literal obstruction in L5-L9 is separate and stronger in its source fidelity, but does not impose exact bottomness.

## 6. Even a successful regularity bound would still need mass

### L10. The compactness implication, with its separate source obligation

**THIS STEP IS PROVED HERE -- conditional implication. [ABSTRACT | CONDITIONAL]**

If (*) is uniformly bounded on exact bottoms, their known fixed-theta trial upper bound for lambda and (1.4) imply a uniform upper bound for `k[chi f_m]`. The source inequality (4.3) and the request's L1 then give
\[
 \sup_m\frac1{2\pi}\int\log(2+|t|)|\widehat{\chi f_m}(t)|^2dt<\infty.
 \tag{6.1}
\]
If, additionally, along an unbounded set of original cells,
\[
 \|\chi f_m\|_2^2\ge\eta>0,
 \tag{6.2}
\]
then T follows and hence RH by the accepted NOESCAPE bridge. Without (6.2), (6.1) alone does not give T.

**Proof.** The Fourier tail in (6.1) is at most `C/log(2+T)` beyond frequency T. The functions have fixed support. Their bounded-frequency parts, restricted to that support, lie in the image of a bounded set under a Hilbert-Schmidt Fourier integral operator; this image is relatively compact. Letting T increase proves L2 precompactness. By (6.2), a strong local subsequential limit is nonzero. A weak subsequence of the unit global f_m has that nonzero localized limit. Density of the fixed theta jets then gives a nonzero pairing with some fixed jet, bounded away from zero on a further subsequence. This is T. No simple eigenvalue or identification with the GREEN complementary response is used. End of proof.

**THIS COMPLETION IMPLIES RH.** The two source estimates (5.1) and (6.2) have not been supplied. Neither is used as a premise of any unconditional conclusion above. In particular, fixed local mass is not a consequence of (6.1); the accepted spatially translating packets have local mass tending to zero. Conversely L8 has local mass tending to one but violates (6.1). These are the two distinct ways compactness can fail.

## 7. Route map, dependency discipline, and adversarial closeout

| Route | Paid result | Decisive missing source comparison | Kill-power / cost |
|---|---|---|---|
| Narrow-edge plus compensated exterior response | (2.4), (3.3) | Selected joint bound (5.1), not separate unsigned bounds | High / medium-high |
| Same-carrier cutoff or an adaptive localized competitor | Nonzero normalization, complete excess/residual ledger | Strict source upper bound for (5.2) | High / high |
| Physical compactness | L10 | Both regularity and positive fixed local mass | High / high |

These are candidate re-representations, not claims of success. The fixed cutoff is not mandatory. A different normalized even competitor returned to the same carrier remains admissible.

**DOWNSTREAM_CONSUMER:** literal fixed-jet NOESCAPE T, then the accepted implication T => RH.

**ACTUAL_CONSUMER_REQUIREMENT:** one persistent fixed finite component on an unbounded original family; not a complete limiting ladder.

**ORIGINAL_REQUESTED_OBJECT:** an actual joint source upper bound (*) or a strict same-carrier descent under escape.

**ORIGINAL_OBJECT_IS:** UNKNOWN as necessary. The fixed-cutoff regularity route is sufficient only with its separate mass input; another mechanism can reach T.

**KNOWN_WEAKER_INTERFACES:** a nonzero weak subsequential limit implies T; one directly bounded fixed-jet overlap also suffices. Neither is supplied here.

**FAILURE_TYPE / EPISTEMIC_STATUS:** NO_DERIVATION / RESEARCH_DEBT for (5.1), (5.2), and (6.2). REOPEN_TRIGGER: a bound derived from the literal eigen-equations and exact minimality, retaining the full compensated far pairing and the narrow-edge term, with residual and true energy-excess sensitivity explicit.

**SCOPED DEATH:** only the quasimode-based regularity assertion stated after L9 is MATHEMATICALLY_DEAD. Its counterexample is L5-L9 using the pinned CONFINE source return. No route-family death is asserted.

**BRIDGE CHECKS:** the nonlocal Caccioppoli/IMS identity gives a signed source ledger, not its upper bound; frequency localization pays the off-edge term but not the far source; the theta-radical/density bridge produces the adversarial controls rather than compactness. No new external theorem was imported to fill the gap. The collapse object would be a genuinely selected estimate on the compensated local-to-exterior response which the controls fail because of a paid exact-minimum input.

**DISCRIMINATOR:** separately evaluate, from their source formulas, the three signed channels `E_m,chi`, `F_far`, and the bounded near term, together with the true minimum excess and the form return budget. Do not define one channel by subtracting the others from the local energy. A zero-consistent or small-residual result without that signed separation is inconclusive.

**Predictions and validation:** LOCALIZE supplied no numerical probability forecasts. The announced checks were whether upper-edge removal pays the remaining projection budget and whether spatially tight oscillatory radical controls exist. L3 confirms the first with its stated unpaid edge; L5-L9 confirm the second. Neither was a prediction of a bottom counterexample. Exact algebra replay checked the pole factor and moving-endpoint polynomial, the trial residual sign, and the direction of the minimum inequality. No literal CCM numerical scan or interval eigenpair test was performed.

**META:** smaller -- only a narrow-edge source return and a derivative-free compensated exterior pairing remain beyond uniform/superpolynomial costs. Killed -- low residual plus tight mass plus negligible edge as a carrier-wide regularity supplier. Do not repeat -- interpreting edge repair as a bound on the distant arithmetic response. Smallest unpaid quantity -- (5.1) on exact bottoms, or a full signed numerator (5.2). Memory -- LOCALIZE: spatially tight theta-radical quasimodes can have vanishing residual/edge/return and divergent local energy; exact spectral selection still unspent.

## 8. Proshka's own line

The new control is not another pair of bumps moving toward the window ends.
It keeps its L2 mass near the origin and moves its frequency instead.
That is why it addresses the regularity half rather than the mass half.
The source is unchanged throughout the construction.
The derivative order increases only after each fixed-order estimate is paid.
This is an existence argument, not an efficient numerical construction.
I would not fit its order to the available small-cell data.
The narrow-edge estimate is useful but cannot be sold as local compactness.
The control has an even smaller edge and still defeats that conclusion.
The same is true of an unweighted exterior-tail estimate.
A tiny exterior L2 tail can carry a large compensated arithmetic interaction.
The next calculation should keep that interaction signed and jointly projected.
A positive reduced Green kernel is not needed for the formulas here.
Nor would assuming one repair the selected estimate without a valid source map.
The first alternative is a bottom-specific estimate of the far response.
It dies if its proof uses only the properties listed in L8.
The second is a different same-carrier variation using exact minimality.
It dies if its claimed gain is merely a small residual in disguise.
The useful data would be separately certified far and edge channels for the saved true bottoms.
The same channels should be measured on independently generated low-residual controls.
I would include the actual energy excess, not infer it from the residual norm.
The request correctly insists that regularity and local mass are distinct.
The pole cancellation is valuable because it removes a false large main-term cost.
It does not make the remaining prime discrepancy a bounded operator uniformly in the window.
The dense radical is powerful in unweighted spaces and dangerous in weighted source pairings.
The RH goal stays unchanged; neither a good decomposition nor an accepted control is its proof.

## 9. Research log

All repository sources below are at `5575dc7b29f4f96c9d9d35e486e3a968cc8556d3`, except the protocol explicitly read at current `rh_clean`.

- **READ, complete:** attached `PROSHKA_REQUEST_LOCALIZE_2026-10-31.txt`; exact SHA-256/size/line check in the header. Authoritative task and write scope.
- **READ, complete:** `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`; judging and delivery protocol.
- **READ, complete:** `docs/routeB_bus/proshka/NOESCAPE_LOCAL_LOG_REGULARITY_ATTEMPT_2026-10-30.md`, blob `8c8273cdd407cf4827584ceb6d6a538091880784`; L1-L9, exact cutoff/primitive identities and the previously unpaid joint bound.
- **READ, relevant initial control and budget sections:** `docs/routeB_bus/source_observability_2026-09-28/DIRECT_THETA_LOCALIZATION_AUDIT_2026-10-06.md`; the top-mode counterexample is not an exact-bottom counterexample, and the old half-carrier split leaves a selected edge debt.
- **READ, lines 1-45:** `docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py`, blob `5cbd156db9be84caa938cdbabd4e9ec0b5a6d2f3`; literal diagonal/off-diagonal source, every prime power and pole normalization. Code was read, not run as an exact-source certificate.
- **READ, sections 1-3 and exact end of section 3:** `docs/routeB_bus/proshka/PROSHKA_VERDICT_CONFINE_2026-10-30.md`, blob `1879347b72d1aa55cf506f5387de37059f929122`; theta analyticity/radicality, the L2 density proof, and the full original-schedule mixed residual estimates. Their accepted PAPER scope is retained.
- **RELAY, not independently reread this batch:** the completed GREEN review and the earlier threshold/Gridnev primary papers. No new theorem from them is a premise here. No claim that the incomplete semantic search proves literature absence.
- **ABANDONED:** carrier-wide cutoff-return smallness; the upper edge remains in (2.5).
- **ABANDONED:** a selected upper-edge estimate alone closes (*); L8-L9 make that edge negligible while the joint expression diverges on the larger quasimode class.
- **ABANDONED:** spatial tightness plus tiny residual gives local compactness; the oscillatory source controls refute this larger-class implication.
- **ABANDONED:** exact minimum stability gives the needed upper local energy; it supplies (1.6), and the direction check (5.3) rejects that abstract inference.
- **REUSABLE:** finite-codimension Sobolev density (4.1); guarded mixed-form estimate (2.4); derivative-free far source (3.2); actual energy-excess correction (1.6).

An auxiliary attempt to download already-read source bytes into the local runtime failed (download-tool URL gate, then local DNS). Those failures did not prevent connector reads and are not evidence about GitHub write capability. No mathematical conclusion uses them.

## 10. Exact validation code and output

The following code was executed with SymPy. It checks algebraic factors and residual signs only; it does not test the new cofinal analytical proofs, prove a CCM eigenpair, or provide an independent review.

```python
import sympy as s
x, a = s.symbols('x a', real=True)
C = s.integrate(((x*x-(x+a)**2)**2)/2, (x, -1, 1-a))
assert s.simplify(C-a**2*(2-a)**3/6) == 0
J = {k: s.integrate(x**k*s.cosh(x/2), (x,-1,1)) for k in (0,2,4)}
pole = J[2]**2-J[0]*J[4]
assert s.simplify(s.expand_trig(
    pole+2*s.integrate(s.cosh(a/2)*C,(a,0,2)))) == 0
P = s.diag(1,1,0)
I = s.eye(3)
H = s.Matrix([[2,-1,3],[-1,1,2],[3,2,4]])
B = s.Matrix([[2,1,1],[1,2,0],[1,0,2]])/4
q = s.Matrix([s.Rational(3,5),s.Rational(4,5),0])
rho = (q.T*H*q)[0]
r = P*H*q-rho*q
z = B*q
e = (I-P)*z
sigma = (I-P)*B*B*q
v = P*z
comm = (z.T*H*z-q.T*H*B*B*q)[0]
r_local = (r.T*P*B*B*q)[0]
N = (v.T*H*v)[0]-rho*(v.T*v)[0]
ledger = ((q.T*H*sigma)[0]+comm+r_local-2*(z.T*H*e)[0]
          +(e.T*H*e)[0]+rho*(e.T*e)[0])
assert s.simplify(N-ledger)==0
assert s.simplify((z.T*H*z)[0]-rho*(z.T*z)[0]
                  -(q.T*H*sigma)[0]-comm-r_local)==0
M=s.symbols('M',positive=True)
A=s.diag(-1,M)
bb=s.Matrix([[s.Rational(1,2),s.Rational(1,4)],
             [s.Rational(1,4),s.Rational(1,2)]])
f=s.Matrix([1,0]); y=bb*f
assert s.simplify((y.T*(A+s.eye(2))*y)[0]-(M+1)/16)==0
assert (y.T*y)[0]==s.Rational(5,16)
assert s.simplify((y.T*A*y)[0]-(-s.Rational(1,4)+M/16))==0
print('PASS: moving endpoint / pole factor / full residual ledger / minimality lower-bound control')
```

Observed output:
```text
PASS: moving endpoint / pole factor / full residual ledger / minimality lower-bound control
```

## 11. One next directive and delivery boundary

**CODEX DIRECTIVE -- one bounded, source-weighted localization discriminator, read-only.**

Use the already saved actual even-bottom eigenpair boxes, without a broad new scan. Fix a nonzero even cutoff with an interior plateau, one fixed `a0>2R`, and the guard width `ceil(sqrt(m))`. First independently audit L5-L9: the Sobolev density, exact finite-jet annihilation, and the nonuniform diagonal return are the new analytic claim, not a routine consequence of small residual. Then for the saved cells compute the narrow-edge term in (2.5) and the far term (3.2) **directly from their full source formulas**, keeping the positive atom sum and continuum compensation jointly. Bound the near and off-edge costs by (3.1) and (2.4), and the complete cutoff return by (2.1)-(2.3); report the actual bottom/energy-excess status of every vector used. Do not recover a channel from the local-energy identity. The aim is to decide whether the saved bottoms show cancellation between edge and far channels, or a small far channel itself; neither finite outcome proves T.

Success report: `LOCALIZE_SOURCE_CHANNELS_CERTIFIED` with separate signed enclosures and all residual/normalization budgets, plus `OSCILLATORY_RADICAL_CONTROL_CONFIRMED_PAPER` if the analytic construction survives audit. Otherwise report `LOCALIZE_FIRST_UNPAID_BOUND` at the first unsupported estimate. No new source inequality is admitted merely because the finite channels are small. A cofinal supplier must use exact minimum selection in a way the L8 controls do not satisfy; absent that step, stop this mechanism rather than repeat the same decomposition.

Delivery is limited to the one new verdict path in the header, using an ordinary non-force GitHub contents commit after reading current HEAD. The actual commit, changed-path check and remote-byte comparison belong in the accompanying response after execution. No Lean source is written, so there is no Lean verification handoff or new axiom profile. This verdict's mathematics remains PAPER pending independent review. RH, T, G1a and G3 are not declared proved.
