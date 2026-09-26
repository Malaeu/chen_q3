# Verdict: `OPEN_ABEL_FORCING_SIGN`

```yaml
REQUEST_ID: REQ-2026-09-26-ABEL-CUMULATIVE-FORCING
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_FULL_FORCING_ABEL_SIGN
SOURCE_COMMIT: 03531e2a5b150c50de0c140223d38fc081daada2
OUTCOME: OPEN_ABEL_FORCING_SIGN
VERIFIER: PAPER
ABEL_IDENTITY_A: VERIFIED
WRONSKIAN_IDENTITY_W: VERIFIED
NEW_RESULT: GROUND_CENTERED_ABEL_IDENTITY_AND_JOINT_ENCLOSURE
SOURCE_UNIFORM_MARGIN_AGAINST_Y2_B: NOT_ESTABLISHED
SIGN_OF_TAU: OPEN
ABEL_METHOD_KILL: NOT_ESTABLISHED
SCHUR_FLOOR: OPEN
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
REPOSITORY_WRITTEN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

**Both proposed identities are correct in the source convention. There is also a useful new reduction:** ground-centering the cumulative forcing extracts a **strictly positive, source-derived coefficient**, with an exact remaining joint correlation. This gives an explicit enclosure for the full weighted Abel sum without requiring any common sign for the \(C_j\).

**It does not yet give either requested margin.** The missing estimate is a signed ground-forcing moment dominating a precisely specified centered forcing contribution. No source witness has been established against the sufficient certificate proposed below, so this is not `ABEL_METHOD_KILL`.

The authoritative TXT was read in full. The recurrence and CCM definitions below were inspected at the requested commit; the predecessor’s stated SHA-256 was not independently recomputed in this no-runtime review. The selected family, splice, carrier, and full forcing remain those of the request. :chatgpt-content-reference{index="0"}

## 1. Source audit of (W), (A), and the endpoint

To avoid confusing the family index with an Abel prefix index, write
\[
m=J_P+\iota+2,\qquad N=6m-1,
\]
for the fixed \(P\). Below, \(j\) denotes a prefix index, not a change of cell.

### The recurrence fixes the minus sign in (W)

Put \(G_m=4\pi^2m^2\). The inspected source crosswalk gives
\[
\ell_k P_{k-1}+b_kP_k+u_kP_{k+1}=EP_k,
\]
where
\[
\begin{aligned}
\ell_k&=-G_m\frac{(2k-1)(2k)}{(4k-3)(4k-1)},\\
b_k&=2k(2k+1)+G_m
 \frac{4k(2k+1)-1}{(4k-1)(4k+3)},\\
u_k&=-G_m\frac{(2k+1)(2k+2)}{(4k+3)(4k+5)}.
\end{aligned}
\tag{1}
\]
The spectral convention is exactly \(E=\Lambda+G_m\); it is not an unshifted recurrence. 

With \(\mu_k=(4k+1)^{-1}\),
\[
\mu_ku_k=\mu_{k+1}\ell_{k+1},\qquad
A_k=-\mu_ku_k
=\frac{G_m(2k+1)(2k+2)}
 {(4k+1)(4k+3)(4k+5)}>0.
\tag{2}
\]
All displayed denominators are nonzero on their stated integer ranges.

Subtract the \(p\)-recurrence multiplied by \(v_k\) from the \(v\)-recurrence multiplied by \(p_k\), then multiply by \(\mu_k\). For
\[
\mathfrak w_k=A_k(p_kv_{k+1}-v_kp_{k+1}),
\]
the result is
\[
\mathfrak w_k-\mathfrak w_{k-1}
=-\Delta E\,\mu_kp_kv_k.
\]
At the left endpoint, \(\ell_0=0\), so \(\mathfrak w_{-1}=0\). Consequently
\[
\mathfrak w_j=-\Delta E\,S_j,
\]
and, using the accepted source positivity \(p_j,p_{j+1}>0\),
\[
\boxed{
r_{j+1}-r_j
=-\frac{\Delta E\,S_j}{A_jp_jp_{j+1}}.
}
\tag{W}
\]

The left-end check is particularly restrictive:
\[
S_0=p_0=v_0=1,\qquad
r_1-1=\frac{\Delta E}{u_0p_1}<0,
\]
and
\[
W_1=-\frac{\Delta E}{u_0}
=\frac{15\Delta E}{2G_m}>0.
\tag{3}
\]
Thus neither the sign nor the initial index in (W) can be reversed.

### The finite Abel endpoint must remain

Set \(C_0=0\). Since
\[
p_kh_k^\sharp=C_k-C_{k-1},
\]
finite summation by parts gives
\[
\begin{aligned}
D_m
&=\sum_{k=1}^{N}(1-r_k)(C_k-C_{k-1})\\
&=(1-r_N)C_N
+\sum_{j=1}^{N-1}(r_{j+1}-r_j)C_j.
\end{aligned}
\tag{A}
\]

There is no \(C_{N+1}\) term and no discarded \(C_0\) term. **There is an indispensable \((1-r_N)C_N\) term.**

The recurrence can also be checked at \(j=N\), but then \(p_{N+1}\) and \(v_{N+1}\) are their genuine source-tail values, not zero boundary conditions. The predecessor identifies those values through the original \(5m\) splice; evaluating the tail at \(6m\) does not move the splice. 

One further endpoint fact will matter below. The accepted geometric source tails make the Wronskian flux tend to zero, hence
\[
S_\infty=0.
\]
Using the predecessor’s positive terminal \(v\)-region and \(p>0\), on that same source domain,
\[
\boxed{
S_N=-\sum_{a=N+1}^{\infty}\mu_ap_av_a<0.
}
\tag{4}
\]
This is an **infinite-tail identity**, not permission to set the finite \(S_N\) equal to zero. The source signs and tail properties used here are those already established in the predecessor; its weight-node test is not being repeated.  

## 2. A new ground-centered Abel identity

This is the additional PAPER result.

Define the positive ground masses
\[
M_j=\sum_{k=1}^{j}\mu_kp_k^2,\qquad M=M_N>0,
\]
and the finite cross-moment
\[
\beta_N=\sum_{k=1}^{N}\mu_kp_kv_k.
\]
Because the source normalization includes \(p_0=v_0=\mu_0=1\),
\[
\boxed{\beta_N=S_N-1.}
\tag{5}
\]

The **minus one is essential**: \(C_j\) and \(M_j\) start at \(1\), whereas \(S_j\) starts at \(0\).

Now center the cumulative forcing by its ground-mass profile:
\[
E_j^\sharp=C_j-\frac{M_j}{M}C_N,
\qquad E_0^\sharp=E_N^\sharp=0.
\tag{6}
\]
This does not alter \(g^\sharp\), \(h^\sharp\), or \(x\). It is an algebraic decomposition of their already fixed cumulative sums.

Apply (A) separately to the ground-mass profile and its centered remainder. Since
\[
\sum_{k=1}^{N}(1-r_k)\mu_kp_k^2=M-\beta_N,
\]
one obtains
\[
\boxed{
\mathcal Q_m
=a_m\,\kappa_mC_N
-\kappa_m\Delta E
 \sum_{j=1}^{N-1}
 \frac{S_jE_j^\sharp}{A_jp_jp_{j+1}},
\qquad
a_m=1-\frac{\beta_N}{M}.
}
\tag{7}
\]

In particular, by (4)–(5),
\[
\boxed{
a_m=\frac{M+1-S_N}{M}>1+\frac1M>0.
}
\tag{8}
\]

**This positive coefficient has a genuine source:** left normalization, the omitted \(k=0\) coordinate, and the positive terminal overlap. It is not a new constant defined to absorb an unknown sign.

It is nevertheless **not the requested positive margin**: it multiplies the still-signed quantity \(\kappa_mC_N\).

### The entire remaining Abel sum is one centered correlation

Use the auxiliary weighted coordinates
\[
\eta_k=\frac{h_k^\sharp}{\mu_k},\qquad
\eta_k^\perp=\eta_k-\frac{C_N}{M}p_k,\qquad
v_k^\perp=v_k-\frac{\beta_N}{M}p_k,
\]
with
\[
\langle a,b\rangle_\mu=\sum_{k=1}^{N}\mu_ka_kb_k.
\]
The source reflection relation makes the quantities here real; no modulus replaces the conjugation in \(F^*g^\sharp\).

Direct expansion gives
\[
\langle v^\perp,\eta^\perp\rangle_\mu
=\sum_{k=1}^{N}v_kh_k^\sharp-\frac{\beta_N}{M}C_N.
\]
Comparing with (7),
\[
\boxed{
\Delta E\sum_{j=1}^{N-1}
\frac{S_jE_j^\sharp}{A_jp_jp_{j+1}}
=\langle v^\perp,\eta^\perp\rangle_\mu.
}
\tag{9}
\]
Therefore
\[
\boxed{
\mathcal Q_m
=a_m\,\kappa_mC_N
-\kappa_m\langle v^\perp,\eta^\perp\rangle_\mu.
}
\tag{10}
\]

This retains the finite endpoint: its contribution has been incorporated exactly into \(a_mC_N\). It also avoids separately bounding potentially poorly conditioned reciprocal factors \(1/(p_jp_{j+1})\).

### A rigorous joint enclosure, without signs for individual \(C_j\)

Put
\[
V_N=\sum_{k=1}^{N}\mu_kv_k^2,\qquad
H_N^\sharp=\sum_{k=1}^{N}\frac{|h_k^\sharp|^2}{\mu_k},
\]
and
\[
\Delta_v=V_N-\frac{\beta_N^2}{M}\ge0,\qquad
\Delta_h=H_N^\sharp-\frac{|C_N|^2}{M}\ge0.
\]
Cauchy–Schwarz applied to (10) yields
\[
\boxed{
\mathfrak M_m-\mathfrak R_m
\le\mathcal Q_m\le
\mathfrak M_m+\mathfrak R_m,
}
\tag{11}
\]
where
\[
\boxed{
\mathfrak M_m=a_m\kappa_mC_N,\qquad
\mathfrak R_m=
|\kappa_m|\sqrt{\Delta_v\Delta_h}.
}
\tag{12}
\]

Equations (7)–(12) hold cellwise throughout the same selected source family. They do not assume a sign for \(\kappa_m\), any \(C_j\), or the full CCM matrix.

The \(\mu\)-inner product is only an auxiliary device for this estimate. **It does not replace the Euclidean CCM norms defining \(X,Y,q_\iota\), or \(z_\iota\).**

For arbitrary forcing vectors with the same \(C_N\) and \(H_N^\sharp\), this radius is sharp: equality occurs when the centered forcing is aligned or antialigned with \(v^\perp\). Those arbitrary vectors are **not** asserted to be admissible selected-source forcing. Thus sharpness explains the information limit of this particular moment certificate; it is not a source counterexample.

## 3. The exact uncontrolled source contributions

The first missing signed input in (11) is
\[
T_m=\kappa_mC_N.
\]
Even controlling it would not suffice without controlling the centered joint contribution
\[
J_m^\sharp
=\kappa_m\langle v^\perp,\eta^\perp\rangle_\mu
=\kappa_m\Delta E\sum_{j=1}^{N-1}
 \frac{S_jE_j^\sharp}{A_jp_jp_{j+1}}.
\tag{13}
\]
These are full-prefix objects, not a return to the old \(k=1\) head test.

Here are their exact source formulas, including the lower moments.

### Literal forcing expansion

For any real coefficient vector \(w=(w_1,\ldots,w_N)\), define
\[
I_m(w)=\sum_{k=1}^{N}w_kh_k^\sharp.
\]
Let
\[
L=\log m,\qquad s_n=\frac12-\frac{2\pi in}{L},
\qquad
\Phi_w(t)=\sum_{k=1}^{N}(-1)^kw_k\mathsf P_{2k}(t).
\]
Then the source incomplete-Mellin formula gives
\[
\boxed{
I_m(w)=\frac{m^{1/4}}{\sqrt L}
\sum_{n=-m}^{m}g_n^\sharp
\sum_{r=1}^{m}r^{-\overline{s_n}}
\int_{r/m}^{1}\Phi_w(t)t^{\overline{s_n}-1}\,dt.
}
\tag{14}
\]
The conjugation, alternating phase, and lower limit are all retained. This is the forcing kernel recorded in the predecessor. 

In this notation,
\[
\boxed{
T_m=\kappa_m I_m(p),\qquad
J_m^\sharp=\kappa_m I_m\!\left(v-\frac{\beta_N}{M}p\right).
}
\tag{15}
\]
The second equality uses \(\langle v^\perp,p\rangle_\mu=0\); it does **not** recompute the forcing for \(v^\perp\).

More explicitly, throughout (14),
\[
\begin{aligned}
g_n^\sharp
=\sum_{n'=-m}^{m}\Bigg[
&Y^2\bigl(K_{\iota,nn'}-\theta\delta_{nn'}\bigr)\\
&+X^2\sum_{a,b=-m}^{m}
\Pi_{na}K_{\iota,ab}\Pi_{bn'}
\Bigg]x_{n'},
\qquad
x_{n'}=\sum_{k'=1}^{N}F_{n'k'}c_{k'}.
\end{aligned}
\tag{16}
\]
Thus the relevant ranges are
\[
\begin{gathered}
m=J_P+\iota+2,\quad N=6m-1,\quad
1\le j<N,\quad 1\le k,k'\le N,\\
-m\le n,n',a,b\le m,\qquad 1\le r\le m.
\end{gathered}
\tag{17}
\]
In particular, every prefix still pairs with the forcing generated by **all** \(k'\) and **all** Fourier modes.

### Both coherent lower moments remain in the centered contribution

Define
\[
\Sigma_0^\sharp=\sum_{n=-m}^{m}g_n^\sharp,\qquad
\Sigma_1^\sharp=\sum_{n=-m}^{m}
(\overline{s_n}-1)g_n^\sharp.
\tag{18}
\]
There is no substitution \(\Sigma_1^\sharp=-\Sigma_0^\sharp/2\).

For \(a_r=r/m\), on \(a_r<t<a_{r+1}\), put
\[
\mathscr H_r^\sharp(t)=
\frac{m^{1/4}}{\sqrt L}
\sum_{n=-m}^{m}g_n^\sharp t^{\overline{s_n}-1}
\sum_{b=1}^{r}b^{-\overline{s_n}},
\qquad 1\le r<m,
\]
and set
\[
A_w(t)=\sum_{k=1}^{N}
\frac{(-1)^kw_k}{2k(2k+1)}\mathsf P_{2k}(t),
\qquad
\mathcal L_L=-\partial_t((1-t^2)\partial_t).
\]
Then \(\mathcal L_LA_w=\Phi_w\). The jumps are exactly
\[
[\mathscr H^\sharp]_{a_r}
=\frac{m^{3/4}}{r\sqrt L}\Sigma_0^\sharp,
\qquad
[(\mathscr H^\sharp)']_{a_r}
=\frac{m^{7/4}}{r^2\sqrt L}\Sigma_1^\sharp.
\]
Consequently,
\[
\boxed{
\begin{aligned}
I_m(w)
={}&\sum_{r=1}^{m-1}
\int_{a_r}^{a_{r+1}}
A_w(t)\,\mathcal L_L\mathscr H_r^\sharp(t)\,dt\\
&+\frac{m^{7/4}}{\sqrt L}
\sum_{r=1}^{m-1}\frac{1-r^2/m^2}{r^2}
\left[
\Sigma_0^\sharp\frac r m A_w'(r/m)
-\Sigma_1^\sharp A_w(r/m)
\right].
\end{aligned}
}
\tag{19}
\]
For completeness, its smooth forcing is
\[
\begin{aligned}
\mathcal L_L\mathscr H_r^\sharp(t)
=\frac{m^{1/4}}{\sqrt L}
\sum_{n=-m}^{m}g_n^\sharp
\left(\sum_{b=1}^{r}b^{-\overline{s_n}}\right)
(\overline{s_n}-1)
\left[
\overline{s_n}t^{\overline{s_n}-1}
-(\overline{s_n}-2)t^{\overline{s_n}-3}
\right].
\end{aligned}
\tag{20}
\]

These follow by linearity from the predecessor’s checked jump/Green identity. Applied to the two vectors in (15), they specify **the signed ground moment and the first centered Abel remainder, each with its smooth and two-moment boundary contributions intact**.  

The \(t=1\) Legendre flux vanishes because \(1-t^2=0\). That does not remove the lower-edge sum, and it does not erase either physical boundary of the logarithmic window.

### MIX, the plane correction, Q6, and prime powers

Equation (16) retains MIX because the full \(x\) remains in the forcing. It retains \(X^2\Pi K_\iota\Pi x\), rather than replacing the forcing by \(Kd\) or by separately computed prefix forcings.

The matrix remains the literal source matrix on \(-m,\ldots,m\):
\[
K_{\iota,nn'}=
W02_{nn'}-WR_{nn'}
-\sum_{\nu=2}^{m}
\frac{\Lambda(\nu)}{\sqrt\nu}
Q_{nn'}(\log\nu),
\tag{21}
\]
with the source’s distinct diagonal branch and complete archimedean entry. The von Mangoldt sum includes every prime power in this finite source range. The general finite wrapper uses precisely these entry constructors.   

The plane data retain the source Q6 correction
\[
d_n=
\left(1+\frac{\omega_n^2-15/4}{16\pi m}\right)b_n^G
-\frac{G'(L/2)}{8\pi m\sqrt L},
\qquad \omega_n=\frac{2\pi n}{L}.
\tag{22}
\]
No edge-free substitute for \(d_n\) or \(\Pi\) is made. Both physical window boundaries remain in the source construction. No global-radical rewrite is used here, so no additional global prime-tail cancellation is silently invoked. 

## 4. Why the existing estimates do not settle (11)

The source-tail budget \(B(m)\) controls the already designated Ferrers truncation error. It does not control \(I_m(p)\), \(I_m(v^\perp)\), or their difference: those are contributions **inside the retained prefix**. Reusing \(B(m)\) as a bound for them would change its domain of validity. The predecessor explicitly leaves its full forcing margin unpaid.  

The accepted weight analysis controls the recurrence-side quantities. In the new enclosure these are \(M,\beta_N,V_N,a_m\). It does not supply a signed lower or upper estimate for
\[
\kappa_mC_N
=\kappa_m I_m(p),
\]
nor a sufficiently small bound for
\[
H_N^\sharp-\frac{|C_N|^2}{M}.
\]
Likewise, positivity of the Robin secant does not determine either forcing quantity. The new positive \(a_m\) therefore cannot be promoted into positivity of \(\mathfrak M_m\), much less of \(\mathcal Q_m\).

A norm-only estimate on \(g^\sharp\) or \(K_\iota\) can bound the radius in (11), but it provides no signed center separated from zero. The required issue is **relative domination**, not merely finiteness of the radius.

Finally, the \(m=13\) reference diagnostics are not being used to establish a source sign, asymptotic, or counterexample. In particular, even the reported alternating prefix signs do not constitute an exact source witness against a universal-sign lemma. Their legitimate role here is the request’s stated guard against assuming such a lemma. :chatgpt-content-reference{index="14"}

Thus the actual remaining comparison is
\[
\boxed{
\mathfrak M_m-\mathfrak R_m>Y^2B(m)
\quad\text{or}\quad
\mathfrak M_m+\mathfrak R_m<-Y^2B(m),
}
\tag{23}
\]
with the prescribed family quantifiers. Neither comparison has been established.

## 5. One discriminating PAPER test

### `TEST_SOURCE_GROUND_CENTERED_ABEL_DISCRIMINANT`

This is cheaper in retained forcing data than controlling every \(C_j\): it needs **one signed moment and one centered norm**, while recurrence-side moments are kept exact. It is a sufficient certificate, not a claimed necessary condition for the full sign.

For one orientation \(\varepsilon\in\{+1,-1\}\), set
\[
\Gamma_m^\varepsilon
=\varepsilon\mathfrak M_m-Y^2B(m),
\]
and test
\[
\boxed{
\Gamma_m^\varepsilon>0,\qquad
(\Gamma_m^\varepsilon)^2
>
\kappa_m^2
\left(V_N-\frac{\beta_N^2}{M}\right)
\left(H_N^\sharp-\frac{|C_N|^2}{M}\right).
}
\tag{24}
\]

**Both inequalities are required.** The squared inequality alone would admit a center on the wrong side.

A pass at \(\varepsilon=+1\) must hold on an explicitly specified unbounded set of selected indices. A pass at \(\varepsilon=-1\) must hold on the entire selected tail. These are the two different quantifier shapes in the request, not interchangeable cellwise choices. :chatgpt-content-reference{index="15"}

To produce a genuine margin, the PAPER certificate must derive explicit source functions \(A(m),R(m)\) such that, on the appropriate indices,
\[
\Gamma_m^\varepsilon\ge A(m),\qquad
\mathfrak R_m\le R(m),\qquad
A(m)>R(m).
\]
Then
\[
\zeta(m)=\frac{A(m)-R(m)}2>0
\]
is justified by those independently proved inequalities, and
\[
\varepsilon\mathcal Q_m>Y^2B(m)+\zeta(m).
\]
Defining \(\zeta\) directly as an unproved separation in (23) is not a certificate.

On the original consumer domain \(Y\rho_m>0\), such a positive-orientation pass gives the first negative sign of \(\tau_\iota\); a negative-orientation pass gives the first positive sign, with the predecessor’s respective bounds
\[
\tau_\iota\le-\frac{\zeta(m)}{Y^2\rho_m^2},
\qquad
\tau_\iota\ge\frac{\zeta(m)}{Y^2\rho_m^2}.
\]
These are conditional consumer implications only. Schur-floor remains separate. 

**Present disposition:** (A), (W), the positive coefficient (8), the exact centered remainder (9), and the enclosure (11) are established by the PAPER derivation above. The signed domination test (24) is not. No full-sign claim and no method-kill follow.

### CODEX DIRECTIVE

**PAPER only:** adjudicate `TEST_SOURCE_GROUND_CENTERED_ABEL_DISCRIMINANT` on the unchanged selected family. Use the exact \(C_N,H_N^\sharp,M,\beta_N,V_N\) above, with \(\beta_N=S_N-1\), and the once-fixed full \(g^\sharp\). Attempt only the signed-moment-versus-centered-norm comparison (24), preserving (14)–(22). A successful delivery must exhibit source-derived uniform estimates and an explicit positive margin with the correct index quantifiers. An exact source failure of (24) refutes **this moment certificate only**, not the full Abel sign. Do not reopen the weight partition, assume common prefix signs, substitute reference forcing, run numerical diagnostics, change repository state, or promote the route.