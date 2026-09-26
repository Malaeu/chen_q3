# STATUS: TRY_GOAL058_SOURCE_CORE_LAG_DECAY

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_CORE_LAG_DECAY
OUTCOME: OPEN_INTERIOR_SQUARE_CORE
REQUEST_ID: REQ-2026-09-26-INTERIOR-SQUARE-CORE-AFTER-ENDPOINT
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_INTERIOR_SQUARE_CORE_AFTER_PAID_ENDPOINT
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 71e056baf76e907468c689204ecc5a0eb1e2876c
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-LARGE-PRIME-SQUARE-INTERIOR-OVERLAP
REQUEST_SHA256_LOCALLY_VERIFIED: f6277f6c11e79f44e6a419fc6286eebf2f2a7112abea05867615057cb80deb74
PREDECESSOR_REQUEST_SHA256_LOCALLY_VERIFIED: 7d64210b75199c2f421ac06289b2d646cbd22a6a9119dc1d38ffaf665f71f064
PREDECESSOR_GIT_BLOB_READ: 0e7b01b7fda145c28576327319b09783c5916ac0
PREDECESSOR_VERDICT_SHA256_PINNED_AUDIT_REPORTED: f14ec30d19415ec331c48c6f0aa84ef496f55d0ba91fc9607ac1573c03f40188
PREDECESSOR_VERDICT_SHA256_LOCALLY_RECOMPUTED: false
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
INTERIOR_SQUARE_CORE_SAVED: NOT_ESTABLISHED
INTERIOR_SQUARE_CORE_LEADING: NOT_ESTABLISHED
ESTABLISHED_C0: NONE
ESTABLISHED_c0: NONE
NEW_SOURCE_ENERGY_BOUND: E11_LE_2_POW_56_TIMES_EXP_MINUS_m_OVER_log_m
NEW_SOURCE_OBSTRUCTION: COMPLETE_T3_BLOCK_HAS_NO_COFINAL_LOWER_ORDER_RELATIVE_BUDGET
OBSTRUCTION_WITNESS: m_p_EQUALS_CEIL_EXP_p_OVER_2_FOR_UNBOUNDED_PRIME_p
REQUESTED_THEOREM_SHAPES_KILLED: NONE
DIAGNOSTIC_THEOREM_SHAPE_REFUTED: SEPARATE_COMPLETE_T3_BLOCK_LOWER_ORDER_BUDGET
PROGRESS_CLASS: FALSIFICATION_PROGRESS
PROGRESS_QUALIFICATION: SOURCE_SPECIFIC_SEPARATE_BLOCK_INTERFACE_ONLY_NOT_CORE_OUTCOME
COGNITIVE_OPERATOR_USED: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4
DISCRIMINATOR: D_m_t_EQUALS_16_E11_MINUS_1_PLUS_t_TIMES_ABS_A_m_t
NEW_PAPER_DERIVATIONS_INDEPENDENTLY_AUDITED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_CUTOFF_SEARCH_EXECUTED: false
LEAN_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
CARRIER_CUTOFF_CHANGED: false
DILATION_BOUNDARY_Q_CHANGED: false
NEW_SEED_SELECTED: false
HONESTY_STATE: CHALLENGER_NOT_RH
EXPONENT_ONE_PRIME_BLOCK: OPEN_SEPARATE
OPPOSITE_SIDE_CORRELATION: OPEN_SEPARATE
INTEGRATED_SYMBOL_DEVIATION: OPEN_SEPARATE
TRANSFER_T: OPEN
ACTUAL_J_SIGN: OPEN
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_INTERIOR_SQUARE_CORE.** Neither requested quantifier for the complete signed core is proved.

There is a new **source-specific analytic obstruction**, not another absolute coefficient-sum estimate: the complete source-source block
\[
S_{3,m}:=4\sum_{p\in\mathcal P_m}(\log p)\widetilde T_{3,p}
\]
has
\[
\frac{|S_{3,m}|}{(1+\log L)E_{11}}\longrightarrow\infty
\]
along an explicitly constructed unbounded subset of the unchanged selected family. Thus an approach assigning separate lower-order relative budgets to all four complete blocks is false already for the third source block. **This is not a leading witness for their signed sum.** The other three blocks remain available to cancel it.

The proof below also gives an explicit upper bound for the actual projection-error energy, retains the finite-window boundary terms, and recombines the four blocks into an exact Fourier-residual representation. One continuous-lag, source-specific candidate lemma is commissioned at the end. It is sufficient, not necessary, and is not claimed proved.

## 1. Source lock and unchanged contract

The full current authoritative TXT was read: **6,539 bytes, 134 LF**. Its SHA-256 was computed locally. The full predecessor source request was also read and locally hashed: **6,136 bytes, 116 LF**. Both hashes appear above. The requested family, source, denominator and endpoint decomposition are fixed by that material. fileciteturn3file0L22-L46 fileciteturn3file1L36-L50

The bootstrap was fetched through the GitHub connector from `rh_clean` and read through its response-format section. The complete predecessor verdict was read at the current pinned commit. I also opened `docs/Codex/PAPER_CHAIN.md`, specifically the requested “large-prime-square interior overlap test” audit. That audit reports **17,402 bytes, 591 LF**, the stipulated predecessor SHA-256, and acceptance of the endpoint result only. The remote SHA-256 is **pinned-audit-reported, not independently recomputed here**; the connector returned the Git blob recorded above. The new mathematical derivations below are not covered by that earlier audit. fileciteturn4file0L2-L4 fileciteturn5file0L2-L4 fileciteturn6file0L2-L2

**[COFINAL_FAMILY | PAPER — admitted source contract]** Fix the same \(P\), and write
\[
m=J_P+j+2\ge2^{16},\quad L=\log m,\quad b=L/2,\quad
Q=\sqrt m,\quad X_2=m^{1/4},\quad \omega_n=2\pi n/L.
\]
All logarithms are natural. Keep the original \(5m\) splice and carrier \(-m\le n\le m\). Put
\[
\mathcal P_m=\{p\text{ prime}:L<p\le X_2\},\qquad
 t_p=2\log p,\quad a_p=b-t_p,\quad w_p=\frac{\log p}{p}.
\]
Keep exactly
\[
g=G'',\quad h=T_mg,\quad f=h-g,\quad E=E_{11}=\|f\|_2^2>0,
\quad \alpha_n=-\omega_n^2b_n,
\quad d=\varepsilon_m\sum_{|n|\le m}\psi_{n,L},
\quad k=f-d.
\]
Here \(k\) is only shorthand for the specified algebraic difference. It is not a replacement source or a replacement denominator. The requested scalar is
\[
V_m^{[0]}=4\sum_{p\in\mathcal P_m}w_p
                 \int_0^{a_p}k(u)k(u+t_p)\,du.
\tag{1}
\]
The exact transfer remains
\[
U_m^{(2)}=V_m^{[0]}+R_{\varepsilon,m}
 +U_{m,\mathrm{small}}^{(2)}+X_{m,\mathrm{large}}
 -L_{m,\mathrm{large}}^{(2)},
\tag{2}
\]
with
\[
|U_m^{(2)}-V_m^{[0]}|
 \le[12(1+\log L)+r_\varepsilon(m)]E,
\quad
r_\varepsilon(m)=\frac{2L}{\sqrt{\pi m\log L}}
 +4\sqrt{\frac5L}+\frac{4\sqrt{15}}L<6.
\tag{3}
\]
The minus sign on the low-frequency term is retained. No bound for translates of \(k\) is imported from the endpoint-profile Gram estimate. fileciteturn3file0L48-L69

## 2. Retained four terms and an exact cancellation-first representation

**[FINITE_CELL | PAPER — exact identities]** Write
\[
\mathcal P(v)=-64v^4+448v^3-660v^2+150v,
\quad h_2(x)=\mathcal P(\pi x^2)e^{-\pi x^2},
\]
\[
s_n=\tfrac12-i\omega_n,\quad
H_2(s;A,B)=\int_A^B h_2(x)x^{s-1}\,dx,
\quad J(\kappa,a)=\int_0^a e^{i\kappa u}\,du,
\quad J(0,a)=a.
\]
The complete source-indexed object remains
\[
\begin{aligned}
\widetilde T_{0,p}[\alpha]
 &=\frac1{Lp}\operatorname{Re}
 \sum_{n,q=-m}^{m}\overline{\alpha_n}\alpha_q(-1)^{q-n}
 e^{i\omega_qt_p}J(\omega_q-\omega_n,a_p),\\
\widetilde T_{1,p}[\alpha]
 &=\frac1{\sqrt L}\operatorname{Re}
 \sum_{n=-m}^{m}\sum_{r\ge1}\overline{\alpha_n}(-1)^n
 (rp^2)^{-s_n}H_2(s_n;rp^2,rQ),\\
\widetilde T_{2,p}[\alpha]
 &=\frac1{\sqrt L}\operatorname{Re}
 \sum_{n=-m}^{m}\sum_{r\ge1}\overline{\alpha_n}(-1)^n
 (p^2)^{s_n-1}r^{-s_n}H_2(s_n;r,rQ/p^2),\\
\widetilde T_{3,p}
 &=\sum_{r,s\ge1}\int_1^{Q/p^2}h_2(rx)h_2(sp^2x)\,dx,\\
V_m^{[0]}
 &=4\sum_{p\in\mathcal P_m}(\log p)
 [\widetilde T_{0,p}[\alpha]-\widetilde T_{1,p}[\alpha]
  -\widetilde T_{2,p}[\alpha]+\widetilde T_{3,p}].
\end{aligned}
\tag{4}
\]
In particular, the literal self diagonal is
\[
\frac{a_p}{Lp}\sum_{n=-m}^{m}\omega_n^4|b_n|^2
                                  \cos(\omega_nt_p).
\tag{5}
\]
These formulas, including their distinct Mellin boundaries and independent indices, are the authoritative formulas—not a new convention. fileciteturn3file0L71-L99

To perform cancellation **before** estimating the four large blocks, extend only the notation for source Fourier coefficients:
\[
e_n=\int_{-b}^{b}g(u)\overline{\psi_{n,L}(u)}\,du,\qquad n\in\mathbb Z.
\]
This does not extend the finite carrier of \(h\). Define
\[
c_{m,n}=
\begin{cases}
\varepsilon_m,&|n|\le m,\\
e_n,&|n|>m.
\end{cases}
\]
Completeness of the Fourier basis on the original window gives
\[
\boxed{
k=-\sum_{n\in\mathbb Z}c_{m,n}\psi_{n,L}
\quad\text{in }L^2([-b,b]),
\qquad
E=E_O+\sum_{|n|>m}|e_n|^2,
\quad E_O=2\int_b^\infty|g(u)|^2du.
}
\tag{6}
\]
This is **Parseval's identity**, the squared-coefficient identity for an orthonormal basis. It uses the actual \(f\), not orthogonality of \(k\).

There is an important nonvanishing check:
\[
\int_{-b}^{b}k(u)\overline{\psi_{n,L}(u)}\,du=-\varepsilon_m\quad(|n|\le m),
\qquad
\int_{-b}^{b}k(u)du=-2G'(b).
\tag{7}
\]
Thus “endpoint-independent coefficient expression” does **not** mean that \(k\) is a pure omitted-mode tail.

For \(0\le t\le b\), define the one-lag correlation
\[
A_m(t)=\int_0^{b-t}k(u)k(u+t)\,du.
\]
Equation (6) gives the exact representation
\[
\boxed{
A_m(t)=\lim_{N\to\infty}\frac1L\operatorname{Re}
\sum_{|n|,|q|\le N}\overline{c_{m,n}}c_{m,q}(-1)^{q-n}
 e^{i\omega_qt}J(\omega_q-\omega_n,b-t).
}
\tag{8}
\]
The limit is justified by \(L^2\) convergence and Cauchy–Schwarz on the overlap interval; no absolute convergence of an infinite double sum is assumed. The diagonal still uses \(J(0,b-t)=b-t\). All four terms in (4) have been combined exactly, not bounded separately or deleted.

## 3. New uniform upper bound for the actual error energy

**[COFINAL_FAMILY | PAPER — new derivation]** The following bound will be used only to expose an invalid separate-block budget:
\[
\boxed{E\le 2^{56}\exp(-m/L),\qquad m\ge2^{16}.}
\tag{9}
\]
It is an **upper** bound. It does not certify a relative bound for the complete core.

### 3.1. Explicit complex-strip majorant from the actual theta source

Twice differentiating the specified source gives
\[
g(z)=e^{z/2}\sum_{r\ge1}\mathcal P(\pi r^2e^{2z})
                                     e^{-\pi r^2e^{2z}}.
\tag{10}
\]
The series and its differentiated series converge locally uniformly for
\(|\operatorname{Im}z|<\pi/4\). Indeed, the real part of each Gaussian exponent is positive there, and any polynomial in \(r\) is dominated by its Gaussian tail. The admitted real evenness extends to this strip by analytic uniqueness.

Put
\[
a=\frac18,\qquad K=2^{25}.
\]
For \(x\ge0\), \(|y|\le a\), and \(R=\pi r^2e^{2x}\),
\[
|\mathcal P(Re^{2iy})|\le1322R^4,\qquad
\operatorname{Re}(Re^{2iy})\ge R/2,
\]
and
\[
R^4e^{-R/2}\le4!\,4^4e^{-R/4}=6144e^{-R/4}.
\]
Since \(r^2\ge r\), the resulting Gaussian sum is at most
\(3e^{-\pi e^{2x}/4}\). Also \(2x\le e^{2x}\), and \(\pi>3\). Consequently, using \(3\cdot1322\cdot6144<2^{25}\), and then evenness,
\[
\boxed{|g(x+iy)|\le K\exp[-e^{2|x|}/2],
\qquad x\in\mathbb R,\ |y|\le a.}
\tag{11}
\]
In particular, the integral of the right side over the real line is at most \(2K\), and
\[
|g(\pm b+iy)|\le Ke^{-m/2}.
\]

### 3.2. The two vertical boundary integrals are retained

For \(n>0\), shift the finite Fourier integral from \([-b,b]\) down to \([-b-ia,b-ia]\). The two vertical sides of the rectangle give, separately, at most
\(Ke^{-m/2}/\omega_n\). Thus
\[
|e_n|\le\frac{2K}{\sqrt L}
       \left(e^{-a\omega_n}+\frac{e^{-m/2}}{\omega_n}\right).
\tag{12}
\]
The same bound holds for \(e_{-n}\). It would be incorrect to discard the second term merely because the real endpoint values match.

Squaring with \((x+y)^2\le2x^2+2y^2\), summing the geometric tail, and using
\(\sum_{n>m}n^{-2}\le1/m\), gives
\[
\sum_{|n|>m}|e_n|^2
\le32K^2e^{-\pi m/(2L)}
 +\frac{4K^2L}{\pi^2m}e^{-m}.
\tag{13}
\]
For the first constant, use
\((1-e^{-x})^{-1}\le1+x^{-1}\) at \(x=\pi/(2L)\), with \(L\ge8\).

For the physical exterior, (11) and \(e^{2s}\ge1+2s\) give
\[
E_O\le2K^2\int_0^\infty e^{-me^{2s}}ds
    \le\frac{K^2}{m}e^{-m}.
\tag{14}
\]
Equations (6), (13), and (14) imply
\[
E\le34K^2e^{-\pi m/(2L)}
  \le2^{56}e^{-m/L},
\]
which proves (9). Both the physical exterior and the finite-contour boundary correction have been accounted for.

## 4. A complete source block is genuinely much larger than the target scale

This section concerns \(S_{3,m}\), **not** \(V_m^{[0]}\).

### 4.1. A fixed positive source interval at the origin

**[ABSTRACT | PAPER — properties of the fixed source]** The explicit polynomial gives
\[
g(0)>8.
\tag{15}
\]
Here is a conservative constant check. On \([3,16/5]\), \(\mathcal P\) is increasing: \(\mathcal P''(3)=-168\), \(\mathcal P'''<0\) there, and \(\mathcal P'(16/5)>1000\). Therefore
\(\mathcal P(\pi)\ge\mathcal P(3)=1422\), and the \(r=1\) contribution exceeds \(1422/64>22\), using \(\pi<4\) and \(e^4<64\).

For \(r\ge2\), \(v=\pi r^2\ge12\), \(\mathcal P(v)<0\), and
\[
|\mathcal P(v)|\le70v^4.
\]
Using \(\pi<16/5\) and \(e^3>20\), the absolute tail is bounded by
\[
7350\sum_{r\ge2}r^8\,20^{-r^2}<13.
\]
The \(r=2\) term is less than 12; for \(r\ge3\) the successive-term ratio is less than \(1/2\), and twice the first such term contributes less than 1. This proves (15) without a numerical source evaluation.

Cauchy's derivative estimate on a complex disk of radius \(1/16\), using (11), gives
\[
|g'(u)|\le16K\quad(u\in\mathbb R).
\]
Hence, with
\[
\delta=\frac1{4K}=2^{-27},
\]
we have
\[
\boxed{g(u)\ge4\quad(0\le u\le\delta),\qquad |g(u)|\le K.}
\tag{16}
\]

### 4.2. A newly derived source decay rate at a prime-square shift

**[ABSTRACT | PAPER — new source estimate]** Put \(\mathcal A(v)=-\mathcal P(v)\). For \(v\ge32\),
\[
32v^4\le\mathcal A(v)\le128v^4,
\qquad \mathcal A'(v)\le264v^3.
\]
An individual positive summand of \(-g(u)\) therefore satisfies
\[
\frac{d}{du}\log\bigl(e^{u/2}\mathcal A(v)e^{-v}\bigr)
 =\frac12+\frac{2v\mathcal A'(v)}{\mathcal A(v)}-2v
 \le17-2v\le-v,
\quad v=\pi r^2e^{2u}.
\]
For \(p\ge2\), \(t=2\log p\), and \(F(u)=-g(u)\) on \([t,\infty)\), it follows that
\[
F(u)>0,\qquad
F(u+s)\le e^{-\pi p^4s}F(u)
\quad(u\ge t,\ s\ge0).
\tag{17}
\]
This is derived directly from the source polynomial. Its rate is **\(\pi p^4\), not \(\pi m\)**. The old exterior estimate is not being extended into the original window.

At the starting point,
\[
F(t)\le256\pi^4p^{17}e^{-\pi p^4}.
\tag{18}
\]
For this bound use \(\sum_{r\ge1}r^8e^{-Vr^2}\le2e^{-V}\) for \(V\ge32\); it follows from \(r^8\le e^{4(r^2-1)}\) and a geometric majorant.

Set \(h_p=p^{-4}\). On \(0\le s\le h_p\), the first source summand alone and \(e^{2h_p}\le1+4h_p\) yield
\[
F(t+s)\ge32\pi^4p^{17}e^{-\pi p^4-4\pi}.
\tag{19}
\]

### 4.3. A signed bound with all of the integration domain retained

**[ABSTRACT | PAPER — new source correlation bound]** For \(p\ge256\), \(h_p\le\delta\). Define
\[
I_g(p,a)=\int_0^a g(u)g(u+2\log p)\,du,
\qquad a\ge0.
\]
The part \([0,h_p]\), using (16) and (19), contributes at most minus
\[
M_p:=128\pi^4e^{-4\pi}p^{13}e^{-\pi p^4}.
\]
On \([h_p,\delta]\), the contribution has the same nonpositive sign. The entire possible contribution with the opposite sign, from \([\delta,\infty)\), has absolute value at most
\[
K\int_\delta^\infty F(t+u)du
\le256K\pi^3p^{13}e^{-\pi p^4}e^{-\pi p^4\delta}.
\]
Its ratio to \(M_p\) is at most
\[
\frac{2K}{\pi}e^{4\pi}e^{-\pi p^4\delta}<\frac12,
\qquad p\ge256.
\tag{20}
\]
For an explicit check, \(p^4\delta\ge32\), \(e^{16}<2^{24}\), and \(e>2\) bound this ratio by \(2^{50-96}\).

If \(0<a<h_p\), the integrand already has the negative sign throughout. For \(a\ge h_p\), the estimate just obtained bounds all possible later compensation. Thus, with the explicit constant
\[
C_g=64\pi^4e^{-4\pi}>0,
\]
we have proved
\[
\boxed{
I_g(p,a)\le0\quad(a\ge0),\qquad
I_g(p,a)\le-C_gp^{13}e^{-\pi p^4}
                       \quad(a\ge p^{-4}),\quad p\ge256.
}
\tag{21}
\]
In particular, the upper envelope in the second assertion is strictly negative. This is a signed proof for this source-source correlation only.

### 4.4. Transfer to the actual indexed \(T_3\) block and an unbounded selected set

**[FINITE_CELL | PAPER — exact source change of variables]** Formula (10) on the real axis and \(x=e^u\) give
\[
I_g(p,a_p)=p\sum_{r,s\ge1}\int_1^{Q/p^2}
                         h_2(rx)h_2(sp^2x)dx
          =p\widetilde T_{3,p}.
\tag{22}
\]
The factor \(p\) comes from \(e^{t_p/2}\). All \(r,s\ge1\) and the exact upper endpoint remain. Fixed-cell interchanges follow from polynomial-Gaussian absolute majorants on \(x\ge1\).

For \(L\ge256\), every term of \(S_{3,m}\) is nonpositive by (21). If any allowed prime \(p\) has \(a_p\ge p^{-4}\), then
\[
\boxed{|S_{3,m}|\ge4C_g(\log p)p^{12}e^{-\pi p^4}.}
\tag{23}
\]
This bound is on the complete block, not just on an integrand majorant or a single unsigned summand.

**[COFINAL_FAMILY | PAPER — explicit obstruction witnesses]** For primes \(p\ge1024\), take
\[
m(p)=\lceil e^{p/2}\rceil,\qquad
j(p)=m(p)-J_P-2,
\]
retaining exactly those with \(j(p)\ge0\). Infinitely many primes exist, so these are an explicitly proved unbounded set of selected indices. No trial vector, source, or seed changes.

Here
\[
\frac p2\le L(p)\le\frac p2+1<p,
\qquad p<X_2(m(p)),
\qquad a_p\ge\frac p4-2\log p\ge\frac p8\ge p^{-4}.
\tag{24}
\]
The middle inequality follows from \(e^{p/8}>p\); the last uses \(\log p\le p/16\) for \(p\ge1024\). In particular \(L(p)\ge512\), so every source-source term in this selected cell has the nonpositive sign required in (23).

Combining (9) and (23),
\[
\boxed{
\frac{|S_{3,m(p)}|}{(1+\log L(p))E_{m(p)}}
\ge\frac{C_g}{2^{54}}
\frac{(\log p)p^{12}}{1+\log L(p)}
\exp\left(\frac{m(p)}{L(p)}-\pi p^4\right)
\longrightarrow\infty.
}
\tag{25}
\]
Indeed \(m(p)/L(p)\ge e^{p/2}/p\), which dominates every fixed power of \(p\). This proves the quantified obstruction:
\[
\boxed{\text{There are no finite }C_3,m_3\text{ such that }
|S_{3,m}|\le C_3(1+\log L)E
\text{ for every admitted selected }m\ge m_3.}
\tag{26}
\]
The theorem shape refuted in (26) is a **separate complete-block budget**. It is not either requested assertion about \(V_m^{[0]}\).

## 5. The first unpaid comparison, and what the obstruction does not prove

**[COFINAL_FAMILY | PAPER]** Define \(S_{i,m}\) by the common factor \(4\sum_{p\in\mathcal P_m}\log p\) applied to the corresponding complete term in (4). The first unpaid source-signed comparison is
\[
\boxed{(S_{0,m}+S_{3,m})-(S_{1,m}+S_{2,m})
       \quad\text{at the actual }(1+\log L)E\text{ scale}.}
\tag{27}
\]
Equivalently, one must control the exact \(c_{m,n}\)-weighted off-diagonal and diagonal expression (8) at the prime-square lags, before applying the positive weights.

Equation (26) rules out the specific triangle strategy
\(|V_m^{[0]}|\le\sum_{i=0}^3|S_{i,m}|\) followed by four separate lower-order relative budgets. It does **not** rule out a signed estimate for (27), pairwise cancellation, or a more direct estimate of (8).

The inverse-dilation source term still has its actual moving restriction. With
\[
H_\alpha(y)=y^{-1/2}\sum_{|n|\le m}\alpha_n\psi_{n,L}(\log y),
\qquad F_+(x)=\sum_{r\ge1}h_2(rx),
\]
its weighted sum remains
\[
\int_1^Q H_\alpha(y)
 \sum_{\substack{L<p\le X_2\,;\ p\text{ prime}\\p^2\le y}}
 \frac{\log p}{p^2}F_+(y/p^2)dy.
\tag{28}
\]
No all-divisor identity has replaced this restricted weight. At \(p^2=Q\), the interior overlap is zero; the earlier exterior strips are still in (2).

Neither the endpoint bound, the previously paid frequency shoulder, nor full-window projection orthogonality controls (27). The new energy **upper** bound (9) likewise supplies no lower witness for it. The constructed unbounded set witnesses (26) only. **There is no established \(C_0,m_0\), no established \(c_0>0\), and no leading selected-index set for the requested core.**

## 6. One falsifiable source-specific lemma, with an explicit consumer

### TEST_SOURCE_CORE_CONTINUOUS_LAG_DECAY

**[COFINAL_FAMILY | CONDITIONAL — proposed, not proved]** Test the fixed candidate
\[
\boxed{(1+t)|A_m(t)|\le16E,
\quad m=J_P+j+2\ge65536,
\quad 2\log L\le t\le b.}
\tag{29}
\]
Use exactly (8), or the equivalent physical kernel below. This tests one translated correlation of the **actual** error, before any prime summation. It is not a renaming of the weighted square scalar: it is a stronger continuous-lag assertion with no arithmetic weights. Its proof would decide the saving outcome; its failure would refute only this fixed sufficient candidate.

The constant 16 and threshold 65536 are part of this proposed test, **not fitted constants or proved estimates**. Do not silently adjust them after a counterexample. The discriminating functional is
\[
D_m(t)=16E-(1+t)|A_m(t)|.
\tag{30}
\]
A proved nonnegative lower envelope for all stated \((m,t)\) establishes the candidate. A proved negative upper envelope at a permitted \((m,t)\) refutes the fixed candidate, not the existence of some other saving constant or threshold for the core.

### Exact implication to the requested saving

**[COFINAL_FAMILY | PAPER — conditional implication proved here]** The predecessor's elementary weight estimate is
\[
S(x):=\sum_{p\le x}\frac{\log p}{p}\le2\log x+2\log2,
\qquad x\ge2.
\]
It is an admitted arithmetic upper bound, not a multiplier-sign theorem. fileciteturn1file0L2-L2

Partial summation, using \(S(x)\le2(1+2\log x)\), gives
\[
\begin{aligned}
\sum_{p\le X_2}\frac{\log p}{p(1+2\log p)}
&=\frac{S(X_2)}{1+2\log X_2}
 +\int_2^{X_2}\frac{2S(x)}{x(1+2\log x)^2}dx\\
&\le2+2\log\frac{1+2\log X_2}{1+2\log2}
\le2(1+\log L).
\end{aligned}
\tag{31}
\]
Since every requested lag lies in the band of (29), that candidate would imply
\[
|V_m^{[0]}|\le64E\sum_{p\in\mathcal P_m}\frac{w_p}{1+t_p}
             \le128(1+\log L)E.
\tag{32}
\]
Only **if (29) is proved**, the requested constants would therefore be
\[
C_0=128,\qquad C_{\mathrm{int}}=134,\qquad C_2=146,
\quad m_0=65536
\]
on the admitted selected tail. These are a proved implication, not an established saving.

For comparison, any independently proved core-leading witness with constant \(c_0\) would still require the exact subtraction
\[
|U_m^{(2)}|\ge
[c_0\ell_m-r_\varepsilon(m)-12(1+\log L)]E,
\]
and the tail condition
\[
r_\varepsilon(m)+12(1+\log L)\le\tfrac12c_0\ell_m
\tag{33}
\]
before a square-leading conclusion. No such core witness is obtained from \(S_3\).

### Two representations of this one test

| Representation | Decisive power | PAPER cost and principal risk |
|---|---|---|
| **Chosen: exact Fourier residual (6)–(8).** The four large source blocks cancel before estimation. | A proof of the single uniform lag envelope closes the requested square saving through (31)–(32). An exact violation rejects the fixed candidate. | One source coefficient estimate and one two-variable correlation estimate. Must retain the low block \(c_{m,n}=\varepsilon_m\), the literal diagonal, and the finite-window overlap. |
| **Alternative: differentiated projection kernel.** Put \(K_m(u,v)=L^{-1}D_m(2\pi(u-v)/L)\); then \(k(u)=\int_{-b}^b\partial_u^2K_m(u,v)G(v)dv-G''(u)\) inside the window. | The same lag bound could follow directly from cancellation in this exact source integral, without separate budgets for (4). | Two coupled source integrals with moving boundaries. Applying absolute values before subtracting the source recreates the obstruction (26). |

The alternative is a representation of the same test, not a second commissioned campaign. The continuous-lag condition is stronger than the arithmetic-weighted requirement and is not declared necessary for the downstream consumer.

## 7. Adversarial controls, predictions, and closeout

**[ABSTRACT | PAPER — planted failure control]** High Fourier frequency alone cannot prove (29). On a window of length \(L\), take the diagnostic function
\(q(u)=\cos(2\pi Nu/L)\), with \(N>m\) divisible by four. It is orthogonal to the original carrier. At \(t=L/4\),
\[
\int_0^{b-t}q(u)q(u+t)du=L/8,
\qquad \|q\|_{L^2([-b,b])}^2=L/2.
\]
Thus
\[
\frac{(1+t)|\int_0^{b-t}qq_t|}{\|q\|_2^2}
=\frac{1+L/4}{4}\longrightarrow\infty.
\tag{34}
\]
For sufficiently large \(L\), this lag lies in the proposed band. This is a counterexample to a **generic high-pass argument**, not a counterexample using the fixed theta source. It forces the proposed proof to use the actual coefficients in (6), rather than their support alone.

**[FINITE_CELL | PAPER — boundary and normalization controls]** At \(t=b\), (8) is zero. For diagonal terms, \(J(0,b-t)=b-t\), not a divided-difference guess. The two vertical contour contributions in (12) remain. The new decay estimate (17) has its own proved \(p^4\) rate and is not an extrapolation of the old \(m\) rate. The denominator remains \(E\), with its physical exterior in (6). No physical square head is equated with its high-frequency part without (2).

**Prediction scoring.** The intake expectation that exact projection cancellation would expose a translated-error comparison rather than settle its sign is **confirmed** by (6)–(8); (7) also blocks a pure-high-pass shortcut. The subsequently registered expectation that the complete source-source block can exceed the actual lower-order energy scale by an unbounded factor is **confirmed** by the explicit selected-source witnesses (24)–(25). The fixed lag candidate (29) remains **UNTESTED / NOT_PROVED**; no successful prediction is retroactively assigned to it.

**What became smaller:** the admissible proof strategies. A separate lower-order budget for the complete source-source block is now mathematically refuted on the actual selected family, not merely unavailable. The exact cancellation-first representation identifies where an alternative proof must act.

**What did not close:** either requested quantified outcome for the core. No whole-square, whole-head, transfer, floor, or RH claim follows.

**Cross-domain checks:** the finite-window Fourier representation is an exact form identity; the attempted vanishing mechanism leaves the nonzero low block (7); the proposed family-deciding object is the source-specific lag envelope (29). The planted mode (34) prevents promotion to a general operator assertion.

```yaml
DOWNSTREAM_CONSUMER: high_frequency_prime_square_supplier_for_the_same_side_head
ACTUAL_CONSUMER_REQUIREMENT: paid_control_of_complete_signed_square_contribution
ORIGINAL_REQUESTED_OBJECT: lower_order_core_saving_or_unbounded_core_leading_witness
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: separate_square_saving_is_not_proved_necessary_for_joint_head_control
KNOWN_WEAKER_INTERFACES:
  - arithmetic_weighted_core_control_can_hold_without_uniform_continuous_lag_decay
  - joint_prime_plus_square_control_can_allow_compensation_between_components
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_COMPARISON: equation_27_with_complete_indexed_terms_4
MINIMAL_MISSING_ESTIMATE: signed_actual_coefficient_correlation_at_prime_square_lags_relative_to_E11
DIAGNOSTIC_KILL:
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: EXPLICIT_UNBOUNDED_SELECTED_SOURCE_COUNTEREXAMPLE_SET
  EXACT_REFUTED_STATEMENT: equation_26_separate_complete_T3_lower_order_budget
  EVIDENCE_REFERENCE: this_verdict_equations_9_21_24_25
  SOURCE_REFERENCE: authoritative_TXT_at_SOURCE_COMMIT_with_request_SHA256_above
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER
  REACHES_REQUESTED_CORE_NEGATION: false
CONTINUOUS_LAG_CANDIDATE:
  STATUS: NOT_PROVED
  CONSTANT: 16
  THRESHOLD: 65536
  DOMAIN: 2_log_log_m_LE_t_LE_log_m_over_2
  SCOPE: COFINAL_FAMILY
  VERIFIER: CONDITIONAL
  SUFFICIENT_NOT_NECESSARY: true
  PROVED_IMPLICATION: candidate_implies_C0_128_Cint_134_C2_146
NEXT_TEST: TEST_SOURCE_CORE_CONTINUOUS_LAG_DECAY
DISCRIMINATOR: equation_30_with_actual_source_coefficients_6
REOPEN_TRIGGER: uniform_source_lag_lower_envelope_or_direct_joint_core_estimate_or_true_core_leading_witness
NOVELTY_AXIS: explicit_source_energy_upper_envelope_and_complete_T3_budget_counterexample
MEMORY_ENTRY:
  target: selected_interior_square_core_after_paid_endpoint
  status: OPEN
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  invariant_learned: source_source_block_can_dwarf_actual_error_while_joint_core_remains_unsettled
  forbidden_future_move: infer_core_leading_from_a_large_signed_source_subblock
  next_decisive_test: TEST_SOURCE_CORE_CONTINUOUS_LAG_DECAY
```

The exponent-one prime block and possible prime/square compensation, opposite-side correlation, integrated symbol deviation, transfer, actual \(J_m\) sign, first \(\tau_j\) sign, Schur-floor, and RH remain open as required. fileciteturn3file0L128-L134

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_CORE_CONTINUOUS_LAG_DECAY`, on PAPER, for the fixed candidate (29), using the exact source coefficients (6) and correlation (8), or the equivalent differentiated projection kernel.** First audit the new source obstruction (9)–(26) at its stated separate-block scope; do not accept it as a core-leading witness. For the lag candidate, establish a nonnegative lower envelope for (30) on every admitted selected \(m\ge65536\) and the full stated lag interval, or give an exact source-based violation and report failure of this fixed sufficient candidate only. A proof transfers with the conditional constants in (32); failure does not negate the original saving or authorize a new constant without a new registration. Retain the original \(E\), the low \(\varepsilon_m\) block in (6), independent Fourier indices, both mixed terms, all \(r,s\ge1\), the literal diagonal, \(p^2\le Q\), the moving \(p^2\le y\) boundary, and the signed transfer (2). No mathematical runtime, numerical cutoff search, Lean, repository write, new seed, source/carrier/\(Q\) replacement, route promotion, or RH claim.
