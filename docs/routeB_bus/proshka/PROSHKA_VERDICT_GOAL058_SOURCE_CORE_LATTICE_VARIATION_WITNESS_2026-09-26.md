# STATUS: TRY_GOAL058_SOURCE_CORE_FINITE_COEFFICIENT_PANEL_MARGIN

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_CORE_FINITE_COEFFICIENT_PANEL_MARGIN
OUTCOME: OPEN_SOURCE_LATTICE_WITNESS
REQUEST_ID: REQ-2026-09-26-SOURCE-CORE-LATTICE-VARIATION-WITNESS
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CORE_LATTICE_VARIATION_WITNESS
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: a351ebed7cba25e98f2d0d67b318e1658b916e63
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-SOURCE-CORE-HALF-LINE-DENSITY-VARIATION
REQUEST_SHA256_LOCALLY_VERIFIED: 15efeb5d6aa109cbaed63ebc9dc00cef8ac70745d114a6e87dcbf2b00f510539
REQUEST_BYTES: 5700
REQUEST_LF: 109
PREDECESSOR_VERDICT_SHA256_LOCALLY_VERIFIED: 575b7b2a88916b4d245a9d030ed2abf0e87530c895f8f70cfb41baaa769ba170
PREDECESSOR_BYTES: 33800
PREDECESSOR_LF: 686
PREDECESSOR_GIT_BLOB_LOCALLY_AND_REMOTELY_MATCHED: 19ac31acda7ac5eb76a400c94c0e2d1d84b5da4a
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
AUDIT_READ: docs/Codex/PAPER_CHAIN.md_source_core_half_line_density_variation_test_at_SOURCE_COMMIT
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
SOURCE_NEGATIVE_FIXED_PANEL_MARGIN: NOT_ESTABLISHED
FIXED_PANEL_WITNESS_EXCLUDED: NOT_ESTABLISHED
SV: OPEN
ORIGINAL_CONTINUOUS_LAG_TEST: OPEN
FROZEN_PANEL: j0_EQUALS_0_AND_js_EQUALS_m_PLUS_s_FOR_1_LE_s_LE_CEIL_log_m
COEFFICIENT_SPLIT: "K = ceil(L) + ceil(L^4), L = log(m)"
NEW_PAID_REMAINDER: ABS_U_lattice_MINUS_U_K_LE_eta_m_TIMES_E11_LT_E11_OVER_48
ETA_m: "1/(4*sqrt(2*L)) + 1/(24*L^2)"
ETA_TENDS_TO_ZERO: true
ADDITIONAL_EXACT_BOUND: FINITE_PREFIX_LOWER_ENVELOPE_FOR_U_lattice_WITH_TAIL_ENERGY_ELIMINATED
PROGRESS_CLASS: REPRESENTATION_PROGRESS
PROGRESS_QUALIFICATION: PAID_FINITE_COEFFICIENT_REDUCTION_NOT_A_SOURCE_SIGN_DECISION
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
ROUTE_SCORE: 3
DISCRIMINATOR: U_lattice_EQUALS_16_E11_MINUS_M_MINUS_W
NEXT_TEST: TEST_SOURCE_CORE_FINITE_COEFFICIENT_PANEL_MARGIN
NEXT_TEST_DISCRIMINATOR: INTERVAL_U_K_MINUS_eta_E_TO_U_K_PLUS_eta_E
REQUESTED_THEOREM_SHAPES_KILLED: NONE
FIXED_PANEL_CHANGED: false
SOURCE_FAMILY_CHANGED: false
CARRIER_CUTOFF_CHANGED: false
DILATION_BOUNDARY_Q_CHANGED: false
DENOMINATOR_CHANGED: false
SOURCE_r_SERIES_TRUNCATED: false
LOW_EPSILON_BLOCK_DROPPED: false
NEW_SEED_SELECTED: false
C0_128: CONDITIONAL_NOT_ACTIVATED
C_INT_134: CONDITIONAL_NOT_ACTIVATED
C2_146: CONDITIONAL_NOT_ACTIVATED
NEW_PAPER_DERIVATIONS_INDEPENDENTLY_AUDITED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_SEARCH_EXECUTED: false
LEAN_EXECUTED: false
LOCAL_FILE_IO_TEXT_VALIDATION_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
HONESTY_STATE: CHALLENGER_NOT_RH
EXPONENT_ONE_PRIME_BLOCK: OPEN_SEPARATE
PRIME_SQUARE_COMPENSATION: OPEN_SEPARATE
OPPOSITE_SIDE_CORRELATION: OPEN_SEPARATE
INTEGRATED_SYMBOL_DEVIATION: OPEN_SEPARATE
TRANSFER_T: OPEN
ACTUAL_J_SIGN: OPEN
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_SOURCE_LATTICE_WITNESS.** I have not proved a negative margin for the actual source, and I have not excluded a negative margin for every admitted selected cell. In particular, I do **not** conclude that the frozen panel is powerless on this source.

The new result is a **paid finite-coefficient reduction of this very panel**. It does not choose different sample points. Let
\[
N=\lceil L\rceil,\qquad K=N+\lceil L^4\rceil.
\]
Using the complete source coefficients through the offset \(K\), the full low block, and both signs of the Fourier index, define \(U_m^{[K]}\) below. The argument proves
\[
\boxed{
|U_m^{\mathrm{lattice}}-U_m^{[K]}|
\le\eta_m E<\frac{E}{48},\qquad
\eta_m=\frac1{4\sqrt{2L}}+\frac1{24L^2}\longrightarrow0
}
\tag{A}
\]
for **every admitted selected \(L>120\)**. Every omitted coefficient is accounted for in this bound. The original denominator, physical exterior, zero-frequency value, and final descent in the panel remain.

A second bound eliminates the unknown coefficient-tail energy altogether from a **lower envelope for the panel margin**, by completing a square. Its sign on the source is also unpaid. These are new analytic enclosures, not a decision of the requested source sign and not a proof of SV.

## 1. Source lock and scope

**[FINITE_CELL | PAPER — transport record]** I read the complete authoritative TXT: **5,700 bytes, 109 LF**. Its locally computed SHA-256 is in the header. I also read the complete mounted predecessor: **33,800 bytes, 686 LF**. Its locally computed SHA-256 equals the requested value, and its locally computed Git blob equals the blob returned at the pinned repository commit. This locks the complete local predecessor, rather than a truncated preview, to the requested repository object. The request ID, boundary, pin, and predecessor agree with the canonical instruction. fileciteturn15file0L1-L20 fileciteturn17file0L3-L5

The bootstrap was fetched from `rh_clean` through the GitHub connector and read through its response-format section. I opened the specifically requested `docs/Codex/PAPER_CHAIN.md` at the current pin, including the complete audit headed **“source core half-line density variation test.”** It accepts the proper central-region bounds and the exact lattice identities, not a full variation budget or an actual negative witness. Its bound is \(E/\sqrt6\), **not** \(E/6\). That audit does not cover the new estimates in this verdict. fileciteturn16file0L2-L4 fileciteturn18file0L2-L2

**[COFINAL_FAMILY | PAPER — admitted contract]** Fix the same \(P\), and keep
\[
m=J_P+j+2,\quad L=\log m>120,\quad b=L/2,\quad Q=\sqrt m,
\quad\omega_n=2\pi n/L.
\]
The original \(5m\) splice and carrier \(|n|\le m\) are unchanged. Keep exactly
\[
\begin{aligned}
h_*(x)&=(24\pi x^2-16\pi^2x^4)e^{-\pi x^2},\\
G(u)&=e^{u/2}\sum_{r\ge1}h_*(re^u),\qquad g=G'',\\
h&=T_mg,\quad f=h-g,\quad E=\|f\|_{L^2(\mathbb R)}^2>0,\\
\psi_{n,L}(u)&=L^{-1/2}e^{i\omega_n(u+b)}\mathbf1_{[-b,b]}(u),\\
\varepsilon&=2G'(b)/\sqrt L,\quad
 d=\varepsilon\sum_{|n|\le m}\psi_{n,L},\quad k=f-d,\\
E_O&=2\int_b^\infty|g(u)|^2du,\quad
 D_d=(2m+1)\varepsilon^2<3E/L,\\
v&=\mathbf1_{[0,b]}k,\quad
 M=\|v\|_2^2=(E-E_O+D_d)/2.
\end{aligned}
\tag{1}
\]
These are the real, even source and projection specified in the request. The half-window function \(v\) is real; it need not be even. Every normalization below continues to use \(E\), not \(M\), a finite coefficient energy, or the norm of a replacement function. fileciteturn15file0L31-L57

**Registration.** Before the tail-reduction test, I registered the expectation that the contribution of discarded coefficient indices could be bounded without settling the source sign. The fixed panel was retained before any such work. No source coefficient, sample value, selected cell, or fitted parameter was numerically evaluated. The analytical split \(K=N+\lceil L^4\rceil\) is only a split inside the exact Cauchy sums; it is not a new carrier or a new panel.

## 2. Recheck the lattice phases, normalization, and direction

### 2.1. Literal source coefficients and grid values

**[COFINAL_FAMILY | PAPER]** For every integer \(n\), keep
\[
e_n=\int_{-b}^b g(u)\overline{\psi_{n,L}(u)}du,\qquad
c_n=\begin{cases}\varepsilon,&|n|\le m,\\e_n,&|n|>m.\end{cases}
\tag{2}
\]
The coefficients are real and even in \(n\). In \(L^2([-b,b])\),
\[
k=-\sum_{n\in\mathbb Z}c_n\psi_{n,L}.
\]
The exact source formula is
\[
\begin{aligned}
\mathcal P(x)&=-64x^4+448x^3-660x^2+150x,\\
e_n&=\frac{2(-1)^n}{\sqrt L}\sum_{r\ge1}\int_0^b
 e^{u/2}\mathcal P(\pi r^2e^{2u})e^{-\pi r^2e^{2u}}
 \cos(\omega_nu)\,du.
\end{aligned}
\tag{3}
\]
All source indices \(r\ge1\) remain in every occurrence of \(e_n\). On a fixed window the polynomial-Gaussian majorant permits this source interchange. Formula (3) supplies exact coefficients; it does not itself supply their required relative sign comparison. fileciteturn15file0L43-L51

Set \(\Psi=\widehat v\), with the unitary Fourier convention, and \(\rho=|\Psi|^2\). For a lattice index \(j\),
\[
J_0(\omega_n-\omega_j,b)=
\begin{cases}
b,&n=j,\\
0,&n-j\ne0\text{ even},\\
iL/[\pi(n-j)],&n-j\text{ odd}.
\end{cases}
\tag{4}
\]
In the odd case \((-1)^n=-(-1)^j\). Therefore, with
\[
H_{m,j}=\sum_{n-j\text{ odd}}\frac{c_n}{n-j},
\]
one gets
\[
\Psi(\omega_j)
=-\frac{(-1)^j}{\sqrt{2\pi L}}
 \left[bc_j-i\frac L\pi H_{m,j}\right],
\]
and hence
\[
\boxed{R_{m,j}=\rho(\omega_j)
=\frac L{8\pi}c_j^2+\frac L{2\pi^3}H_{m,j}^2.}
\tag{5}
\]
The single Cauchy sum is absolutely convergent by \(c\in\ell^2\) and the square summability of \(1/(n-j)\) on the odd differences. The original Fourier expansion may first be restricted to finite partial sums and then passed to the limit through a bounded half-window integration functional. No absolute convergence of an infinite double product is assumed.

The diagonal in (5) is separate from the odd-difference sum: \(n=j\) is not an odd difference. The square of \(H_{m,j}\) retains its independent coefficient indices and cross terms. This checks the factors required by the request. fileciteturn15file0L61-L66 fileciteturn15file0L95-L99

At zero, symmetry gives \(H_{m,0}=0\), so
\[
R_0:=R_{m,0}=\frac{L\varepsilon^2}{8\pi}
=\frac{G'(b)^2}{2\pi}.
\tag{6}
\]
The independent physical check is \(\int_0^b k=-G'(b)\). Thus zero frequency is retained, not silently set to zero.

### 2.2. The panel is unchanged

**[COFINAL_FAMILY | PAPER]** Write
\[
N=\lceil L\rceil,\qquad R_s=R_{m,m+s}\quad(1\le s\le N),
\]
and retain the requested functional
\[
W=2\left[|R_1-R_0|+
 \sum_{s=1}^{N-1}|R_{s+1}-R_s|+R_N\right].
\tag{7}
\]
The predecessor's \(W^{1,1}\) density, its evenness, and its zero limits at infinity imply
\[
\mathcal V:=\int_{\mathbb R}|\rho'|\ge W,
\quad
\Delta^{\rm var}:=16E-M-\mathcal V
\le U:=16E-M-W.
\tag{8}
\]
The last \(R_N\) is the required descent to infinity. It is part of the functional in every subsequent formula. A positive \(U\) does not certify \(\Delta^{\rm var}\). fileciteturn15file0L68-L87

### 2.3. An exact lattice mass identity

**[COFINAL_FAMILY | PAPER — new use of Parseval]** Regard \(v\) as a function on \([-b,b]\), zero on its negative half. Its coefficient in the original orthonormal basis is
\[
\langle v,\psi_{j,L}\rangle
=(-1)^j\sqrt{\frac{2\pi}{L}}\,\Psi(\omega_j).
\]
Parseval on this interval gives
\[
\boxed{\sum_{j\in\mathbb Z}R_{m,j}=\frac L{2\pi}M.}
\tag{9}
\]
Since \(v\) is real, \(R_{m,-j}=R_{m,j}\). In particular,
\[
\boxed{
\sum_{s=1}^N R_s
\le\sum_{j=1}^\infty R_{m,j}
=\frac{LM}{4\pi}-\frac{R_0}{2}
\le\frac{L+3}{8\pi}E.
}
\tag{10}
\]
The factor of two in the positive-frequency sum is important. The mass identity (1), including \(E_O\), is used only for the last upper bound. Equation (10) will pay the amplification of a coefficient-tail error; it is **not** used to decide the panel margin.

## 3. Exact pairing of the positive and negative source tails

**[COFINAL_FAMILY | PAPER — new representation]** Define only an offset notation
\[
a_q=e_{m+q},\qquad q=1,2,\ldots.
\]
These are exactly (3), with \(n=m+q\); they are not freely chosen coefficients. Evenness, (1), and Parseval give
\[
\boxed{E=E_O+2\sum_{q\ge1}a_q^2.}
\tag{11}
\]
Equivalently, \(2M=D_d+2\sum a_q^2\), consistent with (1). The physical exterior has not become coefficient energy.

For a fixed panel offset \(s\), put
\[
\sigma_{m,s}=\sum_{\substack{s\le \nu\le2m+s\\\nu\text{ odd}}}\frac1\nu,
\qquad
\mathcal K_{m,s}(q)=\frac1{q-s}-\frac1{2m+q+s}
\quad(q-s\text{ odd}).
\tag{12}
\]
No value at \(q=s\) is needed: that difference is even and excluded. Pairing the terms with original indices \(m+q\) and \(-m-q\), and retaining the complete low block, yields exactly
\[
\boxed{
H_{m,m+s}=-\varepsilon\sigma_{m,s}
+\sum_{\substack{q\ge1\\q-s\text{ odd}}}
 a_q\mathcal K_{m,s}(q).
}
\tag{13}
\]
The minus sign in the low block comes from \(n-(m+s)<0\) for every \(|n|\le m\). The second denominator in \(\mathcal K\) is the entire negative-index contribution; it has not been dropped.

For any integer \(K>N\), define the auxiliary finite expressions
\[
\begin{aligned}
H_s^{[K]}&=-\varepsilon\sigma_{m,s}
 +\sum_{\substack{1\le q\le K\\q-s\text{ odd}}}
 a_q\mathcal K_{m,s}(q),\\
B_s^{[K]}&=\sum_{\substack{q>K\\q-s\text{ odd}}}
 a_q\mathcal K_{m,s}(q),\\
R_s^{[K]}&=\frac L{8\pi}a_s^2
            +\frac L{2\pi^3}(H_s^{[K]})^2.
\end{aligned}
\tag{14}
\]
Then \(H_{m,m+s}=H_s^{[K]}+B_s^{[K]}\) is an exact identity. The values \(R_s^{[K]}\) are auxiliary numbers approximating the **same** sample values; they are not new samples selected in place of the panel. Define
\[
\begin{aligned}
W^{[K]}&=2\left[|R_1^{[K]}-R_0|+
 \sum_{s=1}^{N-1}|R_{s+1}^{[K]}-R_s^{[K]}|+R_N^{[K]}\right],\\
U^{[K]}&=16E-M-W^{[K]}.
\end{aligned}
\tag{15}
\]
In particular \(R_0\), \(E\), and \(M\) have not changed.

The finite square in (14) keeps the interference explicitly. If \(I_s=\{q:1\le q\le K,\ q-s\text{ odd}\}\), then
\[
\begin{aligned}
(H_s^{[K]})^2={}&\varepsilon^2\sigma_{m,s}^2
-2\varepsilon\sigma_{m,s}\sum_{q\in I_s}a_q\mathcal K_{m,s}(q)\\
&+\sum_{q,\ell\in I_s}a_qa_\ell
 \mathcal K_{m,s}(q)\mathcal K_{m,s}(\ell).
\end{aligned}
\tag{16}
\]
The independent \(q,\ell\), their diagonal, and every source index inside both coefficients remain. No separate lower-order estimate for one of the original four source blocks is being asserted.

## 4. New estimate: all omitted coefficient indices have a paid panel effect

### 4.1. Bound the exact Cauchy tail, not the source coefficients individually

**[COFINAL_FAMILY | PAPER — new derivation]** For \(q>K>N\ge s\),
\[
0<\mathcal K_{m,s}(q)
=\frac{2(m+s)}{(q-s)(2m+q+s)}
<\frac1{q-s}.
\tag{17}
\]
Set
\[
T_K=\sum_{q>K}a_q^2\le\frac{E-E_O}{2}\le\frac E2.
\]
Cauchy–Schwarz and the integral bound for the squared denominators give
\[
\begin{aligned}
|B_s^{[K]}|^2
&\le T_K\sum_{q>K}\frac1{(q-s)^2}\\
&\le\frac{T_K}{K-s}\le\frac{T_K}{K-N}.
\end{aligned}
\tag{18}
\]
Discarding the parity restriction here only enlarges a positive majorant. It does not alter the signed sum (13). There is no assertion that \(T_K/E\) is small. The gain is separation of the Cauchy denominators.

Let
\[
p_s=\sqrt{\frac L{2\pi^3}}H_{m,m+s},\qquad
z_s=\sqrt{\frac L{2\pi^3}}B_s^{[K]}.
\]
By (10) and (18),
\[
\sum_{s=1}^N p_s^2\le A_LE,
\qquad
\sum_{s=1}^N z_s^2\le\delta_{L,K}E,
\tag{19}
\]
where
\[
A_L=\frac{L+3}{8\pi},\qquad
\delta_{L,K}=\frac{LN}{4\pi^3(K-N)}.
\tag{20}
\]
The actual \(E_O\) and \(T_K\) versions of these bounds are sharper; (20) is a source-independent error budget usable without knowing the target sign.

### 4.2. Keep the cross terms when passing to density and variation

**[COFINAL_FAMILY | PAPER]** The diagonal \(La_s^2/(8\pi)\) is identical in \(R_s\) and \(R_s^{[K]}\). Thus
\[
R_s-R_s^{[K]}=p_s^2-(p_s-z_s)^2=2p_sz_s-z_s^2,
\]
and
\[
\sum_{s=1}^N|R_s-R_s^{[K]}|
\le\left(2\sqrt{A_L\delta_{L,K}}+\delta_{L,K}\right)E.
\tag{21}
\]
The error is not bounded by the tail square alone: the first term pays its interference with the complete retained amplitude.

Each \(R_s\) appears twice in the bracket defining the panel path, including its two endpoint appearances when appropriate. Consequently, with \(R_0\) unchanged,
\[
|W-W^{[K]}|\le4\sum_{s=1}^N|R_s-R_s^{[K]}|.
\tag{22}
\]
Combining (21)–(22) yields the quantitative family bound
\[
\boxed{
|U-U^{[K]}|=|W-W^{[K]}|
\le\left(8\sqrt{A_L\delta_{L,K}}+4\delta_{L,K}\right)E.
}
\tag{23}
\]
The final descent term in (7) is included in the factor four, not omitted as an unknown frequency tail.

### 4.3. An explicit split and a vanishing error

**[COFINAL_FAMILY | PAPER]** Now use the deterministic split announced above:
\[
\boxed{K=N+\lceil L^4\rceil.}
\tag{24}
\]
For \(L>120\),
\[
N\le L+1<\frac98L,\qquad L+3<\frac98L,
\qquad K-N\ge L^4.
\]
Using only \(\pi>3\) in (20),
\[
A_L<\frac{3L}{64},\qquad
\delta_{L,K}<\frac1{96L^2},\qquad
A_L\delta_{L,K}<\frac1{2048L}.
\]
Therefore (23) proves
\[
\boxed{
|U-U^{[K]}|\le\eta_m E,\qquad
\eta_m=\frac1{4\sqrt{2L}}+\frac1{24L^2}.
}
\tag{25}
\]
For the stated uniform constant, \(\sqrt{2L}>15\), so the first term is less than \(1/60\). The second is less than \(1/240\). Hence
\[
\eta_m<\frac1{60}+\frac1{240}=\frac1{48},
\qquad \eta_m\longrightarrow0.
\tag{26}
\]
This proves (A) for every admitted selected cell in the requested domain. No asymptotic law for the source coefficients or numerical evaluation was used.

**What (25) pays:** the effect on this frozen panel of every coefficient with original index \(|n|>m+K\), including its cross terms with all retained coefficients. **What it does not pay:** the actual variation between sample nodes, or the sign of the retained source expression. The upper bound \(E/\sqrt6\) on central spectral variation is not added to \(W\): the first panel interval already crosses that spectral region, and that prior estimate is an upper bound, not an extra lower witness.

## 5. A second envelope: eliminate the unknown tail energy for exclusion

**[COFINAL_FAMILY | PAPER — alternative representation, not a second commissioned test]** There is a useful one-sided strengthening of the reduction when the goal is to exclude a witness. Define finite quantities
\[
S_K=\sum_{q=1}^K a_q^2,\qquad
A_K=\frac L{2\pi^3}\sum_{s=1}^N(H_s^{[K]})^2,
\qquad
\lambda_{L,K}=\frac{LN}{2\pi^3(K-N)}.
\tag{27}
\]
All source-series indices in the finitely many \(a_q\) are still retained. Equation (18) gives \(\sum z_s^2\le\lambda_{L,K}T_K\). This time expand the density around the retained amplitude, rather than the full amplitude. The same path estimate proves
\[
|W-W^{[K]}|
\le8\sqrt{A_K\lambda_{L,K}T_K}+4\lambda_{L,K}T_K.
\tag{28}
\]
The energy identity (11) gives the exact budget
\[
16E-M=16E_O+31(S_K+T_K)-\frac12D_d.
\tag{29}
\]
For (24), \(\lambda_{L,K}<1/(48L^2)<1\), so \(31-4\lambda_{L,K}>0\). Combining (28)–(29) and completing a square in \(\sqrt{T_K}\) yields
\[
\boxed{
U\ge\mathcal C_m^{[K]}:=
16E_O+31S_K-\frac12D_d-W^{[K]}
-\frac{16A_K\lambda_{L,K}}{31-4\lambda_{L,K}}.
}
\tag{30}
\]
Explicitly, the tail-dependent part of the lower bound is
\[
\begin{aligned}
&(31-4\lambda)T_K-8\sqrt{A_K\lambda T_K}\\
&\quad=(31-4\lambda)
 \left(\sqrt{T_K}-\frac{4\sqrt{A_K\lambda}}{31-4\lambda}\right)^2
 -\frac{16A_K\lambda}{31-4\lambda}.
\end{aligned}
\]
Thus (30) does not assume the tail energy is negligible. It bounds its most adverse possible effect after accounting for its positive contribution to the original budget.

A source proof of \(\mathcal C_m^{[K]}\ge0\) for all admitted selected \(L>120\) would exclude the fixed-panel witness, regardless of the remaining coefficient tail. The needed source sign of \(\mathcal C_m^{[K]}\) is **not proved here**. A negative value of this lower envelope would not be a negative value of \(U\), and would not refute SV. Equation (30) is a lower envelope for **the panel margin**, not for \(\Delta^{\rm var}\).

## 6. The first unpaid source comparison and why this is still OPEN

**[COFINAL_FAMILY | PAPER — exact epistemic boundary]** The original source comparison remains
\[
W\ \mathop{\lessgtr}\ 16E-M
=\frac{31}{2}E+\frac12E_O-\frac12D_d.
\tag{31}
\]
After the new reduction, its explicitly unpaid retained expression is (15), with
\[
\begin{aligned}
R_s^{[K]}={}&\frac L{8\pi}e_{m+s}^2\\
&+\frac L{2\pi^3}
\left[-\varepsilon\sigma_{m,s}
+\sum_{\substack{1\le q\le N+\lceil L^4\rceil\\q-s\text{ odd}}}
 e_{m+q}\left(\frac1{q-s}-\frac1{2m+q+s}\right)\right]^2.
\end{aligned}
\tag{32}
\]
Every \(e_{m+q}\) here is the literal source integral (3). The remaining decision is a source estimate of the complete finite expression against the original budget, with the error (25), or a proof of the one-sided source sign in (30). Neither has been obtained.

The exact certified enclosure is
\[
\boxed{
U^{[K]}-\eta_mE\le U\le U^{[K]}+\eta_mE,
\qquad \Delta^{\rm var}\le U\le U^{[K]}+\eta_mE.
}
\tag{33}
\]
No sign of either endpoint is claimed. A small enclosure width is not a signed margin.

The admitted norm facts alone do not decide (31). For example, nonnegativity of the sample values and (9) imply only
\[
W\le2R_0+4\sum_{s=1}^N R_s\le\frac{LM}{\pi}.
\tag{34}
\]
The resulting scale grows with \(L\). Failure of this generic estimate to certify a sign is neither evidence that the source margin is negative nor evidence that the panel is powerless.

The source equations do not yet provide an estimate for the retained parity-restricted interference in (32), or for its ordered density increments. Smoothness sufficient for coefficient convergence does not supply a bound relative to the actual tail energy. The central-frequency estimates have their stated proper domain and do not evaluate the carrier-adjacent samples. No separate bound on a source block or an unsigned coefficient support argument fills this gap.

Consequently, **SOURCE_LATTICE_VARIATION_WITNESS_PROVED** and **FIXED_PANEL_WITNESS_EXCLUDED** are both unestablished. This is the request's third outcome, not a statement of mathematical impossibility. The fixed panel has not been changed or declared dead.

## 7. One strictly narrower falsifiable PAPER lemma

### TEST_SOURCE_CORE_FINITE_COEFFICIENT_PANEL_MARGIN

**[COFINAL_FAMILY | CONDITIONAL — proposed source lemma, not proved]** Keep the same selected family, panel, and \(K\) in (24). Test the source sign using the finite-coefficient panel (32), the original \(E,M\), and the proved error (25). The discriminator is
\[
\mathfrak d_m=\frac{U^{[K]}}{E},
\quad\text{with the certified original-margin interval}\quad
\frac UE\in[\mathfrak d_m-\eta_m,\mathfrak d_m+\eta_m].
\tag{35}
\]
The two decisive certificate directions are as follows.

**A negative witness.** At an explicitly identified admitted selected cell, or on an explicitly proved admitted selected sequence, prove from (3) and (32) that
\[
\mathfrak d_m+\eta_m\le-\gamma,
\qquad\gamma>0\text{ explicit}.
\tag{36}
\]
Then \(U\le-\gamma E\) and \(\Delta^{\rm var}\le-\gamma E\). This delivers **SOURCE_LATTICE_VARIATION_WITNESS_PROVED** and refutes **SV only**. For example, a source proof of \(U^{[K]}\le-E/24\) would, by (26), give the original upper margin \(U<-E/48\). This numerical threshold is an illustrative sufficient certificate, not a redefinition of the task.

**Exclusion of this panel witness.** For every admitted selected \(L>120\), prove
\[
\mathfrak d_m-\eta_m\ge0.
\tag{37}
\]
Then \(U\ge0\) for that whole family and the outcome is **FIXED_PANEL_WITNESS_EXCLUDED**. The finite-source lower envelope \(\mathcal C_m^{[K]}\ge0\) in (30) is an alternative sufficient certificate for this same exclusion direction. Neither proof would establish SV.

If neither direction closes, the outcome remains **OPEN_SOURCE_LATTICE_WITNESS**. Failure of (36), failure of (37), or a negative value of the lower envelope (30) does not determine the original margin. A source margin too close to zero for (35) is also unresolved, not refuted.

This is a **finite-coefficient enclosure of the existing test**, not another sufficient interface substituted for SV and not another sample panel. It removes every coefficient index beyond \(m+K\) from the sample comparison with a proved vanishing budget, rather than asking to estimate the same infinite Cauchy sums again. It still requires actual source mathematics for the retained expression. No individual numerical evaluation or enumeration of its coefficients is commissioned.

### Two representations of this one remaining test

| Representation | Discriminating power | PAPER cost and main risk |
|---|---|---|
| **Chosen: finite-coefficient panel enclosure**, (24), (32)–(37). **[COFINAL_FAMILY; CONDITIONAL]** | A source-negative upper endpoint produces the requested witness; a source-nonnegative lower endpoint on every selected cell excludes the panel. | \(N\) fixed density values formed from \(K=O(L^4)\) exact high coefficients and the closed low harmonic sums. No infinite coefficient Cauchy tail remains unpaid in the panel. Source interference and the original energy comparison remain. This is a symbolic proof target, not a proposed large computation. |
| **Alternative: tail-energy-eliminated lower envelope**, (27)–(30). **[COFINAL_FAMILY; CONDITIONAL]** | A uniform nonnegative source value excludes a negative panel margin even under the most adverse remaining tail. | The same finite source coefficients, \(E_O\), and \(D_d\); one scalar square completion eliminates the unknown coefficient-tail energy. It is one-sided: a negative lower envelope proves no source witness. |

Only the named finite-coefficient panel-margin test is commissioned. The second row supplies another valid enclosure for that same test, not another research campaign or a new variation interface.

## 8. Adversarial checks and closeout

**[ABSTRACT | PAPER — planted detector check, not the theta source]** The sign detector is not automatically nonnegative for every real even coefficient sequence. As a unit check only, take a synthetic sequence with \(c_{m+1}=c_{-m-1}=a\ne0\), all other coefficients zero, and synthetic energies \(E=2a^2\), \(M=a^2\), \(E_O=D_d=0\). At the first panel node, the off-diagonal parity sum vanishes and \(R_1=La^2/(8\pi)\), while \(R_0=0\). The path to \(R_1\) and back to zero gives \(W\ge4R_1\). Therefore
\[
\frac UE\le\frac{31}{2}-\frac L{4\pi},
\]
which is negative for \(L>62\pi\). This synthetic check detects the diagonal, factor four, and inequality direction. It is **not** a selected-source witness and it replaces none of the actual coefficients in (3). It also explains why a norm-only universal exclusion argument is unavailable. No source prediction is scored from this diagnostic.

**[COFINAL_FAMILY | PAPER — strongest attack on the new reduction]** The dangerous shortcut would be to truncate (13) and bound only \((B_s^{[K]})^2\). That loses the possibly larger interference term. Equations (21) and (28) explicitly pay it. A second dangerous shortcut would be to treat (25) as controlling unsampled variation; it controls only the error in the already frozen \(W\). Equation (8) remains one-sided.

The boundary inventory is explicit. The original diagonal uses \(J_0(0,b)=b\). Odd and nonzero even differences are handled separately. The singular-looking value \(q=s\) is excluded by parity and its actual diagonal remains in (14). All tail denominators used in (17) are positive because \(q>K>N\ge s\). The original positive and negative Fourier indices are paired exactly, not conflated. The zero node and last tail-to-zero term are retained in both panel expressions. Ceiling values of \(N\) and \(K\) satisfy all inequalities at their jump points; no open gap in the selected domain is introduced. No decay assumption has been extended into the physical window.

**[COFINAL_FAMILY | PAPER — progress and prediction score]** What became smaller is the unpaid coefficient information in the panel numerator: infinitely many coefficient indices now contribute at most \(\eta_m E<E/48\), uniformly over all selected \(L>120\), with \(\eta_m\to0\). A finite-source lower envelope also accounts for every possible value of the remaining tail energy. The registered finite-reduction prediction is confirmed by (25); its explicit nonclaim about the source sign remains the correct limit of the result. The predecessor's proposed source witness remains unresolved, not confirmed or refuted.

No requested theorem shape is killed. No actual source margin has been proved. The three structural connections used are the exact pairing of the two signs of a Cauchy kernel, Parseval for the half-window sample sequence, and quadratic completion to eliminate an unknown tail energy. The vanishing check gives \(H_{m,0}=0\) but the nonzero density (6), not zero variation. A source sign for (35), or a uniform nonnegative source envelope (30), is the remaining family-deciding object for this panel test.

```yaml
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
DOWNSTREAM_CONSUMER: adjudication_of_SV_then_original_lag_and_square_transfer_at_their_separate_scopes
ACTUAL_CONSUMER_REQUIREMENT: sign_of_full_Delta_var_for_SV_or_an_independent_source_lag_proof
ORIGINAL_REQUESTED_OBJECT: negative_fixed_panel_upper_margin_or_uniform_exclusion_of_that_panel
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: a_negative_panel_is_sufficient_not_necessary_for_refuting_SV
KNOWN_WEAKER_INTERFACES:
  - a_direct_negative_full_Delta_var_refutes_SV_without_this_panel
  - a_full_source_SV_proof_can_close_the_lag_supplier_without_any_negative_panel
  - direct_source_lag_or_signed_arithmetic_bounds_can_bypass_SV
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_COMPARISON: finite_source_expression_32_in_panel_15_against_original_budget_31_with_error_25
NEW_CLOSED_QUANTIFIERS:
  - all_admitted_selected_L_GT_120_satisfy_ABS_U_MINUS_U_K_LE_eta_E_LT_E_OVER_48
  - all_admitted_selected_L_GT_120_satisfy_tail_energy_eliminated_lower_envelope_30
MINIMAL_MISSING_SOURCE_ESTIMATE: signed_finite_coefficient_panel_certificate_36_or_37_or_uniform_lower_certificate_30
NEXT_TEST: TEST_SOURCE_CORE_FINITE_COEFFICIENT_PANEL_MARGIN
NEXT_TEST_IS_NEW_PANEL: false
NEXT_TEST_REPLACES_SV: false
DISCRIMINATOR: original_U_enclosed_by_U_K_PLUS_OR_MINUS_eta_E
REOPEN_TRIGGER: source_negative_upper_endpoint_or_uniform_source_nonnegative_lower_endpoint
FIXED_PANEL_ANALYTICALLY_POWERLESS_ON_SOURCE: NOT_ESTABLISHED
KILLED_REQUESTED_THEOREM_SHAPE: NONE
NOVELTY_AXIS: exact_two_sided_source_tail_pairing_with_paid_finite_coefficient_panel_and_eliminated_tail_energy
MEMORY_ENTRY:
  target: fixed_source_core_lattice_variation_witness
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: finite_panel_error_must_pay_Cauchy_tail_interference_and_both_panel_endpoints
  forbidden_future_move: treat_small_panel_approximation_error_or_positive_U_as_a_proof_of_SV
  next_decisive_test: TEST_SOURCE_CORE_FINITE_COEFFICIENT_PANEL_MARGIN
```

The original constants \(C_0=128\), \(C_{\rm int}=134\), and \(C_2=146\) remain conditional. The exponent-one prime block, prime/square compensation, opposite-side correlation, integrated symbol deviation, transfer, actual \(J_m\) sign, first \(\tau_j\) sign, Schur-floor and RH remain open. The prior square transfer is unchanged, including its **negative low-frequency subtraction**. No mathematical runtime, numerical search, Lean execution, repository write, new seed, source/carrier/\(Q\)/denominator replacement, route promotion or RH claim occurred. The new derivations have not received independent review. fileciteturn15file0L102-L109

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_CORE_FINITE_COEFFICIENT_PANEL_MARGIN`, on PAPER, on the same admitted selected cells with \(L>120\), the original frozen nodes \(0,m+1,\ldots,m+\lceil L\rceil\), and the analytical coefficient split \(K=\lceil L\rceil+\lceil L^4\rceil\).** Validate the exact paired source identity (13), the half-window Parseval factor (9), the interference and endpoint factor in (21)–(23), and the uniform error (25)–(26). Then seek the source certificate (36) at an explicit admitted cell or sequence, or the all-selected source exclusion certificate (37); (30) is an alternative lower envelope for that same exclusion direction, not a separate task. Use the complete source formula (3) in every retained coefficient. A negative upper endpoint rejects SV only; a uniform nonnegative lower endpoint excludes this fixed panel only; an unresolved or zero-straddling enclosure returns `OPEN_SOURCE_LATTICE_WITNESS`. Keep the low \(\varepsilon\) block, both Fourier-index signs, independent cross terms, literal diagonal, original \(E_O\) and \(E\), zero node, final descent to zero, and original selected quantifier. Do not reinterpret this finite-coefficient enclosure as a bound for variation between nodes or activate the conditional square constants. No numerical coefficient evaluation, cutoff/grid/index search, panel fitting, mathematical runtime, Lean, repository write, new seed, source/carrier/\(Q\)/denominator change, route promotion or RH claim.
