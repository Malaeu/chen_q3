# STATUS: TRY_GOAL058_SOURCE_CORE_EVEN_PREFIX_CANCELLATION

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_CORE_EVEN_PREFIX_CANCELLATION
OUTCOME: OPEN_SOURCE_LOG_MOMENT_PEAK
REQUEST_ID: REQ-2026-09-27-SOURCE-CORE-LOGARITHMIC-MOMENT-PEAK
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CORE_LOGARITHMIC_MOMENT_PEAK
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: f0428d2c62a8a65d4c4ac7023cabd1e4351d218e
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
HONESTY_STATE: CHALLENGER_NOT_RH
PREDECESSOR: REQ-2026-09-27-SOURCE-CORE-FIRST-NODE-PEAK
REQUEST_SHA256_LOCALLY_COMPUTED: bad0942930c18463556ef35f580a1032eb915ef9cfd5c9e29de8257d36e76833
REQUEST_BYTES: 5824
REQUEST_LF: 109
REQUEST_CR: 0
REQUEST_UTF8_VALID: true
REQUEST_UTF8_BOM: false
REQUEST_FINAL_LF: true
REQUEST_GIT_BLOB_LOCALLY_COMPUTED: 8b9a830f495ea8b7a7e16ffb5d0458adc391156c
INDEPENDENT_PREUPLOAD_REQUEST_CHECKSUM_SUPPLIED: false
PREDECESSOR_VERDICT_SHA256_LOCALLY_VERIFIED: 4398b4aeb4674b7d0df9eee2efc88b44e84eb6238539d17daf1804962268e2d8
PREDECESSOR_BYTES: 33524
PREDECESSOR_LF: 609
PREDECESSOR_GIT_BLOB_LOCALLY_AND_REMOTELY_MATCHED: 7890bbacdd86c98eda14d661298049080ba087cb
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
AUDIT_READ: docs/Codex/PAPER_CHAIN.md_source_core_first_node_peak_test_at_SOURCE_COMMIT
AUDIT_GIT_BLOB_READ: 6e3368c2ad4da9d6c554e67131adf2f850255964
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
LOG_MOMENT_PEAK_PROVED: NOT_ESTABLISHED
LOG_MOMENT_CERTIFICATE_EXCLUDED: NOT_ESTABLISHED
SOURCE_SIGN_QUANTIFIERS_CLOSED: NONE
REQUESTED_THEOREM_SHAPES_KILLED: NONE
NEW_SOURCE_CONTOUR_IDENTITY: ORIGIN_VERTICAL_REAL_PART_ZERO_WITH_EXACT_RIGHT_EDGE_CORRECTION
NEW_SOURCE_EDGE_BOUND: ABS_Z_MINUS_HORIZONTAL_REAL_MOMENT_LE_r_vert_SQRT_E
r_vert: "256*L*(L+2)/sqrt(pi*m) < 1/(64*L^2)"
NEW_FINITE_PREFIX_REDUCTION: FIRST_N_UNWEIGHTED_EVEN_OFFSET_SOURCE_PREFIXES_WITH_PAID_COMPLETE_REMAINDER
PREFIX_RANGE: "1 <= R <= N = ceil(L)"
FAR_MOMENT_BOUND: "abs(Z_far) <= sqrt(L/[4*(2*N-1)])*sqrt(E) < sqrt(E)/2"
NEXT_TEST: TEST_SOURCE_CORE_EVEN_PREFIX_CANCELLATION
NEXT_TEST_STATUS: UNPROVED_SOURCE_CANCELLATION_LEMMA
NEXT_TEST_CONDITION: "L*abs(sum_{ell=1}^R e_{m+2*ell})^2 <= 49*R*E for all R=1..ceil(L)"
NEXT_TEST_POSITIVE_IMPLICATION: "all_selected_prefix_bounds imply chi_m >= 827/240 on all selected L>120"
NEXT_TEST_NEGATIVE_IMPLICATION: REFUTES_ONLY_THE_PROPOSED_PREFIX_CANCELLATION_INTERFACE
PROGRESS_CLASS: REPRESENTATION_PROGRESS
PROGRESS_QUALIFICATION: SOURCE_ENDPOINT_CONTRIBUTION_PAID_AND_COHERENCE_LOCALIZED_NOT_A_SOURCE_SIGN_DECISION
ROUTE_SCORE: 3
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
DISCRIMINATOR: chi_m
NEXT_TEST_DISCRIMINATOR: "49 - L*S_m_R^2/(R*E)"
FIXED_PANEL_CHANGED: false
ORIGINAL_K_CHANGED: false
SOURCE_FAMILY_CHANGED: false
CARRIER_CUTOFF_CHANGED: false
DILATION_BOUNDARY_Q_CHANGED: false
DENOMINATOR_CHANGED: false
SOURCE_r_SERIES_TRUNCATED: false
LOW_EPSILON_BLOCK_DROPPED: false
NEGATIVE_FOURIER_INDICES_DROPPED: false
NEW_DUAL_MASK: false
NEW_SEED_SELECTED: false
SV: OPEN
ORIGINAL_CONTINUOUS_LAG_TEST: OPEN
C0_128: CONDITIONAL_NOT_ACTIVATED
C_INT_134: CONDITIONAL_NOT_ACTIVATED
C2_146: CONDITIONAL_NOT_ACTIVATED
NEW_DERIVATIONS_INDEPENDENTLY_AUDITED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_COEFFICIENT_EVALUATION_EXECUTED: false
NUMERICAL_SEARCH_EXECUTED: false
LEAN_EXECUTED: false
LOCAL_FILE_IO_TEXT_VALIDATION_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
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

Ы. **OPEN_SOURCE_LOG_MOMENT_PEAK.** Neither the requested source peak nor nonnegativity of the logarithmic certificate on the entire selected family is proved. No source cell or sequence with the required negative margin is asserted.

Two results delimit the unpaid comparison. First, the paired logarithmic moment has an exact contour representation: the real contribution from the vertical side at the origin is zero, while the opposite side has an explicit source-relative bound. Thus a separate origin-endpoint term cannot legitimately supply the peak. Second, the complete reciprocal moment can be reduced to the first \(N=\lceil L\rceil\) **unweighted even-offset source prefix sums**, with the remaining moment bounded by \(\sqrt E/2\). This is not a sign conclusion from a norm estimate. The finite source cancellation needed to use that reduction is stated, and remains unproved.

The single next test is an explicit cancellation inequality for those finite prefixes. A proof would exclude the logarithmic certificate, with a positive margin, on the whole original domain. A source counterexample would refute only that stronger cancellation lemma—not prove a logarithmic peak.

## 1. Source lock and audit boundary

**[FINITE_CELL | PAPER — transport record]** The authoritative TXT was read in full: **5,824 bytes, 109 LF**, valid UTF-8, no CR, no byte-order mark, and a final LF. Its computed SHA-256 is the value in the header. No independent pre-upload checksum for this TXT was supplied; the computed hash identifies the attachment actually received. Its ID, boundary, commit, and predecessor binding agree with the canonical request. fileciteturn31file0L1-L20

The complete mounted predecessor was read through its final directive: **33,524 bytes, 609 LF**. Its locally computed SHA-256 is exactly the stipulated `4398b4aeb4674b7d0df9eee2efc88b44e84eb6238539d17daf1804962268e2d8`. Its computed Git blob, `7890bbacdd86c98eda14d661298049080ba087cb`, matches the blob returned at the pinned commit. The local full text, not the abbreviated connector response, supplied the predecessor argument. fileciteturn33file0L3-L5

The bootstrap was fetched from `rh_clean` and read through its response-format section. The only additional project document opened was `docs/Codex/PAPER_CHAIN.md` at the current pin, including the complete section headed **“source core first-node peak test.”** Its limited audit accepts the generating identity, correction and relative error bound. It expressly does not accept an actual-source sign. The new derivations below are not covered by its CLEAN reviews. fileciteturn35file0L2-L2

## 2. Fixed objects and the requested sign

**[COFINAL_FAMILY | PAPER — admitted source contract]** Fix the same \(P\), and every admitted selected
\[
m=J_P+j+2,\qquad L=\log m>120,\qquad b=L/2,\quad Q=\sqrt m,
\quad \omega_n=2\pi n/L.
\]
Keep the original \(5m\) splice, carrier \(|n|\le m\), panel \(0,m+1,\ldots,m+N\), and
\[
N=\lceil L\rceil,\qquad K=N+\lceil L^4\rceil.
\]
Write
\[
\begin{aligned}
h_*(x)&=(24\pi x^2-16\pi^2x^4)e^{-\pi x^2},\\
G(u)&=e^{u/2}\sum_{a\ge1}h_*(ae^u),\qquad g=G'',\\
h&=T_mg,\quad f=h-g,\quad E=\|f\|_2^2>0,\\
E_O&=2\int_b^\infty|g(u)|^2du,\quad B=G'(b),\quad
\varepsilon=2B/\sqrt L,\\
d&=\varepsilon\sum_{|n|\le m}\psi_{n,L},\quad k=f-d,\quad
D_d=(2m+1)\varepsilon^2,\\
M&=\|\mathbf1_{[0,b]}k\|_2^2=(E-E_O+D_d)/2.
\end{aligned}
\tag{1}
\]
The source index is denoted by \(a\) here to distinguish it from a finite prefix length. Every \(a\ge1\) remains. The objects in (1) are unchanged. fileciteturn31file0L31-L39

Set
\[
\mathcal P(v)=-64v^4+448v^3-660v^2+150v,\qquad
 g_a(z)=e^{z/2}\mathcal P(\pi a^2e^{2z})e^{-\pi a^2e^{2z}},
\]
so that \(g=\sum_{a\ge1}g_a\), and retain the actual real coefficients
\[
e_n=\frac{2(-1)^n}{\sqrt L}\sum_{a\ge1}
\int_0^b g_a(u)\cos(\omega_nu)du.
\tag{2}
\]
Evenness and the original projection give
\[
\boxed{E=E_O+2\sum_{q\ge1}e_{m+q}^2.}
\tag{3}
\]
The admitted source estimate \(B^2\le E_O/(\pi m)\) gives
\[
D_d<\frac{3E}{L},\qquad
\frac ME\le\frac12\left(1+\frac3L\right)<\frac{41}{80}.
\tag{4}
\]
These are used as error budgets, not as replacements for the source denominator. The predecessor proves the exterior estimate with the actual polynomial source; the pinned audit retains its exterior-only scope. fileciteturn35file0L2-L2

The exact first-node terms remain
\[
\begin{aligned}
H={}&-\varepsilon\sigma_m+
\sum_{\substack{2\le q\le K\\q\ {
m even}}}
 e_{m+q}\left(\frac1{q-1}-\frac1{2m+q+1}\right),\\
\sigma_m={}&\sum_{\substack{1\le\nu\le2m+1\\\nu\ {
m odd}}}\frac1\nu,
\qquad R_0=\frac{B^2}{2\pi},\\
p_m={}&16-\frac ME+\frac{2R_0}{E}
-\frac{L e_{m+1}^2}{2\pi E}-\frac{2L H^2}{\pi^3E}+\eta_m.
\end{aligned}
\tag{5}
\]
The diagonal is the displayed \(e_{m+1}^2\), not a singular term in the even-offset sum. The complete low block and reflected negative indices remain in \(H\). fileciteturn31file0L41-L55

The target moment and its certificate are
\[
\begin{aligned}
Z_m={}&\int_0^b g(u)\left[
\log\cot(\pi u/L)\cos(\omega_{m+1}u)
-\frac\pi2\sin(\omega_{m+1}u)\right]du,\\
\chi_m={}&16-\frac ME+\frac{2R_0}{E}
-\frac{2Z_m^2}{\pi^3E}+\eta_m+\delta_m.
\end{aligned}
\tag{6}
\]
Here \(\eta_m\) and \(\delta_m\) are exactly the stipulated quantities, with
\(\eta_m<1/48\), \(\delta_m<1/(6L)<1/720\). The original correction remains
\[
\begin{aligned}
C_m^+&=\sum_{\ell\ge1}\frac{e_{m+2\ell}}{2\ell-1}
      =\frac{(-1)^m}{\sqrt L}Z_m,\\
\beta_m&=\varepsilon\sigma_m+
\sum_{\substack{2\le q\le K\\q\ {
m even}}}\frac{e_{m+q}}{2m+q+1}
+\sum_{\substack{q>K\\q\ {
m even}}}\frac{e_{m+q}}{q-1},\\
H&=C_m^+-\beta_m,
\qquad H^2=(C_m^+)^2-2C_m^+\beta_m+\beta_m^2.
\end{aligned}
\tag{7}
\]
In particular, no subsequent representation sets \(\beta_m\) to zero. The accepted comparison gives
\[
\boxed{
\frac{\Delta^{\rm var}}E\le\frac{U^{\rm lattice}}E
\le\frac{U^{[K]}}E+\eta_m\le p_m
\le\chi_m-\frac{L e_{m+1}^2}{2\pi E}\le\chi_m.
}
\tag{8}
\]
This is an **upper**, not a lower, chain for the original variation margin. The panel's zero node and final descent are already included in the accepted inequalities. fileciteturn31file0L52-L71

## 3. Exact endpoint cancellation on a source contour

### 3.1. The paired kernel is one analytic boundary value

**[COFINAL_FAMILY | PAPER — new contour identity]** Put
\[
\lambda=\omega_{m+1},\qquad c=2\pi/L,\qquad s=\frac1{2L}.
\]
The height \(s\) is an explicit analytical contour choice. It changes neither \(K\), the carrier, nor a sampled frequency.

For \(0<x<b\), the radial branch is
\[
\operatorname{atanh}(e^{icx})
=\tfrac12\log\cot(\pi x/L)+i\pi/4,
\tag{9}
\]
so the complete integrand in (6) is
\(2\operatorname{Re}[g(x)e^{i\lambda x}\operatorname{atanh}(e^{icx})]\).
In the open upper rectangle \(0<\operatorname{Im}z\le s\), the argument
\(e^{icz}\) has modulus less than one; the power-series branch of
\(\operatorname{atanh}\) is therefore unambiguous.

The full source series for \(g(z)\) converges locally uniformly in
\(|\operatorname{Im}z|<\pi/4\). On any compact subrectangle, a polynomial times
\(\exp[-\pi a^2e^{2\operatorname{Re}z}\cos(2\operatorname{Im}z)]\)
is a summable Gaussian majorant. The admitted real even source consequently has
\(g(iy)\) real: analytic evenness and conjugation give
\(g(iy)=g(-iy)=\overline{g(iy)}\).

Apply the contour identity to
\[
F_m(z)=2g(z)e^{i\lambda z}\operatorname{atanh}(e^{icz}).
\]
At the origin side, \(F_m(iy)\) is real. Its vertical integral is purely imaginary and contributes **exactly zero** to the real moment. The logarithmic singularities at the two bottom corners are integrable; small corner arcs have integrals tending to zero as their lengths times \(1+|\log\text{length}|\). Neither endpoint neighborhood is deleted.

Define
\[
Y_m=2\operatorname{Re}\int_0^b
 g(x+is)e^{i\lambda(x+is)}
 \operatorname{atanh}(e^{ic(x+is)})dx.
\]
On the right side, \(e^{ic(b+iy)}=-e^{-cy}\) and
\(e^{i\lambda b}=(-1)^{m+1}\). The contour orientation gives exactly
\[
\boxed{
Z_m=Y_m+\mathcal E_m,
\qquad
\mathcal E_m=(-1)^m\int_0^s e^{-\lambda y}
 \log\coth(\pi y/L)\operatorname{Im}g(b+iy)dy.
}
\tag{10}
\]
The sign in (10) follows from bottom = top + left-up minus right-up; the real part of minus \(iF_m\) is \(\operatorname{Im}F_m\).

This is the paired cancellation before estimation. A separate estimate for the logarithmic cosine that treats its origin contribution as a peak would not respect (9)–(10).

### 3.2. The nonzero opposite-edge term is source-paid

**[COFINAL_FAMILY | PAPER — new relative bound]** Let \(v=\pi m\). Differentiating the complete source gives
\[
B=m^{1/4}\sum_{a\ge1}
 [32(va^2)^3-120(va^2)^2+60va^2]e^{-va^2}.
\]
For \(v\ge32\), every summand is positive and the first one proves
\[
B\ge16m^{1/4}v^3e^{-v}.
\tag{11}
\]
For \(0\le y\le s\), \(|\mathcal P(va^2e^{2iy})|\le2048(va^2)^4\).
Also, for \(A\ge8\),
\[
\sum_{a\ge1}a^8e^{-A(a^2-1)}<2.
\]
Indeed, \(8\log a\le4(a^2-1)\); the terms with \(a\ge2\) are bounded by a convergent geometric sum using \(a^2-1\ge a\). Applying this with
\(A=v\cos(2y)>8\), and then (11), gives
\[
|g(b+iy)|
\le4096m^{1/4}v^4e^{-v}e^{v(1-\cos2y)}
\le256vB\,e^{2vy^2}.
\tag{12}
\]
All source summands were bounded, not truncated. Since \(y\le1/(2L)\),
\[
2vy^2-\lambda y\le-\frac{\pi m}{L}y.
\]
The elementary inequality \(\coth z\le1+1/z\), \(z>0\), and the substitution
\(x=\pi my/L\) now give
\[
\begin{aligned}
|\mathcal E_m|
&\le256\pi mB\int_0^s e^{-\pi my/L}\log\coth(\pi y/L)dy\\
&\le256LB\int_0^\infty e^{-x}\log(1+m/x)dx\\
&\le256L(L+2)B.
\end{aligned}
\tag{13}
\]
For the last step use
\(\log(1+m/x)\le\log(m+1)+(-\log x)_+\),
\(\int_0^1-\log x\,dx=1\), and \(\log(m+1)<L+1\).

Combining (13) with the admitted \(B^2\le E_O/(\pi m)\le E/(\pi m)\) proves
\[
\boxed{
|Z_m-Y_m|\le r_{\rm vert}(m)\sqrt E,
\qquad r_{\rm vert}(m)=\frac{256L(L+2)}{\sqrt{\pi m}}
<\frac1{64L^2},\qquad L>120.
}
\tag{14}
\]
For an elementary check of the uniform constant, \(e^{L/2}>L^8\) on this domain: it holds at 120 since \(e^{60}>2^{60}>120^8\), and the logarithmic ratio is increasing. Hence \(r_{\rm vert}<512/L^6<1/(64L^2)\).

The square still retains its interference:
\(Z_m^2=Y_m^2+2Y_m\mathcal E_m+\mathcal E_m^2\).
For example, using the admitted \(|Z_m|\le\sqrt{LE}\), its change is bounded by
\[
\frac{2}{\pi^3E}|Z_m^2-Y_m^2|
\le\frac{2}{\pi^3}r_{\rm vert}(2\sqrt L+r_{\rm vert}).
\tag{15}
\]
This only pays a contour correction. **It does not bound the complete horizontal moment \(Y_m\) at the required energy scale.**

## 4. The first unpaid source inequality

**[COFINAL_FAMILY | PAPER — unresolved comparison]** Set
\[
\mathcal B_m=16E-M+2R_0.
\]
The peak outcome requires an actual admitted cell or a rigorously defined admitted sequence satisfying
\[
\frac{2Z_m^2}{\pi^3}\ge\mathcal B_m+\frac E{24}.
\tag{16}
\]
The exclusion outcome instead requires, on **every** admitted selected cell,
\[
\frac{2Z_m^2}{\pi^3}\le\mathcal B_m+(\eta_m+\delta_m)E.
\tag{17}
\]
Neither comparison is established. These are exactly the request's alternatives, not interchangeable conclusions. fileciteturn31file0L73-L93

The exterior bound controls \(B\), the low block, and (14); it says nothing about the sign or coherence of the remaining interior oscillatory moment. The contour identity removes spurious endpoint contributions but leaves that coherence intact. Taking an absolute majorant of the complete horizontal integrand would likewise require a new relative comparison with \(E\); no such comparison is supplied by analyticity alone.

The energy identity (3) only gives \(|C_m^+|\le\sqrt E\), hence \(Z_m^2\le LE\). Its coefficient in (17) grows with \(L\), while \(\mathcal B_m/E\) remains at a fixed scale. It yields no positive lower bound for (16). A small absolute bound for both numerator and denominator cannot settle their ratio.

In particular, the accepted bound on \(\beta_m\), or the new bound on \(\mathcal E_m\), cannot be promoted to a sign of the main term. There is no negative source margin and no all-selected nonnegative source margin in this review.

## 5. Localize the missing coherence to finite, unweighted source prefixes

### 5.1. Exact source formulas without a logarithmic singularity

**[COFINAL_FAMILY | PAPER — exact representation]** For \(1\le R\le N\), define
\[
S_{m,R}=\sum_{\ell=1}^{R}e_{m+2\ell}.
\tag{18}
\]
These are sums of the actual coefficients, not arbitrary sequences. With
\(\theta=2\pi u/L\), the finite geometric identity yields
\[
\boxed{
S_{m,R}=\frac{2(-1)^m}{\sqrt L}
\sum_{a\ge1}\int_0^b g_a(u)
 \frac{\sin(R\theta)}{\sin\theta}
 \cos((m+R+1)\theta)du.
}
\tag{19}
\]
The quotient in (19) is interpreted by its continuous extension. The entire product has value \(R\) at \(u=0\), and \((-1)^mR\) at \(u=b\). Thus neither endpoint is a deleted singularity. The outside phase is precisely \((-1)^m\), since the offsets are even.

The source sum in (19) is complete. Fixed-cell interchange follows from the same uniform polynomial-Gaussian majorant for \(g_a\), multiplied by the bounded finite cosine sum. No source-index error has been hidden in a remainder.

Let
\[
T_m=\sum_{\ell=1}^{N}\frac{e_{m+2\ell}}{2\ell-1},
\qquad
F_m^{\rm off}=\sum_{\ell>N}\frac{e_{m+2\ell}}{2\ell-1}.
\]
Then, exactly,
\[
\boxed{
Z_m=(-1)^m\sqrt L\,[T_m+F_m^{\rm off}],
\quad
T_m=\frac{S_{m,N}}{2N-1}
+\sum_{R=1}^{N-1}\left(\frac1{2R-1}-\frac1{2R+1}\right)S_{m,R}.
}
\tag{20}
\]
This is summation by parts of the **accepted complete paired moment**. It is not removal of the sine term from (6).

### 5.2. Every omitted offset has a paid joint contribution

**[COFINAL_FAMILY | PAPER]** The integral test and (3) give
\[
\begin{aligned}
\sum_{\ell>N}\frac1{(2\ell-1)^2}
&\le\int_N^\infty\frac{dx}{(2x-1)^2}
=\frac1{2(2N-1)},\\
|F_m^{\rm off}|^2&\le\frac{E}{4(2N-1)}.
\end{aligned}
\]
Thus
\[
\boxed{
\left|(-1)^m\sqrt L F_m^{\rm off}\right|
\le\vartheta_m\sqrt E,
\qquad
\vartheta_m=\sqrt{\frac{L}{4(2N-1)}}<\frac12.
}
\tag{21}
\]
The far moment is not zero. Its mixed term is retained by
\[
Z_m^2=L T_m^2+2L T_mF_m^{\rm off}+L(F_m^{\rm off})^2.
\tag{22}
\]
Consequently, for each source cell,
\[
\sqrt L\,|T_m|-\vartheta_m\sqrt E
\le |Z_m|
\le\sqrt L\,|T_m|+\vartheta_m\sqrt E,
\tag{23}
\]
where a negative left side asserts only a vacuous lower bound.

This splitting uses the already frozen \(N\). Moreover \(2N<K\) for \(L>120\). It is an internal decomposition of \(C_m^+\), not a new coefficient cutoff in \(H\): (7) still contains the original \(K\), low block, reflected term and completion correction. The normalization in (21) is the original \(E\), including \(E_O\).

The conclusion is limited but useful: a large logarithmic moment cannot be supplied by the complete far-offset contribution alone. Source coherence among the first \(N\) even-offset prefixes must also enter. A norm estimate is used only to pay the far contribution, not to claim either requested source sign.

## 6. One strictly narrower falsifiable PAPER lemma

### TEST_SOURCE_CORE_EVEN_PREFIX_CANCELLATION

**[COFINAL_FAMILY | CONDITIONAL — proposed source lemma, not proved]** Test the following fixed inequality on the unchanged source:
\[
\boxed{
L\,S_{m,R}^2\le49R E
\quad\text{for every admitted selected }L>120
\text{ and every integer }1\le R\le N=\lceil L\rceil.
}
\tag{PC}
\]
The complete source formula to test is (19). The constant 49 is fixed here analytically; it is not fitted to evaluated coefficients.

This is a **cancellation hypothesis**, not the ordinary coefficient norm bound. Indeed, ordinary Cauchy–Schwarz only gives \(S_{m,R}^2\le RE/2\), which is too weak throughout the present domain to imply (PC). No argument in this review establishes (PC) for the theta source.

### 6.1. Proved implication to logarithmic-certificate exclusion

**[COFINAL_FAMILY | CONDITIONAL — full implication proof]** If (PC) holds at one cell, all the coefficients in the sum on the right of (20) are positive, so
\[
|T_m|\le7\sqrt{E/L}\,\kappa_N,
\]
where
\[
\begin{aligned}
\kappa_N&=\frac{\sqrt N}{2N-1}
+\sum_{R=1}^{N-1}\sqrt R
 \left(\frac1{2R-1}-\frac1{2R+1}\right)\\
&=1+\sum_{R=2}^{N}\frac{\sqrt R-\sqrt{R-1}}{2R-1}
\le1+\frac14\sum_{j=1}^\infty j^{-3/2}
\le\frac74.
\end{aligned}
\tag{24}
\]
Here \(\sqrt R-\sqrt{R-1}\le1/(2\sqrt{R-1})\),
\(2R-1\ge2(R-1)\), and
\(\sum_{j\ge1}j^{-3/2}\le1+\int_1^\infty x^{-3/2}dx=3\).
Using the exact remainder and its bound in (21)–(23) therefore gives
\[
|Z_m|<\left(7\cdot\frac74+\frac12\right)\sqrt E
=\frac{51}{4}\sqrt E.
\tag{25}
\]
This pays the possible worst sign of the mixed term in (22); it does not assume cancellation between the two portions.

Now retain the original positive terms in \(\chi_m\), or discard them only in the lower-bound direction. Since \(\pi>3\), (4) and (25) imply
\[
\boxed{
\chi_m
>16-\frac{41}{80}-\frac{2(51/4)^2}{27}
=16-\frac{41}{80}-\frac{289}{24}
=\frac{827}{240}>0.
}
\tag{26}
\]
Thus a source proof of (PC) for **every** stated cell would give
`LOG_MOMENT_CERTIFICATE_EXCLUDED`, with a nonnegative lower envelope that is actually uniformly positive. The conclusion is only conditional here.

### 6.2. Exact discriminator and both outcomes

**[COFINAL_FAMILY | CONDITIONAL]** Use
\[
\boxed{
D^{\rm pref}_{m,R}=49-\frac{L S_{m,R}^2}{R E},
\qquad 1\le R\le\lceil L\rceil.
}
\tag{27}
\]
A source-derived nonnegative lower bound for every discriminator (27), on every admitted selected cell, proves (PC), hence the exclusion (26). This would **not** exclude the original first-node certificate: (8) is one-sided and still retains its diagonal and signed correction.

A rigorously negative upper bound for (27) at an explicitly admitted selected pair \((m,R)\) refutes **only (PC)**. It is not a logarithmic peak: a large unweighted prefix may still cancel against later prefixes in (20). It is not a refutation of SV or of any lag statement. A source-sign argument for the original \(Z_m\) would still be needed.

Conversely, (26) proves a necessary localization statement: if the actual \(\chi_m<0\), then at least one of these finite source prefix discriminators must be negative. In particular, any witness for (16) must violate (PC) somewhere within this specified range. This makes the test a necessary obstruction hunt for a peak as well as a sufficient route to exclusion; it does not make its failure sufficient for a peak.

This is not (16) or (17) renamed. It tests **unweighted, linear source sums** over a finite range \(R\le N\), with continuous finite kernels (19), rather than the infinite reciprocal moment or a squared logarithmic integral. All larger offsets have the independent budget (21). The reverse implication from nonnegative \(\chi_m\) to (PC) is not asserted. Hence (PC) is a stronger candidate interface, not a necessary condition for certificate exclusion and not an additional mandatory route supplier.

A zero-consistent original \(\chi_m\) is not a negative witness. A zero-consistent prefix discriminator is not a refutation of (PC). Strict negative upper bounds and all-domain nonnegative lower bounds retain their different roles.

## 7. Direction, scope, and adversarial checks

**[COFINAL_FAMILY | PAPER — requested strictness]** Had (16) been proved, the original constants would give
\[
\chi_m\le-\frac1{24}+\eta_m+\delta_m
<-\frac1{24}+\frac1{48}+\frac1{720}
=-\frac7{360}.
\tag{28}
\]
Then (8) would imply \(p_m<-7/360\) and
\(\Delta^{\rm var}<-7E/360\) at the same admitted cell. A specified sequence must really lie in \(m=J_P+j+2\); no unverified sequence or numerical observation can fill that condition. Equation (28) remains a conditional implication, not a result on the source. fileciteturn31file0L73-L88

**[ABSTRACT | PAPER — branch calibration]** In (9), the boundary ratio is
\((1+e^{i\theta})/(1-e^{i\theta})=i\cot(\theta/2)\), with positive imaginary part for \(0<\theta<\pi\). It gives the minus sign on the sine after the real part is taken. On the constant endpoint-control function from the predecessor, the logarithmic cosine and sine cancel exactly. That is a normalization test, not a replacement source. The contour's zero real left-side contribution is the analytic counterpart of this cancellation for the actual even source.

**[COFINAL_FAMILY | PAPER — strongest objection to the new upper route]** The prefix bound (PC) is substantially stronger than generic energy control and is not implied by a small \(E\), analytic source regularity, or finite \(R\). It could fail. Equations (24)–(26) prove what a source proof would buy, not that the source supplies it. Substituting (PC) without proof would be the first invalid inference.

**[COFINAL_FAMILY | PAPER — conservation]** The physical exterior remains in (1) and (3). Both Fourier signs remain in (7). The low coefficient is never replaced by zero. The first-node diagonal remains in (5) and (8). The frozen panel's zero node and final descent remain in the admitted chain. The cosine and sine in (6) were combined before any contour estimate. Every source index remains in (2), (12), and (19), and every moment-tail contribution remains in (7), (20), and (22). There is no coefficient evaluation, new panel, new mask, cutoff search, or denominator replacement. The ceiling boundaries are covered by the inequalities \(N\ge L\), \(2N-1>L\), and \(2N<K\) for every \(L>120\).

## 8. Route map, predictions, and closeout

| Representation | What it can decide | PAPER cost and main risk |
|---|---|---|
| **Chosen: finite even-offset source prefixes**, (18)–(27). **[COFINAL_FAMILY; CONDITIONAL]** | A full source cancellation proof gives uniform logarithmic-certificate exclusion. A negative prefix margin refutes only this candidate; every actual logarithmic peak must produce such a violation. | At most \(\lceil L\rceil\) unweighted source moments, with one closed finite-kernel formula and a paid complete tail. Better localization than the original \(K\)-length expression; the needed cancellation is unproved. |
| **Alternative: paired analytic contour**, (9)–(15). **[COFINAL_FAMILY; CONDITIONAL]** | Removes a false origin-endpoint mechanism exactly and pays the opposite side. A signed horizontal-moment estimate could still decide the original peak or exclusion. | One complex source integral without real-axis logarithmic singularities. The remaining horizontal oscillation and its comparison with \(E\) are not controlled. This is not a second commissioned test. |

The three connections are an **analytic boundary-value identity** preserving the paired kernel, **discrete summation by parts** converting reciprocal weights into finite source prefixes, and a **one-way quadratic certificate** from prefix cancellation to \(\chi_m\). The demonstrated vanishing concerns the origin's vertical real contribution, not the complete \(Z_m\). The proposed family-deciding object is the actual source cancellation (PC), not merely its formula.

**Prediction/check scoring.** The pre-test progress note identified origin contour cancellation and source-relative control of the opposite edge as the checks to attempt. Equations (10) and (14) confirm these checks at their stated scopes. They do not confirm a peak or an exclusion prediction. The source prefix inequality (PC) is proposed and **not tested to a source-sign conclusion**. The predecessor's unproved source antecedent remains unproved; its accepted identities and corrections are inputs, not new successes.

**What became smaller:** a whole class of separate origin-endpoint peak arguments is ruled out by exact cancellation, and the missing reciprocal-moment coherence is localized to the first \(\lceil L\rceil\) unweighted source prefixes with all larger offsets paid. **What did not close:** either requested source-sign quantifier. No original theorem shape, SV interface, panel, or route family was killed.

```yaml
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
DOWNSTREAM_CONSUMER: chi_m_sign_then_original_first_node_upper_certificate_and_SV_only
ACTUAL_CONSUMER_REQUIREMENT: admitted_source_peak_with_strict_margin_or_all_selected_chi_nonnegative
ORIGINAL_REQUESTED_OBJECT: complete_paired_logarithmic_moment_peak_or_certificate_exclusion
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: logarithmic_certificate_is_sufficient_not_necessary_for_first_node_or_SV_negativity
KNOWN_WEAKER_INTERFACES:
  - negative_original_p_m_can_exist_without_negative_chi_m
  - negative_full_panel_margin_can_exist_without_negative_first_node_certificate
  - direct_lag_or_arithmetic_control_can_bypass_SV
PROPOSED_INTERFACE: actual_source_finite_even_prefix_cancellation_PC
PROPOSED_INTERFACE_IS: SUFFICIENT_NOT_NECESSARY_FOR_LOG_CERTIFICATE_EXCLUSION
EXACT_PROPOSED_IMPLICATION: PC_all_selected_implies_chi_GE_827_over_240_all_selected
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_COMPARISON: equations_16_and_17_for_complete_Z_at_original_E
MINIMAL_NEW_CANCELLATION_TARGET: equation_PC_using_complete_source_integrals_19
REOPEN_TRIGGER: source_proof_of_PC_or_source_signed_Z_bound_crossing_an_original_threshold
DISCRIMINATOR: chi_m
NEXT_TEST: TEST_SOURCE_CORE_EVEN_PREFIX_CANCELLATION
NEXT_TEST_DISCRIMINATOR: D_pref_m_R_in_equation_27
NEXT_TEST_NEGATIVE_RESULT_SCOPE: PROPOSED_PREFIX_LEMMA_ONLY
SOURCE_SIGN_QUANTIFIERS_CLOSED: NONE
NEW_CLOSED_PROPER_CONTRIBUTION_QUANTIFIERS:
  - every_selected_L_GT_120_satisfies_exact_contour_identity_10_and_edge_bound_14
  - every_selected_L_GT_120_satisfies_complete_far_offset_bound_21
KILLED_REQUESTED_THEOREM_SHAPE: NONE
NOVELTY_AXIS: actual_source_endpoint_cancellation_plus_finite_unweighted_coherence_localization
MEMORY_ENTRY:
  target: source_core_logarithmic_moment_peak
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: paired_origin_cancellation_precedes_any_peak_estimate_and_a_negative_log_certificate_requires_a_finite_prefix_coherence_obstruction
  forbidden_future_move: promote_a_paid_correction_or_failed_prefix_upper_interface_to_the_sign_of_the_complete_source_moment
  next_decisive_test: TEST_SOURCE_CORE_EVEN_PREFIX_CANCELLATION
```

The exponent-one prime block, prime/square compensation, opposite-side correlation, integrated symbol deviation, transfer, actual \(J_m\) sign, first \(\tau_j\) sign and Schur-floor remain OPEN. The constants \(C_0=128\), \(C_{\rm int}=134\), \(C_2=146\) remain conditional. The new mathematical derivations have not received independent review. No mathematical runtime, numerical coefficient evaluation, search, Lean execution, repository write, route promotion, or RH claim occurred. fileciteturn31file0L95-L109

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_CORE_EVEN_PREFIX_CANCELLATION`, on PAPER, for the unchanged admitted selected family with \(L>120\), original \(E\), and the already fixed \(N=\lceil L\rceil\).** Test (PC) using the complete theta-source integrals (19), with discriminator (27), without evaluating coefficients numerically. Verify the finite summation-by-parts identity (20), full tail budget (21), and conditional constants (24)–(26). A source-derived nonnegative lower envelope for every (27), for every admitted selected cell, proves `LOG_MOMENT_CERTIFICATE_EXCLUDED` with \(\chi_m\ge827/240\), and nothing stronger. A strictly negative source upper envelope at an explicitly admitted selected \((m,R)\) refutes only this proposed prefix-cancellation interface; report its exact scope and do not call it a logarithmic, first-node, or SV witness. An unresolved source sign remains OPEN and must not be replaced by generic Cauchy–Schwarz. Preserve the original panel and \(K\), both Fourier signs, literal diagonal, zero node, final descent, complete source series, physical \(E_O\), paired kernel, and signed correction (7). No new panel or mask, cutoff search, source/carrier/\(Q\)/denominator replacement, mathematical runtime, Lean, repository write, activation of conditional square constants, route promotion, or RH claim is authorized.
