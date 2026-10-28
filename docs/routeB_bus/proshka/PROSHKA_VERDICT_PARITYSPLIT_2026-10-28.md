# STATUS: TRY_PARITYSPLIT_ODD_RESOLVENT_SIGN

```yaml
OPERATIVE_CLASS: TRY_PARITYSPLIT_ODD_RESOLVENT_SIGN
REQUEST_ID: REQ-2026-10-28-PARITYSPLIT
BOUNDARY_ID: GOAL058_G1_PARITY_SPLIT
REQUEST_COMMIT: 5086bf3f
REQUEST_GIT_BLOB: d41987a009cc5fe84b660c85f96335c271cb584e
SOURCE_BASE_COMMIT: a3174303e451541aad6538991602079ff9d9206f
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_SELECTED_FERRERS_FAMILY
Q1: G1B_KILL_PARTIAL
Q1_FIRST_UNPAID_BOUND: SOURCE_RAYLEIGH_LOWER_MARGIN_ABOVE_ODD_UPPER_ENVELOPE_AND_TRANSFER_ERROR
Q1_CONSUMERS: G1B_NOT_NECESSARY_FOR_MATHEMATICAL_ROOF_GIVEN_G1A_AND_DIRECT_G3
Q2a: G1A_REDUCED_TO_SIGN_LEMMA
Q2a_SIGN_LEMMA: EXISTS_T_BELOW_ODD_SPECTRUM_WITH_NEGATIVE_ODD_RESOLVENT_SECULAR_FUNCTION
Q2b: G1A_UNDECIDED_FIRST_FACT
Q2c: EXACT_BOUNDARY_RESOLVENT_IDENTITY_FOUND_BUT_RATIO_LAW_UNPROVED
SOURCE_FINDING_1: DIAGNOSTIC_ROW_WAS_REALIFIED_NOT_LITERAL_COMPLEX_REFERENCE
SOURCE_FINDING_2: ETA_OVERLAP_SCALING_REQUIRES_FACTOR_2M_PLUS_1
G1B_KILLED_COFINAL: false
G1A_PROVED_COFINAL: false
THETA_WITNESS_FOUND: false
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: ABSTRACT_IMPLICATIONS_AND_COFINAL_ODD_UPPER_ENVELOPE_ONLY
COFINAL_PARITY_SIGN: OPEN
COFINAL_SELECTED_RAYLEIGH_SIGN: OPEN
VERIFIER: PAPER
SYMBOLIC_SANITY_CHECKS: EXECUTED_EXACT_RATIONAL_AND_SYMBOLIC_ONLY
ARB_INTERVAL_EXECUTED: false
LEAN_EXECUTED: false
REPOSITORY_WRITTEN: false
BROAD_NUMERIC_SCAN: false
ROUTE_PROMOTION: false
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## 0. Verdict and source boundary

**Q1 — `G1B_KILL_PARTIAL`.** I do not obtain the requested eventual inequality for the literal selected row. I do prove an explicit, zero-location-independent upper envelope for a **two-dimensional odd trial space**. It gives an odd competitor orthogonal to **any** selected complex row, not merely an exactly even row. The missing input is a lower bound for the selected Rayleigh value exceeding that envelope and the reference-to-source error. No such lower bound is supplied by the table, T5, or the spectral decomposition alone.

**Q2(a) — `G1A_REDUCED_TO_SIGN_LEMMA`.** For the actual CCM displacement identity, strict ordering

\[
\lambda_{\min}(K_m|_{\rm even})<\lambda_{\min}(K_m|_{\rm odd})
\]

already forces **simplicity and nonzero \(\eta\)-overlap**. Those are not three independent suppliers. I eliminate the even block exactly and reduce the ordering to one scalar sign below the odd spectrum; see (4.7)–(4.11). A lowest-odd-pole residue supplies a cheaper sufficient test, with an explicit margin, but is not necessary.

**Q2(b) — `G1A_UNDECIDED_FIRST_FACT`.** No off-critical-zero mechanism forcing failure of this scalar sign is proved. The existing negative-bottom witness does not determine the parity ordering.

**Q2(c).** There is an exact boundary-resolvent identity for the observed ratio. There is **no proved cofinal law** keeping that ratio in a fixed interval, and no justification for identifying the all-ones vector with the pole-term vector. Nonzero \(\lambda_1\) alone does not force nonzero \(\eta\)-overlap.

The requested TXT was read through the GitHub connector at the owner-specified pin; that pinned delivery selects this task. The current protocol was fetched from `rh_clean`. Mathematical sources remain at the request's base commit, not current HEAD. Relevant source definitions and the primary CCM HTML were read, not replaced by summaries. Source references `[S…]` and their exact read scopes are in §9. The earlier verdict is historical context, not an additional theorem premise. No repository or Lean change was made.

### Claim ledger

| ID | Scope / verifier | Established result | What it does not establish |
|---|---|---|---|
| C1 | ABSTRACT / PAPER | Exact complex-row parity repair, (1.3)–(1.5) | A cofinal positive Rayleigh margin |
| C2 | COFINAL_FAMILY / PAPER | Two-dimensional odd upper envelope, (2.12) | An odd lower bound or positive selected Rayleigh value |
| C3 | ABSTRACT / PAPER | Source-transfer budgets, (1.7)–(1.9) | The applicability of the quoted T5 suppliers without their hypotheses |
| C4 | ABSTRACT / PAPER | Strict parity ordering implies all of G1a | The strict ordering on the literal tail |
| C5 | FINITE_CELL / PAPER | Exact odd-resolvent determinant identity, every \(m\) | A cofinal sign from finitely many evaluations |
| C6 | ABSTRACT / PAPER | Negative lowest-odd-pole residue is sufficient, with an explicit margin | Necessity of that residue sign |
| C7 | ABSTRACT / PAPER | Boundary Schur/residue formula for \(\cos^2\) | A source-specific bounded-ratio asymptotic |
| C8 | ABSTRACT / PAPER | G1b is dispensable for the mathematical roof given G1a and direct G3 | An already compiled replacement of the existing wrappers |
| C9 | COFINAL_FAMILY / CONDITIONAL | The resulting selected-row kill criterion, (3.2) | Its currently unpaid lower-envelope hypothesis |

Every result involving the literal source keeps \(m=N\), \(L=\log m\), modes \(-m,\ldots,m\), the identity Gram metric, the entire archimedean term and all prime powers. A generic structured counterexample below is explicitly not another CCM matrix.

## 1. Two source corrections, and an exact repair

### 1.1 The table does not use the stated complex reference row

**[FINITE_CELL | PAPER: source-code audit]** In `[S2]`, `selected_row(m)` first returns the complex reference \(z\). The subsequent code is

```python
zp = z * phase
imag_residue = norm(imag(zp)) / norm(zp)
q = real(zp)
q = q / norm(q)
```

The reported \(a_m,r_m,\delta_m,\alpha_m\) are computed from this last row. The discarded imaginary residue is explicitly nonzero in `[S3]`: approximately \(3.854868\times10^{-3}\) at \(m=2\), and \(1.517671\times10^{-41}\) at \(m=16\). These are noncertified diagnostics, not interval statements. Agreement at two precisions does not make the realification an identity.

The Mellin kernel in `[S5]` has the exact conjugation symmetry

\[
z_{-n}=\overline{z_n}
\tag{1.1}
\]

in its natural real-source phase: the recurrence coefficients are real and the kernel at \(-n\) is the conjugate of the kernel at \(n\). Thus \(\Re z\) is even and \(\Im z\) is odd. **Conjugate symmetry is not reflection-evenness.** An arbitrary phase rotation can mix these real parity parts; the implementation's phase choice must also be audited rather than assumed harmless for `real(zp)`.

Use distinct names henceforth:

\[
q^{\rm ref}=z/\|z\|,\quad q^+=\Re z/\|\Re z\|,
\quad q^{\rm src}=\text{literal selected source row}.
\]

The table's exactly even row is consistent with \(q^+\) in the reported phase. Its parity defect is not a certificate that \(q^{\rm ref}\), much less \(q^{\rm src}\), is exactly even. The older odd-floor audit already warns about selected odd contamination `[S11, PENALTY_SHORTCUT]`.

### 1.2 Realification does not automatically destroy the proposed sign mechanism

**[ABSTRACT | PAPER]** There is a stronger repair than paying a linear perturbation bound. Write

\[
q=c u+i s v,\qquad c^2+s^2=1,
\quad Ru=u,\quad Rv=-v,\quad \|u\|=\|v\|=1,
\tag{1.2}
\]

with real vectors and \(c>0\). Put

\[
a_+=u^*Ku,\quad a_-=v^*Kv,\quad
\mu=\lambda_{\min}(K|_{\rm odd}),\quad d=a_+-\mu.
\]

If the odd part is zero, the same statements hold with \(s=0\). Parity commutation gives

\[
a(q)=c^2a_++s^2a_-,\qquad a_-\ge\mu.
\tag{1.3}
\]

Consequently, if \(d>0\),

\[
a(q)-\mu\ge c^2d>0.
\tag{1.4}
\]

So a proved real-even reference inequality already implies failure of the trial-shifted odd floor for the full complex reference.

For the literal complement, let \(y\) be a real unit odd eigenvector at \(\mu\), put \(\rho=v^Ty\), and choose

\[
w=y+i(s/c)\rho u.
\]

Then \(q^*w=0\), and parity makes its Rayleigh quotient

\[
\frac{w^*Kw}{\|w\|^2}
=\frac{\mu+(s^2/c^2)\rho^2a_+}{1+(s^2/c^2)\rho^2}
\le\mu+s^2d.
\]

Subtracting (1.3) gives the exact one-sided repair

\[
\boxed{\delta(q)\le-(1-2s^2)d-s^2(a_--\mu)
\le-(1-2s^2)d.}
\tag{1.5}
\]

Thus \(s^2<1/2\) and \(a_+>\mu\) imply \(\delta(q)<0\). This uses neither the unknown ground state nor an assumption that every odd vector is orthogonal to the complex reference. It repairs the logical mechanism; it does **not** certify the supplied numerical inequalities or their eventual persistence.

### 1.3 Returning from reference to the exact source costs a relative margin

**[ABSTRACT | PAPER]** Suppose \(b=z+e\), \(\|e\|\le E<Z=\|z\|\), and \(t=E/Z\). After harmless phase alignment,

\[
\left\|\frac b{\|b\|}-\frac zZ\right\|\le2t.
\tag{1.6}
\]

For any \(\Gamma\ge\|K\|\),

\[
|a(q^{\rm src})-a(q^{\rm ref})|\le4\Gamma t,
\qquad
|\delta(q^{\rm src})-\delta(q^{\rm ref})|\le8\Gamma t.
\tag{1.7}
\]

The second inequality follows by a two-plane unitary sending one unit row to the other: its distance from the identity is at most their phase-aligned chordal distance. Conjugating \(K\) changes each compressed minimum by at most twice \(\Gamma\) times that distance; the Rayleigh shift costs the same amount.

One entirely explicit, deliberately loose source bound is

\[
\Gamma_m=(2m+1)\left[2\sqrt m+4\sqrt m\,L+9+
\frac{10+20\pi m}{L}\right].
\tag{1.8}
\]

Indeed, the pole operator has norm at most \(2\sqrt m\), the prime entries have modulus at most \(4\sqrt mL\), and the exact kernel satisfies \(|Q'_{n,k}|\le(2+4\pi m)/L\). In the archimedean entry use
\(\int_0^\infty s e^{s/2}/(e^s-e^{-s})\,ds<5\), and the constant term is bounded by \(4\) for \(m\ge2\). The entry bound is then \(9+(10+20\pi m)/L\); multiplying the maximum entry bound by the dimension proves (1.8). No conjecture on primes is used.

Combining (1.5)–(1.8), a sufficient reference-to-source kill margin is

\[
\boxed{(1-2s_m^2)(a_{+,m}-\mu_m)>8\Gamma_m t_m.}
\tag{1.9}
\]

**[COFINAL_FAMILY | CONDITIONAL]** T5 in `[S6]` supplies an exponentially small upper bound on \(t_m\) only under its matched-port, energy, tail and eventual-threshold hypotheses. It expressly does not apply its eventual estimates to the small diagnostic cells. Superpolynomial smallness alone does not establish (1.9): the margin being compared may be smaller still.

### 1.4 The overlap normalization has a missing dimension factor

**[FINITE_CELL | PAPER: source-code audit]** The script divides \(|\sum_n\xi_n|\) by \(\|\xi\|\sqrt{2m+1}\). With unit \(\xi\) and \(\eta=(1,\ldots,1)\), its quantity is

\[
\cos^2(\xi,\eta)=\frac{|\eta^*\xi|^2}{2m+1}.
\tag{1.10}
\]

Therefore bounded positive \(\cos^2/\lambda_1\), if eventually proved, would mean
\(|\eta^*\xi|^2\asymp(2m+1)\lambda_1\), not \(\asymp\lambda_1\).
For the source Dirichlet vector \(\delta_N=\eta/\sqrt L\), the corresponding factor is \((2m+1)/L\). This is a normalization correction, not an extrapolation of the table.

## 2. Q1: a source-preserving odd upper envelope, with all errors returned

This section pays the proposed upper side without a ground eigenvector. It also removes exact parity of the selected row from the complement-witness construction.

### 2.1 Two global odd null directions without a zero-location premise

**[ABSTRACT | PAPER]** Define

\[
h(x)=(24\pi x^2-16\pi^2x^4)e^{-\pi x^2},\qquad
G(t)=e^{t/2}\sum_{r\ge1}h(re^t).
\tag{2.1}
\]

The elementary Gaussian Fourier calculation gives \(\mathcal F_{2\pi}h=h\), \(h(0)=0\) and \(\int h=0\). Poisson summation then gives \(G(-t)=G(t)\). All real derivatives decay faster than any exponential. Direct Mellin integration, initially for \(\Re s>1\), gives

\[
\widehat G(z)=2s(1-s)\pi^{-s/2}\Gamma(s/2)\zeta(s)
=-4\xi(s),\qquad s=\tfrac12-iz.
\tag{2.2}
\]

Both sides are entire, so the equality holds everywhere. Differentiation multiplies this transform by a polynomial. The explicit Weil formula therefore gives

\[
\mathcal W(G',f)=\mathcal W(G''',f)=0
\tag{2.3}
\]

for each finite-window synthesis \(f\). The transform vanishes at every nontrivial zero, wherever it is located. Conjugate/reflected zero arguments are covered by the usual symmetries of \(\xi\). The mixed zero sum and prime sum converge absolutely here because one factor is smooth and superexponentially decreasing. This is the explicit formula, not its RH-equivalent positivity criterion. The source form and finite compression are those of `[S9,S10; CCM (3.10), (3.18), (4.2)–(4.4)]`.

Choose fixed orthonormal odd functions in this null space:

\[
g_1=\frac{G'}{\|G'\|_2},\qquad
\kappa=\frac{\|G''\|_2^2}{\|G'\|_2^2},\qquad
 g_2=\frac{G'''+\kappa G'}{\|G'''+\kappa G'\|_2}.
\tag{2.4}
\]

Integration by parts proves orthogonality. The second denominator cannot vanish: otherwise the nonzero decaying function \(G'\) would solve a constant-coefficient oscillator equation.

### 2.2 Periodize first, then truncate: the endpoints are exactly paid

**[COFINAL_FAMILY | PAPER]** Let \(b=L/2\), \(I=[-b,b]\), \(\omega_n=2\pi n/L\). For either \(g=g_i\), set

\[
g_L(t)=\sum_{k\in\mathbb Z}g(t+kL),\qquad
p_{g,m}(t)=\frac1L\sum_{|n|\le m}\widehat g(\omega_n)e^{i\omega_nt}
\quad(t\in I),
\tag{2.5}
\]

and extend \(p_{g,m}\) by zero. In the literal source basis
\(\psi_n=L^{-1/2}e^{2\pi in(t+b)/L}\), its coefficients are
\((-1)^nL^{-1/2}\widehat g(\omega_n)\). They are reflection-odd. In particular

\[
p_{g,m}(-b)=p_{g,m}(b)=0.
\]

Thus the zero extension is genuinely in \(H^1(\mathbb R)\); no boundary jump has been silently discarded. The carrier remains exactly \(-m,\ldots,m\).

For explicit Fourier-tail bounds, fix any \(0<\sigma<\pi/4\), for example \(\sigma=\pi/8\), and define

\[
A_{g,\sigma}=\max_{\epsilon=\pm1}\int_{\mathbb R}|g(t+i\epsilon\sigma)|\,dt.
\]

This is a finite fixed constant: the Gaussian series is analytic on that strip, Poisson evenness continues analytically, and both ends have superexponential decay on each closed narrower strip. Contour translation gives
\(|\widehat g(\omega)|\le A_{g,\sigma}e^{-\sigma|\omega|}\).
Put \(r=e^{-4\pi\sigma/L}\), and define

\[
T_g^2=\frac{2A_{g,\sigma}^2}{L}\frac{r^{m+1}}{1-r},
\tag{2.6}
\]

\[
D_g^2=\frac{2A_{g,\sigma}^2}{L}\left(\frac{2\pi}{L}\right)^2r^{m+1}
\left[\frac{(m+1)^2}{1-r}+\frac{2(m+1)r}{(1-r)^2}
+\frac{r(1+r)}{(1-r)^3}\right].
\tag{2.7}
\]

These bound respectively the \(L^2(I)\) tail and its derivative. The sums in (2.6)–(2.7) are geometric sums, not numerical fits.

To include the periodization and exterior returns, define

\[
J_{g,j}(m)=\sup_{t\in I}\sum_{k\ne0}|g^{(j)}(t+kL)|,\quad j=0,1,
\qquad U_g=T_g+\sqrt L J_{g,0},
\]

\[
\begin{aligned}
E_{g,0}&=U_g+\|g\mathbf1_{I^c}\|_2,\\
E_{g,1}&=D_g+\sqrt L J_{g,1}+\|g'\mathbf1_{I^c}\|_2,\\
E_{g,w}&=\sqrt m\,U_g+\|e^{|t|}g\mathbf1_{I^c}\|_2,\\
A_g^{\rm ret}&=\sqrt L\,m^{1/4}U_g+
\int_{I^c}e^{|t|/2}|g(t)|\,dt.
\end{aligned}
\tag{2.8}
\]

These bound the corresponding norms of the **global** error \(e=p_{g,m}-g\). The image sums and exterior terms are explicit Gaussian-series tails, of the form \(O(m^{C_g}e^{-\pi m})\) up to harmless powers of \(L\). They are retained in (2.8), not replaced by zero.

### 2.3 Full Weil-form error, including primes beyond the original cutoff in the return

**[ABSTRACT | PAPER]** For any finite-window \(f\), the pole term costs at most
\(2m^{1/4}A_g^{\rm ret}\|f\|_2\).
For the prime term,

\[
|Q_{e,f}(s)|\le2\sqrt m\,e^{-s}E_{g,w}\|f\|_2\quad(s\ge0),
\qquad
\sum_{n\ge2}\frac{\Lambda(n)}{n^{3/2}}
\le\sum_{n\ge2}\frac{\log n}{n^{3/2}}<5.
\]

Thus the **infinite** mixed prime return costs at most
\(10\sqrt m E_{g,w}\|f\|_2\). All prime powers are present. The infinite tail occurs because the global null function was subtracted, even though the original finite-matrix prime sum stops at \(m\).

For the archimedean term, global \(H^1\) regularity gives

\[
|Q_{e,f}(s)-Q_{e,f}(0)|\le2s\|e'\|_2\|f\|_2.
\]

Together with \(\int_0^\infty s e^{s/2}/(e^s-e^{-s})\,ds<5\) and
\(\gamma+\log(4\pi)<4\), this pays the complete archimedean contribution by
\((9E_{g,0}+10E_{g,1})\|f\|_2\).
Consequently

\[
\boxed{|\mathcal W(p_{g,m},f)|=|\mathcal W(e,f)|
\le H_g(m)\|f\|_2,}
\]

\[
H_g(m)=2m^{1/4}A_g^{\rm ret}+10\sqrt m E_{g,w}
+9E_{g,0}+10E_{g,1}.
\tag{2.9}
\]

Every constant in this envelope is specified by (2.4), (2.6)–(2.9); no uncomputed source spectral gap is used.

### 2.4 A competitor orthogonal to any selected row

**[COFINAL_FAMILY | PAPER]** Set

\[
\varepsilon_m=(E_{g_1,0}^2+E_{g_2,0}^2)^{1/2},\qquad
B_m=\frac{\sqrt{H_{g_1}(m)^2+H_{g_2}(m)^2}}{1-\varepsilon_m},
\quad \varepsilon_m<1.
\tag{2.10}
\]

Since the global \(g_1,g_2\) are orthonormal, the map
\((c_1,c_2)\mapsto c_1p_{g_1,m}+c_2p_{g_2,m}\) has smallest singular value at least \(1-\varepsilon_m\). Its image \(S_m\) is therefore a two-dimensional odd subspace of the original carrier. By (2.9), for every \(p\in S_m\),

\[
|\mathcal W(p,p)|\le B_m\|p\|_2^2.
\tag{2.11}
\]

For **any** unit complex row \(q\), \(S_m\cap q^\perp\) has dimension at least one. Choosing a unit vector there yields

\[
\boxed{\lambda_{\min}(K_m|_{\rm odd})\le B_m,\qquad
\delta_m(q)\le B_m-a_m(q).}
\tag{2.12}
\]

In fact (2.9) also controls the full residual norm of vectors in this small trial space. It does not control the bottom eigenspace of the entire odd carrier.

For every fixed \(0<c<\pi^2/2\), the above choice \(\sigma=c/(2\pi)\) gives

\[
B_m\le C_c\,m\exp\!\left(-c\frac m{\log m}\right)
\quad\text{eventually}.
\tag{2.13}
\]

In particular \(B_m=O_A(m^{-A})\) for every fixed \(A>0\). The constants are fixed analytic norms of the two explicit functions, not constants depending on the claim being proved. This is a PAPER envelope, not an executed interval certificate. Crucially, (2.12) is an **upper** bound on the odd minimum, not an estimate of its absolute value.

## 3. Q1 closeout: what remains unpaid, and which consumers actually need G1b

### 3.1 The missing lower bound is not hidden inside the spectral expansion

**[COFINAL_FAMILY | CONDITIONAL]** A sufficient literal-source kill would now be

\[
a_m(q^{\rm src})>B_m
\quad\text{on every sufficiently late original cell}.
\tag{3.1}
\]

Using the reference rectangle, a directly checkable stronger interface is

\[
\boxed{\frac{z_m^*K_mz_m}{\|z_m\|^2}>B_m+4\Gamma_m t_m
\quad\text{eventually}.}
\tag{3.2}
\]

Then (1.7) and (2.12) give an actual negative upper envelope for the shifted complement and for an odd witness. That would kill G1b in the requested theorem shape. **The strict lower envelope in (3.2) is not proved here.** Nor is the weaker exact target \(a_m>\mu_m\) proved. Failure to prove (3.2) would not refute that target, because \(B_m\) need not be sharp.

**[ABSTRACT | PAPER]** The identity
\(a-\lambda_1=\sum_{i\ge2}(\lambda_i-\lambda_1)|c_i|^2\)
is exact, but supplies no independent lower bound for the row-dependent mass on high eigenvalues. Even for an exactly even row, one needs a lower bound on its spectral weight in a specified even band and a lower bound for that band's energy. A measured angle on finitely many cells gives neither eventual bound.

The null-function approximation also supplies no sign for the selected error energy. When a global null component is removed, the remaining full Weil form is still signed. Its smallness does not imply a positive lower bound. The current shelf therefore supports **`G1B_KILL_PARTIAL`**, not `G1B_KILLED_COFINAL` and not `G1B_SURVIVES`.

### 3.2 Consumers: mathematical necessity versus present implementation

**[ABSTRACT | PAPER]** The source theorem `[S8, lines 161ff.]` consumes a bottom eigenvector, simplicity, and \(\eta^*\xi=1\), plus the displayed bottom-Rayleigh and quotient-basis inputs. It does not consume \(q_m\), \(a_m\), \(r_m\), or a selected-row complement floor.

In `[S7,S11]`, the selected floor and residual-ratio hypotheses feed the existing selected-ground extraction/tracking wrappers. The odd floor is used to exclude an odd ground branch; the tail reindex wrapper consumes it separately. The proposed cellwise replacement would again be a **sufficient supplier** for those wrappers, not a necessary property of the desired ground state.

Once G1a is supplied directly, the chain can instead use that same ground row for G2, G2b and its entire transform, and prove G3 directly at transform level. Then G3c/G4 and the same-family normalization give the convergence consumed by the roof. No mathematical roof link requires G1b in this construction. The existing wrappers do not automatically become compiled proofs with their hypotheses deleted: an honest replacement must preserve the exact ground family, its normalization and tail schedule.

**P1c is confirmed in this mathematical sense.** The construction of the directly normalized family and its convergence remains work; it is not a new admission.

### 3.3 The permitted change of reference row

**[ABSTRACT | PAPER]** A noncircular alternative is the normalized finite Fourier projection of the explicit \(G\), rather than the selected Ferrers combination. It is defined without knowing a ground eigenvector. But replacing the reference changes \(a,r,\delta\); a kill for one selected row is not invariant under this change. No eventual sign for the new row is proved here. The difficulty moves to proving that its transform tracks the **actual** ground transform, with the required normalization. I do not substitute this row for the literal row in the Q1 verdict.

## 4. Q2(a): G1a reduces to one scalar sign, not three spectral suppliers

### 4.1 Exact source blocks and the displacement identity

**[FINITE_CELL | PAPER]** Write

\[
A_n=K_{n,n},\qquad b_n=nK_{n,0}\ (n\ne0),\qquad b_0=0.
\]

These are source entries, not the selected Rayleigh value \(a_m\). The literal kernels give

\[
K_{n,k}=\frac{b_n-b_k}{n-k}\quad(n\ne k),
\qquad A_{-n}=A_n,\quad b_{-n}=-b_n.
\tag{4.1}
\]

Equivalently, with \(D=\operatorname{diag}(-m,\ldots,m)\),

\[
[D,K]=\beta\eta^*-\eta\beta^*,\quad
\beta=(b_{-m},\ldots,b_m)^T,\quad R\beta=-\beta,
\quad RD=-DR.
\tag{4.2}
\]

This is CCM Lemmas 5.1–5.2, and also follows entrywise from the pinned definitions. No sign of \(K\) is assumed.

Let \(\mathsf E\) and \(\mathsf O\) denote the even and odd blocks in the bases supplied by the request. For \(1\le n,k\le m\),

\[
\begin{aligned}
\mathsf E_{00}&=A_0,&
\mathsf E_{0n}&=\sqrt2\,b_n/n,\\
\mathsf E_{nn}&=A_n+b_n/n,&
\mathsf O_{nn}&=A_n-b_n/n,\\
\mathsf E_{nk}&=\frac{2(nb_n-kb_k)}{n^2-k^2},&
\mathsf O_{nk}&=\frac{2(kb_n-nb_k)}{n^2-k^2}\quad(n\ne k).
\end{aligned}
\tag{4.3}
\]

Set

\[
B=\operatorname{diag}(1,\ldots,m),\quad
J=(0\ B),\quad h=(1,\sqrt2,\ldots,\sqrt2)^T,
\quad\beta_o=\sqrt2(b_1,\ldots,b_m)^T.
\]

The lower-left parity block of (4.2) is

\[
\boxed{J\mathsf E-\mathsf OJ=\beta_o h^T.}
\tag{4.4}
\]

### 4.2 Strict parity ordering already forces simplicity and normalization

**[ABSTRACT | PAPER]** Let \(\mu=\lambda_{\min}(\mathsf O)\). Suppose \(x\) is an even eigenvector at \(\lambda<\mu\) with \(\eta^*x=0\). Since \(\beta\) is odd, \(\beta^*x=0\). Equation (4.2) gives

\[
KDx=\lambda Dx.
\]

But \(Dx\) is odd, and \(\lambda<\mu\); hence \(Dx=0\). The kernel of \(D\) is the central coordinate line, whose nonzero vectors have nonzero \(\eta\)-pairing. Thus \(x=0\).

It follows that the functional \(\eta^*\) is injective on every even eigenspace below the odd bottom. Such an eigenspace has dimension at most one. Therefore

\[
\boxed{\lambda_{\min}(\mathsf E)<\lambda_{\min}(\mathsf O)
\ \Longrightarrow\ \text{simple even ground state with }\eta^*\xi\ne0.}
\tag{4.5}
\]

The converse follows because an odd eigenvalue equal to the even bottom would make the full bottom degenerate. Hence, for these source matrices,

\[
\boxed{\mathrm{G1a}\quad\Longleftrightarrow\quad
\lambda_{\min}(\mathsf E)<\lambda_{\min}(\mathsf O).}
\tag{4.6}
\]

This holds for each finite cell, whether the common bottom is positive, zero or negative. It is not a positivity assumption and has no selected-row hypothesis. The normalization observation in CCM just before Lemma 5.4 is consistent with this argument; here the strict parity inequality also supplies simplicity.

### 4.3 Eliminate the even block exactly

**[FINITE_CELL | PAPER]** Define

\[
d=B^{-1}(\sqrt2,\ldots,\sqrt2)^T,
\qquad v(t)=(A_0-t)d-B^{-2}\beta_o,
\]

\[
\boxed{\mathfrak f_m(t)=A_0-t+
 v(t)^T(\mathsf O-tI)^{-1}\beta_o,
\qquad t<\mu.}
\tag{4.7}
\]

Then

\[
\boxed{\det(\mathsf E-tI)=\det(\mathsf O-tI)\,\mathfrak f_m(t).}
\tag{4.8}
\]

**Proof.** For an even coefficient vector \(x\), introduce the invertible coordinates
\(s=h^Tx\), \(y=Jx\). Its central coordinate is \(x_0=s-d^Ty\), and its remaining coordinates are \(B^{-1}y\). The central equation and (4.4) transform \((\mathsf E-tI)x=0\) into

\[
\begin{pmatrix}
A_0-t & \beta_o^TB^{-2}-(A_0-t)d^T\\
\beta_o & \mathsf O-tI
\end{pmatrix}
\binom{s}{y}=0.
\tag{4.9}
\]

The input and output coordinate transformations have equal determinant \(\det B\), so there is no missing determinant or Gram factor. Taking the Schur complement proves (4.8).

For \(t<\mu\), \(\det(\mathsf O-tI)>0\), and \(\mathfrak f_m(t)>0\) for sufficiently negative \(t\). If \(\mathfrak f_m(t)<0\), an even eigenvalue lies below \(t\), and (4.5) applies. Conversely, if G1a holds, choose \(t\) strictly between its even bottom and the smaller of the next even eigenvalue and \(\mu\). Then precisely one even eigenvalue lies below \(t\), so (4.8) is negative. Consequently

\[
\boxed{\mathrm{G1a}\quad\Longleftrightarrow\quad
\exists t<\lambda_{\min}(\mathsf O):\ \mathfrak f_m(t)<0.}
\tag{4.10}
\]

This is an exact equivalence, not a sufficient norm bound relabeled as necessary. It needs only the **odd** block, the source central entry and the displacement row. The scalar function is not asserted to be monotone.

### 4.4 The cofinal sign lemma and its unpaid term

**[COFINAL_FAMILY | CONDITIONAL]** A source-verifiable version is:

> On every sufficiently late original cell, construct source-defined real \(t_m\) and positive \(\ell_m,\kappa_m\) such that
> \[
> \mathsf O_m-t_mI\succeq\ell_mI,
> \qquad
> \mathfrak f_m(t_m)\le-\kappa_m<0.
> \tag{4.11}
> \]

Then the parity gap exceeds \(\ell_m\), and G1a follows by (4.5). These margins are allowed to shrink; no fixed positive floor or polynomial gap is smuggled in. A negative upper envelope for the scalar sign and a positive lower envelope for the odd resolvent domain are required. An unsigned bound on the scalar correlation is not enough.

The first unpaid term is precisely

\[
\big[(A_0-t_m)d-B^{-2}\beta_o\big]^T
(\mathsf O_m-t_mI)^{-1}\beta_o
\ <\ -(A_0-t_m),
\tag{4.12}
\]

together with its certified domain. **No cofinal order of \(\ell_m\), \(\kappa_m\), or the actual parity gap is proved by the present shelf.** Equations (4.7)–(4.12) specify the objects and exact budgets without inventing such an order from the table.

### 4.5 A cheaper sufficient sign: the lowest odd pole

**[ABSTRACT | PAPER]** Let \(\Pi\) be the full spectral projector of \(\mathsf O\) at \(\mu\), including any multiplicity, and put

\[
v_0=(A_0-\mu)d-B^{-2}\beta_o,
\qquad \mathcal R_m=v_0^T\Pi\beta_o.
\tag{4.13}
\]

If there is a higher distinct odd eigenvalue, let \(g_o\) be its distance from \(\mu\). Otherwise set the expressions involving \((I-\Pi)\beta_o/g_o\) below to zero. For \(0<\epsilon\le1\), the exact resolvent decomposition gives

\[
\mathfrak f_m(\mu-\epsilon)
=\frac{\mathcal R_m}{\epsilon}+\mathcal C_m(\epsilon),
\tag{4.14}
\]

with

\[
|\mathcal C_m(\epsilon)|\le C_m:=|A_0-\mu|+1
+\|d\|\|\Pi\beta_o\|
+\frac{(\|v_0\|+\|d\|)\|(I-\Pi)\beta_o\|}{g_o}.
\tag{4.15}
\]

Hence the **single sign** \(\mathcal R_m<0\) supplies an explicit bracket:

\[
\epsilon_m=\min\left(1,\frac{-\mathcal R_m}{2C_m}\right)>0,
\quad t_m=\mu-\epsilon_m,
\quad\mathfrak f_m(t_m)\le-C_m<0.
\tag{4.16}
\]

The resulting parity gap is greater than \(\epsilon_m\). This gives exact orders relative to the actual odd spectral residue and regular remainder; it does not estimate those two source quantities cofinally. No simplicity of the odd bottom is required.

**Strong limitation.** This residue test is sufficient, not necessary. In the structured three-mode example with \(A_0=0,A_1=1,b_1=-1\),

\[
\mathsf E=\begin{pmatrix}0&-\sqrt2\\-\sqrt2&0\end{pmatrix},
\qquad\mathsf O=(2),\qquad\mathcal R=2>0,
\]

yet G1a holds. There are two even eigenvalues below the odd pole, and \(\mathfrak f\) is negative between them. A nonnegative residue therefore cannot kill G1a. If the residue is zero or an interval straddles zero, the discriminator is the full function (4.7) on its certified domain, not an assertion that the parity gap vanished.

## 5. Q2(b): the exact Theta question that remains

**[ABSTRACT | PAPER]** The negative-bottom witness alone cannot decide G1a. For example, the preceding structured matrix, shifted by \(-M_mI\), has

\[
\lambda_{\rm even}=-\sqrt2-M_m,\qquad
\lambda_{\rm odd}=2-M_m,
\]

with a fixed positive parity gap, a simple even bottom and unchanged nonzero \(\eta\)-overlap, for any positive \(M_m\), including
\(M_m=m^\delta/(\log m)^{2\delta}\). Reflection, the diagonal generator and the rank-two commutator are unchanged by this shift.

This is **not** the literal arithmetic CCM family and does not prove that G1a is not Theta-graded. It proves only that the scalar negative-bottom conclusion, even combined with the displayed structural identities, is insufficient to establish a Theta-witness. It avoids the already rejected parity-twin argument.

**[COFINAL_FAMILY | CONDITIONAL]** On the literal family, (4.10) identifies the missing implication exactly. A Theta-witness would have to show that an off-critical zero forces, on infinitely many original cells,

\[
\mathfrak f_m(t)\ge0\qquad\text{for every }t<\lambda_{\min}(\mathsf O_m).
\tag{5.1}
\]

Equivalently it must force the non-strict reversed parity ordering. No such relation between the zero and the **signed odd resolvent correlation** in (4.12) has been established. Neither a full-minimum upper bound nor two separate sector upper bounds supply it. The absence of this implication is not evidence that it is impossible.

**Result: `G1A_UNDECIDED_FIRST_FACT`.** Simplicity and \(\eta\)-normalizability below the odd spectrum are now proved without zero input. Eventual strict parity ordering, and its possible dependence on Theta, remain unpaid.

## 6. Q2(c): the observed ratio is a boundary spectral weight

### 6.1 The pole vector is not the all-ones vector

**[FINITE_CELL | PAPER]** From the literal pole entry in `[S10]`, define

\[
u_n=\frac{L}{L^2+16\pi^2n^2},\qquad
v_n=\frac{4\pi n}{L^2+16\pi^2n^2},\qquad
\kappa_L=32L\sinh^2(L/4).
\]

Then exactly

\[
W_{0,2}=\kappa_L(uu^T-vv^T).
\tag{6.1}
\]

The vector \(u\) is even, \(v\) is odd, and \(u\) is not proportional to \(\eta\) when \(m\ge1\). On a unit even eigenvector,

\[
\lambda=\kappa_L|u^T\xi|^2
-\xi^T(W_{\mathbb R}+\mathrm{Prime})\xi.
\tag{6.2}
\]

Calling \(\lambda\) “the pole-term energy” requires a proved bound or cancellation for the last term. Relating its pole functional to \(\eta\) requires another identity. Neither follows from the displayed ratio. In contrast, \(\eta^T\xi/\sqrt L\) is the endpoint value of the source synthesis, so the observed quantity naturally belongs to a **boundary** resolvent.

### 6.2 Exact Schur/residue identity

**[ABSTRACT | PAPER]** Suppose G1a holds on a particular cell and write \(\lambda=\lambda_1\). In the even block let
\(e=h/\sqrt{2m+1}\) be the normalized all-ones direction. Decompose

\[
\mathsf E=\begin{pmatrix}a_\eta&w^T\\w&C\end{pmatrix}
\quad\text{on }\mathbb Re\oplus e^\perp.
\]

By (4.5), the simple ground vector has nonzero \(e\)-component, and consequently \(C-\lambda I\succ0\). Define

\[
S(z)=a_\eta-z-w^T(C-zI)^{-1}w.
\tag{6.3}
\]

Then \(S(\lambda)=0\),
\(e^T(\mathsf E-zI)^{-1}e=1/S(z)\) where defined, and normalization of the eigenvector gives

\[
\boxed{\cos^2(\xi,\eta)=
\frac1{1+w^T(C-\lambda I)^{-2}w}
=-\frac1{S'(\lambda)}.}
\tag{6.4}
\]

Therefore for \(\lambda\ne0\),

\[
\boxed{\frac{\cos^2(\xi,\eta)}{\lambda}
=-\frac1{\lambda S'(\lambda)}.}
\tag{6.5}
\]

This is an exact identity, not a fit. It includes the dimension normalization in (1.10). But its right side still requires a **source-specific derivative estimate**. It does not establish the observed numerical range or an eventual constant ratio.

When \(\lambda>0\), a second exact identity is useful:

\[
S(0)=\lambda\left[1+w^TC^{-1}(C-\lambda I)^{-1}w\right],
\tag{6.6}
\]

\[
\frac{\cos^2}{\lambda}
=\frac{1+w^TC^{-1}(C-\lambda I)^{-1}w}
{S(0)\,[1+w^T(C-\lambda I)^{-2}w]}.
\tag{6.7}
\]

Let \(\theta=\lambda/\lambda_{\min}(C)<1\). Comparison in the spectral basis of \(C\) yields

\[
\frac{1-\theta}{S(0)}
\le\frac{\cos^2}{\lambda}\le\frac1{S(0)}.
\tag{6.8}
\]

Thus a bounded positive boundary Schur complement \(S(0)\), together with controlled \(\theta\), is a precise possible mechanism for the symptom. Neither a uniform positive bound for this Schur complement nor quantitative control keeping \(\theta\) away from 1 has been proved on the actual tail. The odd gap does not automatically bound this different compression \(C\).

The related identity

\[
\frac{\eta^TK^{-1}\eta}{2m+1}
=\sum_i\frac{\cos^2(\xi_i,\eta)}{\lambda_i}
\tag{6.9}
\]

holds when \(K\) is invertible. If \(K\succ0\), all terms are nonnegative; identifying the sum with its ground contribution would require control of every other even mode. No such dominance is assumed.

### 6.3 Nonzero eigenvalue is not the normalization mechanism

**[ABSTRACT | PAPER]** In the structured three-mode example
\(A_0=12,A_1=2,b_1=1\), the odd eigenvalue is \(1\), while the two even eigenvalues are \((15\pm\sqrt{89})/2>1\). The simple ground state is odd, \(\lambda_1=1\ne0\), and \(\eta^*\xi=0\). This matrix has the same reflection/displacement structure, but is not the literal CCM matrix. It refutes the proposed deduction from nonzero eigenvalue and that structure alone.

Conversely, \(A_0=0,A_1=1,b_1=0\) has a simple even central ground state with \(\lambda_1=0\) and nonzero \(\eta\)-pairing. Thus nonzero eigenvalue is not necessary either.

For the literal CCM family, (4.5) supplies normalization from strict parity ordering, irrespective of the sign or vanishing of \(\lambda_1\). The ratio identity is informative about a boundary spectral weight; it is not a substitute for that parity sign.

## 7. Route map, strongest attacks and dependency epistemics

### 7.1 Two concrete representations for the unresolved signs

| Route | Decisive object / test | Kill-power and cost estimate | Main risk / status |
|---|---|---|---|
| **Chosen: odd resolvent** | A cofinal bracket (4.11), using the exact scalar (4.7); first try the residue (4.13) without making it mandatory | High relevance to G1a; medium algebraic cost, high remaining analytic cost; no full even eigensolve needed | Signed source correlation and domain lower bound are OPEN |
| **Selected-row separation** | A one-sided lower envelope (3.2), compared with the explicit two-dimensional odd envelope (2.10) | Decisive for the exact G1b theorem shape; upper side paid, lower side high cost | Upper envelope may be too loose; a failed comparison is not survival of G1b |

These are proof-cost estimates, not wall-clock promises or measured success probabilities. No escalated computation is authorized by this verdict.

**Cross-domain checks.** The displacement identity supplies the exact parity intertwining (4.4), rather than a generic positivity analogy. The boundary Schur complement supplies the exact resolvent identities (6.3)–(6.8), rather than a guessed pole-energy law. Poisson/Mellin and the Weil formula supply the vanishing identity (2.3), and explicit finite-window returns pay its compression. None of these identities provides the missing selected-Rayleigh lower sign or the cofinal scalar sign (4.12).

**Collapse object.** A source-defined signed odd-resolvent bracket satisfying (4.11) would settle G1a on the whole tail in one move. A lower envelope in (3.2) would kill the selected G1b shape on the whole tail in one move. Neither requires one-cell-at-a-time promotion.

### 7.2 Strongest attacks and precise repair boundaries

**[ABSTRACT | PAPER]** The realification finding is material, but dismissing all the finite observations because of it would also be wrong. Equations (1.3)–(1.5) give an exact repair for a conjugate-symmetric reference, provided the displayed inequalities and odd mass are rigorously supplied. The remaining reference-to-source margin is separate.

**[ABSTRACT | PAPER]** The negative-pole-residue test is not equivalent to G1a. The explicit example following (4.16) defeats that overclaim. Keep (4.10), not merely \(\mathcal R_m<0\), as the equivalent interface.

**[ABSTRACT | PAPER]** Deep negative eigenvalues, even with the same reflection and displacement structure, do not force odd bottom parity. The scalar-shift family in §5 defeats that attempted inference, not a theorem about actual zeta zeros.

**[ABSTRACT | PAPER]** Nonzero ground eigenvalue does not force boundary overlap. The positive, simple odd-bottom example in §6.3 defeats that attempted structural implication. This is not a counterexample to actual G1a on the CCM schedule.

**[COFINAL_FAMILY | PAPER]** The two-dimensional odd near-null space does not order the actual odd minimum relative to the even minimum. A near-zero trial quotient can coexist with a much more negative eigenvalue. Likewise it does not prove that the selected Rayleigh value is positive. The one-sided direction is retained throughout.

The old August odd-floor verdict `[S11]` explicitly says `MATHEMATICAL_TARGET_PROVED_FALSE: false`. Its supplier-shelf rejection must not be promoted to an already proved cofinal negation of the literal odd floor. The independent constant-complement-floor obstruction is a different theorem shape.

### 7.3 Consumer-first contracts

```yaml
G1B_DEPENDENCY_AUDIT:
  DOWNSTREAM_CONSUMER: selected-ground extraction/tracking wrappers; ultimately G2 and hconv
  ACTUAL_CONSUMER_REQUIREMENT: same-family real-rooted ground transform and compact-uniform convergence
  ORIGINAL_REQUESTED_OBJECT: positive selected-row cellwise complement floor plus residual ratio and trial-shifted odd floor
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - G1a supplies the bottom/simple/eta-normalized input to G2 directly
    - direct transform error tending to zero plus G3c/G4 supplies hconv without the norm-floor route
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: parity-aware complex-row repair and uniform two-dimensional odd comparison space
  REOPEN_TRIGGER: an actual cofinal lower envelope above B_m plus the 4*Gamma_m*t_m source return
  COFINAL_KILL_EVIDENCE: NONE

G1A_DEPENDENCY_AUDIT:
  DOWNSTREAM_CONSUMER: ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
  ACTUAL_CONSUMER_REQUIREMENT: bottom eigenvector with one-dimensional eigenspace and nonzero eta-pairing
  ORIGINAL_REQUESTED_OBJECT: strict even-below-odd ordering, simplicity, eta-pairing
  ORIGINAL_OBJECT_IS: PROVED_NECESSARY
  NECESSITY_SCOPE: this simple-even ground interface, not every possible real-zero or RH route
  KNOWN_WEAKER_INTERFACES:
    - the strict parity comparison alone implies the other two requirements by the displacement identity
    - existence of t below the odd spectrum with f_m(t)<0 is equivalent
    - negative lowest-odd-pole residue is sufficient only, not necessary
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: exact odd-only secular function with no even eigenvector input
  REOPEN_TRIGGER: cofinal lower odd-domain and upper scalar-sign certificates in equation 4.11
  MATHEMATICALLY_DEAD: false

THETA_DEPENDENCY_AUDIT:
  DOWNSTREAM_CONSUMER: deciding whether off-critical zeros force failure of G1a
  ACTUAL_CONSUMER_REQUIREMENT: a source-specific implication to failure of equation 4.10
  ORIGINAL_REQUESTED_OBJECT: a cofinal parity/simplicity/normalization witness from an off-critical zero
  ORIGINAL_OBJECT_IS: UNKNOWN
  KNOWN_WEAKER_INTERFACES:
    - source-specific sign control of the odd-resolvent correlation is the first exact target
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: UNRESOLVED
  NOVELTY_AXIS: separates scalar bottom growth from signed parity comparison
  REOPEN_TRIGGER: a zero-residue calculation reaching equation 5.1 on the literal matrices

RATIO_DEPENDENCY_AUDIT:
  DOWNSTREAM_CONSUMER: explanation of the eta-overlap symptom, not a required roof input
  ACTUAL_CONSUMER_REQUIREMENT: quantitative control of -lambda_1*S_prime(lambda_1)
  ORIGINAL_REQUESTED_OBJECT: a pole-energy explanation of cos_squared/lambda_1
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - strict parity ordering already proves nonzero eta-pairing, including at lambda_1=0
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: normalized boundary spectral weight rather than pole vector
  REOPEN_TRIGGER: cofinal boundary-Schur and compression-gap budgets for equations 6.5 through 6.8
```

No `ROUTE_FAMILY` death is asserted. The generic counterexamples refute only the stated structural implications; the source-code finding refutes the claim that the table computed the unmodified complex row. The literal cofinal targets remain separately classified.

## 8. Predictions, validation and meta closeout

### 8.1 Frozen observer predictions

| Prediction | Frozen probability | Fate in this batch |
|---|---:|---|
| P1: cofinal kill / partial / survives | 0.45 / 0.45 / 0.10 | **PARTIAL**. Odd upper side is paid; selected lower margin is not |
| P1c: G1b dispensable given G1a and direct G3 | 0.75 | **Confirmed**, for the mathematical chain; existing wrappers still require honest replacement |
| P2(a): proved / sign reduction / undecided | 0.10 / 0.55 / 0.35 | **Sign reduction**. Simplicity and normalization follow from the one remaining ordering |
| P2(b): Theta-witness found | 0.15 | **Not found; mathematical question remains unresolved** |
| P2(c): exact identity behind the ratio | 0.40 | **Partial**: exact boundary-resolvent identity found; no source-specific bounded-ratio law proved |

The probabilities have not been changed. Lack of a Theta-witness is not a proof that none exists. An always-valid spectral-weight identity is not counted as an explanation of the observed constant-sized range.

### 8.2 Registered checks and what was actually executed

Before the symbolic checks I registered three checks in the conversation: the displacement reduction, the complex-row repair, and a resolvent interpretation rather than a pole-energy identification. The execution was restricted to a small exact SymPy calculation, not a numerical CCM scan.

```text
N=2 exact displacement and secular determinant identities: PASS
Complex-row complement repair identity: PASS
Positive lowest-odd-pole residue does not refute G1a: PASS
Structured nonzero odd ground eigenvalue has zero eta overlap: PASS
Boundary Schur capacity identity: PASS
```

These checks verify algebraic transcriptions and planted counterexamples. The all-dimension implications and the cofinal odd envelope are justified by their PAPER proofs above, not inferred from the symbolic test. No Lean run, interval certification, or independent second reviewer is claimed.

The previously named first fact from THETAGRADE is now more precise: the relevant cofinal unknown is not three independent ground-state properties, but the signed odd-resolvent bracket (4.11). The supplied finite parity data remain diagnostic.

### 8.3 Minimal missing identities and closeout

**What became smaller?** On the G1a side, simplicity and normalization are discharged once parity ordering holds, and that ordering is reduced to an odd-only scalar function. On the G1b side, the odd upper/witness construction no longer requires exact evenness of the selected row; the unpaid side is the selected Rayleigh lower margin.

**What was refuted?** The assertion that the diagnostic row is the unchanged complex reference; the dimension-free reading of the raw \(\eta\)-overlap; and the generic implications “negative bottom forces parity failure,” “nonzero eigenvalue forces normalization,” and “nonnegative lowest-pole residue disproves G1a.” Each has the exact scope and evidence stated above. G1b was not killed cofinally.

**What must not be repeated?** Do not silently realify the selected row, replace a shrinking margin by the phrase “superpolynomial error,” promote the fifteen cells to an eventual statement, or identify a sufficient residue test with the full scalar criterion.

**Smallest source sign:** the lower-domain/upper-sign pair (4.11). **Smallest source kill margin:** (3.2), or a sharper direct \(a_m>\mu_m\) comparison with all source returns paid.

**DISCRIMINATORS:** for a zero-consistent parity calculation, use a strict negative upper enclosure for \(\mathfrak f_m(t)\) below a certified odd lower barrier; if the lowest-pole residue vanishes, evaluate the full regular-plus-pole function rather than conclude equality of sectors. For the ratio, distinguish a constant-sized law from a coincidence by bounding \(-\lambda_1S'(\lambda_1)\), or equivalently the two quantities in (6.8), on the original family. For the proposed G1b kill, the discriminator is a strictly positive lower envelope for \(a^{\rm ref}_m-B_m-4\Gamma_mt_m\), not a fit to \(a_m\).

```yaml
iteration:
  target: GOAL058_G1_PARITY_SPLIT
  status: PROGRESS
  supplier_status: OPEN_SOURCE_SIGNS
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: treat finite realified-row diagnostics as literal cofinal selected-row facts
  new_gap_name: cofinal odd-resolvent sign and selected-Rayleigh separation margin
  invariant_learned: strict parity ordering already forces simplicity and eta-normalizability for this displacement class
  forbidden_future_move: suppress the odd imaginary row or infer cofinal signs from precision agreement
  next_decisive_test: a source-defined odd-resolvent bracket with two one-sided envelopes
  route_score: 4
  route_score_scope: algebraic reduction and falsification of surrogate inferences, not a closed RH front
```

## 9. Research log

### 9.1 Sources actually consulted

Repository sources below are at

```text
https://github.com/Malaeu/chen_q3/blob/a3174303e451541aad6538991602079ff9d9206f/
```

unless explicitly marked otherwise. Source IDs identify material cited in the proof. Git blob IDs are not SHA-256 content hashes. I do not claim to have independently recomputed all the request's SHA-256 prefixes.

| ID | Locator / read scope | Status and use |
|---|---|---|
| S0 | `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, fetched from `rh_clean`; blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13` | **READ**. Protocol and output boundary; the task-specific no-write prohibition is retained |
| S1 | `docs/routeB_bus/proshka/PROSHKA_REQUEST_PARITYSPLIT_2026-10-28.txt`, at `5086bf3f`; blob `d41987a009cc5fe84b660c85f96335c271cb584e` | **READ in full**. Task, pins, requested filename and frozen predictions |
| S2 | `docs/routeB_bus/thetagrade_2026-10-28/parity_gap_table.py`; blob `74f4cc939706c754b5c432a844038dd28878122c` | **READ**. Exact realification, parity bases, complement construction and eta normalization; script not rerun |
| S3 | `docs/routeB_bus/thetagrade_2026-10-28/RESULT.md` and `table_dps170.jsonl`; table blob `22f1a3b6d17db6feb8ba69a3078a567102e0d68e` | **READ diagnostic material**. Nonzero discarded imaginary component and finite observation scope; not a proof premise for any cofinal claim |
| S4 | `docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py`; blob `5cbd156db9be84caa938cdbabd4e9ec0b5a6d2f3` | **READ**. Literal matrix constructor and retained full prime/archimedean terms; no numerical quadrature promoted to a certificate |
| S5 | `docs/routeB_bus/fokas_k_sign_2026-09-25/rectangle_probe.py`; blob `a4994f129bbd018a67fe9f7cf02b20ce49793377` | **READ**. Recurrence and finite Mellin kernel; exact conjugate symmetry, distinct recurrence and carrier cutoffs |
| S6 | `docs/routeB_bus/fokas_k_sign_2026-09-25/SOURCE_TRANSFER.md`, T1–T7 and source-definition block, lines 1–110; blob `d564040c1828673835baeeed43978994ff68cd97` | **READ**. Same-K reference transfer. Quoted T5 constants remain **CONDITIONAL/RELAY** from their upstream proofs, not newly verified here |
| S7 | `docs/Codex/PAPER_CHAIN.md`, roof and G1/G2/G3/odd-floor/residual blocks | **READ**. Consumer map, literal selected family and current hypotheses. Reported Lean status is not a fresh build result |
| S8 | `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean`, full displayed file; blob `be8d8053b0e3166e593e430a27140436d9de4f23` | **READ**. Reflection theorem and exact inputs of the real-zero consumer; no Lean execution |
| S9 | `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean`, definitions and wrapper, lines 1–160; blob `972223c3f3a93d1ccab750086de0eb467bb74efa` | **READ**. General finite carrier, all-ones vector, normalization and literal entry reuse |
| S10 | `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean`, generic kernels and entries, lines 1–150; blob `960f1de9d00e9ca4b309a99fe98be48db40cdb31` | **READ**. Source pole rank-two decomposition, finite prime sum, complete archimedean term |
| S11 | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SELECTED_FERRERS_ODD_SECTOR_FLOOR_DISCRIMINATOR_2026-08-30.md`, request/source audits, penalty shortcut and class decision | **READ relevant sections**. Selected odd contamination and the distinction between shelf rejection and mathematical refutation. External results relayed there are not imported |
| S12 | `docs/routeB_bus/proshka/THETAGRADE_AUDIT_2026-10-28.md`; blob `5ef6f4621cb49ce2df3a8a98d832fcdf41c2882d` | **READ**. Prior parity-twin correction and withdrawn overclaims. Its external theta-manuscript extraction is **RELAY and unused** in this batch |
| S13 | CCM, *Zeta Spectral Triples*, `arXiv:2511.22755v1`, primary HTML, (3.10), (3.18), (4.2)–(4.4), Lemmas 5.1–5.4, Theorem 5.10 and §8 | **READ primary source**. Exact form/displacement and conditional consumer. No assertion that its missing spectral steps are already proved |
| S14 | The earlier `PROSHKA_VERDICT_THETAGRADE_2026-10-28.md`, content supplied in this conversation | **READ prior-turn content**. Historical starting point only; its pinned repository copy was not independently re-fetched and supplies no new premise |

Primary external locator:

```text
https://arxiv.org/html/2511.22755v1
```

No PDF was analyzed; the primary HTML contains the equations and theorem statements used. No additional OpenAI manuscript claim is used. Files outside `docs/routeB_bus/` actually opened were `docs/Codex/PAPER_CHAIN.md` and the three listed Lean source files; no personal archive was scanned.

### 9.2 Candidate arguments rejected or limited

| Candidate | First exact obstruction / retained repair |
|---|---|
| Treat the realified table row as the full selected reference | `[S2]` explicitly deletes a nonzero imaginary part; repaired by (1.3)–(1.9), not by pretending equality |
| Infer eventual negative complement from fifteen cells | There is no tail quantifier; T5's production bounds are also outside the small diagnostic range |
| Infer the needed lower energy from the observed angle | The spectral-band weight and band-energy lower bounds are not supplied |
| Infer selected-Rayleigh positivity from proximity to a global Weil null function | The residual full Weil form is signed; an upper bound on its modulus does not determine its sign |
| Interpret the odd near-null space as an odd spectral floor | It supplies trial upper bounds only; lower eigenvalues may exist |
| Declare G1a false when the lowest-odd-pole residue is nonnegative | The exact three-mode plant after (4.16) has positive residue and G1a true |
| Deduce a Theta-witness from negative-bottom growth | The shifted structured family in §5 preserves G1a while its bottom becomes arbitrarily negative |
| Identify the all-ones overlap with pole energy | The literal pole vector is \(u_n=L/(L^2+16\pi^2n^2)\), not \(\eta_n=1\); the remaining form is not proved null |
| Deduce eta-normalizability from a nonzero eigenvalue | The positive odd-bottom plant in §6.3 has eigenvalue 1 and zero eta overlap |

### 9.3 Reusable intermediate identities

The complex-row witness (1.5) transfers an even-reference spectral failure to a mildly odd-contaminated complex row without a first-order operator-norm loss. The two-dimensional odd construction (2.12) supplies an exact orthogonality witness even when the row is not parity-pure. The determinant identity (4.8) retains all source entries and removes the even eigensolver from the sign question. The residue expansion (4.14) gives a useful sufficient test but does not settle its source sign. The capacity identity (6.6) explains exactly which extra estimate would make a bounded-ratio observation meaningful. None is silently substituted for its remaining analytic inequality.

## 10. Proshka's own line

I chose the displacement identity because it removes two alleged G1a obligations rather than estimates them separately.  
The nearest alternative was a direct comparison of two very small eigenvalues.  
That comparison remains valid, but its subtraction hides the source mechanism.  
The second alternative was to improve the selected residual bound first.  
That would still target an interface the roof does not need.  
The first move beyond this batch is a one-sided source estimate for the odd-resolvent scalar.  
It must retain its resolvent domain and signed correlation together.  
A positive lowest-pole residue would kill only the cheap residue shortcut, not the full scalar route.  
The second move is to isolate the leading selected-row energy after the null component is removed.  
It must be a lower bound, not another estimate of an absolute remainder.  
A leading term of uncontrolled sign would stop that proposed G1b kill.  
I would ask for one rigorously enclosed complex-reference cell only to audit the instrument, not to extrapolate the tail.  
I would ask that it print the natural-phase even and odd components separately.  
I would also ask for the odd spectral residue and its regular remainder at that same cell.  
Those quantities would test whether the cheapest sufficient sign has the right orientation.  
What surprised me was that exact parity was obtained by a real projection in the diagnostic script.  
The omitted component may be tiny, but its deletion still changes the mathematical row.  
What also matters is the factor of the carrier dimension in the overlap statistic.  
The most useful structural fact is that a strict parity gap already gives simplicity and normalization.  
That statement is insensitive to whether the bottom eigenvalue is positive or negative.  
I distrust every argument that turns a small upper envelope into a positive lower margin.  
I also distrust a cofinal claim whose only evidence lies below the stated source threshold.  
The split is useful even though the requested cofinal kill remains unpaid.  
It separates a dispensable tracking certificate from the actual real-zero consumer.  
The next useful result must sign one of the two remaining scalar quantities, not enlarge the table.

## 11. Exactly one next directive

**CODEX DIRECTIVE — read-only mathematical target, no Lean or repository edits:** establish or falsify a **source-defined odd-resolvent bracket** (4.11) on the original eventual \(m=N\) schedule. The input is the literal block (4.3), not a fitted matrix or selected-row surrogate. First extract the actual lowest-pole term (4.13) together with the regular remainder (4.15); use it only when its sign supplies (4.16), and otherwise retain the full equivalent criterion (4.10). The validation gate is a positive lower envelope for \(\mathsf O_m-t_mI\) and a strictly negative upper envelope for \(\mathfrak f_m(t_m)\), with all source entries, multiplicities, tails and thresholds retained. Success closes G1a by (4.5), not G3 or RH. Failure must return the first unpaid signed source term and its exact domain; a failed residue shortcut or finite inconclusive interval must not be reported as a cofinal counterexample.

RH remains OPEN. No route promotion and no owner-level RH claim is made.
