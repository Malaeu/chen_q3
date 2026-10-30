# Signed-cut alias return — 2026-10-30

## Brief

For a real unit bottom \(c=(c_0,\ldots,c_m)\) of the literal even CCM matrix, exact minimality gives every prefix cross-cut \(C_q(c)=\sum_{i\le q<j}A_{ij}c_ic_j\le0\), but fixed-jet escape has not supplied a positive cut or another descent. The multiplier identity turns the bottom into a positive-semidefinite **signed** graph Laplacian; a primary effective-resistance theorem gives a concrete overload test for a negative edge against its positive backbone. This is a conditional partial bridge: the source-specific overload under escape remains open.

The exact source normalization is \(L=\log m,\ N=m,\ 0\le i,j\le m\), in the orthonormal even basis \(e_0=\psi_0,\ e_i=(\psi_i+\psi_{-i})/\sqrt2\). For distinct indices, the full source entry is
\[
A_{ij}=d_id_j\frac{i\beta_i-j\beta_j}{i^2-j^2},\quad d_0=1,\ d_i=\sqrt2\ (i>0),
\]
where
\[
\beta_i=\frac{\kappa i}{L^2+16\pi^2i^2}
+\frac1\pi\int_0^L j(s)\sin(2\pi is/L)\,ds
+\frac1\pi\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\sin(2\pi i\log n/L),\qquad
\kappa=32L\sinh^2(L/4),\quad \beta_0=0,\quad
j(s)=\frac{e^{-s/2}}{1-e^{-2s}}.
\]
This is the pole, archimedean, and complete supported prime-power source of the task verdict, §6, (6.1)–(6.4) (input SHA-256 79b5f4869f75d0f14b056d9543914e05a57ab8101bfe30b1db63c09d77161f71). For an exact real unit bottom \(A_mc=\lambda c\), set \(w_{ij}=-(A_m)_{ij}c_ic_j\), \(i<j\). The verdict’s multiplier identity, §5 Lemma 8 (5.4), is exactly
\[
 y_i=a_ic_i\quad\Longrightarrow\quad
y^T(A_m-\lambda I)y=\sum_{i<j}w_{ij}(a_i-a_j)^2\ge0\qquad(a\in\mathbb R^{m+1}).
\]
Thus \(w\) defines a signed graph Laplacian on vertices \(0,\ldots,m\); the step potential \(a_i=\mathbf1_{i\le q}\) gives \(\sum_{\partial\{0,\ldots,q\}}w_{ij}=-C_q(c)\ge0\). The exact-entry and cut decomposition is recorded in §§5–6; the source verdict leaves its strict source comparison (7.6) open.

**Negative controls.** The verdict’s diagonal escaping-bottom control has \(A_{ij}=0\) off diagonal, hence \(w_{ij}=0\), every cut is zero, and the positive backbone is disconnected: the effective-resistance theorem is correctly inapplicable. A separate exact three-vertex diagnostic shows why testing only prefix cuts is weaker than testing arbitrary multipliers. Take \(w_{12}=w_{23}=1,\ w_{13}=-3/4\). All three cut weights are nonnegative (the two prefix weights are \(1/4\)); nevertheless \(R^+_{13}=2\), \((3/4)R^+_{13}=3/2>1\), and \(a=(1,1/2,0)\) has signed energy \(1/4+1/4-3/4=-1/4\). With \(c=(1,1,1)/\sqrt3\) and \(A=3L(w)\), this is \(w_{ij}=-A_{ij}c_ic_j\) and \(Ac=0\), but \(c\) is stationary, not a bottom. The failed naive step is to infer stability of the full form from its prefix-cut tests alone.

Search rewrites used only as hints: **UNVERIFIED** — (i) regard \(w_{ij}\) as signed conductances after the exact ground-state transform; (ii) test whether fixed-jet escape forces an edge’s negative magnitude times its positive-network effective resistance above \(1\). Neither is a result about the CCM source.

## Worked primary bridge

Daniel Zelazo and Mathias Bürger, *On the Robustness of Uncertain Consensus Networks*, arXiv:1408.4471, §IV, Theorem IV.7 and its proof, PDF p. 8; journal version: IEEE Transactions on Control of Network Systems 4(2), 2017, DOI [10.1109/TCNS.2015.2485458](https://doi.org/10.1109/TCNS.2015.2485458). The primary arXiv PDF was fetched from [arxiv.org/pdf/1408.4471](https://arxiv.org/pdf/1408.4471), independently reread, and saved as [ZELAZO_BUERGER_2015_SIGNED_LAPLACIAN_EFFECTIVE_RESISTANCE_ARXIV_1408.4471.pdf](../../literature/ZELAZO_BUERGER_2015_SIGNED_LAPLACIAN_EFFECTIVE_RESISTANCE_ARXIV_1408.4471.pdf). SHA-256: d5c5a5fd842b2f1f04f46b8f57ca8b761ccf084b01ac249bf4f98d2a95582884. Version assumption: this is the 14-page arXiv PDF returned on 2026-10-30 (PDF metadata creation date 2015-03-03); the hash pins the exact bytes, and no arXiv version suffix is claimed.

The theorem assumes that the positive-edge graph \(G_+\) is connected and that there is exactly one negative edge \(e=(p,q)\) of weight \(-\alpha\). Its conclusion is: “Then L(G) is positive semi-definite if and only if |W(e−)| ≤ R−1_uv(G+).” (Theorem IV.7, §IV, PDF p. 8; 12 words quoted.) The proof applies a Schur complement, reducing semidefiniteness to the scalar condition \(\alpha R^+_{pq}\le1\).

Here is the exact instability direction used for the Q3 mapping. Let \(L_+=\sum_{w_{ij}>0}w_{ij}(e_i-e_j)(e_i-e_j)^T\), \(d=e_p-e_q\), and let \(e=(p,q)\) be a negative edge of weight \(-\alpha\). No global connectivity is needed. If \(p,q\) lie in distinct connected components of \(G_+\), take \(a=1\) on the component of \(p\) and \(a=0\) on all other components. Then \(a^TL_+a=0\), while the selected edge contributes \(-\alpha\) and every other negative edge contributes at most zero. If \(p,q\) lie in the same positive component \(K\), set \(R^+_{pq}=d^T(L_+|_K)^\dagger d\). Cauchy–Schwarz on \(\mathbf1_K^\perp\) gives \(1=(d^Ta)^2\le(a^TL_+a)R^+_{pq}\) whenever \(a_p-a_q=1\), with equality at \(a=(L_+|_K)^\dagger d/R^+_{pq}\), shifted by a constant to make \(a_q=0\). The positive-conductance maximum principle gives \(0\le a_i\le1\) on \(K\); extend it by zero on every other positive component. Thus \(a^TL_+a=1/R^+_{pq}\). For a unified formula, set \(R^+_{pq}=\infty\) when the endpoints are in distinct positive components (the pseudoinverse expression is used only within one component), with \(1/\infty=0\). In either case, every other negative edge contributes a nonpositive term, so for a graph with any number of negative edges,
\[
a^TL(w)a\le \frac{1}{R^+_{pq}}-\alpha.
\]
Consequently, an edge crossing positive components, or an internal edge with \(\alpha R^+_{pq}>1\), produces a negative multiplier direction. For a literal CCM bottom, \(y=a\odot c\) is in the same finite carrier and the identity above would give \(y^T(A_m-\lambda I)y<0\), contradicting exact minimality. Since the selected negative edge has \(w_{pq}<0\), both \(c_p,c_q\ne0\); the chosen voltage has \(a_p=1\), so \(y\ne0\). Normalizing gives the exact gap formula
\[
\frac{y^TA_my}{\|y\|_2^2}-\lambda
=\frac{y^T(A_m-\lambda I)y}{\sum_i a_i^2c_i^2}
\le \frac{1/R^+_{pq}-\alpha}{\sum_i a_i^2c_i^2}<0
\]
in the same-component overload case; for a crossing edge, replace the numerator bound by \(-\alpha\). The paper’s multi-edge iff theorem has additional edge-disjoint-path hypotheses and is not being imported; the one-edge instability implication above follows directly because all remaining negative terms only lower the test energy.

For a unit approximate vector \(c\), \(\lambda=\langle c,A_mc\rangle\), and residual \(r=(A_m-\lambda I)c\), the exact correction to the multiplier identity is \(\langle a^{\odot2}\odot c,r\rangle\). For the bounded voltage \(0\le a_i\le1\), its magnitude is at most \(\|r\|_2\). Thus the test still descends if the independently established overload margin satisfies \(\alpha-1/R^+_{pq}>\|r\|_2\). The actual nonnegative escaping trial family in the input verdict, §3 Lemmas 4–5, (3.1)–(3.16), has unit vectors \(g_m\) with \(\|A_m\operatorname{coeff}(g_m)\|_2=O_A(m^{-A})\) and every fixed-jet projection \(O_{r,A}(m^{-A})\), for each fixed \(A,r\), but these are not exact bottoms. Writing \(v_m=\operatorname{coeff}(g_m)\) and \(w_{ij}(v_m)=-(A_m)_{ij}(v_m)_i(v_m)_j\), its Rayleigh residual is also superpolynomial: if \(\lambda_m=v_m^TA_mv_m\), then \(\|(A_m-\lambda_mI)v_m\|_2\le2\|A_mv_m\|_2=O_A(m^{-A})\). We have not evaluated the sign or scale of any \(\alpha_eR_e^+-1\). The trials therefore neither verify nor refute the overload condition: a descent for them is compatible with T and cannot prove T. Residual accuracy alone does not pay an unknown or faster-vanishing overload margin.

## Hypothesis map and disposition

| Item | Status | Exact mapping / gap |
|---|---|---|
| Real exact bottom and full source matrix | **PROVED in the input verdict** | Realification: §1 Lemma 1. Entries retain pole, archimedean, and every supported prime power: §6 (6.1)–(6.4). |
| Signed-Laplacian multiplier identity and nonnegative prefix cuts | **PROVED in the input verdict** | §5 Lemma 8 (5.4), and coefficient-cut test (5.1)–(5.3). This is the stability side only. |
| Positive-component structure for \(w_{ij}=-(A_m)_{ij}c_ic_j\) on an escaping-bottom tail | **OPEN** | Exact bottomness excludes negative edges crossing distinct positive components, but no useful componentwise resistance estimate is proved. |
| A selected source edge with \(\alpha R^+_{pq}>1\) from fixed-jet escape | **OPEN** | This is one checkable sufficient source estimate, not a necessary characterization of general instability. It must use the exact entries above; no sign or resistance margin follows from jet escape alone. |
| Applying the single-edge theorem verbatim to the CCM graph | **INAPPLICABLE as an exact fit** | The transformed graph can have many negative edges. The direct voltage argument above proves only the stated sufficient instability test for any selected edge. |
| Residual-only extension to the escaping radical trials | **FALSE as a general inference** | The correction costs \(\|r\|_2\); the source margin has no lower bound and may shrink faster. These vectors are trials, not exact bottoms. |

The triangle is also the minimality discriminator: it satisfies every prefix-cut inequality but has a negative arbitrary-multiplier form. Here \(\|y\|_2^2=5/12\), so its normalized energy gap is exactly \((-1/4)/(5/12)=-3/5\). Its failure to be a bottom is exactly detected by effective resistance. A second diagnostic separates the selected-edge condition from general signed instability: on the positive path \(1-2-3-4\) with unit weights, add negative edges \(13\) and \(24\), each of weight \(-2/5\). Each edge separately has \(R^+=2\) and \(\alpha R^+=4/5<1\), yet \(a=(3,2,1,0)\) has energy \(3-(2/5)(4+4)=-1/5\). Thus one-edge overload is a sufficient mechanism only, not necessary even for an arbitrary instability direction. The task’s other diagonal control, \(A=\operatorname{diag}(-2,0,\ldots,-1\text{ at }m)\), has a fixed true bottom and an escaping excited vector; for that excited vector \(w=0\), so the criterion is inapplicable and low energy/stationarity cannot replace exact bottom minimality. The diagonal escaping-bottom control likewise defeats any claim that this graph criterion applies without its positive-component hypotheses. Root reports that an independent algebra review accepted the componentwise competitor, residual guard, factors, and full-source retention; root’s exact SymPy check confirmed the triangle values above. These are bounded algebra checks, not cofinal evidence.

The first shelf query used the three dictionaries “signed Laplacian cut stability”, “Loewner displacement oscillation”, and “frustration index ground-state binding”. It returned ASK_STATUS: INCOMPLETE because the q3 semantic-index freshness check failed, so absence is not established. The exact local gap/projective-overlap receiver surfaced by the shelf is not used: its required source coercivity/gap inputs are already unpaid. Stieltjes/Markov positivity is not reused.

**Disposition:** PARTIAL_ANALOGUE, not EXACT_FIT. Remaining estimate: a cofinal literal-source bound that, from fixed-jet escape of actual bottoms, forces a crossing negative edge or an internal effective-resistance overload. This is a stronger, transformation-specific sufficient obstruction, not equivalent to T; T asserts persistent fixed-jet overlap, not a signed-graph edge condition. No cofinal or asymptotic overload evidence is established. One next bounded test: for the actual escaping-bottom class, bound \(\alpha_eR^+_e-1\) for one selected internal negative edge using every pole, archimedean, and prime-power contribution; stop if no positive margin survives the full source. \(T\) and RH remain open.
