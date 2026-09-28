Ы. **NO: the identified SOURCE_TRANSFER argument does not consume a multirow observation map \(S_m\). The proposed \(\gamma_{m,r}\) test is undefined for this route as stated.** Replacing \(S_m\) with one or two scalar functionals creates a different test whose minimum gain is structurally zero in the dimensions below. **That is not a KILL of Route B.**

:chatgpt-content-reference{index="4"}[Complete PAPER verdict and bounded CODEX DIRECTIVE](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_ROUTEB_SOURCE_OBSERVABILITY_2026-09-28.md)

## 1. What T1–T4 actually consume

I checked the complete **SOURCE_TRANSFER.md**, the observability diagnostic’s **README**, and the proposed step in **NEXT.md** at repository snapshot `78618b65152bc2b3b6aec4c6f1f460dd08617684`.

**T1** uses the same full \(K_m\), its ground projector, row closeness, and projection contraction. **T2–T3** add center normalization and a conditional center floor. **T4** supplies the common-scalar source decomposition and the energy/tail error. None supplies a multirow observer or a lower injectivity bound on \(V_{m,r}\). The center coordinate is a scalar normalization functional evaluated on the particular row—not an observer required to distinguish every low-eigenvalue direction. 

Indeed, put
\[
d_m=b_m-\widehat z_m,\qquad
\eta_m=\frac{E_m}{Z_m}<1,\qquad q_m=\frac{b_m}{\|b_m\|}.
\]
Then
\[
\|b_m\|\ge Z_m-E_m,\qquad
\|(I-P_0)b_m\|\le Z_m\alpha_m+E_m,
\]
and therefore
\[
\boxed{\|(I-P_0)q_m\|
\le \frac{\alpha_m+\eta_m}{1-\eta_m}.}
\]

**No spectral-gap denominator and no minimum singular value appear.** The diagnostic README itself explicitly records that SOURCE_TRANSFER does not define the requested multirow \(S_m\), and that neither it nor \(\gamma_{m,r}\) was computed. 

The two parameters in \(z(c_0,c_4)\) do not automatically become two observation rows. Neither \(Z_m\) nor \(E_m\) is a linear functional. Derivative rows or \(F_m^*\) would need a new, explicit consumer proof.

## 2. The rank-nullity obstruction

**[ABSTRACT | PAPER]** For the algebraic check only, associate the given row with
\[
\ell_m(v)=\widehat z_m^*v:
\mathcal H_m\longrightarrow\mathbb C,
\]
using the original Hermitian Euclidean norm and complex absolute value. On any \(r\)-dimensional subspace,
\[
\operatorname{rank}(\ell_m|_{V_{m,r}})\le1,
\qquad
\dim\ker(\ell_m|_{V_{m,r}})\ge r-1.
\]
Thus
\[
\boxed{\inf_{\substack{v\in V_{m,r}\\\|v\|=1}}
|\widehat z_m^*v|=0\quad\text{for every }r\ge2.}
\]

Even the hypothetical stack
\[
v\longmapsto
\begin{pmatrix}\widehat z_m^*v\\b_m^*v\end{pmatrix}
\in\mathbb C^2
\]
has rank at most two:

| \(r\) | Single functional | Pair \((\widehat z_m^*,b_m^*)\) |
|---:|---|---|
| 1 | May be positive or zero. | May be positive or zero. |
| 2 | **Minimum gain is zero.** | Positivity requires independent restrictions. |
| 3–4 | **Minimum gain is zero.** | **Minimum gain is zero.** |

Moreover, with Euclidean codomain norm, the paired minimum gain for \(r\ge2\) is at most \(E_m/\sqrt2\). To see this, choose a unit vector orthogonal to \((\widehat z_m+b_m)/2\); the two outputs are opposite halves of \((b_m-\widehat z_m)^*v\). Dividing both rows by the same \(Z_m\) gives the bound \(\eta_m/\sqrt2\).

**Successful source approximation can therefore make this artificial two-row map nearly rank one.**

The decisive sanity check is the abstract perfect-transfer case
\[
b_m=\widehat z_m=Z_mu_m,\qquad \alpha_m=\eta_m=0.
\]
Transfer is exact, yet the scalar and duplicate-row minimum gains vanish for \(r\ge2\). This is an algebraic check of the proposed detector, **not an asserted CCM source example**.

Eigenvalue splitting cannot remove a rank-nullity kernel. A zero minimum gain also does not mean the whole map has rank zero; it means its restriction is not injective.

## 3. The diagnostic that actually matches the transfer

Use the **same-ground overlaps**
\[
\rho_m^{\rm ref}=|u_m^*\widehat q_m|,
\qquad
\rho_m^{\rm sel}=\frac{|u_m^*b_m|}{\|b_m\|}.
\]
With \(\alpha_m\) defined exactly as in your request,
\[
\boxed{(\rho_m^{\rm ref})^2+\alpha_m^2=1.}
\]
For the selected row, writing \(\beta_m=\|(I-P_0)q_m\|\),
\[
(\rho_m^{\rm sel})^2+\beta_m^2=1,
\qquad
\boxed{\rho_m^{\rm sel}\ge
\frac{\max\{0,\sqrt{1-\alpha_m^2}-\eta_m\}}{1+\eta_m}.}
\]

The minimal diagnostic is therefore **\(\alpha_m\), \(\eta_m=E_m/Z_m\), the ground overlap, and the resulting transfer bound**. Report a selected overlap only when the actual selected row is available; otherwise report its enclosure. Keep the source’s common phase/scalar when establishing \(\|b_m-\widehat z_m\|\le E_m\).

**G1 remains separate.** SOURCE_TRANSFER identifies \(P_0\) with the projector onto a **simple ground state**; T1–T4 do not prove that simplicity. Nonzero overlap with one chosen ground vector does not exclude another orthogonal ground vector. 

A separate theorem
\[
\ker(K_m-\lambda_0I)\cap\ker(\widehat z_m^*)=\{0\}
\]
on the **entire actual ground eigenspace** would imply simplicity. It is not supplied by T1–T4. Nor may the lowest reflection-even eigenvector silently replace the full-\(K_m\) ground state: that identification must be established.

## 4. The four midpoint values do not decide T7

Your reported values at \(m=8,12,16,24\) are **finite, subthreshold midpoint diagnostics**, not an eventual rate certificate. Even if all four were exact, they would neither prove nor refute
\[
\boxed{m^{H/2}\sqrt{\log m}\,\alpha_m\longrightarrow0
\quad\text{for every fixed }H\ge0.}
\]

For each fixed strip height \(H\), the relevant quantities are
\[
A_H(m)=m^{H/2}\sqrt{\log m}\,\alpha_m,
\]
and
\[
D_H(m)=m^{H/2}\sqrt{\log m}\,
\frac{\alpha_m+\eta_m}{1-\eta_m}.
\]
When \(\eta_m\le\tfrac12\),
\[
D_H(m)\le A_H(m)+4m^{H/2}\sqrt{\log m}\,\eta_m.
\]
SOURCE_TRANSFER pays the error-ratio term only under its matched **T5 hypotheses and eventual thresholds**; the transform bound retains its **center-floor** premise. The four angles establish neither supplier. 

A source-derived upper envelope for \(A_H\) tending to zero would prove the rate for that \(H\). A positive lower bound along an unbounded admitted sequence for even one fixed \(H\) would refute T7. Four points or fitted slopes do neither.

**Next step:** retain the literal source objects, replace the undefined \(\gamma\)-versus-splitting criterion with the \(\alpha\)/error-ratio/ground-overlap diagnostic, and target the actual scaled tail bound. Even failure of T7 would reject this sufficient vector-norm route—not automatically transform tracking, whose cancellations that norm bound may lose. No G1/G3 closure or RH claim follows.