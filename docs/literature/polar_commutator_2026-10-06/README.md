# Bounded alias check: polar double commutator (2026-10-06)

## Exact obstruction

For \(L=\log m\), the actual carrier is
\(\mathcal V_m=\operatorname{span}\{e_n:|n|\le m\}\subset L^2(0,L)\),
with \(Xf(x)=xf(x)\), \(F_L=(I-R)Z_L\), and the unitary polar factorization
\(F_L=V_LM_L\). Put \(Y_L=V_L^*XV_L\), so \(0\le Y_L\le LI\). The exact
remaining operator is
\[
 D_L=M_L^{-1}[M_L,[M_L,Y_L]]M_L^{-1}
     =M_LY_LM_L^{-1}+M_L^{-1}Y_LM_L-2Y_L.
\]
The needed assertion is the carrier-wide upper form bound
\[
 \langle f,D_Lf\rangle\le D_{\rm arch}(f)+C_\eta m^\eta\|f\|_2^2
 \quad(f\in\mathcal V_m),
\]
for each \(\eta>0\), eventually in the original integer schedule. The exact
source and prior identities are in
`docs/routeB_bus/source_observability_2026-09-28/PROSHKA_CAUSAL_DRESSING_INLINE_2026-10-06.md`,
especially (28)–(36). In that file (35) is proved; (36), displayed above,
is explicitly open. The alias check does not alter that status.

## Three object dictionaries and search rewrites

1. **Similarity / numerical range:** the map
   \(\mathcal S_M(Y)=M Y M^{-1}\); the required form is the Hermitian part of
   \(\mathcal S_M(Y)-Y\) after pairing against a carrier vector.
2. **Log-positive commutator:** with \(A=\log M\), the algebraic expression is
   \(D=2(\cosh(\operatorname{ad}_A)-I)Y\), where
   \(\operatorname{ad}_A(Y)=[A,Y]\). **UNVERIFIED as an estimate route:**
   recognizing this functional calculus supplies no form sign or growth bound.
3. **Energy / metric distortion:** for the usual convention linear in the
   second slot,
   \[
   \langle f,Df\rangle
     =2\operatorname{Re}\langle Mf,YM^{-1}f\rangle-2\langle f,Yf\rangle
     \le 2L\|Mf\|\,\|M^{-1}f\|.
   \]
   **UNVERIFIED as a supplier:** it reduces the requested estimate to a
   source-specific simultaneous metric bound, which has not been proved.

These are search descriptions of the same exact object, not three proofs.

## Explicit negative control

Let \(M=\operatorname{diag}(k,1)\), \(k>0\), and
\(Y=(L/2)\begin{psmallmatrix}1&1\\1&1\end{psmallmatrix}\), \(L>0\). Then
\(0\le Y\le LI\) but
\[
 D=(L/2)(k+k^{-1}-2)
   \begin{psmallmatrix}0&1\\1&0\end{psmallmatrix}.
\]
Its eigenvalues have both signs, and its positive eigenvalue grows like
\(Lk/2\). Thus positivity of \(M,Y\), or a norm estimate using only their
individual positivity and \(\|Y\|\le L\), cannot provide the needed upper
bound. This does not instantiate the source \(F_L\) or its archimedean form;
it only rejects the unrestricted operator-positivity shortcut.

## Worked primary-literature check

Fetched and reread Rajendra Bhatia, Fuad Kittaneh, and Ren-Cang Li,
“Some inequalities for commutators and an application to spectral variation.
II,” *Linear and Multilinear Algebra* 43 (1997), 207–219, DOI
[10.1080/03081089708818526](https://doi.org/10.1080/03081089708818526).
The downloaded author-hosted copy is
`bhatia_kittaneh_li_1997.pdf`, SHA-256
`1fb41f3dfd9e98bb6f1c8e0c5334f8fa6e50b07ad0e3923a8ce0e74ee74bc238`.

Theorem 2.1, journal pp. 208–209 (PDF pp. 3–4), assumes a positive-definite \(\Gamma\)
and Hermitian \(A,B\), and states for every unitarily invariant norm
\[
 \|\!\|\!\|A-B\|\!\|\!\|^2
 \le \|\!\|\!\|A\Gamma-\Gamma B\|\!\|\!\|
    \cdot\|\!\|\!\|\Gamma^{-1}A-B\Gamma^{-1}\|\!\|\!\|.
\]
This is a genuine worked similarity/commutator theorem, but it does not
estimate the signed quadratic form of \(D_L\). Setting \(A=B=Y_L\) makes its
left side zero, and identifying either conjugate \(M_LY_LM_L^{-1}\) with a
Hermitian \(A\) is invalid in general. So the source supplies no map to the
carrier, no \(D_{\rm arch}\) term, and no subpolynomial-in-\(m\) bound.

## Status and next step

- **PROVED:** exact polar identity (33)–(35) in the local source; the two
  finite-dimensional rewrites above; the counterexample separating positivity
  from the required one-sided form estimate.
- **OPEN:** a source-specific bound on
  \(\|M_Lf\|\|M_L^{-1}f\|\), or another cancellation estimate, for every
  \(f\in\mathcal V_m\) that pays against \(D_{\rm arch}(f)\) with only
  \(m^\eta\|f\|^2\) remainder.
- **FALSE as a free lemma:** positivity of \(M_L\) and \(0\le Y_L\le LI\)
  alone gives a sign or a useful \(m\)-uniform upper bound.
- **INAPPLICABLE:** Bhatia–Kittaneh–Li Theorem 2.1 as a supplier for (36),
  because it controls unitarily invariant norms of Hermitian-variable
  differences through generalized commutators, not the required signed form.

Next bounded mathematical check: derive a bound using the explicit
\(F_L=(I-R)Z_L\) and \(F_L^{-1}\) in (28)–(29), retaining the coupling to
 the actual carrier and \(D_{\rm arch}\). Stop this alias route unless the
result proves (36) with constants uniform in \(m\); a condition-number bound
or a renamed version of (36) is not progress.

Root reread the rendered formula (2.1), journal p.209: the squared norm is bounded by the PRODUCT of two norms; corrected the first report's sum transcription. Exact short quote: “for every unitarily invariant norm.” Author-hosted source: https://bpb-us-e1.wpmucdn.com/websites.uta.edu/dist/7/5059/files/2021/06/bhkl1997.pdf .
Shelf query returned ASK_STATUS: INCOMPLETE (semantic-index freshness failure); no absence claim.
