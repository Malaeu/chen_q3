# Sonin / prolate compression over function fields — alias hunt 2026-09-11 (two streams, observer re-checked)

Question: has anyone built the Sonin/prolate compression of Weil positivity for curves over F_q, and does it reproduce Hodge index?
Answer: NO such construction exists in the fetched literature (Connes 1999, CC 2020, CCM 2023/24, CC 2018, Deitmar 2002, HP 2014/2019,
Bombieri 2000, Meyer 2005, Milne 2015, Garcia 2005). But the Toeplitz half of our sibling IS published (Hallouin–Perret).

## EMMANUELHALLOUINANDMARCPERRET-2014 — arXiv:1409.2357; TAMS 372 (2019) 5409–5451, DOI 10.1090/tran/7813 (identity of the two versions not checked)
VERBATIM (abstract, HAL/TAMS version, relayed by agent): «We explain how Riemann hypothesis for the curve X can be merely seen as an euclidean property,
coming from the Toeplitz shape of some intersection matrix on the surface X × X together with the general theory of symmetric Toeplitz matrices.»
VERBATIM (arXiv text line 312): «A symmetric Toeplitz matrix is a symmetric matrix whose entries x_{i,j} depend only on |i−j|»; their x_i = ((q^i+1) − #X(F_{q^i}))/(2g√(q^i)),
γ^k = p(Γ_k)/√(2g q^k) ∈ E_X, Gram(γ^0…γ^n) Toeplitz, PSD by Hodge index (their Prop. 5, Thm 6 «Toeplitz version of Riemann hypothesis for curves»).
Observer check: 2g·x_m = T_μ(m) = Σ_l e^{imθ_l} exactly (genus 2, q=4, m=1..5, 6 digits). Their Gram = our T_μ/(2g): our step (1) of SIBLING2 is theirs.
Gives: the published supplier of «Castelnuovo form = Toeplitz of the zero measure ⪰ 0 by Hodge index», all genus, no defect. CC-WEILPOS-2020 cite it as [21]: «closely related to the technique applied in [21] in the context of RH for curves over finite fields».
Does NOT give: the half-line Toeplitz A_{t,x}=φ(x+t) (Fourier coefficients of Xi), V = AᵀT_μA, the continuous bridge V_f, Weil distribution, Sonin, prolate (greps: 0). Novelty pass: our headline must be A and the bridge, never T_μ ⪰ 0.

## CONNES-TRACE-1999 (already on shelf) — function-field section §VIII
VERBATIM (line 1967): «Remember that we are still in positive characteristic where RH is actually a theorem of A.Weil.»
Line 1868, eq. (12): Trace(P̂_Λ P_Λ U(h_χ)) = (2N+1)l − f l + (2−2g)l; line 2096: lower bound (2N+1) − f + (2−2g) for dim B_{Λ,χ} vs dim S_{Λ,χ} = 2N+1 → codim 2g−2+f, identified with the vanishing conditions at the zeros of L (Weil VII.6).
Gives: over F_q the compression has a FINITE defect of exact codimension 2g−2+f, and that defect IS the zeros, not an artefact. Positivity there is not derived from the compression; b)⇒a) uses Weil's theorem. No Hodge index anywhere.

## ANTONDEITMAR-2001 — arXiv:math/0111108, «A semi-local trace identity and the Riemann hypothesis for function fields»
VERBATIM (line 991): «It would be nice to find a direct prove of this identity in general.» Abstract: the semi-local trace identity «becomes equivalent to the Riemann hypothesis for function fields».
Gives: Connes' compression Q_{S,Λ,0} posed over a curve over F_q; the identity ⟺ RH(F_q); NOT proved directly, 24 years open. No Γ_{F^k}, no NS(X×X), no Hodge. This is the gap our sibling can address: connect Q_{S,Λ,0} to the Hodge-index form (SIBLING4 (b′) with a published object).

## ALAINCONNESANDCATERINACONSANI-2018 — arXiv:1805.10501, «The Riemann-Roch strategy, complex lift of the Scaling Site»
VERBATIM (§3, p.17, relayed): «the function f defines a divisor D on the surface, as a linear combination of Frobenius correspondences. Then, if one assumes the positivity of s(f,f) > 0 for some f, it is the existence part of the Riemann-Roch theorem which yields a contradiction.»
Gives: D as a linear combination of Frobenius correspondences is standard dictionary — our D_x is not new as a divisor; new is φ = Fourier coefficients of Xi and V = AᵀT_μA. Direction there: F_q → char 0 lift; no F_q compression.

## Also fetched, not shelf items (agent locators, not re-checked by observer)
CCM 2310.18423: «the obtained invariantly defined Sonin space should … play the role of the sought for Weil cohomology … (up to a finite dimensional possible discrepancy)» — the defect acknowledged as open; no F_q. Bombieri 2000 (Lincei): truncations count zeros off the line; F_q only as motivation. Meyer 2005: spectral line over F_q exists, positivity not derived. Milne 1509.00797 Thm 1.5: Castelnuovo–Severi from Hodge index, «equivalence defect» def(D)=2d1d2−D². Garcia 2005 (Serre explicit formulae): half-line tests over F_q, but RH is a PREMISE there.
Not obtained: Yoshida ASPM 1992 (paywall), Omar–Bouanani Li criterion over F_q (403), Haran (books).
