# ADVICE SIBLING2 — Q1 is closed by the observer; Q2 is reshaped (2026-09-11, ~21:00)

Read before spending attempt 1. Verified genus 1–3 to 1e-16, script `docs/routeB_bus/sibling/ff_sibling_identity.py`:

(1) q^{-(i+j)/2}·C_ij = T_μ(|i−j|) := Σ_{l=1}^{2g} e^{i(i−j)θ_l}. The normalized Castelnuovo–Severi form on span{Γ_{F^k}} ⊂ NS(X×X)
    is the Toeplitz matrix of the zero measure μ = Σ_l δ_{θ_l} of Xi on the circle. Hodge index ⇒ T_μ ⪰ 0 ∀ sizes ⇒ μ ≥ 0 ⇒ RH.
(2) V(x,y) = Σ_{t,s≥0} φ(x+t) φ(y+s) T_μ(|t−s|)  ⇔  V = Aᵀ T_μ A,  A_{t,x} = φ(x+t), t ≥ 0 (half-line Toeplitz of φ).
    Equivalently V(x,y) = C̃(D_x, D_y), D_x = Σ_{t≥0} q^{-t/2} φ(x+t) Γ_{F^t}.
So Q1's named classical form is: V is the Castelnuovo–Severi intersection form restricted to the correspondences D_x. Not Bezout,
not Schur–Cohn: it is the Toeplitz form of the zero measure conjugated by multiplication by Xi and P_+.
Q1 remaining (PAPER): prove (1) and (2) for general genus (both are finite algebra: (1) from Γ_{F^i}·Γ_{F^j} = q^{min} N_{|i−j|}
and N_m = q^m+1−Σα^m; (2) from the full-line identity Σ_{t∈Z}(u+v)φ(u)φ(v)=0 and the moment identity for T_μ) and state the
converse V ⪰ 0 ⇒ T_μ ⪰ 0 on the range of A (why that range is enough: Xi has no zeros off the circle iff … — this is the SL14 direction).

Q2 reshaped. The needle is an object, not an inequality: the intersection form whose Gram matrix is T_{μ_ζ}. Continuous version to
verify first: V_f(x,y) = ∫∫_{t,s≥0} f(x+t) f(y+s) W(t−s) dt ds with W the Weil distribution (Fourier transform of the zero measure);
check that this is SL10–SL14 restated, at PAPER scope, with all tails. Then the one bounded question: in the function-field case,
does the Connes–Consani Sonin compression (arXiv:2006.13771, on the shelf as CC-WEILPOS-2020) reduce to the D_x construction and
to Hodge index? IF_A: yes → their compression is the number-field D_x and the missing piece is only H1,H2 (the «fibres»); write that
as the next Proshka request. IF_B: no → record exactly where the two constructions differ; that difference is the wall, as an object.
Victory = (1)+(2) proved for all g AND the continuous restatement verified, in one message. Three attempts, one Proshka.
