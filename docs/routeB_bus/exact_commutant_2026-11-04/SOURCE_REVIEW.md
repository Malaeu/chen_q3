# Independent Gate0 source review

DIAGNOSTIC_NEVER_A_PROOF. Registration supplied by the parent:76ddfb77a7d9b1f9e5e1bfa6cb5747f14ab48ec3. This review has executed no numerical computation or matrix scan. **Primary-source algebraic comparison PASS.** Independently read Suzuki, arXiv:2206.03682v4, equation(1.1), page1, from the readable `suzuki_actual.pdf` and its extracted text. The parent supplies PDF SHA256 `eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41`, matching the pinned repository LFS pointer. An earlier invalid download was not used. This paper comparison does not itself report the separately assigned numerical Gate0 result.

The reviewed implementations are the pinned ground-packet `inputs/source_50777d4.py` and `inputs/analytic_source.py`, supplied blobs f8b558f8fd7e2cda65158856ae6bfa9011f5cd0a and27bbaabbc5938b3157b5bc20f5e6db2f882122c0. The source's constant physical basis function is φ0=1/√L, with L=logm. For ζ, the literal source has

    A00=c+(2/L)∫₀ᴸ u j(u)du+2∫ᴸ∞j(u)du
        +(32/L)sinh²(L/4)
        −(2/L)Σ_{n≤eᴸ}Λ(n)n^(−1/2)(L−logn),
    j(u)=e^(−u/2)/(1−e^(−2u)),
    c=−γEuler−log(8π)−π/2=ψ(1/4)−logπ.

The n=eᴸ atom vanishes exactly. This formula follows directly from the constant-mode quadrature integrand2u/L, the full tail2[atanh(e^(−L/2))+atan(e^(−L/2))], the signed prime diagonal, and the square of pole[0]. It is also the analytical builder's constant-mode formula, with its explicit geometric remainder. Quadrature-rounded output is a numerical approximation to this identity, not an exact special-function value by definition.

Consequently

    (L/2)A00=4(e^(L/2)+e^(−L/2)−2)
       −Σ_{n≤eᴸ}Λ(n)n^(−1/2)(L−logn)
       +[(ψ(1/4)−logπ)L]/2
       +[ζ(2,1/4)−e^(−L/2)Φ(e^(−2L),2,1/4)]/4.

For the last line, expand j(u)=Σ_{r≥0}e^(−aᵣu), aᵣ=2r+1/2. The combination of interior and full tail integrates exactly to Σ(1−e^(−aᵣL))/aᵣ²; converting aᵣ=2(r+1/4) gives the Lerch/Hurwitz expression. Omitting the tail before this conversion would give a different identity. Every coefficient and sign in this source-derived expression is fixed; the prospective Suzuki comparison must use this full expression without silent repair.

The higher-moment verdict's printed pole check8(e^(L/2)+e^(−L/2)−2)/L=P00 is algebraically correct, as is its prime coefficient−2/L. Suzuki(1.1), page1, defines Ψ by exactly the displayed complete expression, writing C=π²+8G=ζ(2,1/4). His Gamma term is t[Γ′(1/4)/Γ(1/4)−logπ]/2 and his Lerch term is [C−e^(−t/2)Φ(e^(−2t),2,1/4)]/4. Both match term by term; the prime sum uses all von Mangoldt prime powers including its vanishing endpoint. Thus A00=2Ψ(L)/L follows with precisely the factor2 in verdict(2.3), no mismatch and no repair. Suzuki Theorem1.1(1) subsequently states the transform for Imz>1/2; that larger analytic implication is outside this Gate0 source-normalization audit. The parent's separately registered numerical Gate0 remains independently reported.
