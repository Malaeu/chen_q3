# Capacity evaluation validation

The table contains 203 positive zeta ordinates at180 dps:202 at or below400 and the first above,401.839228600533. The first138 ordinates are inherited from the prior180-digit table; source and code hashes are retained.

Every basis transform at all202 used ordinates was checked at180 dps by the rational expression against direct sinc evaluation. Maximum absolute differences:3.278e-179 for m16 and1.104e-178 for m24. E has unweighted positive-zero rows and no additional2π factor.

Independent physical integration uses the normalized cosine basis over[-L/2,L/2]. Checks cover the first zero, last used zero, and zero closest to a modal frequency (indices1,3,202 for m16 and1,6,202 for m24). Eight-panel GL128 agrees with direct sinc to at worst4.820e-180 for m16 and2.296e-164 for m24. GL96 gives a worst high-frequency error2.562e-100, so the finer quadrature materially verifies that tail row.

These are numerical normalization checks, not interval enclosures or a proof that the truncated zero Gram equals the full arithmetic matrix. The distinction between EᵀE and2EᵀE is preserved: even real transforms have equal values at both positive and negative zero ordinates.
