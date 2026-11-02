# EDGE_LAW_v1 zeta preregistration

DIAGNOSTIC_NEVER_A_PROOF. Written before computing the new m160,200,240 cells.

Use literal N=m,L=log m, T=1.1*2pi*m/L and the positive-zeta-zero row-space complement J-perp. Select its normalized minimum eigenvector f. Prediction: R=lambda/[|f(L/2)|^2 log(T)/(pi T)] lies in[3,5] for each new cell.

Discriminator: preserve the same physical cosine basis, endpoint value, cutoff and complement; report all three ratios and their precision checks without selecting cells. Kill the finite prediction if any reliably computed ratio lies outside[3,5]. Do not replace the endpoint with a projected theta profile or change the minimum-vector definition. This finite experiment cannot prove an asymptotic edge law or RH.

Checks: control row-space QR residual/rank and compressed eigenpair residual; retain all Mangoldt powers and the pole. Main runs use120dps and GL192 on eight panels; one selected cell is recomputed at160dps/GL256. Dense source matrices remain local optional caches; publication cells retain the full physical coefficient vector and scalar/provenance diagnostics.
