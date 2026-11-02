# Registered predictions and stop conditions

Registered before certificate computations. Scope: fixed finite DH Rayleigh witnesses; no global theorem or RH claim.

1. The m51 dyadic witness should have negative Rayleigh quotient near −1.32685772638906e−47. Certification requires an Arb upper endpoint strictly below zero and absolute enclosure width below 1e−49.
2. The m55 dyadic witness should have negative Rayleigh quotient near −0.66392064608105. Its upper endpoint must also be strictly negative.
3. Use the exact algebraic DH parameter, every log-derivative coefficient through m, the odd archimedean kernel, and no pole term. Fixed dyadic modal coefficients define the witness exactly; numerical eigenvectors only supply a candidate.
4. Integrate the scalar archimedean correlation with rigorous Arb/acb quadrature away from zero; retain an explicit near-zero bound and the exact arch tail. Numerical precision agreement alone is not certification.
5. Discriminator: a nonnegative upper endpoint, failed/nonfinite integral, missing term, or unverified near-zero inequality blocks the certificate. Increase precision or change the rigorous integration representation; do not relabel an ordinary numerical estimate as certified.
6. Stop the m51 certificate attempt if a practical bounded refinement cannot reach width <1e−49; report the specific unresolved enclosure. Preserve outputs and unsuccessful status honestly.
7. Formula (7.1) envelope evaluations using previously computed δ are diagnostic only unless their R and the true-Q residual δ are independently interval-certified. The positive c_D is EulerGamma+log(8π/5)−π/2; it is the negative of the original signed constant.
