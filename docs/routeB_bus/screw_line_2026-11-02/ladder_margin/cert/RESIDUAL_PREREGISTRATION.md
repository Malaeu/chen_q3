# Fixed dyadic backward-error certificate — before execution

The direct interval LDL succeeded at M32 but its interval widths inflated
at M64,W5,pivot159 and included zero. This is an unresolved interval
calculation, not a negative source witness. Keep the original failed cell.

Prediction (probability .99): a validated backward-error certificate for
the identical finite matrices succeeds at512bits and series error1e-50.
Construct a numerical Cholesky L and inverse approximation B, then freeze
their binary floating values as EXACT dyadic integers. Numerical signs
never decide the certified conclusion.

Verify by exact integer arithmetic that epsilon_p=||I-BL||_p<1 for p=1,infinity.
Then ||L^-1||_p<=||B||_p/(1-epsilon_p). This gives a rigorous lower
eigenvalue for LL^T. Subtract an outward upper norm bound on A-LL^T,
where A is reconstructed from the complete interval source. Accept only
a strictly positive final lower interval. The saved dyadic witness can
be replayed without numpy or scipy.

Discriminator: independent exact-integer product residuals; source interval
residual, both induced norms, outward lower endpoint. Existing direct LDL
certificates remain a separate check on the smaller cells. No matrix node,
source coefficient or acceptance threshold changes. Budget3minutes per
cell; preserve any unresolved/failure output.

Scope remains only the listed finite nodes. The all-node interstitial
coercivity is unpaid, independently of success here.
