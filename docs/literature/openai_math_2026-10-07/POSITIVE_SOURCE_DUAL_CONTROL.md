# Positive-source dual descent: bounded negative control

Question after Direct Shift Q1: could Psi_(3/8)>=0, monotonicity of the source prefix (nonnegative source measure), and the imported power-discrepancy bound alone supply the signed Abel-kernel inequality? The following synthetic continuous-source construction rejects that generic implication. It does NOT reject an argument using the actual von Mangoldt measure, Euler product, or further arithmetic identities.

## Source and scope

Keep EXACTLY Suzuki's smooth B_sigma and shifted ramp normalization from SHIFTED_ARITHMETIC_RESERVE.md. Primary Suzuki arXiv:2206.03682v4, Theorem4.1 and §11; local PDF SHA256eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41, https://arxiv.org/abs/2206.03682v4 . Theorem4.1 states: “There exists t0 > log 2 such that Ψ(t) > 0 for 0 < t < t0.” Its displayed small-interval proof uses numerical critical-point calculations; we use the published theorem here, not a newly certified interval computation.

For t<=log2, B0=Psi0, since all prime ramps vanish. For t>=log2,
B0'(t)=2exp(t/2)+c0-R0'(t)>2sqrt2+c0>0,
c0=-(EulerGamma+pi/2+3log2+logpi)/2.
Hence B0>=0 globally. Suzuki's positive shift Tomega maps (t-log n)_+ to n^-omega(t-log n)_+; the exact source identity therefore gives Bomega=Tomega B0>=0 for omega>=0. This uses the integral formula and does not differentiate B0 at its singular initial derivative.

## All-time higher positivity, failed descent

Fix omega=3/8, eta=5/16, delta=11/32, beta=27/32 and0<epsilon<1/2. Choose smooth0<=chi<=1, zero on x<=X0 and one on x>=2X0. Set
p(x)=chi(x)[1+epsilon x^-5/32 cos(logx)],
dP(x)=p(x)dx,
Psi_sigma^P(t)=B_sigma(t)-int_1^exp(t) x^(-1/2-sigma)(t-logx)dP(x).
The source is nonnegative and atomless. For fixed X0, P(x)-x=O(x27/32), which is stronger than the imported7/8 magnitude allowance. This is a bound on the synthetic counting function, not a zero-free theorem for an associated L-function.

Before T0=logX0, Psi_omega^P=Bomega>=0. Thereafter, the derivative of the baseline source ramp is at most8(exp(t/8)-X0^1/8); the absolute derivative of the oscillatory ramp is at most32epsilon X0^-1/32. Thus
(Psi_omega^P)'(t)>=8X0^1/8+c_omega-R_omega'(t)-32epsilon X0^-1/32>0
for all t>=T0 after choosing X0 large. Therefore Psi_omega^P(t)>=0 for ALL t>=0, not merely eventually.

At eta, put z=1/32+i and T1=log(2X0). The baseline density contributes the growing main term exp((3/16)t)/(3/16)², cancelling B_eta's same term and leaving an affine remainder. The compact transition interval contributes only affine terms for t>=T1. The oscillatory ramp on[T1,t] is exactly
Re[(exp(zt)-exp(zT1)-z(t-T1)exp(zT1))/z²].
Consequently
Psi_eta^P(t)=-epsilon Re[exp(zt)/z²]+O(t).
Along t_n=2pi n-arg(z^-2), Psi_eta^P(t_n) tends to minus infinity. All positive-source and higher-positivity conditions remain satisfied.

## Decision and semantic return

Root derived the delayed-source construction; squarefree_conductor_check independently verified the all-time strengthening, ramp map, derivative bound and growing oscillation. PAPER negative control using the cited small-interval theorem; no Lean certificate.

The source-specific dual certificate proposed after Q1 cannot be justified solely from nonnegative source weights, the power discrepancy bound and higher-shift positivity. Those constraints admit this example. The next certificate must explicitly use a property absent here: the actual discrete prime-power/Euler structure, or another independently proved source constraint. Merely adding monotonicity of A_omega does not repair the generic descent.

Alias dictionaries: positive-measure moment cone / dual Volterra inequality; Mellin oscillatory perturbation with compact compensation; stochastic-order preservation under exponential untilting. Local shelf query positive measure integrated discrepancy exponential tilt dual cone returned INCOMPLETE (semantic-index freshness), not absence. Existing exact Suzuki source used; no newly imported theorem supplies the missing arithmetic constraint.

Generic cone-only dual descent: rejected at stated scope. Actual arithmetic inequality(61), RH and all original Q3 consumers remain OPEN. Q2 NOT sent. Next action is to identify an independently established arithmetic constraint before asking for another dual certificate; otherwise return to another documented consumer rather than repeat this implication.
