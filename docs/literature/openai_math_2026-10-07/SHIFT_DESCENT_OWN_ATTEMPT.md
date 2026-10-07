# Direct shift descent: own attempt, 2026-10-07

Consumer: Suzuki Theorem11.1, eventual nonnegativity of the ORIGINAL Psi_eta for a smaller eta, supplies zero-freeness Re(s)>1/2+eta. External ZF78 remains an unverified premise. The attempt tests whether its positive Psi_(3/8) and our full arithmetic source automatically pay this consumer. They do not via a bounded-remainder estimate.

Source: Suzuki arXiv:2206.03682v4 §11, https://arxiv.org/abs/2206.03682v4; local PDF docs/routeB_bus/litreview/pdfs/2206.03682.pdf SHA256 eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41. Local text lines2102–2175 contains both shift identity and full zero/prime-power formulas. Root reread these; squarefree_conductor_check independently audited the following identities and negative control. This is a paper audit, not Lean admission.

## Exact remainder

Set omega=3/8. Zeros gamma of xi(1/2-i gamma) obey |Im gamma|<=omega under ZF78. Counting multiplicity,

Psi_omega(t)=A_omega t+B_omega+R_omega(t),
A_omega=sum_gamma omega/(gamma²+omega²)=xi'/xi(1/2+omega)>0,
B_omega=sum_gamma (gamma²-omega²)/(gamma²+omega²)²,
R_omega(t)=-sum_gamma exp(-omega t)[(gamma²-omega²)cos(gamma t)+2gamma omega sin(gamma t)]/(gamma²+omega²)².

All coefficient sums converge absolutely; |R_omega(t)|<=C_omega uniformly t>=0, since each exponential trigonometric factor is bounded and the coefficients are O(|gamma|^-2). Boundary zeros do not create singular denominators: gamma=+-i omega would be a real xi zero, excluded by zeta(sigma)<0 for 0<sigma<1. Quartet pairing gives A_omega>0, including possible nonreal boundary zeros.

For 0<h<=omega define
T_-h f(t)=exp(ht)f(t)-2h int_0^t exp(hu)f(u)du+h² int_0^t(t-u)exp(hu)f(u)du.
Direct integration gives T_-h(t)=t and T_-h(1)=1-ht. Thus exactly

Psi_(omega-h)(t)=(A_omega-h B_omega)t+B_omega+T_-h R_omega(t).

The uniform remainder bound yields only
|T_-h R_omega(t)|<=C_omega(4exp(ht)-3-ht)<=4C_omega exp(ht).
It cannot pay the required eventual lower bound
T_-h R_omega(t)>=-(A_omega-h B_omega)t-B_omega.
That inequality is the missing signed estimate, not a consequence of the displayed magnitude bound.

## Negative control and retained arithmetic target

Take a finite symmetric zero quartet {+-g+-i delta}, g>0, 0<eta=omega-h<delta<omega. Its finite screw-function model has Psi_omega>=0 by the same logarithmic-derivative/Nevanlinna argument. At eta its zero formula contains a nonzero oscillation of size exp((delta-eta)t), hence arbitrarily negative values. This refutes automatic descent from strip confinement, symmetry, positivity and bounded R alone. It is NOT a zeta counterexample and does not kill arithmetic descent.

The actual source remains Suzuki's full prime-power sum sum_(n<=exp(t)) Lambda(n)n^(-1/2-eta)(t-log n), with every smooth gamma/pole term. Existing SCALAR_RESERVE_OWN, SELBERG_SCALAR_AUDIT and JOINT_LATTICE_AUDIT already show that generic convexity loss or a change of summation does not establish its signed reserve. No prime-power sector or early history may be dropped.

Semantic return dictionaries: inverse Volterra positivity / resolvent cone; exponentially tilted integrated Chebyshev discrepancy / one-sided Tauberian remainder; stop-loss order under exponential untilting. These are UNVERIFIED search hints, not new suppliers. The existing Suzuki theorem is an exact conditional consumer; it does not provide the arithmetic inequality. Next bounded question must seek a genuinely stronger signed source estimate, or explain precisely which previously proved Q3 input supplies it. A new representation alone does not count as progress.

Status: bounded-magnitude descent STALLED; actual signed descent OPEN. No improved zero-free strip, SP or RH established. Q7 not sent.
