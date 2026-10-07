# Uniform inverse-series tail budget

2026-10-07. Continuation of PARITY_REFLECTED_BRANCH.md. This estimates the left-contour branch only, conditional on the source reflection and kernel estimates. It does not estimate the contour residues or the final joint additive pairing.

Use the original row ball q_m<=C Z^M and powerful-part dyad q_m,pow~Z^O, with X=Z^N and fixed good squarefree d coprime to m. All M,N,O and delta=log_Z q_d lie in bounded ranges. Let tau>0 be fixed.

## Tail without a bound on r

The old active good radical has norm at most C Z^(M-O/2): a valuation-one prime contributes its norm, while the active radical of the powerful part is at most its square root. Adding the exponent-four primes of d gives

q_c,new <= C Z^(M-O/2) q_d.

Consequently every reflected kernel at scale X q_d^5 q_r^6 has argument a*q_mu with

a >= c Lambda_r,   Lambda_r=Z^(N-2M+O) q_d^3 q_r^6.

The source support mu in lambda^(-4)O minus zero has a fixed positive minimum norm. Source 3089ff bounds the cusp coefficient divided by sqrt(q_mu) by a constant, and every local column factor by q_p^(1/2). The total local factor is at most C Z^(M/2-O/4)q_d^(1/2). The local choices cost a divisor factor, uniformly absorbed into Z^epsilon on the stated bounded ranges.

For Lambda_r>=Z^tau and sufficiently large Z, the kernel's rapid large-argument bound and the lattice sum with exponent A>1 therefore bound the row norm of the weighted r term in equation (2) by

constant_A * M_A(V) * Z^(M-O/4+epsilon) q_d^2 q_r^2 Lambda_r^(-A).

Here Z^(M/2) bounds the square root of the number of original rows; C_d and all phase factors have modulus at most one. Constants may depend on fixed arithmetic data, exponent ranges, tau and kernel order, not on d,r or the moving rows.

Write A=B+1. On the discarded r set, use Lambda_r^(-B)<=Z^(-tau B), and use the remaining Lambda_r^(-1) exactly. The sum of row norms is at most

constant * M_A(V) * Z^[M-O/4+2M-O-N-tau B+epsilon] q_d^(-1)
  * sum_{rad(r)|d} q_r^(-4).

The last sum is at most the fixed Dedekind-zeta value zeta_F(4). Choose B large after fixing the exponent ranges and desired saving D. This makes the entire discarded inverse-series tail O(Z^(-D)) in row norm, with a finite higher seminorm of V. In particular no bound on rho=log_Z q_r was assumed to prove tail summability.

The remaining branch thus has

3delta+6rho < 2M-O-N+tau,                                 (1)

up to harmless fixed support constants absorbed by a slightly larger tau. If 3delta exceeds 2M-O-N+tau, the whole left branch is negligible. This says nothing about its contour residues.

## What the retained branch still costs

For bounded d and retained r exponent ranges, the frozen-d moment from PARITY_REFLECTED_BRANCH.md applies. In the balanced squarefree case M=N,O=0 its norm is at most Z^(M/2+epsilon), before multiplication by q_d^(3/2)q_r^2. The constraint (1) gives

q_r <= Z^((M+tau)/6) q_d^(-1/2).

The number of r supported on d within any polynomial range is O_epsilon(Z^epsilon). Proof: for any fixed a>0, the count up to R is at most R^a product_{p|d}(1-q_p^(-a))^(-1); for each fixed a,b>0 the product is at most C_(a,b) q_d^b. Choose a,b after fixing the polynomial ranges.

Triangle over the retained r terms therefore gives only

norm_m J_left <= Z^(5M/6+tau/3+epsilon) q_d^(1/2)

in this balanced case, plus an arbitrarily small tail. This is a bound, not an improvement over the original completed-row norm Z^(M/2+epsilon). It deliberately retains the cost that a formal fixed-d reflection can hide. For d=1 the exact series contains only r=1 and the original moment should be used instead of this coarse envelope.

Independent bounded check PASS: mobius_source_audit verified the all-r tail split, norm aggregation, retained cutoff, smooth-supported count and final balanced exponent. Root compared the source reflection support/local bounds (1795–1803, 3092–3105), kernel bound (1860–1864), lattice estimate (2618–2636), and frozen-row moment proof (3180–3276). This is a checked derivation conditional on those source estimates, not an independent audit of the whole manuscript.

A useful next estimate must exploit cancellation in the joint additive pairing, or improve this retained-branch bound together with the residue contribution. Uniform tail decay alone does not close the low estimate.
