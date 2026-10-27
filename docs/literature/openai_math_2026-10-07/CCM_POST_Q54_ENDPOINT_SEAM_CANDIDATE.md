# Candidate: endpoint curvature has an original-P cutoff contribution of order m

2026-10-27. ROOT CANDIDATE, independent review pending. This concerns Q54
Phi''_0 only, not a lower bound for A, T, K or their extremal eigenvalues.

## Exact source decomposition

Let H=mu*(log^2), h_n=Lambda(n), all indices <=m. Write
D_m f(t)=sum_n h_n/sqrt(n) f(t+log n) and
I_d=int conj(f(t)) f(t+log d)dt, with original zero extension.
The exact endpoint formula, by two divisor inversions, is

 Phi''_0 = (1/2)||D_m f||^2
  + sum_n [H(n)-2Lambda(n)log n]/n ||f||^2
  -2 Re sum_(dk<=m) Lambda(d)Lambda(k)/(k sqrt(d)) I_d
  +(1/2) Re sum_n H(n)/sqrt(n) I_n.

Changing I to its conjugate does not change displayed real terms. Both
hyperbolic cutoffs and every prime power are retained. H>=0 and H(n)<=log²n,
since sum_(d|n)H(d)=log²n. Chebyshev/partial summation give
sum_(n<=m)Lambda(n)/sqrt(n)<=C sqrt(m), sum Lambda(n)/n<=L+3.
Thus all terms outside the first square are bounded in absolute value by
C[sqrt(m)(1+L)^2+(1+L)^3]||f||². This is a two-sided error bound, not
an instruction to discard its signs when computing the actual source.

## A true compact contact profile

Choose nonzero real g in C_c^infinity(R), and put
f0=(d²/dt²-1/4)g, normalized in L2. It is nonzero, compactly supported,
and int exp(±t/2)f0(t)dt=0 by two integrations by parts. Place f0 at L/2
inside [0,L]; its endpoint value is exactly zero. No RH hypothesis.

Set t=L/2-L+v and n=mx. Then

 m^(-1/2) D_m f(t)
 = (1/m) sum_(n<=m) Lambda(n)(n/m)^(-1/2) f0(v+log(n/m)).

The unconditional prime number theorem for the actual Lambda measure
implies convergence, locally in v, to
 J(v)=int_0^1 x^(-1/2)f0(v+log x)dx
     =exp(-v/2) int_(-infinity)^v exp(u/2)f0(u)du.
On each fixed compact v interval the integrand has support away from x=0;
partial summation gives uniform convergence there. J is not identically
zero: J'+J/2=f0. Choose a fixed compact interval E with int_E|J|²>0.
It follows ||D_m f||² >= c m eventually. Full exponential contact makes
J vanish after the whole support has been traversed, but not during the
partial traversal at the finite n=m boundary.

## Return to the exact sparse P

For fixed epsilon>0, Fourier project this translated compact f onto the
original |j|<=floor(m^epsilon) modes of [0,L], then impose the original
three contacts by their Gram correction. Use the same estimates as
CCM_SPARSE_BAND_RECEIVER.md (4)-(5), now with a fixed smooth compact profile.
For each fixed q>=2 the L2 error is
O_q(L^(q-1/2) M^(1/2-q))=o(1); the contact Gram is eventually >=I/2.
Call the resulting original-P function f_m. Its norm tends to1.

||D_m(f_m-f)|| <= C sqrt(m)||f_m-f||=o(sqrt(m)).
Hence ||D_m f_m||²>=c' m. Apply the exact source decomposition to f_m,
including its actual projection tails. The other terms remain o(m), so

 Phi''_0[f_m] >= c'' m ||f_m||²

for every sufficiently large m at each fixed epsilon. Constants may depend
on the chosen profile and epsilon; no uniform onset in epsilon is claimed.

## Scoped consequence, if review accepts

The sufficient Q54 demand Phi''_s <= C_epsilon m^(2kappa(epsilon))||f||²
on ALL original-P f and 0<=s<=m^(-kappa), with kappa(epsilon)->0,
cannot hold: its interval includes s=0 and choose 2kappa<1.
This rejects that stronger curvature supplier. It does not reject a bound
for R_tau-Phi_tau, the original source, selected witnesses, or another
signed finite-tau completion: the exact identity contains compensating terms.
Rollback: before requiring uniformly small curvature; retain joint finite-tau
credit if that representation is pursued. No Q55 sent; goal OPEN.
