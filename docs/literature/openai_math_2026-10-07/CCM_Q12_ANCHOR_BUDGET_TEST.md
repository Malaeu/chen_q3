# Post-Q12 own attempt 1: can moving the temporal anchor reduce the price?

2026-10-22. ROOT PAPER calculation, bounded scalar-budget test; no arithmetic
gain, no source impossibility theorem. This is a continuation of Q12, not Q13.
Exact local search in CCM notes and September OPENSGN found the anchored
representation, not an already supplied smaller anchored bound. This limited
search is not a complete literature/supplier absence claim.

## Contract

Keep the original complex vector c in ran P, N=m, L=log m, original frequencies
and all three constraints. For 0<=a<=L put psi_a(t)=f(t+a), zero outside
[-a,L-a]. Translation preserves the full arithmetic Q, L2/H1 norms and zero
exponential moments: each moment only acquires a nonzero scalar factor.
The derivative bound remains ||psi_a'||<=Omega||psi_a||.

Do NOT assume the corrected Suzuki Gram is translation invariant. Define its
own N_a and Delta_a=N_a-Q for every anchor; thus Q=N_a-Delta_a separately.
The question is only whether optimizing a in the proved Q12 scalar envelope
can lower its power. There is no decomposition of f and no discarded cross term.

## Full return of the same estimates

The proof of Q12(4.5) uses total exponential moments, not symmetry of endpoints.
It therefore gives the same pole convolution k*psi_a with norm at most2.
The arch difference formula and its tail also retain the same C_Omega.

Write T_-=a and T_+=L-a. The prime Volterra operator is a direct sum on the
negative and positive half-lines. On each side outward shifts only see prime
powers n<=exp(T_side). Their contraction estimates give

    ||B_pr psi_a|| <= max(W(exp(a)), W(exp(L-a))) ||psi_a||
                   = W(exp(max(a,L-a))) ||psi_a||.

This norm bound uses orthogonality of the two temporal supports only before
the Fourier multiplier; it does not assert that their actual Gram cross terms
vanish. Q12's full rank-one contraction subsequently pays them jointly.
W includes every prime power. The original linear prime form still runs to m.

Consequently the SAME sufficient defect budget becomes

    e_m(a)=2[1+(W(exp(max(a,L-a)))+C_Omega)^2]+2W(m)+c_A,
    Delta_a <= e_m(a)||f||²-D_arch(f).

W is nondecreasing, so this displayed budget is minimized at a=L/2 (possibly
also on a finite plateau). The elementary W(y)<=6sqrt(y) relaxation has leading
Gram price 72 exp(max(a,L-a)), plus 12sqrt(m) from the full linear prime form.
For a=theta L its Gram exponent is max(theta,1-theta)>=1/2.
Even permitting a to depend on m cannot lower this relaxed exponent, since
max(a,L-a)>=L/2 pointwise. The midpoint was already the optimum of this bound.

## Decision and limits

Moving one anchor while retaining precisely Q12's norm separation supplies no
smaller budget. This is an optimization of a proved upper bound, NOT a lower
bound for Delta_a, its Gram, Q, or any CCM eigenvalue. No PNT asymptotic is needed.
We do not optimize this parameter further. The first unpaid information remains
the actual xi-dependent complementary projection and its relation to the same
prime coefficients before scalar separation, Q12(3.5)/(6.1).

Next substantive test should retain that multiplier and both temporal halves;
another anchor, scalar norm constant, or renamed full target is insufficient.
No new Pro request sent. RH and eta(epsilon)->0 remain OPEN.
