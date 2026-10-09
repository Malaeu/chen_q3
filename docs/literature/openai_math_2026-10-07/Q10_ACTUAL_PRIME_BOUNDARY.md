# Actual Mobius one-prime boundary: an exact masked shell energy

2026-10-09. Independent bounded audit PASS (q05_moment_audit). Continuation of W1–W5 in
Q10_WEIGHTED_SCALE_WINDOW_TEST.md, same Q10.18 consumer. RH/SP OPEN.
This uses the actual polynomial, not the generic support control.

## P1. Fixed data and finite-scale identity

Fix actual sixthfree element u, original good mask R=ag, one good prime
p not dividing R, q=qp, delta=1/10, and D0>0. Write psi=psi_u(p).
First assume psi!=0, so |psi|=1. Let

 M(N)=M_u^[R](N;W), M_p(N)=M_u^[Rp](N;W),
 v(N)=1_(N<=D0) M(N),
 A_p v(N)=sum_(j>=1) psi^j q^(-j/2) v(N/q^j).

The accepted Q8 all-powers mask inversion is exact at each finite N:

 M_p(x)=sum_(k>=0) psi^k q^(-k/2) M(x/q^k).            P1

The sum is locally finite by the fixed annular support. It is not a
squarefree-only divisor sum. Original S exclusions, u-zeros, finite-ray
nu and common W remain unchanged. If psi=0 then A_p=0; p|R is not an
active factor at all.

## P2. Sum the actual outside tail before estimating it

For N>D0 there is a unique J>=1 with

 D0 q^(J-1)<N<=D0 q^J,  x=N/q^J in(D0/q,D0].

Exactly the terms j>=J survive the cutoff of v. Therefore P1 gives

 A_p v(N)=psi^J q^(-J/2) M_p(x).                     P2

For the SINGLE-PRIME quadratic Q_p[v]=|v|^2-|A_pv|^2,
v vanishes on this outside region. The shell change of variables gives

 integral_(D0 q^(J-1))^(D0 q^J) Q_p[v](N) N^delta dN/N
   =-q^(-J(1-delta))
       integral_(D0/q)^D0 |M_p(x)|^2 x^delta dx/x.

Since delta<1, the nonnegative shell energies sum geometrically:

 I_out,p[v]= -lambda/(1-lambda) E_p(D0),              P3
 lambda=q^(delta-1),
 E_p(D0)=integral_(D0/q)^D0 |M_u^[Rp](x;W)|^2 x^delta dx/x.

All terms are retained. Endpoints do not affect these integrals. This
proves convergence of this actual outside tail directly. If psi=0,
I_out,p=0 instead; no nonzero-character formula is applied at that zero.
The sign is nonpositive; it is strictly negative only if E_p(D0)>0.
No quantitative lower bound for that energy is asserted.

This shows exactly what the apparent weighted contraction spends for
one active prime: an ORIGINAL masked shell energy, not an unspecified
small truncation error. It is not an obstruction theorem for the full
arithmetic prefix.

## P3. What the available moment actually pays

Conditionally use Q10.10, with the moving mask Rp and its explicit
norm^epsilon loss. Summing only actual rows with psi_u(p)!=0 and any
original nonnegative row mask, and then enlarging this row subset, gives

 sum_u rho(qu/U) |I_out,p[v_u]|
  << (UD qR q)^epsilon(1+T1)^A * lambda/(1-lambda)
    [ U D0^delta (1-q^(-delta))/delta
      + U^(1/6) D0^(delta+5/6)
          (1-q^(-(delta+5/6)))/(delta+5/6) ].          P4

The original sixthfree element rows, including S-valuations and units,
remain those of the source moment. Assume D0<=C D as in that lemma;
empty/subunit ranges use the same finite-support convention. The common
profile is fixed before all row sums. This is an upper bound on the
magnitude, not a lower bound on E_p.

For any fixed allowed prime q, normalizing by D0^delta leaves the SAME
U+U^(1/6)D0^(5/6) exponent as the old moment. Thus P4 alone provides no
new U-power gain. Larger q reduces its explicit factor but does not pay
all the fixed small-prime terms or the mixed terms of the full operator.
There is no sum over primes hidden in P4; such a sum would require its
own budget and all intersections.

## P4. The mixed boundary that remains

The full finite-prime quadratic is exactly

 Q_K[v](N)=sum_(T subset {p in P_K : p does not divide R})
              (-1)^|T| |A_T v(N)|^2,
 A_T=product_(p in T) A_p, A_empty=I.                 P5

The A_p commute as causal dilations; all independent positive prime
powers are included. Outside D0 the empty term vanishes. P3 evaluates
the singleton terms of P5, but subsets of size>=2 have both signs and
must remain. Their truncation condition couples their norms through
product_p qp^(j_p)>=N/D0; replacing it with independent cutoffs would
change the operator. No sum of the singleton identities is claimed to
be the complete I_out.

Next actual input: control the complete mixed tail P5 (and lower-window
complement) jointly under the original g,a,u weights, or bypass that
boundary with a direct Q10.18 arithmetic estimate. A fresh generic
full-scale multiplier estimate cannot replace this task. No new Pro
question has yet been sent.

Review: independent read-only q05_moment_audit PASS; its prime-support
index notation correction is incorporated. P1–P3,P5 are exact coefficient/operator identities;
P4 is conditional on the same source moment as Q10, not independently
certified source mathematics. No full inverse/high/RH gain.
