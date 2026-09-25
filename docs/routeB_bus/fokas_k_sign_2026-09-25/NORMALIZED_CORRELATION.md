# Signed density test for the full central form

2026-09-25. Same Ferrers row, plane and literal K; no new source family.
This follows R3 and the Rayleigh identity in ALGEBRA.md. Write q=z/||z||
for the **finite central or rectangle row**, not the infinite Ferrers source.
Let v be a unit companion of Pi z in range(Pi). Then q and v are orthogonal.
The central sign is tau_c=v*Kv-q*Kq=-Pfull/(||z||²||Pi z||²).
Its passage to the infinite source still needs the existing rectangle/tail budget.

## Exact reduction

Let Q(x) be the entire ccmQKernel matrix, n,j=-m,...,m, L=log m,
and Delta(x)=v*Q(x)v-q*Q(x)q. With the literal prime powers retained,

    tau_c = integral_0^L h(x) Delta(x) dx
            - sum_{k=2}^m Lambda(k)/sqrt(k) Delta(log k),
    h(x) = 2 cosh(x/2) - exp(x/2)/(2 sinh x).

Indeed W02=integral 2cosh(x/2)Q(x) dx, entry by entry. For diagonal
frequency b=2pi n/L and a=1/2,

    integral_0^L (L-x)cosh(ax)cos(bx) dx
      = (cosh(aL)-1)(a²-b²)/(a²+b²)².

Multiplication by 4/L gives the closed W02 diagonal. Off-diagonal entries
follow from integral cosh(ax)sin(bx) dx=b(1-cosh(aL))/(a²+b²).
Since Q(0)=2I and both vectors are unit, Delta(0)=0: the scalar WR constant
and the subtracted Q(0) integrand cancel exactly. No individual nonconstant
matrix contribution is discarded.

The weight has one zero x*=log t*, where t*>1 solves t*³-t*-1=0.
Its sign is negative below x* and positive above x*, because

    h(x) = exp(x/2)/(2sinh x) * (exp(3x)-exp(x)-1)/exp(2x).

Both kernel branches also give Q'(0)=-(2/L)11*, so with
A=|sum v_n|²-|sum q_n|²,

    Delta'(0)=-2A/L,     lim_{x->0+} h(x)Delta(x)=A/L.

These identities hold for complex coefficients; squared sums are squared
moduli. Thus a source-specific endpoint comparison is visible, but does not
control the integral or the prime samples.

## Executed discriminator: pointwise positivity fails

The simplest sufficient approach would require h(x)Delta(x)>=0 everywhere
and nonnegative signed prime contributions. It already fails for the finite
m=2 reference row despite its certified positive full tau_c.

The new Arb script uses the same exact rational rectangle and rigorously
bounded Gaussian plane as arb_m2_certificate.py. It obtains, on the ENTIRE
rectangle,

- endpoint limit: [4.372467 +/-4.14e-7] > 0;
- Delta(L/2): [-1.222039 +/-3.78e-7] < 0.

At L/2, Q is exactly diag((-1)^n). For m=2, h(L/2)>0 follows without
numerics: t=exp(L/2)=sqrt(2), t³-t-1=sqrt(2)-1>0. Consequently the signed
density is strictly negative there, and by continuity on a neighborhood.
The only prime term k=2 is exactly zero since Q(L)=0. Together with the
previous whole-rectangle negative R3 certificate, this proves that a positive
integral here includes both positive and negative density regions.

This is a rigorous finite obstruction to pointwise positivity on this reference
cell, NOT a cofinal counterexample, NOT a failure of the full signed test, and
NOT a result about the final shifted schedule (m=2 is below its source threshold).
It selects integrated signed comparison, rather than pointwise positivity, as
the next mechanism to investigate. A family estimate still needs to preserve
both density signs and all prime samples; the exact reduction alone supplies
neither a leading term nor its remainder bound.

Reproduce:

    .venv/bin/python docs/routeB_bus/fokas_k_sign_2026-09-25/normalized_correlation_certificate.py

Source: CCMFiniteWeilSourceMatrixN1.lean definitions ccmQKernel, ccmW02Entry,
ccmWREntry, ccmPrimeEntryN1; same finite Fourier carrier used throughout this packet.

## Component discriminator (diagnostic only)

The unchanged central form at m=4 has signed R3 contributions
W02=+34.1910791766, -WR=-75.1221402151, -Prime=+40.7333298795.
Their sum is -0.197731159056: only 0.13178% of the sum of absolute
contributions remains. At m=2 the corresponding cancellation factor is
3.108; at m=4 it is 758.841. These two cells do not establish growth with m.
The three normalized tau contributions at m=4 are respectively
-0.351670772937, +0.772665319445, -0.418960791762.
Thus neither W02 nor the prime contribution supplies the observed positive
tau by itself. An absolute-value bound which loses this cancellation is
already inefficient in this cell. This is evidence for a joint signed estimate,
not a proof that all componentwise estimates must fail.

`quartic_components.py --m 4 --dps 120` reproduces the diagnostic. All three
contributions and the total agree to the displayed 35 digits between m2
70/110-digit runs and m4 90/120-digit runs. The root independently reran the
m4 120-digit delivered script. Quadrature/eigenvalue outputs remain uncertified.
