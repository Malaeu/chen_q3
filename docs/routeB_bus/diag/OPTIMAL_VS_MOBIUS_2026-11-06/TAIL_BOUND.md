# Exact relation and independent tail bound

The archive stores the projection solution `c_plus=G^{-1}b`. The physical
free coefficients used throughout this experiment are `c=-c_plus`, so
`R_c(k)=1+sum_{n=2}^N c_n (k mod n)/n`. For the taper the physical coefficients
are `a_n=mu(n)(1-log(n)/log(N))`, n>=2. In both cases define

```
D_c(s) = sum_{n=2}^N c_n (n^(-s)-1/n),
c_1 = -sum_{n=2}^N c_n/n,  D_c(1)=0.
```

This is the centered polynomial `V_N-V_N(1)` for the taper. It is not the
uncentered BCF polynomial. The induced n=1 coefficient is not an extra free
coordinate in the Part A statistics.

Let `rho_n(x)={1/(nx)}`. On `x in (1/(k+1),1/k)` the function
`rho_n-rho_1/n` equals `(k mod n)/n`; it vanishes for x>1. Since
`M rho_n(s)=-zeta(s)n^(-s)/s`,

```
M[chi + sum c_n(rho_n-rho_1/n)](s) = (1-zeta(s)D_c(s))/s.
```

Mellin-Plancherel, exactly as in pinned R7 §2, therefore gives

```
E(c) = sum_{k>=1} R_c(k)^2/[k(k+1)]
     = (1/(2*pi)) int_R |1-zeta(1/2+it)D_c(1/2+it)|^2/(1/4+t^2) dt.
```

There is no RH or simplicity premise. R7's opposite coefficient sign in its
projection-coordinate display must be converted together with the residual
sign; using the archive's positive coefficients directly in `1-zeta D` is
incorrect. The continuous integrand is even for these real coefficients.

## Independent bound beyond T

Put `f(y)=exp(-y/2) R_c(floor(exp(y)))` for y>=0 and zero otherwise.
Its Fourier transform, with kernel exp(-ity), is the Mellin transform above.
For any integer K>=2, truncate `f_K=f 1_[0,log K)`, and set

```
B = 1 + sum_{n=2}^N |c_n|,
V_K = |R_c(1)|
    + sum_{k=1}^{K-1} |R_c(k)| (1/sqrt(k)-1/sqrt(k+1))
    + sum_{k=2}^{K-1} |R_c(k)-R_c(k-1)|/sqrt(k)
    + |R_c(K-1)|/sqrt(K).
```

The expression V_K is the total variation of f_K extended by zero: the first
and last terms pay the endpoint jumps, the second pays the smooth derivative
on each cell, and the third pays the internal jumps. Consequently integration
by parts for bounded-variation functions gives `|Fourier(f_K)(t)|<=V_K/|t|`.
Also `||f-f_K||_2^2<=B^2/K`, since |R_c(k)|<=B. Plancherel and the triangle
inequality in the restricted Fourier L2 space give the explicit bound

```
Tail_c(T) := (1/(2*pi)) int_{|t|>T} |Fourier(f)(t)|^2 dt
          <= (V_K/sqrt(pi*T) + B/sqrt(K))^2.
```

The factor pi includes both signs of t. `tail_bound.py` evaluates this
expression independently of the Gram error and continuous head using Arb
128-bit balls. Optimal coefficients are the exact binary64 values obtained by
parsing the CSV, matching the vector used by the numerical calculation; taper
coefficients use Arb enclosures of their real logarithmic definition. All
K in {16,64,256,1024,4096,16384,65536} are reported, and the smallest valid upper
bound is selected. JSON upper bounds are rounded outward on conversion to
binary64. The finite residual recurrence is
`R(k)-R(k-1)=sum c_n/n - sum_{n|k} c_n`, starting at R(0)=1.

These bounds are deliberately elementary and loose. Combining a numerically
estimated head H with `[0,Tail_upper]` is a diagnostic consistency enclosure;
H itself has convergence evidence, not an interval quadrature certificate.
Neither `E-H` nor agreement with E is used to manufacture the tail bound.
The exact identity is analytic; this computation does not certify its numerical
value to 1e-10 or certify the zeros or an asymptotic statement.
