# Conventions and the correction to task B.2

All fits vary only the physical free coefficients n=2..N:

```
L=log N, x_n=log(N/n)/L,
a_1=1, a_n=mu(n) P(x_n) (n>=2),
s=sum a_n/n, S=sum a_n, b=1+(S-s)/2,
u=sum a_n log(n)/n,
q_1=1-s, q_n=a_n (n>=2).
```

Thus sum q_n/n=0, sum q_n=2b-2, and the centered Dirichlet polynomial
is D(z)=sum_{n>=2} a_n(n^(-z)-1/n). This is the ec1e2e96 free-coordinate
convention. Raw a_1=1 need not equal P(1) in an unconstrained profile fit.
The constant term of D is q_1, not raw a_1.

With these definitions the fixed-vector Gram objective remains
E=1+2 sum_{n>=2}a_n log(n)/n+a^T G a. The reciprocity objects are

```
B=2b(1+u)-s,
F(x)=sum_{n=1}^N (q_n/n) B_1(n*x)+sin(2*pi*x)/pi,
B_1(x)={x}-1/2 off integers, and 0 at integers,
L_N(F)=sum_{k=2}^N (q_k/k) sum_{r=1}^{k-1}cot(pi*r/k) F(r/k).
```

The algebra of pinned reciprocity (4)--(6),(14)--(15) applies to arbitrary
real free coefficients, not just the log taper: E=B-pi*L_N(F). J2 evaluates
the rational-point functional directly, rather than defining it by this
identity. Bounds proved only for the log taper, such as norm(F)<=7/log N,
are comparison benchmarks for fitted profiles, not imported theorems for them.

## Exact head identity

Use the standard generalized von Mangoldt convolution

```
Lambda_j(r) = sum_{d|r} mu(d) log(r/d)^j,
Lambda_0(r) = 1_{r=1}.
```

For P(x)=sum_{j=1}^d p_j*x^j, all r<=N satisfy

```
A_P(r) = sum_{n|r} a_n
       = 1-P(1)
         + sum_{j=1}^d p_j/L^j
             sum_{k=0}^j binomial(j,k) log(N/r)^(j-k) Lambda_k(r).
```

Proof: for every divisor n of r, write log(N/n)=log(N/r)+log(r/n),
expand by the binomial theorem, and sum with mu(n). Replacing the natural
coefficient mu(1)P(1) by the fixed raw a_1=1 adds 1-P(1) for **every r**,
because 1 divides every r. It is not an indicator supported only at r=1.
For the log taper P=x this reduces to 1_{r=1}+Lambda(r)/L.

The literal formula A=sum_j p_j Lambda_j/L^j in task B.2 omits the shifted
binomial terms (and, for a free endpoint, the raw-a_1 adjustment). It already
fails algebraically for P=x^2, N=4, r=2: the direct sum is 3/4, whereas the
literal expression is 1/4. This counterexample was identified before numerical
runs. R4 is scored for the literal requested formula; the corrected identity
is a separate validation. For a spline, A is calculated by the direct divisor
sum, with no global polynomial identity asserted.

## Core and Fourier energy

For every positive integer k put A_P(k)=sum_{n|k,n<=N}a_n. Then

```
R(k)=1+sum_{n=2}^N a_n (k mod n)/n
    =1+k*s-sum_{r=1}^k A_P(r).
```

The same R8 cutoff is used: K=ceil(N*sqrt(N)), head=sum_{k=1}^N
R(k)^2/[k(k+1)], shoulder=sum_{k=N+1}^{K-1} R(k)^2/[k(k+1)], H=head+shoulder.
The finite core is not the infinite full Gram norm.

Parseval gives the exact finite expression

```
norm(F)^2 = sum_{h,k<=N} q_h q_k gcd(h,k)^2/(12 h^2 k^2)
            +(1/2-q_1)/pi^2.
```

Using gcd(h,k)^2=sum_{d|h,d|k} J_2(d), the double sum equals
sum_d J_2(d)*(sum_{d|n,n<=N}q_n/n^2)^2/12. This reorganization preserves
all cross terms. J4 compares its norm with independent integration of F(x)^2
between rational breakpoints, with midpoint values used where required.

## Energy-mask clarification

The frozen shorthand "same disjoint delta-energy classes" means disjointness
within each inherited partition: n<=sqrt(N) versus n>sqrt(N), squarefree versus
non-squarefree, and primes versus proper prime powers versus other. The
additional mask n>N/2 and masks from different partitions overlap; their shares
must not be added as one partition. No mask or scoring rule is changed.
