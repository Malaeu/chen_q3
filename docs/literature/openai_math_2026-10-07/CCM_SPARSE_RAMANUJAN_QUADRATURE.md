# Ramanujan quadrature on a sparse band: a larger sieve level, with exact return

2026-10-08. Bounded derivation independently checked by read-only sparse_band_receiver: S1-S5 PASS, including fixed-order uniformity, exact signed return and the convolution mean. Same original K_m, N=m, L=log m. This extends R5-R7 of CCM_DENSITY_PAIRING_TEST.md on a test subspace only. It proves no prime spectral bound.

Fix alpha,beta>0 with alpha+2beta<1, M=floor(m^alpha), R=floor(m^beta). Let Q_M(s) denote the principal |j|<=M submatrix of the original Q(s), and P be the orthogonal projection in this band onto the original b,v_+,v_- constraint kernel. Put A_M(t)=P Q_M(log t) P/sqrt(t). Let chi be fixed and smooth with compact support in (1/2,1). All constants below may depend on chi,alpha,beta and the fixed differentiation order J, never m.

## Nonstationary calculation

Retain exactly lambda_R,C_R,nu_R,b_R of the density note. The additive character coefficient l1 norm of nu_R is at most R^2/C_R, its constant coefficient is 1, and every nonzero reduced frequency has denominator at most R^2.

For every original matrix entry restricted to this band, the oscillatory frequencies satisfy |omega|<=2pi M/L. After t=my, a Poisson frequency has phase m[xi log y+2pi(theta-h)y], xi=omega/m. On supp chi, |xi/y|<=4pi M/(mL). The condition

    M R^2 <= m L/8                                             (S1)

therefore ensures |xi/y|<=(pi/2)|theta-h| whenever theta-h is nonzero. Higher derivatives of xi log y have the same uniform bound by a constant times |theta-h|. J integrations by parts, with no endpoint terms, give C_J m^(1/2-J)|theta-h|^(-J). Sum over h for fixed theta costs at most C_J R^(2J), J>=2. The theta=h=0 contribution is exactly the retained smooth integral. Diagonal amplitudes -2log(y)/L and offdiagonal 1/[2pi i(j-k)] coefficients have bounded fixed derivatives uniformly; the latter entries are differences of two allowed phases.

The row count is now 2M+1, not 2m+1. Orthogonal compression costs nothing. Consequently

    ||sum_n chi(n/m)nu_R(n) A_M(n)-integral chi(t/m) A_M(t)dt||
       <= C_J M m^(1/2-J) R^(2J+2)/C_R.                       (S2)

Multiplication by log(t)/C_R has fixed derivative cost O(L/C_R), so

    sum_n chi(n/m)b_R(n) A_M(n)
      = integral chi(t/m)[log(t)/C_R] A_M(t)dt + E_b,
    ||E_b|| <= C_J M m^(1/2-J) L R^(2J+2)/C_R^2.             (S3)

The power of m on the right, ignoring logarithms and C_R>=1, is

    alpha+1/2+2beta-J(1-2beta).

As beta<1/2, for each prescribed T>0 a fixed J makes this < -T-1. Condition S1 holds eventually since alpha+2beta<1. Thus errors are O_T(m^(-T)). No derivative order grows with m.

## Exact arithmetic return, not a small remainder claim

Since R<m/2 eventually, every prime on the support is >R, and b_R(p)=Lambda(p). The original signed smooth upper block is exactly

    sum_n chi(n/m)Lambda(n) A_M(n)
       -integral chi(t/m)(1-1/t) A_M(t)dt
     = integral chi(t/m)[log(t)/C_R-1+1/t] A_M(t)dt + E_b
       +sum_n chi(n/m)[Lambda(n)-b_R(n)] A_M(n).             (S4)

The final sum contains composites and prime powers and retains their signs. Positive scalar b_R does not imply matrix positivity. Lower blocks remain absent from this bounded calculation and must be paid before full-source use.

## Size of the smooth scalar coefficient

An elementary convolution evaluates C_R=log R+O(1). Set a(n)=mu(n)^2/phi(n), and define multiplicative g by

    g(p)=1/[p(p-1)], g(p^2)=-1/[p(p-1)], g(p^j)=0 (j>=3).

Prime-power multiplication gives a=g*(n->1/n). Both sum |g(d)| and sum |g(d)|log(2d) converge: their Euler factors involve O(p^-2) and their logarithmic derivatives O(log(p)/p^2). Moreover sum g(d)=product_p[1+g(p)+g(p^2)]=1, absolutely. Therefore

    C_R=sum_(d<=R) g(d) H_floor(R/d)=log R+O(1).

Indeed H_floor(x)=log x+gamma+O(1/x) for x>=1. The error (1/R)sum_(d<=R)d|g(d)| is bounded by sum |g(d)|. The missing tail in the coefficient of log R is bounded by sum_(d>R)|g(d)|log d; the logarithmic g sum is finite. These bounds give a uniform O(1), sufficient here.

For R=floor(m^beta) and t in the support, uniformly

    log(t)/C_R = 1/beta+O(1/L).                            (S5)

Thus the smooth scalar coefficient in S4 tends to 1/beta-1, not zero. Since beta<(1-alpha)/2, this constant is > (1+alpha)/(1-alpha)>1. This is a scalar mean calculation only: it is NOT a lower bound for the P-compressed matrix, whose constraints can cause further cancellation. It does not kill signed composite cancellation or establish a parity barrier theorem.

## Decision

Sparse bandwidth permits polynomial R instead of the earlier R^2<=L/8. This is a real enlargement of the proved quadrature range. It does not by itself make the source discrepancy small: S4 is the exact next joint signed target, and the full range of t must still be handled. The conditional sparse-band receiver remains distinct from full-SP moment control. No new Pro question is sent by this derivation.
