# Full Ramanujan quadrature payment on the sparse CCM band

2026-10-08. Root derivation; independent read-only sparse_band_receiver audit PASS for F1-F5 and the conditional quantifiers of OPEN F6, including both endpoints and the smaller-band derivative bound. Original N=m matrix, L=log m, band |j|<=M and its original b,v_± constraint projection P. Let E_R,D_R,C_R be exactly L5 of CCM_LOG_DENSITY_CANCELLATION.md. All integers 1<=n<=m and all integration endpoints are retained.

## Uniform partial sums of the finite density

The finite expansion nu_R(n)=sum_theta c_theta exp(2pi i theta n) has c_0=1, sum |c_theta|<=R^2/C_R, and every nonzero reduced theta has denominator <=R^2. For theta not integer, geometric summation gives

    |sum_(n=1)^k exp(2pi i theta n)|<=1/|sin(pi theta)|<=R^2.

The last inequality follows from sin(pi x)>=2x for 0<=x<=1/2 and ||theta||>=R^-2; the loose constant is valid. Therefore for every real t>=1,

    B_R(t)=sum_(1<=n<=t)nu_R(n)-(t-1),
    |B_R(t)|<=1+R^4/C_R.                                  (F1)

The zero frequency contributes floor(t)-(t-1) in [0,1]. No full-period averaging or short-interval prime assumption is made.

## Full endpoint-safe Abel return

Put f(t)=log(t)P Q_M(log t)P/sqrt(t). Both f(1)=0 and f(m)=0; the latter uses the original Q(L)=0, which survives the principal band and compression. The discrete Hilbert commutator formula in CCM_PRIME_TRANSITION_TEST.md gives on the smaller band

    ||Q_M(s)||<=2, ||Q_M'(s)||<=D_M=(2+8pi M)/L.

Indeed its Hilbert matrix is a principal compression of norm <=pi and max |omega_j|=2pi M/L. P is fixed in t. Consequently

    ||f'(t)||<=[2+(1+D_M)log t]t^(-3/2),
    integral_1^m ||f'(t)||dt <=8+4D_M.                     (F2)

Here integral_1^infinity t^-3/2 dt=2 and integral_1^infinity log(t)t^-3/2 dt=4. Keeping the sign of 1-log(t)/2 could improve the constant, but is unnecessary.

Since b_R(n)=log(n)nu_R(n)/C_R, matrix-valued Stieltjes integration by parts with F1 gives exactly

    E_R= -1/C_R integral_1^m B_R(t) f'(t)dt,
    ||E_R|| <= (1+R^4/C_R)(8+4D_M)/C_R.                    (F3)

The atom at 1 is multiplied by f(1)=0, and the upper boundary vanishes by f(m)=0. Thus this is the FULL E_R, not a smooth-block proxy; no lower blocks or endpoint terms remain unpaid in F3.

## Quantifiers and the remaining source

For fixed alpha,beta>0, alpha<1, M=floor(m^alpha), R=floor(m^beta), C_R>=1 and F3 yield

    ||E_R||=O_(alpha,beta)(m^(alpha+4beta)).                 (F4)

No condition alpha+2beta<1 is needed for this coarser global bound. The previous superpolynomial smooth-block estimate remains available when its extra condition holds. For a fixed alpha,beta, F4 is NOT subpolynomial in m and must not be called such.

Combining F3 with the exact L5 identity, the only unpaid term of this decomposition is

    D_R=sum_(1<=n<=m)(Lambda(n)-b_R(n))
                        P Q_M(log n)P/sqrt(n).             (F5)

It includes small primes <=R and all prime powers and composites. Pointwise signs of Lambda-b_R do not imply a matrix sign.

An explicit sufficient new interface would be: there is an absolute finite c>0 such that for every sufficiently small fixed alpha,beta>0,

    lambda_max(D_R)<=C_(alpha,beta) m^(c(alpha+beta)) eventually. (F6)

F6 is OPEN. If proved, for any fixed hypothetical off-critical delta>0 choose alpha,beta once so that max(alpha+4beta,c(alpha+beta))<delta. The accepted sparse receiver applies to this fixed alpha and gives a negative term of order m^delta/(log m)^(2delta), contradicting the floor obtained from F3,F6 and the O(log m) archimedean term. This parameter choice depends on the hypothetical fixed zero; it never varies with m. Constants and onset may depend on the fixed parameters/zero. Thus F6 would suffice to exclude all off-critical zeros without falsely claiming a fixed-alpha subpolynomial estimate from F4.

Only F1-F4 and the exact F5 identity are new checked PAPER results here. No F6, full-SP estimate, RH result or new Pro dispatch is claimed.
