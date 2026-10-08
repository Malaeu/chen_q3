# Own Q4 extension — many flat directions do not give a free bulk bound

2026-10-08. Original full K_r, d=2r+1,L=log r,r>=4. Uses independently accepted Q4(6)-(12); no new zero-free premise. Consumer: every-eta full negative floor. This attempt tests whether the controlled boundary direction can be expanded into a controlled spanning family.

For any unimodular phases z_j, set c_j=z_j/sqrt(d). In Q4 notation,

 C c=diag(dar)c+pi^(-1)(diag(h)Hc-H diag(h)c).

The absolute row sum of H is H_(r+j)+H_(r-j)<=2H_(2r)<=6L. Therefore ||Hc||_infinity<=6L/sqrt(d), while ||H||<=pi. Retaining the actual joint primitive estimates ||h||<=12sqrt(r)L^(5/2), ||dar||<=24sqrt(r)L^(5/2) gives

 ||Cc|| <=12sqrt(r/d)L^(5/2)(3+6L/pi)<=40L^(7/2).

For the last constant, r/d<1/2 and L>=log4 imply
 (12/sqrt(2))(3/log4+6/pi)<35<40.
The full background satisfies ||B||<=50L, so ||Kc||<=100L^(7/2). This holds for every phase choice, but it does not establish positive energy for those choices: Q4's positive Rayleigh quotient was proved for the particular all-ones vector only.

Take the exact orthonormal Fourier vectors c^(ell)_j=d^(-1/2)exp(2pi i ell(j+r)/d), ell=0,...,d-1. Summing their squared image norms gives

 Tr(K²)=sum_ell ||Kc^(ell)||² <=10000 d L^7.

Thus the number of eigenvalues <=-s is at most10000 d L^7/s², and ||K||<=100sqrt(d)L^(7/2). These are valid consequences, but the last exponent1/2 does not improve the already available conditional3/8+epsilon lower floor.

For a projection P onto k of these orthonormal directions, ||KP||<=100sqrt(k)L^(7/2), and
 J=K-(I-P)K(I-P)=PK+KP-PKP
 satisfies ||J||<=300sqrt(k)L^(7/2). Hence deleting k polylogarithmically many flat directions has a subpolynomial endpoint return; deleting k~r^a pays r^(a/2) up to logarithms. No lower floor for the remaining compression has been proved. No stepwise summability is inferred.

This rejects the inference that individual polylogarithmic column bounds automatically control their entire span at the same cost. It is not a counterexample to SP, nor proof that the displayed dimension loss is necessary for this particular K. The missing input is joint signed/correlated control on the remaining source, or a stronger bound on this span. Independent ccm_window_transport audit PASS: constants, all-phase extension, orthonormal Fourier basis, Hilbert-Schmidt identity and k-direction return checked. The sqrt(k) statement applies to the specified orthonormal directions; a nonorthogonal span needs its Gram conditioning. Adjacent-endpoint padding/subspaces remain an additional obligation.
