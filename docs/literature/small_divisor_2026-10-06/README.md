# Small-divisor quadrature: primary-source fit

- Juan Arias de Reyna, Explicit van der Corput’s d-th derivative estimate,
  arXiv:2407.02094v1 (2 July 2024), Lemma5, printed page4.
  https://arxiv.org/pdf/2407.02094
  Local PDF SHA256: 7c3d87ef5550a3fe7a8d1c85961299e0c835f2824cd862bbc245350fca9546a2.
  Root read the lemma and its proof. Hypotheses: real C² phase on (X,X+Y],
  Y>=1, 0<lambda<=f''<=Lambda. Conclusion: |sum e(f(n))|<=
  A/sqrt(lambda)*(Lambda Y+2), A=2.79368380731<3.
  Exact application: f(u)=-t log(u)/(2pi), u in [N,2N], t>N,
  lambda=t/(8pi N²), Lambda=t/(2pi N²), interval length<=N;
  intervals of length<1 are bounded directly. Negative t by conjugation.
- Kiran S. Kedlaya, Notes on analytic number theory, §18.2, Eq18.2.1.
  https://kskedlaya.org/ant/chap-bombieri2.html
  Root read the displayed Vaughan identity for n>z. Setting y=z=U and
  grouping the third sum by a gives alpha_U(a)*Lambda(b), a,b>U.
  Only the convolution identity is used. Bombieri–Vinogradov estimates
  on this page are NOT imported into the carrier problem.

These inputs verify the Type-I error estimate only. They supply neither
Type-II signed compensation nor a whole-matrix lower bound.
