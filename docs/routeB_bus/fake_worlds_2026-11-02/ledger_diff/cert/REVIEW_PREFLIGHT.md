# Bounded read-only check of C(iii) and the interval callback

DIAGNOSTIC_NEVER_A_PROOF. Independent check by the C(i) worker of the root's
`preflight.py` and emitted `preflight.json`; no source edits or new eigensystem.

**CONFIRMED within the explicitly numerical finite-zero-census scope.**

- The theta majorant follows from `|a(n)|<=1`, `n^2>=n`, and
  `sum n exp(-alpha*n*u)=exp(-alpha*u)/(1-exp(-alpha*u))^2`.
  On the radius-4 disk centered at `2+it`, real parts lie in `[-2,6]`.
  The two completion-integral powers are bounded by `2u^3` for `u>=1`.
  The displayed elementary integral therefore bounds the disk modulus by
  `352.385...<512`, uniformly in the disk's imaginary center.
- On its center, `|D(2+it)|>=2-zeta(2)` and
  `|Gamma(3/2+it/2)|^2=pi(1/4+t^2/4)/cosh(pi*t/2)` give the stated lower
  bound `C exp(-pi|t|/4)`, with `C=0.631806...>1/2`.
- The zero strip `-1<Re rho<2` follows from absolute Dirichlet comparison
  at real part 2, completion entireness, and functional reflection.
  A unit-height slab in this strip lies inside radius 3.5 about
  `2+i(j+1/2)`: its squared distance is at most `9+1/4<3.5^2`.
  Jensen with radii 4 and 3.5 bounds its count by `100+7(j+1)`;
  the chosen constants safely dominate the logarithmic and linear terms.
- `(1+cos(2*pi*x/L))^K` has a zero of order `2K` at each endpoint.
  Thus all boundary terms in 16 integrations by parts vanish for K>=8.
  The derivative L1 bound by sqrt(L) times its physical L2 norm is correct,
  and that L2 norm is the coefficient sum used in the script.
- Critical-line pairs contribute `2 F G`; a reflected off-line quartet
  contributes `4 Re(F G)`. The tail's separate factor 2 covers negative
  heights. The monotone sum bound `f(N)+integral_N^infinity f(x)dx` is valid
  for the positive decreasing function `(107+7x)/x^32`.
- The three profile vectors, their norms, and mixed source/zero pairings
  match the stated physical Fourier convention. Their differences are below
  the conservative tail budgets. Neither finite matrix quadrature nor finite
  zero census is mislabeled as interval-certified in the output.

The C(i) Arb callback was also rechecked. `sinc` is entire, including zero.
The sole denominator `sinhc(s)=sinc(i*s)` has poles of the reciprocal away
from the real integration path at nonzero imaginary multiples of pi.
Complex-ball inclusion and nonfinite reciprocal evaluations preserve the
analytic integration contract when a trial integration region reaches such a
zero; no branch-dependent formula is used. The exact sinc identity removes
the real endpoint singularity before integration. Ignoring the callback's
analytic flag introduces no unsupported branch in these entire/meromorphic
expressions.

No error or additional scoped gap was found. The zero-location/completeness
limitation remains exactly the numerical limitation stated by the preflight.
