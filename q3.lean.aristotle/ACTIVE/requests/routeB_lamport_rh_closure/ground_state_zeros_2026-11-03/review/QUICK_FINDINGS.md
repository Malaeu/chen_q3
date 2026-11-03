# Initial findings and requests

2026-11-03; before completed spectral/root payload. Numerical diagnostic only.

Independent quickcheck.py passes at 90 decimal digits. The stable sinc and
rational transform agree to 1.05e-90 at real/complex generic arguments.
Internal harmonic continuations agree to 3.07e-91; exterior harmonic
residuals are below 7.51e-92. A generic vector has no internal harmonic
zeros, whereas the constant single-mode vector does. This is an explicit
discriminator against counting all sine-factor zeros.

The copied DH census contains 798 distinct saved positive-height
coordinates: 746 line roots plus 52 off-line roots belonging to 26
quartets. All pairs lie numerically inside the open critical strip and
have sigma_left+sigma_right=1 at the check precision. No interval
completeness or simplicity conclusion follows.

Early implementation requests sent to workers:

- Use both parity blocks and the signed parity/simple gaps. A lowest
  even vector remains a lowest even vector if odd0 is smaller.
- Require vector convergence and gap separation, not merely tiny floating
  eigenvalues/residuals in a near-null cluster.
- Preserve physical sinc continuation at all internal harmonics, external
  structural roots as their own kind, and polynomial-only comparison.
- Use actual strip coordinates t=gamma+i*(1/2-sigma); pure imaginary
  transform roots are height zero and excluded from positive-height counts.
- The draft root classifier used imag.contains(0) to call a numerator
  root real. This needs a documented isolating/conjugation guarantee,
  stronger real enclosure, or unresolved classification with escalation.
- Match counts must include both surplus directions and an explicit
  accuracy threshold. A minimum-cost assignment always pairs the smaller
  set and does not itself establish recovery.
- Polynomial arithmetic precision replay is distinct from replay of a
  source matrix and its selected eigenvector. A double-valued root
  distance cannot validate many-digit agreement.

These are preliminary requests, not findings against an exact final
payload. The later final review must check whether each was addressed.
