# Shifted xi kernel: source check for growth answer6

Focused shelf search found no matching fixed-shift supplier in the current
bus/literature subset; this is not an absence claim. Earlier boundary-Pick
alias was already recorded as criterion-only. Primary sources read below.

- Jeffrey C. Lagarias, Zero Spacing Distributions for Differenced L-Functions,
  arXiv:math/0601653v2, 30 Jan 2006.
  https://arxiv.org/pdf/math/0601653
  SHA256 a4d023226c1827456b21d45e999633a5a8d6479e15bac9bd6f2de7c36c80dc8f.
  Lemma2.1(1), printed p5, and Lemma6.1(i), printed p18, give the
  unconditional Hermite–Biehler property of xi(1/2+h-iz) for h>=1/2.
  EXACT_FIT: h=3/2 gives xi(2-iz). No small-shift conditional part used.
- Baranov–Belov–Borichev, Spectral synthesis in de Branges spaces,
  arXiv:1309.6915, downloaded primary PDF.
  https://arxiv.org/pdf/1309.6915
  SHA256 450c51cd2a3b18be4b37915669f828c377cc7833467612794264c26e7305edab.
  Section2.1, printed pp8–9, equation(2.1): norm and reproducing kernel;
  following paragraph: F -> F/E is a unitary map onto H² minus Theta H²,
  Theta=E#/E inner. EXACT_FIT to the auxiliary positive kernel and model
  projection only. No source-observation transfer or sampling floor follows.
- NIST DLMF5.4.3 https://dlmf.nist.gov/5.4.E3 gives
  |Gamma(iy)|²=pi/(y sinh(pi y)); with the recurrence it yields the
  exact boundary gamma factor in answer6 (15).

Root read these statements directly 2026-10-06. They support the auxiliary
construction, not RH. The paper audit verifies the application and its
obstructions. The negative diagonal is independently reproduced by
shifted_xi_diagonal_certificate_2026-10-06.py using rational arithmetic,
without importing Proshka's executable code. This is not Lean validation.

## Direct signed-form alias: not a new sign supplier

Suzuki, arXiv:2606.09096v3 (23 Sep2026), primary HTML
https://arxiv.org/html/2606.09096v3 , Theorem1.1 and (2.9)-(2.10), was
read by the bounded alias worker and root. It realizes the LOCAL signed
Weil form by the screw kernel and Friedrichs extension. The source
explicitly identifies screw positivity as RH-equivalent; no fixed
PiTheta transfer is supplied. Existing local v1 usage cards were also
read and are not identified with v3. Do not infer global temperedness
from continuity alone; the supported/local distribution identity is
all that is used here. ask.sh freshness returned INCOMPLETE, not absence.
