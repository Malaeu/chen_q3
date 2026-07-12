# D0_7E_OWNER_INPUT — ExactDetectorBDefinition (owner-ratified)

Date: 2026-07-12 · Owner channel: Mythos · Status: IMMUTABLE OWNER INPUT · NOT_RH.
Answers: `D0_7E_OWNER_INPUT_REQUEST.md` (node `D0.7e ExactDetectorBDefinitionAndCrosswalk`).
No numerical reconstruction is used anywhere below; every number is either a classical constant or a per-cell certified artifact reference.

---

```text
DETECTOR_B_NAME:
  bDet — CentralMellinCalibration (центральная меллиновская калибровка).

PARAMETER_REGIME:
  finite (m, N): cells lambda_m with lambda_m^2 in N (working set Lambda),
  N = N(lambda_m) per D0 rule F2.4 (form N = ceil(kappa*lambda^2); anchor
  (lambda^2=13, N=120)). lambda-only notation forbidden until N fixed
  (PEN_3_3_G04 finite-parameter discipline).

SCALAR_FIELD_AND_TYPE:
  bDet_(m,N) : R  (real scalar per cell; no z-dependence; proof of reality
  under REAL_COMPLEX_PHASE below).

EXACT_FORMULA:
  Primary definition (tracker-vs-Xi central calibration):
    bDet_(m,N) := Fhat_(m,N)(0) / Xi(0),
  where, with the frozen normalized trial k_(1,lambda,N) = s_(lambda,N) *
  P_(lambda,N) g_lambda (PEN_3_3_G04 §4) and the raw map of D0 draft F5.1:
    F_(m,N)(z)    := Integral_{lambda^-1}^{lambda} k_(1,lambda,N)(u) * u^(iz) du/u,
    Fhat_(m,N)(z) := gamma(1/2 + iz) * F_(m,N)(z),
    gamma(s)      := (1/2) s (s-1) pi^(-s/2) Gamma(s/2),
    Xi(z)         := xi(1/2 + iz).
  Exact simplification (one-line identity, since Xi(0) = gamma(1/2)*zeta(1/2)
  and the gamma-factor cancels at the central point):
    bDet_(m,N) = F_(m,N)(0) / zeta(1/2)
               = sqrt(2 log lambda_m) * c0(k_(1,lambda,N)) / zeta(1/2),
  where c0 := <V_(0,lambda), k_(1,lambda,N)> is the n = 0 coefficient in the
  frozen character basis (D0 line F1.3), i.e. literally one entry of the
  persisted coefficient vector, and zeta(1/2) = -1.46035450880958681...
  (classical constant). No Gamma evaluation is needed to compute bDet.

NORMALIZED_OBJECT:
  Carrier: H_lambda = L^2([lambda^-1, lambda], du/u) (PEN_3_3_G04 §4).
  Object: the tracker Fhat_(m,N) — an element of H(Omega), Omega =
  {|Im z| < 5/2} (D0 draft F5.2/F5.4), built from the exact normalized trial
  vector k_(1,lambda,N). bDet calibrates the TRACKER against Xi at the
  central point z = 0.

NORMALIZATION_IDENTITY:
  On the nonzero locus bDet_(m,N) != 0 define
    G_(m,N)(z) := Fhat_(m,N)(z) / bDet_(m,N).
  Then, exactly,
    Fhat_(m,N)(z) = bDet_(m,N) * G_(m,N)(z),   and   G_(m,N)(0) = Xi(0)
  by construction. Consequence (c-b unification): the tracking scalar c_j of
  the working roof 3.3' is DEFINED as c_j := bDet_(j); the roof hypothesis
  liminf |c_j| > 0 becomes exactly the lower bound of interface I-b2.

DOMAIN_AND_NONVANISHING:
  bDet_(m,N) = 0  <=>  c0(k_(1,lambda,N)) = 0  <=>  the multiplicative-window
  mean Integral k1 du/u vanishes. This is NOT forced by the packet's exact
  time-side zero integral (that kills hhat(0), a different functional); no
  structural zero is known. Discipline:
   - per-cell: interval certificate |c0| > 0 read directly from the persisted
     coefficient vector (it is one stored entry);
   - cells with certified c0 = 0 are excluded and flagged
     B_CENTRAL_ZERO_CELL; cofinality of the surviving set is then a named
     obligation;
   - large-lambda nonvanishing is NOT claimed here: it is the registered
     obligation PO_B_NONVANISH, a sub-leaf of the shared nondegeneracy lemma
     NORM_NONDEG (serves H1-c, H3c, H4d simultaneously).

REAL_COMPLEX_PHASE:
  Real. Proof: g_lambda is real-valued, hence the basis coefficients satisfy
  c_(-n) = conj(c_n), so c0 in R; s_(lambda,N) > 0; zeta(1/2) in R. Therefore
  bDet in R. Phase/sign convention: the sign is inherited from the frozen
  packet phase I_(n,lambda) > 0 (PEN_3_3_G04 §1) and is REPORTED per cell,
  never normalized away; the detector consumes |bDet|.

W_PRIME_CROSSWALK (theorem statement; registered obligation PO_D0_7E_XWALK):
  Let v1 be the even-sector ground with phase <v1, k1_even> >= 0 (D0 F4.4),
  alpha_(m,N) the canonical parity-projected Rayleigh excess (D0 F3.2),
  DeltaE_(m,N) the true complementary spectral distance of the H4 ledger, and
    WPrime_(m,N)^2 := |bDet_(m,N)|^2 * lambda_m * alpha_(m,N) / DeltaE_(m,N),
  with bDet the scalar defined ABOVE (independently of any spectral data).
  THEOREM SHAPE to be proved: if the two-sided bound of interface I-b2 holds
  (0 < c_low <= |bDet|*sqrt(lambda_m) <= C_b * lambda_m^(q_b + 1/2)), then for
  every compact K subset S there exist A_K < infinity and eps_(m,N,K) -> 0:
    sup_K |Fhat_(m,N) - bDet_(m,N) * Xi|
      <= A_K * [ WPrime_(m,N) + |bDet_(m,N)| * delta_dict_(m,N) ] + eps_(m,N,K),
  where the first term arises from the strip-evaluation constant of F5.1
  (sqrt(2 log lambda) * lambda^(1/2 - delta_K)) composed with the two-step
  Davis-Kahan / Kato-Temple bound sqrt(alpha/DeltaE) <= eta/DeltaE of the H4
  two-level ledger, and delta_dict is the H3c dictionary convergence term of
  the calibrated ground tracker. Proof route: F5.1 strip bound + Kato-Temple
  + two-level Davis-Kahan + Groskin-dictionary pointwise convergence +
  Vitali. NON-TAUTOLOGY: bDet is defined by a central VALUE of the tracker;
  WPrime is defined by SPECTRAL quantities; the theorem CONNECTS the two —
  WPrime is at no point redefined, and the inequality direction (tracking
  error controlled by WPrime) is exactly what roof 3.3' consumes.

SOURCE_POINTER:
  Owner-ratified NEW definition (explicitly declared as such), anchored to:
   - PEN_3_3_G04_OBJECT_DICTIONARY.md §4 (k1, s_(lambda,N), H_lambda) —
     sha256 010282dda8b76e8a9e0ea184f14a62d34f60b0d4b588f8f0e541b97a959ef71e;
   - D0 draft lines F1.3 (basis), F5.1 (raw map + strip constant),
     F5.2/F5.4 (tracker, Omega), F4.4 (ground phase) — this-session pen,
     destination docs/EXACT_OBJECT_FAMILY.md;
   - classical constant zeta(1/2) (Lean: Mathlib riemannZeta at 1/2;
     interval arithmetic for numerics).
  New proof obligations registered by this input (connecting bDet to ZEO):
   - PO_B_NONVANISH  (large-lambda nonvanishing of c0; sub-leaf of NORM_NONDEG);
   - PO_B_BOUNDS     (interface I-b2/I-b3: two-sided bound, q_b declared);
   - PO_D0_7E_XWALK  (the crosswalk theorem above).

MANDATORY FIREWALL (confirmed verbatim):
  bDet is not bWeil_j;
  bDet is not OCR xihat;
  bDet is not automatically bPilot = ||E(g04)||;
  bDet is not automatically sTrial^(-1) = ||gTrial||;
  the definition itself does not claim H4d uniform bounds
    (they remain the obligations PO_B_NONVANISH / PO_B_BOUNDS);
  the W-prime crosswalk is not obtained by tautologically redefining W-prime
    (WPrime keeps its spectral definition; bDet enters it as the
     independently defined central calibration, connected by PO_D0_7E_XWALK).
```

## Judges shipped with this input (pre-registered)

1. Per-cell certificate at lambda^2 = 13, 14, 17: bDet = sqrt(2 log lambda) *
   c0 / zeta(1/2) evaluated intervально from the persisted coefficient entry;
   report value AND sign. Expectation (FIT_NOT_LAW, from the measured WPrime
   slope -5.003): |bDet| * sqrt(lambda) approx const, i.e. q_b approx -1/2 —
   a falsifiable expectation for PO_B_BOUNDS, not an input.
2. N-stability: bDet at (13, 90) vs (13, 120) within factor 3.
3. Two-way evaluation: F_(m,N)(0) via the stored-coefficient identity vs
   direct quadrature of Integral k1 du/u — machine-zero agreement.
4. Plant: a shadow copy with the c0 entry zeroed must yield bDet = 0 exactly
   and must trip the B_CENTRAL_ZERO_CELL guard; a checker not tripping is
   itself invalid (PLANT_INERT).

## Stop codes introduced

B_CENTRAL_ZERO_CELL · D0_7E_XWALK_OPEN (crosswalk theorem not yet proved —
current honest state) · PLANT_INERT.

NOT_RH. This input defines an object and registers obligations; it proves no
RH-level statement.
