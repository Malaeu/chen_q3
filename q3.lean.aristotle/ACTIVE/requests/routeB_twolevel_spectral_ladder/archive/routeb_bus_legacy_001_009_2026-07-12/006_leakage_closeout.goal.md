# 006 — LeakageCloseout_v1

/goal LeakageCloseout_v1 for Route B / Route Z E5. CHEAP compute.
NOT_RH. No Phase 2. No QW/packet changes. ACTIONS LOG mandatory.
Answer file: bus/006_leakage_closeout.answer.md (handoff format).
Reference: docs/PEN_3_1_4a_LEFT_EDGE_v3.md Sections 7 and 9.
NOTE: execute AFTER 004 and 005 (smallest-NNN rule stands).

G1 H2 CONSTRAINT ROW (strict rubric; no numerics accepted as proof):
  open the g04 constructor (true-precision packet builder); exhibit the
  linear condition set on (c_0, c_4). REGISTERED: exactly two conditions
  {int f = 0, f(0) = 0} (or an equivalent pair spanning them), quoted
  verbatim from code with line numbers (0.6); if only int f = 0 is
  imposed and f(0)=0 is emergent-numeric => H2_NUMERIC_ONLY escalation
  (0.3); anything else => report (0.1).
  Code: H2_CONSTRAINT_EXHIBITED / H2_NUMERIC_ONLY / H2_OTHER.

G2 POISSON TAIL TRUNCATION TEST (decides the 1.17% mismatch):
  extend the F2 Poisson side from k <= 8 to k <= 40 (same quadrature
  discipline, Legendre/Bessel cross-check at 3 random k).
  REGISTERED: relative mismatch |direct - Poisson(k<=40)|/|direct|
  drops below 2e-3 (0.6); FORK: stalls above 5e-3 => the residual is
  NOT truncation => named SECOND_EDGE_CHANNEL, report partial sums
  vs k to localize (0.3).
  Code: TRUNCATION_CONFIRMED / SECOND_EDGE_CHANNEL / AMBIGUOUS.

G3 S_TAIL CERTIFICATE (numbers for the v3.1 Lemma):
  S_tail(numeric) := sum_{k=2..200} |c_0 mu_0 psi_0(k) + c_4 mu_4 psi_4(k)|
                     / |mu-scale as in the note|.
  Report partial sums at k = 8, 20, 50, 100, 200 and the per-mode sums.
  REGISTERED: S_tail(200) <= 0.5 * |psi(1)-combo| (0.6); convergence
  visible (increment from k=100 to 200 below 5% of total) (0.7).
  Code: STAIL_CERT_OK / STAIL_DIVERGENT_SUSPECT.

G4 PLANT REDESIGN (phase judge that actually bites for h0/h4):
  recompute the F2 Poisson side with the CONJUGATE Fourier convention
  (e^{-icxy}: mu_n -> conj(mu_n)) AND with a single-mode sign flip
  (c_4 -> -c_4) as two separate shadow runs.
  REGISTERED: conjugate-convention shadow changes the Poisson value by
  < 1e-6 relative (h0/h4 has real mu; the conjugation is inert BY
  STRUCTURE — this documents WHY, closing the K1 gap honestly) (0.7);
  the c_4 sign-flip shadow breaks direct/Poisson agreement by >= 10x
  the current mismatch (0.8) — THIS is the informative plant.
  Code: PLANT_REDESIGNED_FIRES / PLANT_STILL_INERT.

FINAL STEP: one history line in ROUTE_B_STATE.md; answer file; git add;
STOP. Do not select next gate.
