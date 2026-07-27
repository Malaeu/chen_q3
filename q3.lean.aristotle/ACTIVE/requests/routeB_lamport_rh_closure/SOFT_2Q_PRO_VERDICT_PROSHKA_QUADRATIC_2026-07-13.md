# SOFT_2Q — PRO VERDICT (Proshka V1, round 4: quadratic divisor route) — 2026-07-13

Status: `EXTERNAL_VERDICT_TRANSCRIPT_CONDENSED_FAITHFUL / AUTHORITY_FOR_QUADRATIC_DIVISOR_GATE / NOT_RH`
Channel: V1 (Proshka, kill+repair). Round 4 (fork adjudication requested by
SOFT_2). Materialized by Mythos (V2); theorem statements, proofs, plants and
codes are verbatim-faithful; prose condensed. Supersedes the linear DAG.

## TOP-LEVEL

```text
C1 polarization:            KILLED   (SOFT_C1_POLARIZATION_TARGET_MISMATCH)
C2:                         CONDITIONAL SURVIVOR after weakening (C2')
C3 theta/Mellin crosswalk:  KILLED as crosswalk; retained as TARGET module
Phase recovery:             REMOVED from the demand set
RH:                         NOT_RH
Route score:                5/5
```

Main result: do NOT reconstruct the linear limit from quadratic data. For RH
it suffices to identify the HERMITIAN PRODUCT H*H^sharp: the zeros of the
product already carry the divisor information.

## 1. C1 KILLED

Polarization turns Q(h)=B(h,h) into a sesquilinear form, but its natural
zero-side output is sum_rho F(rho-1/2)*conj(G(1/2-conj(rho))) — not
<Xi*gamma_0, phi>. Producing a linear functional would need one fixed g_0
"representing" the distribution Xi*gamma_0 — which is the old S2 hidden in
the choice of g_0. Also no canonical linear map phi -> f_phi with
phi = f_phi * f_phi^sharp exists on a full signed test class (square-root map
nonlinear, non-unique, undefined for sign-changing phi).

## 2. C3 KILLED AS CROSSWALK, KEPT AS TARGET MODULE

Theta/Mellin solves the TARGET side (Xi unconditionally representable without
critical-line zero sums) but not the source mismatch: the finite corpus
outputs F*F^sharp (quadratic), theta/Mellin outputs the linear object
Xi*gamma_0; the phase falsifier blocks quadratic->linear. Lawful role of C3:
unconditional identification of the TARGET HERMITIAN PRODUCT
(Xi*gamma_0)(Xi*gamma_0)^sharp. Code if misused as crosswalk:
SOFT_C3_LINEAR_SOURCE_OBSERVABLE_MISSING.

## 3. C2' — THE SURVIVOR (weakest working form)

Do not demand |H|^2 + phase rigidity => H = c*Xi*gamma_0. Demand only:
  H*H^sharp = c * (Xi*gamma_0)(Xi*gamma_0)^sharp.

## THEOREM SOFT_2_QuadraticDivisorTransfer (PROVED HERE)

Let S = {|Im z| < 1/2} be the connected symmetric strip and F -> F^sharp ONE
source-locked antilinear involution preserving the real axis (exact formula —
conj(F(conj z)) or conj(F(-conj z)) — must be pinned to D0.6). Let F_j be
holomorphic on S. Assume:
 Q1 (real-zero approximants): Z(F_j) ∩ S ⊂ R for all j;
 Q2 (normal family): for each K ⋐ S, sup_j sup_K |F_j| < ∞;
 Q3 (nonzero anchor): F_j(z_*) = A_* ≠ 0 at fixed z_* = i/4;
 Q4 (quadratic pairing identification): for every phi in C_c^inf(I),
     <F_j F_j^sharp, phi> -> c <T T^sharp, phi>, T := Xi*gamma_0, c > 0,
     gamma_0 in O(S)^x.
Then all zeros of Xi in S are real; hence RH.

PROOF. By Q2 + Montel pass to F_{j_k} -> F locally uniformly. Q3 gives
F(z_*) = A_* ≠ 0, so F not identically 0. Real zeros + Hurwitz give
Z(F) ∩ S ⊂ R. The involution is continuous for locally-uniform convergence,
so F_{j_k}F_{j_k}^sharp -> F F^sharp locally uniformly. Q4 + distributional
uniqueness give F F^sharp = c T T^sharp on I; both sides are restrictions of
holomorphic functions, so the identity theorem extends the equality to all of
S. All zeros of the left side are real (zeros of F are real; zeros of F^sharp
are reflections of real zeros, hence real). If Xi(z_0) = 0 for some
z_0 in S \ R, then T(z_0) = 0 (gamma_0 zero-free), so F(z_0)F^sharp(z_0) = 0,
forcing a non-real zero of F or of F^sharp — contradiction. Hence
Z(Xi) ∩ S ⊂ R; by the classical interface, RH. QED. (Conditional roof: it
does not prove Q1–Q4.)

## PHASE: from bug to gauge

F_j -> e^{i theta_j} F_j changes no F_jF_j^sharp. Phase-probe reinterpretation:
FAIL due to global/moving phase only -> C2' SURVIVES; FAIL because no single
source-locked sharp involution exists -> C2' dies; PASS with exact fixed
phase -> stronger than required. (FixedGaugeSquareRootRigidity exists as an
optional stronger theorem but is NOT needed for RH.)

## NEW DAG (replaces linear 3.1–3.4)

SOFT-3Q.1 exact finite quadratic pairing
SOFT-3Q.2 joint tail convergence
SOFT-3Q.3 unconditional target-product identity (theta/Mellin module)
SOFT-3Q.4 quadratic pairing convergence
SOFT-3Q.5 divisor transfer (the theorem above)

## STRONGEST ATTACKS (standing)

(1) Target must be literally (Xi*gamma_0)(Xi*gamma_0)^sharp — if it is again a
zero-counting distribution / Weil functional / Xi'/Xi:
SOFT_C2_TARGET_PRODUCT_MISMATCH. (2) The SAME sharp on finite source, cluster
limit, and target — else SOFT_C2_SHARP_CONVENTION_MISMATCH. (3) gamma_0
defined beforehand and zero-free — else SOFT_C2_GAMMA_POSTHOC.

## CODEX DIRECTIVE (verbatim)

TARGET: SOFT_2_QuadraticDivisorTransfer — prove/typecheck the abstract
theorem. Inputs: connected symmetric strip S; source-locked involution sharp;
locally bounded holomorphic F_j; real-zero property; fixed nonzero anchor;
distributional convergence of F_jF_j^sharp; target T = Xi*gamma_0 with
gamma_0 zero-free. Forbidden: linear pairing with F_j; phase reconstruction;
critical-line zero sum; defining gamma_0 as F/Xi; importing RH; numerical
phase evidence as proof.
Validation plants:
 P1 multiply every F_j by arbitrary unit phases -> theorem must remain valid;
 P2 delete the real-zero hypothesis -> counterexample F(z)=z-i, G(z)=z+i must
    kill the theorem;
 P3 replace target TT^sharp by Xi'/Xi -> typecheck must fail;
 P4 allow gamma_0 a zero -> divisor conclusion must fail.
Success: SOFT_C2_QUADRATIC_DIVISOR_ROOF_LOCKED.

## META

Killed: C1; C3-as-crosswalk; linear S2; phase recovery as RH requirement.
Survivor: C2' quadratic product identity + real-zero roof.
Smallest gap (then): ExactFiniteHermitianProductPairing.
"The phase falsifier did not kill the soft route; it forced us to stop
demanding information the square fundamentally does not contain."

NOT_RH.
