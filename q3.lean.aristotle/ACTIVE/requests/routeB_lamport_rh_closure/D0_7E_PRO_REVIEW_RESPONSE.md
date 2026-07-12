# D0_7E_PRO_REVIEW_RESPONSE — adjudication of PRO_REVIEW_REQUEST (D0.7e.5)

Date: 2026-07-12 · Reviewer channel: PRO (triad: Theorist → Прошка/Luise → Research → CC-Shadow)
Reviewed artifact: `D0_7E_CENTRAL_MELLIN_CALIBRATION.md` (audit) + `D0_7E_OWNER_INPUT.md`
(sha256=a0f8ef78ec023aeef34f6ae03769faaf675a94d30d93b85a5da5258cb2f0bfed) + `STATE.json`
+ `ROUTE_B_THEOREM_CONTRACT_v1.md` + `ALPHA_DETECTOR_OBJECT_LOCK.md`.
Status of this document: REVIEW VERDICT + OWNER_APPROVAL_REQUIRED (DAG revision needs
Ылша's ratification line, §7). NOT_RH.

---

## 1. Verdict one line

**Option B, AMENDED (B′): accept the retyping of D0.7e.5 to a typed non-circular
consumer slot, but the downstream address of the full tracking theorem is the
H3 tier ONLY — NOT D0.8.** D0.8 is a child of D0 and hence upstream of H3/H4;
moving the theorem there reproduces the same cycle
`D0.7e/D0.8 -> D0 -> H3/H4 -> theorem` that motivated the request. Option B as
written ("move to D0.8/H3") is half-correct; the D0.8 half is rejected.

## 2. Answer to the question for Louise

**D0.7e requires only the non-circular algebraic `bDet` consumer identity.**
Three independent authorities converge:

1. The D0.7e node statement in `STATE.json` itself ends with "**without importing
   later uniform bounds**". The owner proof route (F5.1 strip bound + Kato–Temple +
   two-level Davis–Kahan + Groskin dictionary + Vitali) consumes exactly those later
   uniform bounds (H3c, H4 ledger). So the full theorem is unprovable AT THIS ADDRESS
   by the node's own contract — not merely inconvenient.
2. H3's node statement already claims the theorem: "The same normalized real-zero
   approximants **track Xi uniformly on every compact substrip**", with failure code
   `GROUND_TRIAL_TRACKING_MISSING` and with H3c owning the joint N–λ diagonal
   quantifier (`JOINT_N_LAMBDA_QUANTIFIER_MISSING`) — precisely the two ingredients
   the audit flags as absent in D0.7e.5. The DAG already has a room reserved for
   this theorem; D0.7e.5 was trying to occupy someone else's room.
3. The primary source (`H8ULBMAL/fulltext.md:1240-1255, 1293-1297, 1469-1477`)
   names trial-to-ground tracking as the main missing step — outlook, not theorem.

Additional decisive reason against Option A: **α has no authoritative definition
anywhere in the corpus** (`ALPHA_DETECTOR_OBJECT_LOCK`: slot A1 MISSING, status
OBJECT_DICTIONARY_MISSING). Option A would force minting `α :=` inside a D0 leaf —
a reconstruction forbidden by the lock's discipline and a violation of the
one-dictionary rule (Contract PO-13: one object in paper and Lean). α's birthplace
is the H0 glossary slot A1, nowhere else.

Option C is rejected: it busts two already-PROVED decomposition contracts
(D0.7.0 `D0_7_DECOMPOSITION_LOCKED`, D0.7e.0 `D0_7E_DECOMPOSITION_LOCKED`), forces
re-validation of every assembly under them, and removes ZERO mathematical content
from the gap — the uniform evaluation estimate is missing under any ordering.
Hardness conserved, hiding places multiplied (K8 violation).

## 3. Repaired statement of D0.7e.5 (the slot, exact)

Retype D0.7e.5 as `TypedWPrimeConsumerSlot`:

```text
(i)   TYPE. On BDetNonzero, with typed hypothesis parameters
      alpha_(m,N) >= 0, DeltaE_(m,N) > 0, delta_dict_(m,N) >= 0, and a limit
      filter F on I_fin (all four SUPPLIED DOWNSTREAM, none defined here),
      the expression
        WPrime_(m,N)^2 := |bDet_(m,N)|^2 lambda_m alpha_(m,N)/DeltaE_(m,N)
      is well-typed, and its bDet argument is the D0.7e.2 scalar — literally
      the same constant sqrt(L_m) c0/zeta(1/2), by name and by value.
(ii)  NON-CIRCULARITY LEMMA (provable now, from D0.7e.2 + D0.7e.4 alone):
      bDet is a function of the trial coefficient c0 and classical constants
      only; no spectral quantity (mu_i, alpha, DeltaE) occurs in its
      definition. Hence the crosswalk inequality shape is non-tautological:
      left side analytic, right side spectral, shared factor bDet defined
      independently of both sides' remaining content.
(iii) CONSUMER IDENTITY (provable now, algebra): on the typed domain,
        WPrime^2 * DeltaE_(m,N) = |bDet|^2 lambda_m alpha_(m,N),
      and the roof-3.3' scalar is DEFINED c_j := bDet_j, so the roof
      hypothesis liminf|c_j| > 0 is verbatim interface I-b2's lower bound.
(iv)  EXPORT. The full compact-strip tracking inequality (owner input lines
      78–98) is exported verbatim as obligation PO_D0_7E_XWALK with new
      address at the H3 tier (§4), keeping its exact registered wording.
```

Acceptance criteria for the retyped leaf (fail-closed):

- `SLOT_VACUITY` plant: deleting the slot must break the downstream H3-tier
  assembly typecheck (reassembly test). A slot whose deletion breaks nothing
  is vacuous and must fail validation.
- `TAUTOLOGY` plant: any redefinition of WPrime via bDet inside the downstream
  proof must trip the owner's NON_TAUTOLOGY firewall.
- The four typed parameters must remain UNINSTANTIATED in D0.7e (grep-guard:
  no `alpha :=`, no `DeltaE :=`, no filter selection inside the leaf).

## 4. New address and acyclic prerequisite DAG for the full theorem

Register a new leaf `H3e ExactWPrimeTrackingTheorem` (or fold into PO-10
DetectorBridge — owner's choice of label), with dependencies

```text
H3e <- {D0 (closed dictionary incl. D0.7e slot), H3a, H3b, H3c (delta_dict and
        joint N-lambda filter), H4 two-level ledger node (true DeltaE),
        H0 slot A1 (alpha), PO_XWALK_UNIFORM_EVAL (§5)}.
```

Direction check: D0.7e (slot) -> D0 -> {H3, H4} -> H3e. No edge returns into
D0. `D0_7E_XWALK_DEPENDENCY_CYCLE` is discharged by construction, not by hope.
D0.8 keeps only the same-object crosswalk audit (its current statement),
explicitly WITHOUT the tracking inequality.

The limit quantifier: the typed slot carries the filter F as an interface
parameter; the CHOICE (joint diagonal per H3c's "source-locked joint N-lambda
diagonal") is made once, at H3c, and inherited by H3e. This kills
`D0_7E_XWALK_LIMIT_QUANTIFIER_MISSING` at the D0.7e address and re-homes it to
the node already tasked with it.

## 5. The uniform-constant gap: registered as its own obligation

`D0_7E_XWALK_UNIFORM_CONSTANT_GAP` does not dissolve under B′; it moves to one
named statement with fewer hiding places. Register at the H3 tier:

```text
PO_XWALK_UNIFORM_EVAL: a weighted evaluation/cancellation theorem for T_m on
compact K ⊂ S beating the raw bound sup_K|T_m f| <= sqrt(L_m) lambda_m^a ||f||.
```

CC-Shadow arithmetic (one line, decisive per K2): with I-b2 alone,
`|bDet| sqrt(lambda_m) >= c_low` gives an uncompensated factor
`sqrt(L_m) lambda_m^a / c_low` — divergent for every a >= 0 (even a = 0 leaves
sqrt(2 log lambda_m) -> ∞). **No declared q_b can repair this; the gap is in the
evaluation estimate, not in the b-bounds.** Plausible absorption route (registered
as SUGGESTION, not theorem): strengthen the H4b gap-floor exponent demand from
m3 − m1 >= 1 + q_b to m3 − m1 >= 1 + q_b + a_K + margin, letting WPrime's decay
absorb lambda_m^a sqrt(L_m); the pen must verify whether the H4a/H4b pair
mechanism tolerates this without breaking the r13 probe bands.

## 6. `D0_7E_B_BOUND_CONTRACT_MISMATCH` is a convention offset, not a conflict

Contract v1 slot A6: `0 < c0 <= |b|·sqrt(λ) <= C_b·λ^(q_b)`.
Owner I-b2: `0 < c_low <= |bDet|·sqrt(λ) <= C_b·λ^(q_b + 1/2)`.
These q_b differ by exactly 1/2: `q_b^{v1} = q_b^{owner} + 1/2`. Under the
FIT_NOT_LAW expectation |bDet|·sqrt(λ) ≈ const, the owner convention gives
q_b^{owner} = −1/2 and the v1 convention gives q_b^{v1} = 0. Note the v1 form
with q_b < 0 would CONTRADICT its own lower bound c0 > 0 on cofinal Λ — cheap
arithmetic that shows the two documents cannot both use "q_b ≈ −1/2".
REPAIR: pin ONE convention in H0 slot A6 and add the crosswalk line above to
the glossary. (Also: the audit cites "Contract v2"; the project doc is v1 —
citation drift, fix the pointer.)

## 7. Owner decisions required (ratification block)

```text
[ ] R1. Approve B′: retype D0.7e.5 per §3; export PO_D0_7E_XWALK to H3 tier
        per §4 (this is the owner-approved DAG revision the audit requires).
[ ] R2. Choose label: new leaf H3e vs fold into PO-10 DetectorBridge.
[ ] R3. Pin the q_b convention (v1 or owner) + glossary crosswalk line (§6).
[ ] R4. Pin kappa in N(λ)=ceil(kappa·λ²) or confirm the two-parameter (m,N)
        carrier stays; the anchor (λ²=13, N=120) must NOT be back-solved into
        kappa (reconstruction ban) — D0_7E_N_SCHEDULE_UNPINNED stays open
        until an owner line pins it.
[ ] R5. Confirm α's definitional home is H0 slot A1 (AlphaDetectorGlossaryBlock),
        consumed by H3e via the typed interface only.
```

## 8. Registered predictions (score me later)

- P1: After R1, `validate_d0_7e.py` (revised) passes; D0.7e and D0.7 close as
  definitional layers; the active stop relocates to the H3 tier. Predicted new
  primary stop: `PO_XWALK_UNIFORM_EVAL`.
- P2: The uniform evaluation gap will NOT close from I-b2 + any q_b declaration
  (arithmetic of §5); it will require genuinely new cancellation input. If it
  closes without one — reopen this review, I was wrong about where the mass sits.
- P3: Per-cell judges at λ² ∈ {13, 14, 17} will show |bDet|·sqrt(λ) constant
  within factor 3 (consistent with q_b^{owner} = −1/2 as FIT_NOT_LAW).

Most likely failure point of B′: **slot vacuity** — D0.7e.5′ degenerates into
bookkeeping that certifies nothing, and the closure of D0.7e becomes cosmetic.
Pre-planned response: the SLOT_VACUITY plant of §3 is mandatory in the revised
validator; if the plant is inert, the retyping is rejected and we fall back to
keeping D0.7e.5 BLOCKED (honest state) rather than closing it emptily.

## 9. Status line

**OPEN / NOT_RH.** This review proves nothing about RH; it relocates one
theorem to its acyclic address, retypes one leaf, and converts two vague codes
(`XWALK_UNIFORM_CONSTANT_GAP`, `B_BOUND_CONTRACT_MISMATCH`) into one named
obligation and one convention pin. The unknown is smaller and better named
than before (K8 satisfied). What would change the verdict: an owner line
showing D0.7e was always intended to carry the full tracking theorem — then
Option A applies and its cost (independent in-leaf proofs of α, ΔE, δ_dict,
filter, uniform estimate) must be paid explicitly.
