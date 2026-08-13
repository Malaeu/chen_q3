# Mythos verdict — Goal 058 next G1/G3 source task

Date: 2026-08-13

Source request:
`docs/routeB_bus/proshka/PROSHKA_MYTHOS_REQUEST_GOAL058_NEXT_G1_G3_SOURCE_TASK_2026-08-13.md`

Attachment SHA-256 supplied to Mythos:
`6409bad6c8b36525969a2840f70ab7a7ee9f06bcfa4df32b4074ebcb6cc86392`

## Verbatim response

**MYTHOS ATTACK CONTRACT — RETURN** (attack conducted against the byte snapshots carried in the brief; pin 66ed3c33 / canonical request 52d1c48d acknowledged)

```yaml
MYTHOS_VERDICT: REVISE

ATTACKED_PRIMARY: >-
  ARISTOTLE_G3_LITERAL_PROJECTIVE_DECAY_SOURCE
  (a fortiori ARISTOTLE_JOINT_LITERAL_FESHBACH_SOURCE;
   ARISTOTLE_G1_LITERAL_CCM_GAP_SOURCE separately inadmissible: a uniform-in-j
   separation needs entry-asymptotics of W02−WR−Prime that have zero
   materialized Lean ingredients at the pin — a manufactured task)

FIRST_HIDDEN_BINDER_OR_OBJECT_MISMATCH: >-
  The cofinal target "sourceCCMGroundProjectionErrorSq S_j i_j xi_j -> 0"
  contains the binder j ↦ xi_j with NO literal denotation in the tree.
  There is no Lean object selecting "the bottom eigenvector of
  ccmWeilMatFinite(m_j,N_j)". Every discharge of that binder fails a rule:
  (a) xi free — refuted by the already-compiled zero-overlap plant
      (goal058ConnectorZeroOverlapPlant_projection_zero: error = full mass);
  (b) xi_j := "the bottom eigenvector" — a definite description that smuggles
      existence + simplicity, i.e. a renamed G1 premise (falsifier 5/8);
  (c) xi_j := realified trial — refuted by the compiled [1, I] plant
      (goal058ConnectorPhasePlant_no_common_real_phase).

COUNTEREXAMPLE_OR_REASON: >-
  Five-line kernel plant: carrier Fin 2, K = 0 (every unit vector is a bottom
  eigenvector), row = ![1, 0]. Then xi = ![1,0] gives ErrorSq = 0 while
  xi = ![0,1] gives ErrorSq = 1 on the SAME eigenspace. Without a simplicity
  selector the per-cell value of the G3 target does not exist; the cofinal
  decay statement is ill-typed before G1-grade selection data. The wall is not
  merely open — as currently phrased it is not a proposition.

SMALLEST_REPAIR: >-
  Re-class (the brief permits one added class):
  ARISTOTLE_G1_G3_COUPLING_CONNECTOR — an exact finite energy/floor sandwich
  with the ground eigenpair and complement floor as EXPLICIT per-cell binders
  (role-labelled consumer slots in the H2a gap_clause shape, i.e. exactly what
  a future G1 certificate emits — not premises smuggled into a supplier).
  ROLE: EXACT_SOURCE_CONNECTOR_NOT_COFINAL_SUPPLIER, same legal class as the
  just-proven Hermitian connector. It merges the walls honestly: any future G1
  floor family plus a trial-energy envelope yields G3's ErrorSq control through
  this theorem, then the proven connector, then KernelL2 — formalizing exactly
  what the M1C cell measured. Mandatory extra plant: the degenerate-eigenspace
  ill-posedness example above, compiled, as the permanent selector-necessity
  falsifier.

RECOMMENDED_EXACT_THEOREM_HEAD: |
  namespace Q3.RouteB

  theorem sourceCCMGroundProjectionErrorSq_le_trialEnergyExcess_div_floor
      (S : D0Pstar.ProlateCanonicalSourceData)
      (i : D0Pstar.PairIndex)
      (mProject : ℕ)
      (lam mu2 : ℝ)
      (xi : CCMModeFinite i.N → ℝ)
      (hxi : xi ⬝ᵥ xi = 1)
      (heig :
        ((ccmWeilMatFinite mProject i.N).map (Complex.ofReal)) *ᵥ
          (fun j => (xi j : ℂ)) = (lam : ℂ) • (fun j => (xi j : ℂ)))
      (hfloor : ∀ w : CCMModeFinite i.N → ℂ,
        star (fun j => (xi j : ℂ)) ⬝ᵥ w = 0 →
          mu2 * (star w ⬝ᵥ w).re ≤
            (star w ⬝ᵥ
              (((ccmWeilMatFinite mProject i.N).map Complex.ofReal) *ᵥ w)).re)
      (hlt : lam < mu2) :
      sourceCCMGroundProjectionErrorSq S i xi ≤
        ((star (D0Pstar.sourceCCMComplexRow S i) ⬝ᵥ
            (((ccmWeilMatFinite mProject i.N).map Complex.ofReal) *ᵥ
              D0Pstar.sourceCCMComplexRow S i)).re − lam) / (mu2 − lam)

  end Q3.RouteB
```

**Attack notes on my own recommendation, pre-armed (three, with dispositions):** (1) *"hfloor is a renamed gap"* — it is a consumer slot, not a supplier claim: the theorem's role field and evidence boundary state it supplies neither wall; its hypothesis shape is byte-compatible with the output of `gap_clause`/`H2a_SimpleEvenGround_FromPenaltyCoercivity` (`β ≤ μ` on the complement), which is precisely where future G1 certificates plug in. The falsifier-5 rule bans hidden premises in a *supplier*; a role-labelled connector with the ill-posedness plant attached is the opposite of hiding. (2) *"decomposition q = ⟨xi,q⟩xi + w needs ErrorSq = ‖w‖²"* — this is the star-symmetric normSq identity, finite algebra of the same class Aristotle already produced in `complexRow_projection_error_identity`; no new API. (3) *"complexification via Matrix.map is a new object"* — it is definitional (`map Complex.ofReal`), proved-inside-the-theorem per the standing REAL/COMPLEX connector rule from the correction delta; the plant carrier for the ill-posedness example must use the same map to block a carrier swap.

**Evidence boundary:** finite-cell connector only; G1 OPEN, G3 OPEN; no cofinal inference, no promotion, no PX, no RH claim. If Прошка's independent selection is `NO_SOUND_ARISTOTLE_SOURCE_TASK_AVAILABLE`, my REVISE stands as the constructive alternative: one sound bounded task exists, and it is the head above.

## Codex preliminary audit

The selector objection is valid and is preserved for Proshka adjudication.
The proposed inequality is not itself a G1/G3 supplier because `hfloor` is a
gap-shaped input. A generic sibling already exists as
`weighted_projective_defect_le_rayleigh_excess_div_gap` in
`WeightedRayleighProjectiveDefect.lean`; therefore any Aristotle task must be
justified as a literal-source connector rather than a new mathematical source.
The proposed head also leaves `mProject` independent of the literal pair index
`i.m`. That makes the matrix family freely substitutable even while the trial
row remains source-locked. A same-family repair must use
`D0Pstar.sourceCCMFiniteMatrix i` directly or require `mProject = i.m`; merely
hard-coding the row is insufficient. The direction of the Hermitian projective
error and the exact real/complex matrix coercivity surface still require
kernel-checked verification.
