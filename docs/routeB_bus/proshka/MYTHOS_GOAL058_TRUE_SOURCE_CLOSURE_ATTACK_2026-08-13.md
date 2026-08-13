Packet verified: SHA-256 6639f9a6… — byte-exact match against the declared lock; read in full (198 lines). Attack conducted against the pinned objects and the paper facts as locked. Response follows the packet contract.

PRIMARY: NO_SOURCE_PACKAGE_FROM_CURRENT_INPUTS

Grounds before the numbered items, because they are quantitative and decisive. Two independent obstructions, one per estimate:

Floor obstruction (scale wall). Every transfer-shaped candidate (prolate comparison, norm-resolvent, perturbation of the prolate gap) dies by arithmetic, not by taste: the complement floor of the literal family at the certified control cell sits at the 1e−55…1e−51 scale, while the arithmetic corrections W_R + Prime that separate ccmWeilMatFinite from any prolate model are not exponentially small in any available norm. The bottom structure of the Weil form is an emergent cancellation phenomenon between W02 and the corrections; a comparison inequality ‖K − ΠP_λΠ‖ ≪ prolate-gap is false by dozens of orders. The packet's own rule ("error norm small relative to a proved prolate gap") therefore excludes every comparison the current sources can state. No current CCM theorem touches the second spectral level of the literal matrix: Thm 1.1/5.10 assume, Prop 3.4 controls only the lowest-eigenvalue convergence — provenance for δ_j: OPEN, with no partial supplier.

Decay obstruction (order-of-quantifiers). ‖r_j‖/δ_j → 0 is not evaluable before δ_j exists; and independently, at the control cell the plain ratio is O(1) (residual mass at the 1e−51 even level over a ~3e−55 complement floor), so the decay must come from genuinely improving trial accuracy along j — which is verbatim the paper's missing step 2. Provenance: OPEN. The parity/normalization exit alone is receiver-ready (EtaNonzero, sector criterion) — supplied conditionally on simplicity, hence not a package.

1. FIRST_LOAD_BEARING_SOURCE_LEMMA. The smallest theorem not on disk is the complement floor itself, and the only source mechanism visible for it that is cancellation-aware (hence not killed by the scale wall) is the divided-difference structure of the explicit source function: by the on-disk identity ccmWeilMatFinite_structured_offdiag (:330), the literal matrix is Loewner-plus-diagonal in one explicit arithmetic function β (ccmBetaScalar :20). The invention required is the quantitative definiteness of that β-form off the trial line.

Mathematical statement (invention core): for the literal β = ccmBetaScalar m and mode nodes, the quadratic form Σ_{j≠k} w̄_j w_k (β_j−β_k)/(x_j−x_k) + Σ_j (Wdiag_j − a) |w_j|², restricted to w ⊥ sourceCCMComplexRow, admits an explicit lower bound δ(m,N)·‖w‖² > 0 for (m,N) in one precommitted coupled cone — every constant traced to prime sums.

Lean-shaped head (floor form the package consumes):

lean
theorem ccmBeta_dividedDifference_complement_floor
    (S : D0Pstar.ProlateCanonicalSourceData)
    (σ : ℕ → D0Pstar.PairIndex) (hcof : PairCofinal σ)
    (hguard : Filter.Tendsto
      (fun j => ((σ j).N : ℝ) / Real.log ((σ j).m)) Filter.atTop Filter.atTop) :
    ∀ᶠ j in Filter.atTop, ∃ δ : ℝ, 0 < δ ∧
      ∀ w : CCMModeFinite (σ j).N → ℂ,
        star (D0Pstar.sourceCCMComplexRow S (σ j)) ⬝ᵥ w = 0 →
          δ * (star w ⬝ᵥ w).re ≤
            (star w ⬝ᵥ
              ((((D0Pstar.sourceCCMFiniteMatrix (σ j)).map Complex.ofReal)
                 - (a_lit (σ j) : ℂ) • 1) *ᵥ w)).re

2. INPUT_PROVENANCE. β definition — disk (CCMFiniteWeilSourceCommutator.lean:20,:24). Off-diagonal closed form — disk (:330). Diagonal entry formulas — disk (CCMFiniteWeilSourceMatrix.lean). Trial row and a — disk (D0PstarCCMFiniteSourceResidual.lean). Chebyshev-class prime bounds — Mathlib, partial. Quantitative divided-difference definiteness modulus of β off the trial line — OPEN (the invention). Coupled cone beyond the N/log m → ∞ guard — OPEN until the modulus fixes it. Trial-accuracy envelope for ‖r_j‖ — OPEN (second load-bearing lemma, SourceTrialResidualEnvelope; ordered after the floor because the ratio is vacuous without δ). Nothing relabelled.

3. G1_G3_EFFECT (finite spectral argument, receivers already on disk). Given the floor: the running exact decomposition K − aI = |q⟩⟨r| + |r⟩⟨q| + C with C ≥ δ on ran Q yields, by the standard rank-two Feshbach reduction, that the spectrum of K below a + δ − 2‖r‖ consists of exactly one simple eigenvalue whose eigenvector satisfies ‖(I−P)ξ‖ ≤ ‖r‖/δ — G1 simplicity and isolation; evenness and the η-normalization exit then follow from the on-disk parity machinery (EtaNonzero:188, sector criterion), discharging the packet's third head. Tracking: ErrorSq ≤ (‖r‖/δ)² feeds the kernel-checked connector, whose KernelL2 factor closes the transform side — G3 modulo the decay estimate. The chain is receiver-complete; only the two OPEN sources are missing — confirming the packet's framing rather than adding a decomposition.

4. SCHEDULE. Precommitted σ(j) = (m_j, N_j) = (j+2, (j+2)²): PairCofinal — trivial; guard N_j/log m_j = (j+2)²/log(j+2) → ∞ — one-line Lean lemma (provable now, no obstruction). The smallest missing schedule lemma is not existence but compatibility: that the floor's cone (item 1's OPEN modulus region) contains a tail of σ — undecidable until the modulus exists; marked OPEN, not manufactured.

5. ARISTOTLE_TASK: NO_SOUND_ARISTOTLE_TASK_AT_THIS_BOUNDARY. The load-bearing lemma is quantitative asymptotics of explicit prime sums with cancellation; it is not bounded finite algebra, and every bounded sub-piece I can state is another identity or receiver — which the acceptance gate rightly refuses to count. Better an honest boundary than a busy Aristotle.

6. ATTACK_YOUR_OWN_PROPOSAL. (i) Monotone-is-not-enough plant: the Loewner matrix of x³ on three nodes is indefinite although x³ is strictly monotone — so first-order monotonicity of β cannot supply the floor; the modulus statement must be of form-definiteness type, and any draft proving only entrywise positivity dies on this compiled plant. (ii) Free-trial mutation: with q replaced by any unit vector orthogonal to the true low eigenspace, a exceeds the second level and C acquires a negative direction — the floor is FALSE for a free trial binder; the head must hard-code sourceCCMComplexRow (it does). (iii) Killed-schedule mutation: inserting m_k = 2^{(k+1)^2}, N_k = k+1 must be rejected inside the lemma by the explicit hguard hypothesis, not by ambient convention — the guard is a binder, so the mutation fails to elaborate against hguard. (iv) Prolate re-entry: any proof routing the modulus through a prolate operator-norm comparison re-collides with the scale wall above; the provenance table pins prolate comparison as UNAVAILABLE_AT_THESE_SCALES, so such a draft fails provenance review even if it elaborates.

Boundary: architecture/judge output only. G1 OPEN, G3 OPEN, Route B CHALLENGER_NOT_RH, BUS_010 VOID, no promotion, no RH claim. The wall now has its true name: one arithmetic definiteness estimate for the divided-difference form of β — the first theorem of this project that no amount of plumbing can replace.
