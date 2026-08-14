# Goal 058 G1 cofinal complement floor — Mythos verdict

Date: `2026-08-14`

Transport: same living Goal 058 Mythos chat; completed naturally; final
browser-visible response extracted from the response article.

Captured response body: `12173` UTF-8 bytes.

Captured response body SHA-256:
`c992df19b4002fd594ad15d8e1aebfaae0920dc8926bfef5df6590fdbc5c0655`

Evidence boundary: external architecture audit. It is not a Lean proof, a
positive-floor supplier, G1/G3 closure, Route B promotion, or RH claim.

## Verbatim visible response

All six files read at HEAD 7266ad45. Audit follows, dossier form, context before conclusions.

ACCESS REPORT

I/O ledger — G1 required outputs fixed: even ground ξ0_j, gap envelope D(j), Rayleigh-excess A(j), odd-mass W(j), with W + A/D → 0 on one precommitted cofinal schedule; killed shortcuts (commutator, beta-only) recorded; both reviewers at the same boundary.
Gram-checker closeout — checker proved, ask.sh preflight ×3 found no pre-existing literal supplier; next address Goal058.G1.CofinalComplementFloor; axiom surface clean.
Odd-tail coercivity — sourceWeilOddTailAmbientCoercive_explicit i: floor 1/2 of the source Weil form on the closed span of odd graph modes past the explicit cutoff, for every i : PairIndex (schedule-generic supplier).
m=13 Schur matrix receiver — sourceWeilOddTargetFloorSchurPositive13_iff_ccm_corrected_energy: an iff (equivalence, no sign) reducing odd target-floor positivity to nonnegativity of q* · ccmWeilMatFinite 13 R₁₃ · q − targetFloor·⟨q,q⟩ − ⟨corr q, q⟩, where R₁₃ = sourceWeilOddTailCutoff and corr is the actual infinite-tail inverse-weighted correction (not a truncation).
Complement-floor checker — predicate sourceCCMComplexTrialComplementFloor S i β on (sourceCCMFiniteMatrix i, sourceCCMComplexRow S i, a = sourceCCMFiniteRayleigh S i); Gram soundness; Fin 3 collapse plant with second ground vector Y rejecting every β > 0.
Spectral receiver — floor ⇒ unit bottom eigenpair, (ε+β)-gap on ξ0⊥, and projective defect ≤ ‖r‖²/β². Consumes the floor; supplies nothing.

ARCHITECT — the structural fact the six files jointly force

Given the on-disk reflection symmetry ([K, J] = 0, J the parity involution) and assuming the source row q is exactly even (this evenness is used below and must be separately verified on disk — if the row carries odd contamination, every statement acquires a W(j) correction term), the complement q⊥ splits J-invariantly as (even ∩ q⊥) ⊕ odd, and B = Q(K − aI)Q is parity-block-diagonal. Hence the exact factorization:

complement floor β on q⊥ = min( even-complement floor, minSpec(T_odd) − a )

So the wall is not one object but two, and the six files populate them asymmetrically:

Odd leg (parity exclusion, quantitative): files 3+4 live here. Supplier (file 3) is real and i-generic; receiver (file 4) is an unsigned identity at m=13.
Even leg (the true spectral gap D(j)): nothing on disk. No even-tail coercivity twin, no even-head certificate, no receiver beyond the generic one.

One bonus corollary of the receiver in file 6, worth recording: once the floor holds and defect = 1 − |⟨ξ0, q⟩|² ≤ ‖r‖²/β² < 1, simplicity forces ξ0 to have definite parity, and an odd ξ0 would be orthogonal to the even q (defect = 1, contradiction). So evenness of the ground is a downstream corollary of floor + tracking + evenness of the row — parity exclusion need not be certified as an independent theorem if the floor route closes. But the floor's own truth contains the odd lower bound (odd ⊂ q⊥), so the odd leg cannot be skipped either way.

LAWYER — answer to the hostile specialization question: NO.

The odd-tail 1/2 plus the m=13 corrected-head receiver do not specialize to sourceCCMComplexTrialComplementFloor on the full complex trial line or any cofinal selectedPairIndex schedule. Exact object mismatch, six points:

Carrier. File 3 floors a closed subspace of the infinite-dimensional H_m (odd modes past the cutoff). The target floors the rank-one complement of a trial line inside the finite ℂ^(CCMModeFinite i.N). The odd lane is trial-blind — the row q never appears in files 3–4 at all.
Operator. Odd lane: the source Weil sesquilinear form / ccmWeilMatFinite 13 R₁₃ (head sized by the cutoff). Target: sourceCCMFiniteMatrix i (sized by i.N along the schedule). Even granting these instantiate the same family, the instantiation parameters (m, dimension) differ; identity is not established by the six files.
Shift. Odd lane subtracts the fixed scalar sourceWeilOddTargetFloor. Target subtracts the S-dependent Rayleigh value sourceCCMFiniteRayleigh S i. These are not interchangeable, and the exchange rate is exact and unforgiving: B(a) = B(a*) − (a − a*)Q, so every unit of shift discrepancy eats a full unit of β. Even a fully signed odd target-floor supplies the odd leg only under the compatibility premise targetFloor ≥ a_j + β_j eventually — an A-type Rayleigh upper bound nowhere on disk.
Sector. The odd lane says nothing — zero — about the even directions of q⊥, which is where the ledger's D(j) lives and where the trial line's competitor eigenvector would sit.
Schedule. File 4 is pinned to m = 13 by name (Pullback13, Synthesis13); the ∀N quantifier ranges only over the auxiliary coordinate, which the file itself proves irrelevant on finite odd sums. If the precommitted schedule has m_j → ∞ (the ledger's λ = √m language implies exactly that), m=13 is a single fiber, categorically not cofinal. Nuance in your favor: the supplier (file 3) is already ∀i — only the receiver is pinned.
Modality. File 4 is an iff — it exposes the missing sign, its own docstring says so. File 3 signs the tail only. Neither, nor their composition, produces β > 0 on q⊥.

CRITIC — parity vs gap, cleanly separated; falsifiers

Simple + reflection-commuting ⇒ even ground is FALSE, and F1 below is the two-line witness. What commuting + simplicity gives is definite parity, sign undecided. Parity exclusion = minSpec(T_odd) > minSpec(T_even) — the odd lane's business. Spectral gap = intra-even complement floor — absent. Neither implies the other; the collapse plant already kernel-checks that structure implies neither.

F1 (parity-sign flip). Fin 2, J = swap, K = [[0,1],[1,0]]. [K,J] = 0; eigenpairs: even (1,1) ↦ +1, odd (1,−1) ↦ −1. Ground is odd and simple. Any claim "commuting + simple ⇒ even ground" must reject this or is broken. Bonus: with q = even unit vector, a = Rayleigh(q) = 1, the complement (odd line) has shifted energy −2 — the floor fails exactly because parity exclusion fails, confirming the factorization.

F2 (tail floor without complement floor). Extend the on-disk Fin 3 collapse plant: K₃ ⊕ I_n (coercive "tail" block with floor 1 ≥ 1/2), q = q₃ ⊕ 0, a = 0. Tail coercivity holds; yet Y ⊕ 0 remains a second ground direction in q⊥ with zero shifted energy — every β > 0 rejected. Kills "odd-tail 1/2 ⇒ complement floor" permanently.

F3 (shift mutation between lanes). Fin 2, K = diag(0,1), q = e₀, Rayleigh a = 0: complement floor β = 1 holds. Mutate the shift to a fixed "target-floor" scalar 1: shifted energy on e₁ becomes 0 — every positive floor dies. Kills silent substitution of sourceWeilOddTargetFloor for sourceCCMFiniteRayleigh (mismatch 3). Auxiliary reject-rule: any "13" appearing inside a schedule-quantified claim is an immediate schedule-leak reject.

SYNTHESIZER — overlooked supplier verdict and the smallest noncircular carrier

Overlooked supplier: NONE for the complement floor, in all six files — consistent with the recorded triple ask.sh miss. What the search did find is an unledgered partial reduction: files 3+4 jointly reduce the m=13 odd target-floor sign to exactly two objects: (a) a quadratic-form upper bound on oddTailInverseWeightedCorrection — and here the tail coercivity does real work: tail ≥ 1/2 in form sense ⇒ T_tail⁻¹ ≤ 2 ⇒ ⟨corr q, q⟩ ≤ 2‖Cq‖² with C the head-tail coupling (standard Schur-complement bound (correction of a coercive block dominated by coupling² over the floor)); (b) one finite corrected-energy inequality on ccmWeilMatFinite 13 R₁₃. Not a G1 closure, but a genuine narrowing of the odd leg to receiver-grade work plus one finite cell.

MINIMAL_NEW_CARRIER — sector-split, noncircular by construction:

C1 (odd leg, uniform). m-generic version of the file-4 receiver + the correction bound (a) + a uniform corrected-head lower bound for all schedule m ≥ m₀ (the head size R(m) grows with m, so per-cell certificates don't suffice — this is the ledger's "new uniform mathematics", now localized to one inequality family).
C2 (even leg, the real wall). Even-tail coercivity twin of file 3 — blocked today by the missing even low-band lemma (…FinsuppShift_sq_le_lowBand is odd-specific; the archimedean multiplier bound is parity-agnostic) — then a uniform even-head complement floor at an explicit fixed shift a* with fixed β* > 0.
C3 (link). Rayleigh-proximity transport |a_j − a*| ≤ β*/2 eventually (an A-type bound; legal one-way import from the G3 Lemma 7.2 side — G3→G1 dependency, no feedback loop) + the exact identity B(a_j) = B(a*) − (a_j − a*)Q, yielding β_j ≥ β*/2 at the literal Rayleigh shift. Then residual_j/β_j → 0 ⟸ residual_j → 0 with β bounded below — G1's quantitative demand collapses onto G3's rate plus one fixed positive constant. That is the noncircular separation: the floor comes from tail coercivity + finite head arithmetic, independent of where the ground actually sits; the trial's proximity is consumed, never assumed, in producing the floor.

Smallest single theorem to commit first: the correction bound (a) — pure receiver-side functional analysis, no new analytic import, converts the m=13 iff into "odd sign ⟸ one finite matrix inequality".

Aristotle. Proshka's NO_SOUND_ARISTOTLE_TASK_AT_THIS_BOUNDARY stands and this audit does not overturn it: the first leaves (correction bound, even low-band twin) manipulate project-internal infinite-dimensional objects — not bounded self-contained cells. First future eligible candidate: an exact-rational Gram factorization of one corrected even-head block at fixed j, with pre-supplied rational entries — that is an exact certificate, not numerics, and matches the checker's design intent. Not yet.

PRIMARY_ROUTE: SECTOR_SPLIT_COMPLEMENT_FLOOR (even-complement floor at fixed shift a* + uniform odd corrected-head bound + Rayleigh-proximity transport; odd tail already supplied by file 3)
OVERLOOKED_SUPPLIER: NONE_FOR_COMPLEMENT_FLOOR; partial unledgered reduction found — files 3+4 reduce m=13 parity exclusion to one tail-correction quadratic bound plus one finite ccmWeilMatFinite 13 R₁₃ corrected-energy cell
OBJECT_MISMATCH: (1) carrier: closed odd-tail subspace of H_m vs rank-one trial-line complement in ℂ^(CCMModeFinite i.N), odd lane trial-blind; (2) operator: ccmWeilMatFinite 13 R₁₃ (cutoff-sized) vs sourceCCMFiniteMatrix i (N-sized), instantiation parameters differ; (3) shift: fixed sourceWeilOddTargetFloor vs S-dependent sourceCCMFiniteRayleigh S i, exchange rate 1:1 against β; (4) sector: even directions of q⊥ entirely unserved; (5) schedule: m=13 single fiber vs cofinal m_j → ∞ (supplier i-generic, receiver pinned); (6) modality: iff without sign + tail-only sign ≠ complement floor
MINIMAL_NEW_CARRIER: C1 uniform odd corrected-head lower bound (all schedule m ≥ m₀) via m-generic receiver + Schur correction bound; C2 even-tail coercivity twin (needs even low-band lemma) + uniform even-head complement floor at fixed shift a* with fixed β* > 0; C3 Rayleigh-proximity transport |a_j − a*| ≤ β*/2 with exact shift identity, giving β_j ≥ β*/2 and residual_j/β_j → 0 from residual_j → 0 alone
EXACT_NEXT_LEAN_HEAD: NOT_READY — the oddTailInverseWeightedCorrection / InverseWeightedData definition files were not in this read set; queued in order: (1) sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le (correction ≤ 2·coupling² from tail floor 1/2), (2) sourceWeilEvenTailAmbientCoercive_explicit (even twin), (3) even-head Gram-certificate schedule family
ARISTOTLE_BOUNDARY: NOT_AUTHORIZED (unchanged; first future-eligible candidate: exact-rational Gram factorization of one corrected even-head cell, after the correction and tail bounds exist locally)
G1_STATUS: OPEN
G3_STATUS: OPEN (unchanged by this audit)
STOP_CODE: ODD_TAIL_AND_M13_RECEIVER_DO_NOT_SPECIALIZE_TO_COMPLEMENT_FLOOR_SECTOR_SHIFT_SCHEDULE_MISMATCH_EVEN_COMPLEMENT_SUPPLIER_MISSING
