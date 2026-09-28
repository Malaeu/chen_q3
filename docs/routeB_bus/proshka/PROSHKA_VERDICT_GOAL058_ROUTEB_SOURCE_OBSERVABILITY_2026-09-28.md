# STATUS: TRY_GOAL058_SOURCE_OBSERVABILITY_DIAGNOSTIC_REPAIR

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_OBSERVABILITY_DIAGNOSTIC_REPAIR
OUTCOME: NO_MULTIROW_OBSERVER_CONSUMED_BY_SOURCE_TRANSFER
REQUEST_ID: REQ-2026-09-28-ROUTEB-SOURCE-OBSERVABILITY
REVIEW_SCOPE: GOAL058_G1_G3_ROUTE_B_WELL_POSEDNESS_AND_NEXT_DIAGNOSTIC_ONLY
REQUEST_BASIS: CURRENT_INLINE_REQUEST_AND_IDENTIFIED_SOURCE_TRANSFER
SOURCE_SNAPSHOT_READ: 78618b65152bc2b3b6aec4c6f1f460dd08617684
SOURCE_TRANSFER_GIT_BLOB: d564040c1828673835baeeed43978994ff68cd97
OBSERVABILITY_README_GIT_BLOB: d36020037440ad45c1a8a89a1f7350220fad0bc4
NEXT_MD_GIT_BLOB: 128d0436bc2ebe1aaa18f51c0af102bad9234413
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: ABSTRACT
VERIFIER: PAPER
GAMMA_STATUS: UNDEFINED_FOR_THE_STATED_ROUTE_OBSERVER
SINGLE_SCALAR_FUNCTIONAL_LOWER_GAIN_ZERO: EVERY_r_GE_2
PAIRED_SCALAR_FUNCTIONAL_LOWER_GAIN_ZERO: EVERY_r_GE_3
STRUCTURAL_ZERO_IS_ROUTE_KILL: false
G1_SIMPLICITY_OR_PARITY_CLOSED: false
G3_T7_RATE_CLOSED: false
FOUR_MIDPOINTS: USER_REPORTED_NOT_INDEPENDENTLY_CERTIFIED_HERE
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR_USED: UNIT_AUDIT
NUMERICAL_EXECUTION: false
LEAN_EXECUTION: false
REPOSITORY_WRITTEN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **NO. SOURCE_TRANSFER (T1)–(T4) does not consume a multirow observation map whose restriction to the lowest reflection-even eigenspaces must have a positive minimum gain.** The proposed \(\gamma_{m,r}\) is therefore **undefined as a diagnostic of that transfer**, until such a map and its consumer are actually specified. Substituting one or two scalar functionals makes a different, well-defined algebraic test, but it has unavoidable kernels. Those kernels are not a Route B failure.

## 1. What was checked and what the transfer actually uses

**[FINITE_CELL | PAPER — source inspection, not a numerical certificate]** I read the complete `docs/routeB_bus/fokas_k_sign_2026-09-25/SOURCE_TRANSFER.md`, the observability probe's README, and the relevant proposed diagnostic in `docs/Codex/NEXT.md`, all at the retrieved snapshot recorded above. This is a finding about that identified argument, not a claim that no other file anywhere could define an observer. The current request supplied no commit pin; the header identifies the snapshot actually examined.

The full source specifies the following uses:

| Source equation | Actual input or operation | What it does not supply |
|---|---|---|
| **T1** | Same full \(K_m\), its ground projector, row closeness, projection contraction, and a lower bound on \(\|b_m\|\). | No injectivity estimate on a low-eigenvalue subspace. |
| **T2** | The center identity \(T(q,0)=\sqrt{\log m}\,q_0\), a finite Bessel bound, and \(|\widehat z_{m,0}|>E_m\). | No stack of independent source observations. |
| **T3** | A conditional, matched selected-source center floor; the T1 leakage bound. | No new observation rows and no proof of that floor's premises. |
| **T4** | \(b_m=a_m/\kappa_m\); the reference row at the same two Robin-interval centers; full energy-variation and tail error bounds. | The two energy parameters are not two observation rows; the error bound is not a row. |

The center coordinate used in T2–T3 is a scalar normalization functional evaluated on the particular row. The projectors and transform are also linear objects. Their presence does **not** define the proposed multirow \(S_m\) or an observability lower bound on \(V_{m,r}\). fileciteturn49file0L2-L2

The proposed numerical step in `NEXT.md` asks for \(\gamma_{m,r}\) and compares it with eigenvalue splitting. The probe README explicitly records that the cited SOURCE_TRANSFER does not define that multirow \(S_m\), so neither \(S_m\) nor \(\gamma_{m,r}\) was computed. Its derivative Rayleigh probes are not a source-consumed observation map. fileciteturn51file0L2-L2 fileciteturn50file0L2-L2

## 2. The transfer is complete without such an observer

**[ABSTRACT | PAPER — applied to the stated source contract]** Represent the coefficient rows as columns in their original Hermitian Euclidean space \(\mathcal H_m\), with inner product \(x^*y\). Assume \(\|u_m\|=1\), \(P_0=u_mu_m^*\), and retain the source's common-scalar/phase convention in \(b_m=a_m/\kappa_m\). Put
\[
 d_m=b_m-\widehat z_m,
 \qquad \eta_m=E_m/Z_m<1,
 \qquad q_m=b_m/\|b_m\|.
\]
The original error bound and orthogonal projection give
\[
\begin{aligned}
\|b_m\|&\ge Z_m-E_m>0,\\
\|(I-P_0)b_m\|
&\le\|(I-P_0)\widehat z_m\|+\|d_m\|
\le Z_m\alpha_m+E_m.
\end{aligned}
\]
Consequently
\[
\boxed{\beta_m:=\|(I-P_0)q_m\|
\le\frac{\alpha_m+\eta_m}{1-\eta_m}.}
\tag{1}
\]
This is precisely T1. There is no inverse of \(K_m\), no eigenvalue-splitting denominator, and no minimum singular value of a source map. The same full \(K_m\) must determine \(P_0\) for both rows. Changing \(K_m\) would require an additional projector-comparison argument. fileciteturn49file0L2-L2

The overall phase of \(u_m\) does not affect \(P_0\), leakage, or overlap magnitudes. Normalizing \(a_m\) instead of \(b_m\) changes only a unit phase. However, the relative phase and scalar in the *unnormalized closeness bound* are source data; they cannot be altered independently while retaining the same \(E_m\).

## 3. Rank-nullity: why the proposed replacement test produces structural zeros

**[ABSTRACT | PAPER]** For this check only, form the scalar functional
\[
\ell_m(v)=\widehat z_m^*v:\mathcal H_m\longrightarrow\mathbb C,
\]
using the original Euclidean domain norm and complex absolute value in the codomain. This is a natural functional associated with the given row, **not an additional assertion that the transfer consumes a new observer**. Its normalized version is \(\widehat q_m^*v\).

On any \(r\)-dimensional complex subspace \(V\),
\[
\operatorname{rank}(\ell_m|_V)\le1,
\qquad
\dim\ker(\ell_m|_V)\ge r-1.
\]
Thus the unit-sphere infimum is exactly zero for every \(r\ge2\). The same statement holds over a real, source-compatible realization with real scalar functionals.

Even stacking the two specified rows gives only
\[
\mathcal O_m(v)=\begin{pmatrix}\widehat z_m^*v\\ b_m^*v\end{pmatrix}
:\mathcal H_m\longrightarrow\mathbb C^2,
\]
with the Euclidean codomain norm and rank at most two. Therefore:

| Dimension \(r\) | One scalar functional | Pair \((\widehat z_m^*,b_m^*)\) |
|---:|---|---|
| 1 | May vanish or be positive. | May vanish or be positive. |
| 2 | **Zero lower gain.** | May vanish; positivity needs independence after restriction. |
| 3 | **Zero lower gain.** | **Zero lower gain.** |
| 4 | **Zero lower gain.** | **Zero lower gain.** |

There is also a useful bound for the two-row test. Let \(c_m=(\widehat z_m+b_m)/2\). For any \(r\ge2\), choose a unit vector in \(V\cap c_m^\perp\). On it,
\[
\|\mathcal O_m v\|_2
=\frac{|(b_m-\widehat z_m)^*v|}{\sqrt2}
\le\frac{E_m}{\sqrt2}.
\]
Hence its minimum gain is at most \(E_m/\sqrt2\); with both rows divided by the **same** \(Z_m\), it is at most \(\eta_m/\sqrt2\). Successful source approximation can therefore make this artificial two-row map nearly rank one.

**Planted check.** In the abstract perfect-transfer case \(b_m=\widehat z_m=Z_mu_m\), one has \(\alpha_m=\eta_m=\beta_m=0\), while the one-row and duplicate two-row lower gains vanish on every \(r\ge2\) subspace containing the ground direction. This is not offered as a selected CCM witness; it proves that the proposed structural-zero criterion cannot distinguish perfect transfer from failure.

These conclusions are independent of eigenvalue splitting. A zero minimum gain is not necessarily a rank-zero map: it means the restriction is not injective. Arbitrary row scaling also changes a nonzero \(\gamma\), so comparing its numerical size with a spectral gap needs a proved, normalized consumer—not an observed similarity of decay.

## 4. Minimal well-posed diagnostic and the G1 boundary

**[ABSTRACT | PAPER]** The existing ground overlaps are
\[
\rho_m^{\rm ref}=|u_m^*\widehat q_m|,
\qquad
\rho_m^{\rm sel}=\frac{|u_m^*b_m|}{\|b_m\|}.
\]
They satisfy the exact phase-invariant identities
\[
\boxed{(\rho_m^{\rm ref})^2+\alpha_m^2=1,
\qquad (\rho_m^{\rm sel})^2+\beta_m^2=1.}
\tag{2}
\]
The source closeness gives the separate lower bound
\[
\boxed{\rho_m^{\rm sel}\ge
\frac{\max\{0,\sqrt{1-\alpha_m^2}-\eta_m\}}{1+\eta_m}.}
\tag{3}
\]
The minimum diagnostic is therefore **\(\alpha_m\), \(\eta_m\), and the same-ground overlap**, together with the transfer upper bound in (1). Record the actual selected overlap when the source row is available; otherwise report only its proved enclosure. Do not substitute a reference midpoint for a full selected row or assign it an unproved tail bound.

Two equivalent diagnostic representations are available without changing the source: **projection leakage** (one projected residual and the error ratio) and **ground overlap** (one scalar inner product after identifying the same ground state). The first tests the transfer budget; the second checks the ground identification and the identity (2). Neither is an inverse problem on the lowest four modes. For very small leakage, evaluating the projected residual avoids subtracting nearly equal numbers in \(1-\rho^2\).

**[ABSTRACT | PAPER — G1 limitation]** SOURCE_TRANSFER identifies \(P_0\) with the projector onto a **simple ground state**; it does not prove simplicity in T1–T4. Nonzero overlap with one chosen ground vector does not exclude a second orthogonal ground vector. A separate theorem
\[
\ker(K_m-\lambda_0I)\cap\ker(\widehat z_m^*)=\{0\}
\]
would imply simplicity by rank-nullity if proved on the **entire actual ground eigenspace**, without assuming simplicity first. That statement is not supplied by the transfer. Injectivity on the span of several distinct lowest eigenvectors is a different and unnecessarily stronger demand.

Likewise, a lowest reflection-even eigenvector is not automatically the full \(K_m\) ground state. The r=1 formula \(|\widehat q_m^*u_m|=\sqrt{1-\alpha_m^2}\) applies to the proposed \(V_{m,1}\) only after those ground objects are identified. If simplicity is independently known, reflection commutes with \(K_m\), the reference is even, and the overlap is nonzero, parity then follows; those antecedents must not be hidden in a numerical basis choice.

## 5. Four midpoint angles do not decide T7

**[FINITE_CELL | CONDITIONAL — user-reported numerical evidence, not an interval certificate here]** The supplied values are
\[
\begin{array}{c|cccc}
m&8&12&16&24\\\hline
\alpha_m&0.055342160605&0.059589624762&0.057575447710&0.053206801408.
\end{array}
\]
They concern four finite subthreshold reference midpoints. They neither prove nor refute
\[
\boxed{m^{H/2}\sqrt{\log m}\,\alpha_m\longrightarrow0
\quad\text{for every fixed }H\ge0}
\tag{T7}
\]
on the original admitted selected tail. Even exact finite values cannot decide that tail limit. No power law, plateau, or eventual decay rate is certified by this list. The separate observability README does not supply these four reference-row angles; it explicitly says that its own run did not construct that reference row. fileciteturn50file0L2-L2

**[COFINAL_FAMILY | CONDITIONAL]** For each fixed \(H\), the useful rate diagnostic is
\[
A_H(m)=m^{H/2}\sqrt{\log m}\,\alpha_m,
\qquad
D_H(m)=m^{H/2}\sqrt{\log m}\,
\frac{\alpha_m+\eta_m}{1-\eta_m}.
\tag{4}
\]
When \(\eta_m\le1/2\), the accepted T6 estimate gives
\[
D_H(m)\le A_H(m)+4m^{H/2}\sqrt{\log m}\,\eta_m.
\]
T5 pays the second term only under its matched source hypotheses and eventual thresholds. T3 additionally retains its matched center floor. Neither supplier is established by the four midpoint angles. Under those supplied conditions, proving T7 is sufficient for this vector-norm tracking route. fileciteturn49file0L2-L2

The **discriminator for T7** is a tail envelope for \(A_H\): a uniform upper envelope tending to zero proves the rate for that fixed \(H\); a positive lower bound along an unbounded admitted sequence, for even one fixed \(H\), refutes T7. A finite fit does neither. Failure of T7 would still not, by itself, refute locally uniform transform tracking, because the norm estimate can lose transform cancellations. SOURCE_TRANSFER explicitly preserves this distinction. fileciteturn49file0L2-L2

## 6. Closeout and dependency boundary

**[ABSTRACT | PAPER]** The prediction registered before the rank check is confirmed: one scalar observation cannot be injective on an r-dimensional space with r>=2. The paired-row check strengthens the diagnosis but is not counted as a prior prediction. The invalid inference is **structural zero => Route B death**, not any claim about the actual source's eventual overlap.

```yaml
DOWNSTREAM_CONSUMER: SOURCE_TRANSFER_T1_AND_CONDITIONAL_T3_T7
ACTUAL_CONSUMER_REQUIREMENT: SAME_GROUND_PROJECTOR_ROW_ERROR_CENTER_FLOOR_AND_TRACKING_RATE
ORIGINAL_REQUESTED_OBJECT: MULTIROW_S_m_WITH_LOW_SUBSPACE_MINIMUM_GAIN
ORIGINAL_OBJECT_IS: NOT_NECESSARY
KNOWN_WEAKER_INTERFACES:
  - T1_projection_contraction_plus_eta_less_than_one
  - same_ground_overlap_identity_and_selected_overlap_lower_bound
FAILURE_TYPE: NO_SOURCE
FAILURE_SCOPE: PROPOSED_MULTIROW_GAMMA_DIAGNOSTIC_ONLY
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: DISTINGUISH_PARTICULAR_ROW_TRACKING_FROM_SUBSPACE_INJECTIVITY
REOPEN_TRIGGER: SOURCE_DEFINED_OBSERVER_WITH_NORMALIZED_ROWS_AND_EXACT_TRANSFER_CONSUMER
T7_DISCRIMINATOR: SCALED_ALPHA_ON_THE_ORIGINAL_ADMITTED_TAIL
PREDICTION_SCALAR_RANK_OBSTRUCTION: CONFIRMED
NEXT_DECISIVE_TEST: SAME_SOURCE_ALPHA_ETA_GROUND_OVERLAP_CONSISTENCY_AND_RATE
FORBIDDEN_FUTURE_MOVE: CALL_A_STRUCTURAL_KERNEL_A_ROUTE_B_KILL
```

No G1/G3 closure, actual-source counterexample, repository-wide nonexistence result, or RH claim is made. No numerical or Lean execution was performed. This is a local PAPER well-posedness review, not an independently reviewed asymptotic source theorem.

## CODEX DIRECTIVE

**Replace the proposed gamma-versus-splitting death test with a same-source transfer diagnostic.** At each already authorized cell, retain the literal full \(K_m\), the source phase/scalar, the same ground projector, and the full error bound. Report \(\alpha_m\), \(\eta_m=E_m/Z_m\), \(\rho_m^{\rm ref}\), the selected overlap or its bound (3), and the transfer bound (1), distinguishing midpoint evidence from certified enclosures. Check (2) and record how the reflection-even eigenvector is identified with the full ground state; unresolved simplicity/parity remains a G1 premise, not a numerical conclusion. For G3, examine (4) only at the already required fixed strip heights and seek a source-derived tail envelope, with the T5 and center-floor hypotheses stated. Do not construct derivative or transform-adjoint rows, demand a positive scalar minimum gain for r>=2, or infer Route B death from a structural kernel, a failed sufficient bound, or four subthreshold points. Any revival of a multirow observer first requires its exact source definition and a proved place in the unchanged transfer. No route promotion or RH claim.
