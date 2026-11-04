# Pre-run predictions — corner versus whole matrix

DIAGNOSTIC_NEVER_A_PROOF. Route B: CHALLENGER / NOT_RH. Separate diagnostic lane; no D0 or route-state change.

## Owner predictions (verbatim)

D1: m_matrix < m_corner for every (a, γ) on the grid. P = 0.80

D2: m_corner grows with γ, while m_matrix stays essentially flat once T_m > γ. P = 0.60

D3: the negative eigenvector peaks at frequency ω ≈ γ (within 2π/L). P = 0.75

## Fixed experiment contract

- Literal even physical L2 basis, j=0,...,m (dimension m+1), L=log m, d0=1, dj=sqrt(2), omega_j=2pi*j/L. Unit eigenvectors use this basis.
- Admissibility follows HIGHER_MOMENTS §1 exactly: T_m=(1+(1+log L)/(4L))*2pi*m/L. Require strict T_m>γ. Also record Ω_m=2pi*m/L and whether γ exceeds Ω_m; do not silently replace the cutoff.
- a in {0.05,0.1,1/3}; γ in {14,50,200,800}. a=1/3 is evaluated as an exact rational at high precision.
- Q=4 Re(c c^T), c_j=2*d_j*z*sin(zL/2)/(sqrt(L)*(z²−omega_j²)), z=γ+ia, multiplicity one. Gate at m=80: direct coefficient construction versus independent physical-kernel quadrature must agree entrywise within1e-12. Apparent resonances use their removable values.
- First eligible m is found among integers m>=16. Corner is scanned at every eligible integer through3000. Matrix starts at that first eligible integer and scans consecutive integers until a trigger, so a claimed first threshold has no skipped predecessors. After first detection, use additional validation checkpoints through3000, or an explicitly documented feasible cap.
- Corner trigger: strict negative (A+Q)[0,0]. Matrix trigger: lambda_min(A+Q)<−1e-6. Confirm each first matrix trigger using a freshly assembled source and a Rayleigh witness at >=50 decimal digits; distinguish a witness from a complete high-precision ordering computation. Recheck predecessor when the threshold is later than admissibility.
- At every matrix-grid cell, unplanted lambda_min(A)>=−1e-12 and a=0 must not trigger either detector. Tiny floating negative values are unresolved noise, never planted detections. Any failed control stops scoring until resolved.
- The pinned MPFR source is retained unchanged. A zeta-only vectorized implementation is allowed for scale, only after comparison against that source at m=80 and selected larger cells; all prime powers, full archimedean terms, endpoint tails and pole are retained.
- Report a censored threshold as >M, never as an observed crossing. When matrix is detected before the exhaustive corner scan cap and corner is not, D1 is supported only with that censoring made explicit. Both-censored cases are inconclusive.
- D2 is reported in two parts: ordered corner thresholds/censor bounds against γ, and raw matrix thresholds together with admission-adjusted delay m_matrix−m_admit. Operational conditional flatness means delay<=max(2,0.05*m_admit); this does not turn raw γ-dependent admissibility into a claim of constant raw m_matrix.
- D3 is literal: peak coefficient energy |v_j|² at the first detected matrix cell must satisfy |omega_peak−γ|<=2pi/L. Record the peak, centroid, top modes and boundary-of-band flags. An unavailable frequency is a failure of the stated prediction, not an excuse to widen its tolerance.
- Budget: benchmark actual source/eigensolver work after this file is committed. Escalate precision or lower the documented cap when required; no numerical stabilization occupies a cofinal quantifier. Preserve failures and actual tested cells. No RH claim.

## Source pins

- 2ad7342c: 2ad7342c2d0b236f627aa23ccc955e2190ffcade
- c8ef1314: c8ef1314c1fbc9e8292f3bc92d18d6fc2716eaa0
- 5e61a39d: 5e61a39dc564fe76487146823f0b5d711014f981
- Matrix builder Git blob prefix:27bbaab (verify full blob/SHA256 before execution).

This file is committed before any numerical experiment in this packet. Read-only source inspection and experiment design precede it; no matrix, gate, detector or control has been run.

## Addendum B+ preregistration (before any B+ numerical run)

Owner predictions (verbatim):

K1: C*(m) ≤ 16 for zeta at every m (implied by Γ envelope if A ⪰ 0). P = 0.97

K2: for the planted quartet with a = 1/3, C*(m) grows roughly like m^{1/3}. P = 0.70

K3: at u = 0.9 the corner never fires, while the p⊥ detector does fire. P = 0.85

K4: for DH the p⊥ core breaks (C*(m) clearly growing) at some m ≤ 3000. P = 0.60

Source: e586ebbadf0729f37f70d4fea99d780b23f7932f, PROSHKA_VERDICT_TWO_CORES_2026-11-04.md, blob4663cd8ef05f3a54c48def00824442d640e0b4eb, §2/§4.1/§9. No theorem is imported as a proved arithmetic supplier.

Conventions fixed before B+ runs:

- W=I+X, S=W^{-1/2}. For B+1 use the stated generalized quotient on physical z⊥p. In normalized coordinates y=W^{1/2}z this means y⊥S p, so compute (S B S)|_(S p)⊥. Never project onto p and then silently treat the Euclidean mass as W.
- The planted physical A+Q is H+pp*−B_eff with B_eff=B−Q. Report C* of B_eff (K2) and explicitly distinguish the unchanged original-prime B, whose C* is identical to unplanted zeta. H/p remain unchanged by this added quartet.
- B+2 primary is the physical pole-null generalized minimum of A(0.9)+Q relative to W, therefore normalized constraint S p. Also report the literal as-written (S(A(0.9)+Q)S)|_p⊥ as a separate convention. Do not merge their values or call the latter exactly pole-null in physical coordinates.
- DH uses its own signed Dirichlet coefficients, conductor5 odd gamma, and NO zeta pole. The source-native p_D=0, so p_D⊥ is the full carrier, as §9 states. Do not insert the zeta pole into DH.
- B+1 core grid: m in {16,32,50,51,54,64,80,128,208,256,512,750,1000,1500,2000,3000}, plus observed main-task first thresholds. All a in {.05,.1,1/3}, gamma14/50 plants; original zeta and DH. Scope K1 support only to actual tested cells, never every integer outside that grid or a cofinal quantifier.
- B+2 exhaustive corner scans use every integer16..3000 with the same admissibility rule, u=9/10 exact at high precision, unplanted and all6 plants. Test Sobolev/pole-null detectors first at admitted integer and then consecutively until trigger, or explicitly censor at a measured feasible bound; add common checkpoints to3000. Unplanted u=.9 is a changed form and is not required to be positive; record its behavior separately instead of mislabelling it an original-zeta control failure.
- B+3 DH main detectors: scalar corner every integer16..3000; raw even matrix consecutively from16 until first lambda<−1e−6 (or documented cap), then common checkpoints. C* from B+1. Confirm negative witnesses at >=50dps with DH's own source.
- K2 operational power check uses RAW positive C*_eff, no posthoc baseline subtraction: log-log fit on tested m>=512, with slope in [.20,.47] and a positive growth ratio, scored separately for gamma14 and50. Auxiliary C*_eff−C*_zeta may be shown but cannot replace this score. Nonpositive fitted inputs or dominance not reached are reported explicitly.
- K4 operational 'clearly growing' means a factor>=2 from m512 to3000 AND a positive log-log tail slope>=.1; any observed C*_DH>16 is separately flagged. If reference/tail values are nonpositive, no shifted-log fit or synthetic ratio is allowed. A negative result is a finite-budget failure of this prediction, not a cofinal theorem.
- No RH claim, route promotion, source clipping, or reinterpretation of the original D predictions. All B+ results join the same final results commit; this append-only preregistration is committed first.

## Addendum B++ address preregistration (before address calculations)

AD1: ≥ 90% of DH events sit within 1 grid step of an off-line zero. P = 0.80

AD2: events are NOT explained by on-line zeros better than by off-line ones. P = 0.85

AD3: larger β ⇒ earlier first detection (rank correlation of β vs first m < 0). P = 0.65

Fixed address-test contract:

- Use the saved dense DH screen at rh_clean@2820569c for all integer m=2..2000. Reconstruct only row0 and diagonal entries with its original selected-entry source, not new eigenproblems. An event is a unique (m,j), j=1..m, with Ajj<0 OR det(A[{0,j},{0,j}])<0; retain both flags separately. Record the constant diagonal too; flag any A00<0 separately. Do not double-count overlap.
- Reproduce saved negative diagonal and determinant counts at every m before scoring. Strict signs remain the original screen's numerical signs; inherited selected MP confirmations are provenance, not interval certification for every event. Preserve margins.
- Zero input is the pinned numerical census blob35396541cbc976d0dc8a1c76bf45802c8602bb84 through height900. Distance is abs(omega-gamma)/(2pi/log m). beta denotes sigma_right; also report displacement beta-.5. Compare to nearest off-line pair by height and to nearest critical-line zero. Record their identities and distances.
- Do not silently claim census completeness above900. Score the owner-requested all-events census statistic and report a separate omega<=900 subgroup; flag upper-edge events where a missing zero above900 could change the nearest neighbor. This numerical census is not independently certified here.
- AD1 uses the fraction of all unique events with off-line distance<=1. AD2 is operationally supported only if off-line one-step hit rate>=on-line hit rate AND median off-line distance<=median on-line distance; give both constituent metrics and paired win fraction rather than retuning the criterion. Report both tests again within the census range.
- Null control: fixed NumPy PCG64 seed20261104;1000 independent uniform frequencies on [0,Omega_m] per distinct event m, reweighted by that m's event count. Also compute exactly the20 smallest original-zeta physical diagonals (including j=0), at every event m; present equal-m and event-count-weighted statistics. No zeta zeros are used as the null target; both controls use the same DH zero census.
- For every off-line pair below900, first detection is the earliest saved integer m at which ANY event mode is within one frequency step of its height (not necessarily that pair's nearest-neighbor assignment). Distinguish diagonal/minor firsts, observation/censoring, and record q=2pi*m/log m. Plot observed first m against beta and gamma. AD3 primary Spearman rank correlation uses observed pairs only, with censored pairs listed separately; also report sensitivity assigning censored firsts2001 and a height-adjusted partial-rank diagnostic if defined. A negative correlation is a finite observation, not a detection theorem.
- Existing main/B+ review is historical at its bound hashes. This append-only preregistration precedes address calculations and does not alter previous predictions/scores. Address results join the packet; no RH/D0/route-state change.
