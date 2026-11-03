# SOS audit, same-ambient stitch and conditioning

**DIAGNOSTIC_NEVER_A_PROOF. Route B = CHALLENGER / NOT_RH.**

LIT_QUICKCHECK was completed before B/C (`81b657e`); the concurrent independent literature replay (`8bc588d`) is preserved. A is published separately in `4fe4292`, source and independent audit in canon and mirror. This packet contains B/C, all checkpoints, precision receipts and fixed-cutoff sensitivity tables.

## A: first step log3 SOS

`FIRST_STEP_LOG3_SOS_PAPER_AUDIT_PASS`. Both embedded generator runs produce payload SHA256 `8b7fb1900093eb47e663ae352e0b52a2ad18043bd5d654e0f1a71aacec5ddcc0`. Bareiss exact divisions/positive minors and independent rational LDL reconstruction pass. Independent operator-error bounds are below 1.784e-18 and 1.741e-18, respectively, hence below 2^-40. The audited source concludes W[f] >= 2^-30 ||f||^2 for support length at most log3. It does not certify arbitrary long histories or their short new extensions. See the separate source/audit and first_step_log3_sos_audit_2026-11-03 packet.

## B: one step-profile ambient

All 36 baseline cells use one declared physical step space per m, with both Schur constructions inside that space. Rank and inertia agree at 80/100 digits; the designated 120-digit replay also agrees. The section energy uses fresh-coordinate norm one. When the old block is indefinite, its completion is stationary and the unrestricted old-coordinate infimum is minus infinity.

|world|m|dim J|section energy|angle(f,J), degrees|full norm(AQ)|requested ratio|
|---|---:|---:|---:|---:|---:|---:|
|dh|16|3|0.991911465|26.621605|2.47606243|1.0073065|
|dh|24|3|1.18493939|36.8887795|0.050152722|1.77788068|
|dh|32|5|1.28888824|37.8577982|0.0722338749|1.23858959|
|dh|40|5|1.56523666|30.7304636|0.0685022558|1.01390603|
|plant|16|19|0.635412301|19.2406217|3.67534028|0.210089572|
|plant|24|27|0.462308558|4.53781699|4.07792948|1.30291766|
|plant|32|33|0.616761342|5.53852713|4.3564711|1.21202711|
|plant|40|41|0.800997696|4.32192234|4.57039295|1.15882348|
|zeta|16|23|0.311313831|2.90976976|3.67621406|1.25358719|
|zeta|24|31|0.347445518|4.54720791|4.07822393|0.540036449|
|zeta|32|37|0.496873755|4.74337109|4.35679651|0.964400773|
|zeta|40|45|0.658377967|3.52868184|4.57039567|0.831212221|

Key obstruction: zeta m24,c=1/4 has N_A(2)=dim J=31, yet the eliminated D-2I block has only 28 negatives and the quiet Schur has 3. The identity is 31=28+3. Its full quiet residual is 4.07822, so the quiet-below-2 hypothesis fails. Count equality alone is insufficient. The original even-CCM residual theorem is not transferred to this step carrier.

The proposed universal synchronization of raw Schur signs is not validated: the planted baseline has negative full/old inertia and a positive raw section Schur. The corrected full-inertia comparison passes, while the requested analytic stitch remains unproved. This exception is not counted as a successful optimizer or hidden by dropping old negative directions.

Resolved DH control: the additional m40 carrier has 949 physical bins, used by both coordinate systems. The old block is numerically positive (minimum 8.72047e-6); the full source minimum is -0.00151499925 and the section Schur minimum is -0.06106305735. Primary/secondary quiet Schur minima at threshold zero are -0.078464955 and -0.008242089. Both coordinates therefore detect the negative line in the same ambient. Under kappa=1 it resides in the eliminated quiet block instead. This is numerical, not an outward-rounded sign certificate.

## C: literal even CCM, every integer m16..120

Coverage: **315/315 world/m cells**, 945 base-cutoff rows and 2659 total base/sensitivity rows. No count or residual is copied from the B step carrier. All m are outside the inherited theorem's L>=16 asymptotic regime.

|world|cutoff|cells|J=0|sigma resolved|lambda_r statuses|
|---|---|---:|---:|---:|---|
|zeta|c_quarter|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|zeta|c_half|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|zeta|kappa_one|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|dh|c_quarter|105|11|105|{'CACHED_MP_VALUE': 40, 'REPLAY_MP_FULL_SPECTRUM': 65}|
|dh|c_half|105|105|105|{'CACHED_MP_VALUE': 40, 'REPLAY_MP_FULL_SPECTRUM': 65}|
|dh|kappa_one|105|0|105|{'CACHED_MP_VALUE': 40, 'REPLAY_MP_FULL_SPECTRUM': 65}|
|plant|c_quarter|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|plant|c_half|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|plant|kappa_one|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|

|zeta m|cut|dim J|delta=norm(AQ)|N_A(2)-dim J|raw sigma_min|lambda_r|
|---:|---|---:|---:|---:|---:|---:|
|120|c_quarter|53|5.89647104e-06|11|9.93931577e-15|2.67205045e-17|
|120|c_half|42|5.53043399e-15 [floor]|22|7.218508e-32|1.67106259e-43|
|120|kappa_one|65|4.78629344|-1|1.02923513|2.23548244|
|24|c_quarter|14|0.0628324792|2|0.0119518534|0.0077809225|
|24|c_half|11|0.000142611248|5|6.05818815e-08|6.59130144e-09|
|24|kappa_one|17|2.95652943|-1|1.09828183|2.48845319|
|65|c_quarter|31|0.000444125537|7|8.61461831e-09|2.67195923e-10|
|65|c_half|25|2.68667012e-09|13|4.59139636e-18|2.05457521e-24|
|65|kappa_one|38|1.43728783|0|1.13339512|2.79696486|
|78|c_quarter|37|0.000399228883|8|3.10168808e-09|2.61902887e-10|
|78|c_half|29|6.38636773e-11 [floor]|16|2.26713271e-21|3.79302422e-29|
|78|kappa_one|44|1.15241152|1|0.928668139|1.96764161|

The kappa=1 m24 calibration repeats the known failure: delta=2.956529432>2 and N_A(2)-dim J=-1; the eliminated negative index is 16 rather than 17. Primary/secondary fixed c can make delta very small without saturating the count. At m120 the primary zeta defect is 11 despite delta about 5.9e-6; the secondary defect is 22. These finite observations do not contradict an asymptotic theorem.

The 111.0295355/111.8746592 pair enters together at m65 for c=1/4, together at m55 for c=1/2, and separately at m77/m78 for kappa=1. Every flagged cutoff is also evaluated at T plus/minus half the local mean spacing, with the same source matrix. The per-zero table flags normalized included gaps below 0.3 and separately retains the last-zero lookahead.

Conditioning is not a signed-source discriminator: at m120 primary raw sigma is 9.9393e-15 for zeta and 9.8497e-15 for the plant. In every matched cutoff/sensitivity row, the plant adds two real conditions, decreases dim J by two, decreases N_A(2) by one, and therefore increases N_A(2)-dim J by exactly one. The weak raw capacity barely changes while the full relative index sees the quartet.

Matched planted rows: 859; observed (defect increment, count increment, dimension increment): {'(1, -1, -2)': 859}. This is a finite diagnostic, not a proved index law.

The minimum included zero gap is also insufficient: the same gap can accompany raw singular values differing by many orders as the cutoff changes. At zeta m120 primary/secondary sigmas differ by about 1.38e17. Full weak-pair coordinates/masses, all gaps, interpolation rank and source normalization remain necessary. See CARD_CONDITIONING and CARD_PLANTED_RELATIVE_INDEX.

A delta marked [floor] lies below the saved floating diagnostic radius; it is not a resolved source residual at that displayed size. Every full CSV row retains delta_numeric_radius. In particular zeta m120 secondary delta about 5.53e-15 is at the floating floor, whereas its scalar lambda_r and raw sigma have separate MP replays.

Full guarded Schur status counts: {'NUMERIC_IDENTITY_PASS': 2659}. All eliminated indices are retained; unresolved sigma/eigenvalue cases retain explicit status and blank ratios. High-precision scalar eigenvalue replays do not turn float projectors or Schur blocks into interval calculations.

## Reproduction and analytic handoff

Read NORMALIZATION.md, B_stitch/RESULT.md and C_conditioning/METHOD.md first. CONDITIONING_DIGEST.csv gives all945 base rows directly with eight-significant-digit display rounding, explicit floating delta floors and diagnostic radii; this rounding is not an accuracy claim. Full scalar CSVs and raw matrix/checkpoint data are retained losslessly in the publication archive when large. Run `python3 unpack_data.py` to restore them, then the scripts in their own directories. PUBLICATION_ARCHIVE.json records every member and part hash; SHA256SUMS records the directly published packet. REPLAY_DEPENDENCIES.json pins existing repository dependencies. No external service credentials are needed for numerical replay.

The useful handoff is a complete common-threshold inertia ledger with estimates on D-CI, B and G, rather than a raw Schur sign or raw capacity. lambda_r of the sorted full spectrum is not automatically a lower bound on the arbitrary interpolation complement. No cofinal bound, RH proof, source-sign estimate or route-state change is claimed.
