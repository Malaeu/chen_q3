# Route B TwoLevelSpectralLadder Static Schur Effective Packet Audit

1. S0 stable in N and reproduces mu_i grid-wide? [UNKNOWN/BLOCKED; completed cells=2/9; partial max rel err=3.36375364254436835246144939414461875382951968271821819971724767360393340131955518847533981E-8; saved mu max N90->N120 drift=0.20757277251360681996837131141285103325331835984605300344938037681100789848363765]
2. Dressed vectors match true xi_i? [UNKNOWN/BLOCKED; A3 not run because full N=120 C-solve blocked before key-case deflation stage]
3. xi_1 aligned with k1 AND even? [|<xi1,k1>|=0.99999999807157316138625507089641000698971005399497190376890762078042451824120685; parity=1.0; YES from prior FeshbachGate key case]

Status: diagnostic only. Not a proof of RH. Not a Route B kill.
Phase 2 was not run. The full ladder CLI was not rerun. QW formulas and packet definitions were not changed.

## Verdict

- Verdict code: `STATIC_SCHUR_AUDIT_BLOCKED`
- Blocked object: `Persisted request-local high-precision Schur block cache (T/G/B/C or C eig/deflation data) for N=120 grid, or a dedicated efficient deflated C-solver gate before full StaticSchurEffectivePacketAudit.`
- Partial JSON: `out/static_schur_blocked_partial.json`
- Progress JSON: `out/static_schur_progress.json`

## T0 Data Integrity

- `routeb_ladder_pilot.py` was imported read-only; formulas and packet definitions were not edited.
- Existing saved grid JSON contains scalar outputs but not full matrices/vectors (`T`, `G`, `B`, `C`, `Mperp`) needed to complete this gate without recomputation.
- Recompute used the same `build_tau_matrix`, `make_packets`, `g04`, `g26`, `g048perp`, and `dps_for_lam` code paths.
- Working dps for the completed partial cells was 186 at `lambda_sq=12`.

## Partial A1 Evidence

| lambda_sq | N | theta1 | theta2 | theta3 | max rel err theta vs saved mu | elapsed_s |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | 60 | `9.1907269287163916861664575566288597101639121330300310401762863324321857516137426361202783e-54` | `7.11259687318362161132451253406747880862414618022394621827724255995779582220358315752282953e-50` | `2.87245756570411842376065059240025892246978167816745304065008980626270159871818495222801092e-46` | `1.85085883584117871245128532417631253821377526569096846190977338821220973462270234211135128E-8` | `70.24821996688843` |
| 12 | 90 | `5.88065555715749651088321706188243576317594768654971182647620012378781123475267642470357489e-54` | `4.45629850275589669208760109942600733240198328722726171179280429021102696832289983396165996e-50` | `1.86994361013080106065419935474085560432380983379151317485481670343879088960034235130600728e-46` | `3.36375364254436835246144939414461875382951968271821819971724767360393340131955518847533981E-8` | `219.6178960800171` |

Prior completed FeshbachGate key case `lambda_sq=14,N=120`:

- Static S0 max rel err vs mu: `2.7829597914348580034377361994040392356119546652559590454462478146954549738952952E-8`.
- Static S0 eigenvalues: `['1.4598129516305681180148416570676839963751586021555448492816815824395750774529992e-64', '1.6680022749699100017824623264342277287224255156933852301196875928321584265277953e-60', '9.3843339084565853023912909554223973850358920026137583286907745247578232475431967e-57']`.

Saved raw finite-N mu drift from old grid JSON, included only as diagnostic context:

| lambda_sq | drift mu1 N90->N120 | drift mu2 N90->N120 | drift mu3 N90->N120 |
|---:|---:|---:|---:|
| 12 | `0.12900531515922219734197021311061671014955508091119751546904550505524977579358550` | `0.093683869122441615018664383021589205983330038194968542206573082668143896004033138` | `0.094511993687825853566705745250462410976281565055870415855773752088245415640125388` |
| 13 | `0.16860556276686476127516953064878857110720166697024595911304451735272102062959020` | `0.13881338973705078174320190246661402415670450002954146358339475408349745266560019` | `0.15916042908410565838495465504454995740560912878425753315795970698649207548671937` |
| 14 | `0.20757277251360681996837131141285103325331835984605300344938037681100789848363765` | `0.16689944399527350775030189010533801426582454886420937453246801945747929516017007` | `0.14512791468040696429731519924842797391947775886886304540372418807669542602812556` |

## Blocked Tasks

- `A1 full 9-point S0 grid`
- `A2 mandatory direct-vs-deflated C inversion robustness`
- `A3 static-S0 dressed vector vs truth recomputation`
- `A4 dynamic Schur S(mu1) deflated comparison`
- `A6 class fits from completed S0 grid`
- `A7 full identity ledger`

## Runtime Block

- The run completed `lambda_sq=12,N=60` and `lambda_sq=12,N=90` and then entered `mp.lu_solve(C,B)` for `lambda_sq=12,N=120`.
- This is the exact expensive object required by the gate: direct dense high-precision inversion of the complement block `C`.
- Continuing the same direct method across all `N=120` grid points plus mandatory A2 deflation would be an uncontrolled long run, so the audit stops fail-closed instead of manufacturing a pass/fail verdict.

## Judge Re-Arm Status

- Per-grid tau-entry and planted-violation checks were not completed because the audit stopped at the first large `C` solve.
- No theorem claim is made from fitted constants, zero-side matching, or saved raw drift.

## Boundary Note

BoundaryOperatorConstructionAudit was not run here. In this finite S1 matrix, the W02/pole contribution is already inside tau by the C1 pilot calibration; this audit makes no boundary speculation.

## Next Exact Gap Suggestion

Ask Proshka whether to authorize a small solver/cache gate first: persist request-local `G,B,C` or C-eigendecomposition/deflation data for `N=120`, then rerun StaticSchurEffectivePacketAudit from cached Schur blocks. The alternative is to accept this as `STATIC_SCHUR_AUDIT_BLOCKED` and route to BoundaryOperatorConstructionAudit / ProlateBranchBasisConstructionAudit.

