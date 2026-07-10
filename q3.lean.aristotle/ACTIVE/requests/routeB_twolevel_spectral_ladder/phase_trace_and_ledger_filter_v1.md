# PhaseTraceAndLedgerFilter_v1

## Headlines

1. Phase constant artifact confirmed? NO
2. Ledger envelope consistent? YES
3. GUE modulation status: `GUE_MODULATION_ABSENT`
4. F4/J=2000: `NOT_RUN`
5. Verdict code: `PHASE_STRUCTURE_DEEPER`, `LEDGER_ENVELOPE_CONSISTENT`, `GUE_MODULATION_ABSENT`

Diagnostic only: not RH, no Phase 2, no heavy compute, no QW formula changes, no packet-definition changes, no Q3 mainline changes.

## F1 Phase Trace

- normalization line: `zero_sum_profile_v2.py:143` `return mp.sqrt(sum(abs(z) ** 2 for z in coeffs))`.
- K return line: `zero_sum_profile_v2.py:205` `return (lam ** (1j * t)) * total / mp.sqrt(L)`.
- norm type: `sqrt(sum |c_n|^2)`; complex norm arg `0.0`.
- global phase of c_n set: `not persisted; inferred only from dumped K_j phases`.
- all 500 phase phi0 `-0.0122693665827`, tan(phi0) `-0.0122699822858`.
- all 500 post-fix circular MAD `0.035980699028`, median `|Im/Re|` `0.0479967748999`.
- original j<=100 dust-range phi0 `-0.29824847764`, tan(phi0) `-0.307418163251`.
- original j<=100 post-fix circular MAD `0.633535768114`, median `|Im/Re|` `1.03049658955`.
- registered tan(phi0)=0.63+-0.05 pass: `False`.
- code: `PHASE_STRUCTURE_DEEPER`.

## F2 Ledger Filter

- J>=300 C mean `7.91499181721e-29`.
- C range `[min,max] = [7.51673171429e-29, 8.18818000937e-29]`.
- max relative deviation from mean `0.050317184`; stable +-15 pass `True`.
- C registered range pass `True`.
- contrast C/(1.784*k_edge) range `[1.16433626256, 1.26834311395]`; registered contrast pass `False`.
- code: `LEDGER_ENVELOPE_CONSISTENT`.

| J | R_J/a1 | C | C/(1.784*k_edge) |
| ---: | ---: | ---: | ---: |
| 100 | `0.688067564084` | `7.70424398864e-29` | `1.19338177715` |
| 150 | `0.578324787821` | `7.94836666717e-29` | `1.23119620208` |
| 200 | `0.493645598846` | `8.01261688249e-29` | `1.24114851359` |
| 250 | `0.419144088556` | `7.91509828428e-29` | `1.22604295383` |
| 300 | `0.337116961965` | `7.51673171429e-29` | `1.16433626256` |
| 350 | `0.319214528442` | `7.68705895542e-29` | `1.19071982804` |
| 400 | `0.317874907913` | `8.01052419428e-29` | `1.24082435772` |
| 450 | `0.307414012823` | `8.18818000937e-29` | `1.26834311395` |
| 500 | `0.285868925246` | `8.17246421272e-29` | `1.26590874851` |

## F3 GUE Probe

- normalized spacing: `delta_j=(gamma_{j+1}-gamma_j)*log(gamma_j/(2pi))/(2pi); backward difference at j=500`.
- Spearman j=50..500: `0.013926835809`.
- Spearman post-peak: `0.0157876671271`.
- code: `GUE_MODULATION_ABSENT`.

## F4

- status: `NOT_RUN`.
- reason: F1 did not confirm the registered constant-phase artifact on the original dust range.

## State Policy

- `PHASE_CONSTANT_ARTIFACT_CONFIRMED` not recorded because F1 did not repair the original j<=100 dust range or registered tan(phi0).
- Ledger envelope C is stable near `8e-29`, but final requested DISPLACED_PROFILE/phase promotion is not applied.
