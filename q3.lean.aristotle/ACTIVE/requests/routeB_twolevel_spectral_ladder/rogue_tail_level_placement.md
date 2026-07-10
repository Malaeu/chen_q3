# Route B TwoLevelSpectralLadder Rogue Tail Level Placement Audit

Status: diagnostic only. Not a proof of RH. Not a Route B kill.
Phase 2 was not run. The full ladder was not rerun. QW formulas and packet definitions were not changed.
No slopes are used in this audit.

## Headline

1. Is rogue below `lambda2_G`? [YES]
2. Is rogue below actual `mu2`? [NO]
3. Does rogue invalidate the two-level G4 lower bound? [YES for the current repaired 3-vector packet placement; not a Route B kill]
4. Verdict code: `ROGUE_BELOW_SECOND_LEVEL_CONFIRMED`

## Inputs Used

- `report.md`
- `nu_complement_audit.md`
- `rogue_tail_audit.md`
- `out/lambda_sq_14_N_120.json`
- `out/nu_complement_lambda_sq_14_N_120.json`
- `out/rogue_tail_lambda_sq_14_N_120.json`

The repaired high-precision `lambda_G` and `nu_tail` values are taken from the complement/rogue-tail audit JSON, not from the older float64 projected `lambda_G` values in the phase1 JSON. Actual `mu1`, `mu2`, and `mu3` are taken from the existing full-matrix N120 phase1 JSON.

## Base N120 Values

| quantity | value |
|---|---:|
| `lambda1_G` | `3.9285077482964378234005407361846759791247416851200922263791098777128270823251073e-28` |
| `lambda2_G` | `7.5110032640263442408588918481367677993404755977336349973856903773509738386175771e-28` |
| `lambda3_G` | `1.1552588608928484370318667777805945411432515263325018627033866381285154081209062e-27` |
| `nu_tail` | `3.2960935495481850719138529050771074433659529435430161949242288195308989982566486e-53` |
| actual `mu1` | `1.4598129516305608574358609264922179071797113743878582206556358479950433608366779e-64` |
| actual `mu2` | `1.6680022583588869596654056727736096522590303309993518433644085253282379668077549e-60` |
| actual `mu3` | `9.3843336472943064927066176234582865627823597812140712761977363506071252695875636e-57` |

## Required Comparisons

| comparison | value | sign |
|---|---:|---|
| `nu_tail - lambda1_G` | `-3.92850774829643782340054040657532102430623449373480171866836554111753272802348780757711804691010017433514e-28` | negative |
| `nu_tail - lambda2_G` | `-7.51100326402634424085889151852741284452196840634834448967494604075567948431595760757711804691010017433514e-28` | negative |
| `nu_tail - lambda3_G` | `-1.155258860892848437031866744819659045661400807193972811932312204468985972690744250757711804691010017433514e-27` | negative |
| `nu_tail - mu1` | `3.296093549533586942397547296502748834101030764471219081180350237324342639776698166391633221e-53` | positive |
| `nu_tail - mu2` | `3.29609338274795923602515693853654016600498771763998309498904448309004646543285191922451e-53` | positive |

Therefore `nu_tail < lambda2_G`, but `nu_tail > mu2`.

## Merged Candidate Low Spectrum

Sorted ascending for `{lambda1_G, lambda2_G, lambda3_G, nu_tail}`:

1. `nu_tail = 3.2960935495481850719138529050771074433659529435430161949242288195308989982566486e-53`
2. `lambda1_G = 3.9285077482964378234005407361846759791247416851200922263791098777128270823251073e-28`
3. `lambda2_G = 7.5110032640263442408588918481367677993404755977336349973856903773509738386175771e-28`
4. `lambda3_G = 1.1552588608928484370318667777805945411432515263325018627033866381285154081209062e-27`

Within the repaired packet-plus-tail candidate set, the rogue tail enters before the first and second packet levels.

## Actual Full-Matrix Comparison

The existing N120 full-matrix low spectrum has:

```text
mu1 < mu2 < mu3 < nu_tail << lambda1_G < lambda2_G < lambda3_G
```

Numerically:

| comparison | value |
|---|---:|
| `mu1 - lambda1_G` | `-3.9285077482964378234005407361846759776649287334895313689432489512206091751453959256121417793443641520049566391633221e-28` |
| `mu2 - lambda2_G` | `-7.511003264026344240858891848136751119317892008864038343328962641254451248314267106481566355914746717620331922451e-28` |
| `mu2 - nu_tail` | `-3.29609338274795923602515693853654016600498771763998309498904448309004646543285191922451e-53` |
| actual `mu2 - mu1` | `1.66785627706372390357966208668096043046831235986191305754234296174343846247167123221e-60` |
| packet `lambda2_G - lambda1_G` | `3.5824955157299064174583511119520918202157339126135427710065804996381467562924698e-28` |

This means the rogue tail is not below actual `mu2`; it is not the first or second full-matrix level in this N120 model. However, it is still far below the repaired packet's `lambda2_G`, so the current 3-vector packet cannot justify the two-level G4 lower-bound placement by itself.

## Precision Cross-Check

The dps+80 run has the same sign pattern:

| comparison | value |
|---|---:|
| `nu_tail - lambda1_G` | `-3.92854603233480352927466894263063284098046064223258161881689419827531293825836013412411373824337436062393e-28` |
| `nu_tail - lambda2_G` | `-7.51104356064092412158286500068004933398512717866944670713398780402863701320309163412411373824337436062393e-28` |
| `nu_tail - lambda3_G` | `-1.155264287298428782081916143595741036456704521339152377437751827244095469106963893412411373824337436062393e-27` |

The conclusion `nu_tail < lambda2_G` is stable under the existing dps+80 audit.

## Interpretation

The previous `lambda3_G` tail test was stronger than the two-level question. For the two-level gap, the relevant packet placement check is against `lambda2_G`. This audit shows the rogue tail is below `lambda2_G`, so the repaired current 3-vector packet placement fails the two-level packet test.

At the same time, the actual full-matrix `mu2` is much smaller than `nu_tail`, so the rogue tail does not itself enter before actual `mu2`. The current finite model therefore has a deeper mismatch than the single rogue vector: the first two actual full-matrix levels are already far below the repaired packet levels.

Next gate remains local and diagnostic: determine whether the missing low levels/tail behavior come from a missing prolate comparison branch, an admissibility/boundary leak, or another packet-definition limitation. No global Route B claim follows from this audit.

## Proshka Follow-Up

After this audit, Proshka selected the next gate:

```text
NEXT_GATE = FullLowEigenvectorBlockLedgerAudit
```

Reason: the actual full-matrix order is `mu1 < mu2 < mu3 < nu_tail`, so the immediate issue is no longer the tail vector alone. The next diagnostic should identify the actual low eigenvectors `xi1`, `xi2`, `xi3` and explain why they sit far below the repaired packet levels.

Do not continue a tail-only rogue comparison first. Do not run Phase 2, rerun the full ladder, change formulas, change packet definitions, or claim Route B killed.
