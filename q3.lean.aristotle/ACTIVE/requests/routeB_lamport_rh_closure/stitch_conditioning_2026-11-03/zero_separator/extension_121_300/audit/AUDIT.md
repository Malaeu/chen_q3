# DH quartet inclusion audit

**No missing quartet detected; no B/C recomputation is required by this audit.** DIAGNOSTIC_NEVER_A_PROOF.

The exact table `/workspace/conditioning_input/dh_zeros.json` contains all four requested quartets, represented by upper-half-plane left/right pairs with right coordinates approximately (0.808517182457,85.699348485378), (0.650830080610,114.163342730757), (0.574356050451,166.479305913168), and (0.724257694627,176.702461242856).

Its SHA256 is `e2f5f86d960aff5b45a318723072a1a2c67df3f00b6d213535274831c9afdee1` (69981 bytes), matching REPLAY_DEPENDENCIES.json. Its locally computed Git blob ID `741fa6be24f8c85acd07147b4b284c8076d727f1` matches the remote table blob at rh_clean `3691f8e`.

Pinned source B `docs/routeB_bus/stitch_conditioning_2026-11-03/B_stitch/stitch.py`, Git blob `a901d8de8eec3db801e13d00c75125d9269aef32`, explicitly includes both complex evaluation points γ±i(σ−1/2), then takes Re and Im of each: **four real conditions per quartet**. Every ordinary positive-height line zero gives two real conditions in this full-real step carrier. The inclusion condition is strictly `gam<T`.

Pinned C `C_conditioning/core.py`, Git blob `db7a86251f31d55e7fd6ac226b702f1476819edd`, matches the local source byte for byte. It evaluates only one complex point in the even carrier, and uses its Re/Im: **two real conditions per quartet**, with signed metric weights +4 and −4. A line zero gives one real condition. C also uses strictly `g<T`.

Independent saved-data checks, rather than documentation alone:

- All 24 saved B DH cells pass expected row counts `2*line_count+4*quartet_count`. Every included quartet has both complex-point labels, matching its exact table height. Maximum saved T is 89.4199722838615: the first quartet is included when eligible; the other three are outside every B cutoff, hence their absence there is intentional.
- All 315 saved DH C rows in `conditioning.csv` pass expected raw counts `line_count+2*quartet_count` and independent distinct-height counts `line_count+quartet_count`. Maximum T is 199.695900020262, so all four quartets are covered by eligible C cutoffs.

C CSV files do not persist every raw evaluation-row label; their independent evidence is both saved counts, combined with the byte-verified source loop that processes every eligible table event. This audit does not claim a numerical replay of their matrix entries or a new zero-table completeness certificate.

Full per-cell/per-row evidence is in `evidence.json`; count verification is reproducible with `python audit.py`. Source copies are provided only as readback evidence. No source eigenproblem, remote write, or changes outside this audit directory were performed.
