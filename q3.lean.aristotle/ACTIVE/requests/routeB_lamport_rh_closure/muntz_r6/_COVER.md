# Müntz R6 harvest cover

```yaml
project_id: c746a674-5849-4dfa-9e4c-b7dd5af231b2
run_label: R6_RMINUS_HALFPLANE
aristotle_summary_run: 24590110-d241-4553-905a-e163c0692f3e
source_archive: q3.lean.aristotle/aristotle_output/c746a674_R6_RMINUS_HALFPLANE_2026-07-30/output-final.tar.gz
source_archive_sha256: 6d94cb8240fe956f724dbb051bdf85733cae04dbeb0bdb706d054fff27f46758
lean_status: HARVESTED_NOT_BUILT
aristotle_actions_by_codex: false
closed_upstream_hole: Rminus_differentiableOn_halfPlane
authoritative_evidence: RequestProject/*.lean
result_md_status: STALE_R5_POISON_LABEL
result_md_is_verdict: false
```

## Harvest boundary

The extracted Aristotle tree was copied without changing source bytes.  The
R6 `RequestProject/TailAnalyticity.lean` replaces the R5 `sorry` in
`Rminus_differentiableOn_halfPlane` with a proof using
`Estar_bounded_by_sqrt_of_zeroMass` and
`mellin_differentiableAt_of_isBigO_rpow`.

This package was harvested only.  It was not rebuilt or integrated by Codex;
local compilation belongs to the later v3 consumer goal.

## POISON LABEL — stale `RESULT.md`

`RESULT.md` is stale R5 text and contains exactly:

```text
MELLIN_DSLOPE_ANALYTICITY_GAP
```

That file is **not a verdict for R6** and must never be used to judge this
harvest.  Judge only the harvested Lean sources and a later explicit local
build.
