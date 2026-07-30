# Müntz v3 harvest cover

Date: 2026-07-30
Goal: `039_muntz_v3_consumption`
Project: `987ff124-3032-42e5-aa9f-24ceef69f62a`
Task: `472e126c-759f-4c69-8816-fa013ff740b2`
Cloud status: `COMPLETE_WITH_ERRORS`, 100%
Verdict source: Lean sources, never the cloud status string

## Provenance

The conductor-delivered archive is:

```text
q3.lean.aristotle/aristotle_output/987ff124_MUNTZ_V3_POLESUBTRACTED_2026-07-30/output-final.tar.gz
sha256 c69483c0238fe923b2f927458e5fe63855060042e378a662a13321d5c3fd776e
```

All seven files actually present in that archive were copied here without
changing bytes. A direct `cmp` against the delivered extraction passes for
every harvested file.

## Harvested files

| File | SHA-256 |
|---|---|
| `ARISTOTLE_SUMMARY.md` | `c965e629e51330d5a70b007a1c4cdbcc0e7a913eab51f05133bbde8e57772142` |
| `README.md` | `39ec8cd0459306d9f50cf0c0da2aaf858aeaba5affa9ae26c3dbaee9f872f0ab` |
| `RequestProject/.gitkeep` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `RequestProject/Main.lean` | `0b2e52db207610f0e63c3dac3e61c5d14f26d0119ccd11756cdbeeab80f3b888` |
| `lake-manifest.json` | `116c6ef00aa899fb38c08c5e4c92c0e434d0e7f9d574fcb5d4d42cc90ffb07cb` |
| `lakefile.toml` | `b1481968ce2912f2b85288fc18aa05fb22750e4083f9e03f49f59a8814ba268a` |
| `lean-toolchain` | `db7bb24b756d745bbde83fe92718b51bd3625dae3701ba0f598d0eedcd3f3028` |

## RESULT.md inventory discrepancy

The delivered tar archive contains no `RESULT.md`. The authenticated Aristotle
code tree for the same project also lists no `RESULT.md`. Therefore Goal 039
does not fabricate one or relabel another file as source-locked output.

The exact final cloud output is preserved verbatim in the delivered
`ARISTOTLE_SUMMARY.md`; its primary message is
`MELLIN_DSLOPE_ANALYTICITY_GAP`. That text is a gap report, not a verdict on
the locally consumed layer.

## Independent source audit

```text
RequestProject/Main.lean lines: 239
lake build: PASS
taint matches in harvested Main.lean: 0
checked main declarations: 18
axioms for every checked declaration:
  [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, declaration `axiom`, `native_decide`, or `exact?` is
present in the harvested Lean source.

## Local Goal 039 additions

The following are new local files, not cloud-harvest bytes:

| File | Purpose | SHA-256 |
|---|---|---|
| `RequestProject/MellinCompactSupportAnalyticity.lean` | closes exact T4a | `0cf35bb021fbb888b6507e8d0dfbb61dc790d60ec4af7c8e9b5fec3928943c22` |
| `RequestProject/MuntzV3Unconditional.lean` | consumes T4a into T5 and its two corollaries | `7bc8e8dbec15ff87a067462a8e7e4cf5a6804c737d067fc046a5d4db3739bef2` |

Both build against the pinned Lean 4.28.0 / Mathlib v4.28.0 project and use
exactly `[propext, Classical.choice, Quot.sound]`.

Lane status remains `CHALLENGER / NOT_RH`; Bus 010 remains void.
