# Independent verification with `leanprover/comparator`

This directory packages the RH claim for [comparator](https://github.com/leanprover/comparator),
the Lean FRO's trusted-verification tool, in the layout used by `openai/NavierStokesAndEuler`
(`ComparatorChallenges/`) and `anthropics/zeta-23-lean` (`comparator/`). Comparator builds a
*trusted* challenge module and an *untrusted* solution module in a sandbox, exports both, checks
that the solution proves **exactly** the challenge statements, that the proofs use **only** the
axioms `propext`, `Classical.choice`, `Quot.sound`, and replays the solution through the Lean
kernel (optionally also through the independent `nanoda` kernel).

| file | role | trusted? |
|---|---|---|
| `Challenge.lean` | (1) `RiemannHypothesis.riemannHypothesis : RiemannHypothesis` — the Clay statement in Mathlib's type, copied from `google-deepmind/formal-conjectures` `FormalConjectures/Millenium/RiemannHypothesis.lean`; (2) `Q3Comparator.rh_strip_iff_riemannHypothesis` — the project's strip form of RH (body of `Q3.RH`, inlined from Mathlib alone) ⟷ Mathlib `RiemannHypothesis`. Proofs `sorry`. | yes — read it |
| `Solution.lean` | proves (2) by `Q3.rh_iff_mathlib` (`Q3/Proofs/RouteB/MathlibRiemannHypothesisBridge.lean`). (1) is deliberately absent until the roof is unconditional. | no (checked by comparator) |
| `config-bridge.json` | theorem (2) only — runnable today | yes |
| `config-rh.json` | theorem (1) only — the `PX_RH_CLAIM` run; fails while `PX_RH_CLAIM: NOT_MADE` | yes |
| `PrintAxioms.lean` | `#print axioms` for the bridge — the quick check without comparator | — |

What a skeptical reader has to trust: Mathlib's `riemannZeta` and `RiemannHypothesis`,
`Challenge.lean`, the Lean kernel, and comparator's own assumptions (its README). Nothing under
`Q3/` needs to be read to know *what* is claimed.

## Why the bridge exists

The roof `Q3.rh_of_canonical_slots` (`Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean`) concludes
`Q3.RH`: every zero of `riemannZeta` with `0 < Re s < 1` has `Re s = 1/2`. The Clay/Mathlib statement
quantifies over every zero that is neither trivial nor `s = 1`. The two are equivalent by two classical
inputs, both in Mathlib: `riemannZeta_ne_zero_of_one_le_re` and the functional equation
`riemannZeta_one_sub` (zeros with `Re s ≤ 0` are trivial). `Q3.rh_iff_mathlib` proves the equivalence;
`Q3.riemannHypothesis_of_rh` is the one-line consumer for the day the roof closes.

## Quick check (no extra tooling)

```bash
cd q3.lean.aristotle
lake build Solution
lake env lean comparator/PrintAxioms.lean
# every line must read:  '<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Full comparator run

Tools (built 2026-09-09, Lean toolchain of this project is `v4.26.0`):

| tool | where | note |
|---|---|---|
| `comparator` | `/mnt/hdd01/Soft/GitHub/lean-comparator-4.28/.lake/build/bin/comparator` | tag `v4.28.0` (no `v4.26.0` tag exists; toolchain 4.28.0). Why not `v4.27.0`: that tag's own parser accepts only export format `2.0.0`, while every lean4export tag from `v4.20.0` on emits `3.1.0`; from `v4.28.0` comparator parses through lean4export's `Export.Parse` and accepts `3.1.0`. **One local patch** in `Main.lean` `buildLandrunArgs`: a `--` is inserted before the sandboxed command (upstream has it from `v4.34`), because landrun 0.1.18 otherwise swallows the `--` that separates lean4export's modules from its constants (observed: `unknown module prefix 'Q3Comparator'`). The patch touches argument order only, not any check; `git diff` in that clone shows it. The `v4.27.0` clone at `lean-comparator/` is kept only as a record. |
| `lean4export` | `/mnt/hdd01/Soft/GitHub/lean-lean4export/.lake/build/bin/lean4export` | tag `v4.26.0` — must match the project toolchain |
| `landrun` | `/mnt/hdd01/Soft/GitHub/lean-landrun/bin/landrun` | Go build from `Zouuup/landrun` main (0.1.18, commit 811cfff). Wants Landlock ABI v9; this kernel (7.0) offers v8, so comparator's `--best-effort` flag is what makes it run: the sandbox is the v8 subset, not the full v9 one. |
| `nanoda_bin` | `/mnt/hdd01/Soft/GitHub/lean-nanoda/target/release/nanoda_bin` (`ammkrn/nanoda_lib` branch `debug` at 2026-09-09) | optional second kernel; **does not work with this pairing yet**: on the export it prints `Error: invalid digit found in string` and comparator dies on a broken pipe. Open item: pin nanoda to the commit contemporary with comparator v4.28.0. `config-bridge.json` therefore has `enable_nanoda: false`; `config-rh.json` keeps `true` as the intended claim-run setting and must be fixed before that run. |

**Machine-specific trap.** `LD_LIBRARY_PATH` on this machine contains `/usr/lib/x86_64-linux-gnu/`,
so the clang bundled with every elan toolchain loads the *system* `libLLVM.so.19.1` and dies with
`undefined symbol … LLVM_19.1`. Any `lake build` that links an executable must run with
`env -u LD_LIBRARY_PATH`. Building `.olean` files is unaffected.

Run from `q3.lean.aristotle/` (where `lakefile.toml` is):

```bash
export PATH=/mnt/hdd01/Soft/GitHub/lean-landrun/bin:/mnt/hdd01/Soft/GitHub/lean-lean4export/.lake/build/bin:$PATH
env -u LD_LIBRARY_PATH lake env /mnt/hdd01/Soft/GitHub/lean-comparator-4.28/.lake/build/bin/comparator comparator/config-bridge.json
```

Do not pre-build `Challenge`/`Solution` before a run you want to rely on (comparator README,
assumption 2); for the `PX_RH_CLAIM` run use a fresh clone. Success ends with `Your solution is okay!`.

## Record

| date | config | result | note |
|---|---|---|---|
| 2026-09-09 | `config-bridge.json` + `enable_nanoda: true` | FAIL at the nanoda step | Lean kernel replay had passed in the previous row; nanoda binary rejects the export (`invalid digit found in string`) — tooling, not mathematics |
| 2026-09-09 | `config-bridge.json` | `Your solution is okay!` (3 m 47 s) | Lean kernel replay; `Solution` had been compiled once earlier in the same session (a failed run on an export-format mismatch), so assumption 2 was formally not met — a bridge check, not the claim run | The two `[[lean_lib]]` stanzas at the end
of `lakefile.toml` (`srcDir = "comparator"`) make `Challenge` and `Solution` resolvable by those bare
names, as comparator expects.
