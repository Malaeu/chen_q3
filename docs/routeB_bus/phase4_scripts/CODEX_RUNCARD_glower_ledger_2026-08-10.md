# RUNCARD [→CODEX] · GLOWER ledger production run · 2026-08-10

Repo: github.com/Malaeu/chen_q3, branch rh_clean. Author of script: Mythos
(tested in container at N=100 and N=240 against tip 702e041). READ_ONLY
numerics; the script writes nothing into the repo by itself.

## 1. Materialize and commit (canon+mirror one commit)
Place `glower_head_drift_ledger.py` at
`docs/routeB_bus/phase4_scripts/glower_head_drift_ledger.py`
(Linux clone: /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean; Mac clone:
/Users/emalam/GitHub/rh_lean_01_2026). Commit message suggestion:
`[Bus] GLOWER ledger: column profile + table majorant with gamma floor (Mythos, tested N=240)`.

## 2. Production run (under nohup, ~1–3 h)
```
cd <repo>/docs/routeB_bus/phase4_scripts
nohup python3 glower_head_drift_ledger.py --N 960 \
  --csv /tmp/glower_ledger_960.csv > /tmp/glower_ledger_960.log 2>&1 &
```
Defaults already set: dps=300, dps-tail=40, R=70, tau=0.5,
cert-head ladder "240,360,480", cuts "120,240,480,960".

## 3. Expected terminal codes
- `GLOWER_LEDGER=MAJORANT_PASS_TABLE S=<S*> tau=<t> gamma=<g>` — rigorous:
  every cut N' in (S*,960] has corrected head >= gamma*I; S* = measured
  ground-tail decay boundary (new Input-B observable).
- `MAJORANT_NONPOSITIVE` on all rungs — diagonal minorant insufficient even
  at S=480: itself a structural result (report, do not tune silently).
- `MAJORANT_INSUFFICIENT_PRECISION` — rerun with higher --dps.
- `TAIL_MINORANT_FAILED` — contradicts journal R1; stop and report.
NOTE: gamma is an EIGEN-scale object (~1e-55, neighbor of beta*), not the
journal LDLT pivot scale (~1e-10). Do not compare them.

## 4. Already-measured integration facts (container, N=240, dps=200)
- PASS at S=180: gamma = 1.398238e-55 (S=120 rung NONPOSITIVE) => S*<=180 at N=240.
- Octave (120,240]: Sum(w) = 2.330e-01 vs journal pivot drop 2.740216e-12,
  rho ~ 1.2e-11 => P-L1 preview REFUTED_LOOSE.
- P-L3 at N=240: autocorr r=0.267 (lag 16) => NOT_CONFIRMED (threshold 0.30).

## 5. Registered predictions to score after the run (K6, frozen now)
- P-L1 final, octave (480,960], operationalization in script docstring:
  expect REFUTED_LOOSE. Mythos assigns p=0.90 to that verdict.
- P-L3 at N=960 (890-point profile): CONFIRMED with p=0.70 (standing bet).
- P-L4 (new): first passing rung S* = 240 at N=960, p=0.65.
- P-L5 (new): gamma(960) in [0.7e-55, 2.1e-55], p=0.60.
Paste the four verdict lines + S*, gamma, top-5 peaks into the journal
(PHASE4_RESULTS append, same style as R5) and update ROUTE_B_STATE.md last.

## 6. Optional second command (only if all rungs fail)
Rerun with finer ladder: `--cert-head "480,600,720" --dps 360`.
