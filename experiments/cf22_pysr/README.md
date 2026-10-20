# Full centered CF22: bounded numerical pilot

**PARKED_REOPENABLE (2026-10-20).** See [archive and reopening conditions](ARCHIVE_2026-10-20.md). This is not the default Q3 continuation. Saved artifacts remain in place.

This experiment computes the finite source
`C = E_M - lambda R_H - D_diag`, then searches for a short upper envelope
of `q = C / (P U^(1/6) L^(5/6))`. A finite passing candidate is not a
CF22 power-saving theorem or an RH result.

## Source and scope

Definitions: `docs/literature/openai_math_2026-10-07/PROSHKA_VERDICT_FULL_CUSP_PAIR_Q07.md`,
CP.4–CP.6 (lines 140–174). Original character conventions also occur in the
embedded manuscript in `PROSHKA_FULL_CUSP_PAIR_Q07.txt`, lines 16722–16797.
The exact finite-field routines are adapted from the appendix of
`PROSHKA_VERDICT_SIGNED_INCIDENCE_Q03.md`.

The pilot uses the admissible fixed specialization `S = primes above 6`,
trivial `nu`, both character orientations, and one common fixed smooth profile:

```
rho(y) = W(y) = exp(1 - 1/(1-(2y-2)^2))  if 1/2 < y < 3/2,
               0                       otherwise.
C_H = 2.
```

This specialization is explicitly distinguished from all other fixed characters,
profiles and heights. It does not test their universal quantifier.
Elements retain all six units and bad-prime factors. Good column and amplifier
indices are ideals, not six copies of each ideal. Sixth-free restrictions apply
to the original `u` rows, not the raw comparison rows `w`.
No coprimality condition between `u` and the amplifier is introduced.

`plan.json` was saved before source evaluation or regression. Whole scales
8, 12, 20, 32 belong to training; 48 and 64 belong to validation.
Both endpoints of the prescribed L window and both r endpoints are retained.
At these very small scales the amplifier contains only the unit ideal.
This is a significant limitation on arithmetic discovery, even though the
finite sums themselves are complete.

## Execution

An isolated environment was created outside the repository:

```sh
uv venv --python 3.12 /tmp/cf22-pysr-venv
uv pip install --python /tmp/cf22-pysr-venv/bin/python python-flint 'pysr==2.7.2'
/tmp/cf22-pysr-venv/bin/python experiments/cf22_pysr/evaluate.py \
  --plan experiments/cf22_pysr/plan.json \
  --output experiments/cf22_pysr/results/dataset.json
PYTHON_JULIACALL_THREADS=1 /tmp/cf22-pysr-venv/bin/python \
  experiments/cf22_pysr/search.py \
  --dataset experiments/cf22_pysr/results/dataset.json \
  --output experiments/cf22_pysr/results/search
```

Consult each script's `--help` for the implemented command interface.
The search is serial, seeded, without batching or warm start. Its iteration
budget is primary; a wall-clock cap is an additional safety limit and can make
the stopping point machine-dependent. Save the actual Julia manifest and package
versions with each run.

Arb encloses source arithmetic and candidate evaluations. Training uses floating
representations only. Candidate formulas must be frozen before validation.
Each validation row is classified separately as PASS, REFUTED, or UNRESOLVED;
a mean score cannot replace this check. The training-maximum constant is an
empirical no-power-gain baseline, not the inherited analytic CF22 envelope.
Training rows are also checked with intervals before a candidate is marked usable.
Frozen equation literals mean exact decimal rational numbers; these certified
formulas may differ slightly from internal Julia floating constants.

No Route B state, Lean declaration or RH export is modified by this experiment.
