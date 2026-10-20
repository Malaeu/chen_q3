# Arithmetic character fingerprint and bounded symbolic search

Read RESULT.md for the actual outcome and scope. Source: pinned full pair
ledger, every signed pair retained. Fingerprints evaluate the original sixth
character on9 fixed small arguments; no target sum or row ID is a feature.

Reproduce with the existing environment; new output paths are required:

```sh
/tmp/cf22-pysr-venv/bin/python -m unittest discover -s experiments/cf22_pysr/character_features -p 'test_*.py' -v
/tmp/cf22-pysr-venv/bin/python experiments/cf22_pysr/character_features/features.py --output /tmp/character-new-dataset.json
PYTHON_JULIACALL_THREADS=1 /tmp/cf22-pysr-venv/bin/python experiments/cf22_pysr/character_features/search.py --dataset /tmp/character-new-dataset.json --output-dir /tmp/character-new-search
python3 experiments/cf22_pysr/character_features/verify_candidates.py --output /tmp/character-new-verification.json
```

The last command verifies the SHIPPED run using standard-library rational
interval arithmetic; it does not run PySR. Model candidate checks in search.py
use Arb192bits, separately from floating-point proposal search. Printed symbolic
constants are fixed rational literals for refutation. Do not infer impossibility
of nearby formulas or universal adequacy of the finite fingerprint.

`dataset.json.gz` contains all13434 rows (deterministic gzip, mtime0).
`audit.json` retains metadata without the full table; `search_run/manifest.json`
was saved before the fit. All Pareto candidates and their original CSV are
retained. The checkpoint.pkl is a PySR artifact; replay of certificates needs
no unpickling. `candidate_verification.json` certifies one strict disjointness
witness per candidate. The full-panel feature selection makes test exploratory.
The search time cap is60seconds; initialization/validation are outside it.
