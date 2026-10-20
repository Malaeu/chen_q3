# Local full-pair identifiability audit

Target: complete unordered signed D_ij from the pinned pair decomposition.
No raw source sums are recomputed; all20 configurations and13434 stored pairs
participate. Exact Fraction comparisons use stored certified interval endpoints.
The audit verifies physical-minus-raw compatibility and complete-C reassembly.
Norm-based features are checked first, then strengthened by pair group and
per-column prime-ideal norm/exponent patterns. Both profiles fail with322
feature groups having incompatible output intervals. This count includes
conjugate orientations and is not322 independent mathematical experiments.

PySR admission is HOLD. No model is fitted; no dependencies installed.
A no-collision outcome would only pass a necessary finite test, not establish
universal identifiability or eligibility to train on unique row identifiers.

Reproduce with fresh output paths:

```sh
python3 -m unittest discover -s experiments/cf22_pysr/local_block -p 'test_*.py' -v
python3 experiments/cf22_pysr/local_block/audit.py --output /tmp/cf22-local-audit.json
python3 experiments/cf22_pysr/local_block/verify_witnesses.py --output /tmp/cf22-local-witnesses.json
```

`result.json` is the full audit summary with exact witnesses and feature keys.
`witness_verification.json` independently replays two fixed source witnesses;
it does not import the auditor. `VALIDATION.json` binds source and output hashes.
`RESULT.md` gives the Russian explanation and the next missing input.
