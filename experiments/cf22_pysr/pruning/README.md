# Finite-panel coefficient pruning

Contract: every one of the saved 20 configurations must satisfy
`C <= alpha*P*U + kappa*S*U**(-delta)`, `S=P*U**(1/6)*L**(5/6)`.
Coefficients alpha,kappa are nonnegative. This is a new finite-panel contract,
not the original asymptotic CF22 claim. Input C includes every signed group.
All inputs are pinned to existing repository artifacts; no source sums or fits
are computed. The original heldout labels are provenance only: this experiment
uses all rows, and its example boxes were chosen after inspecting the panel.

`prune.py` uses 192-bit Arb enclosures, checks all three groups against full C,
computes necessary coefficient thresholds and tests parameter boxes. A strict
positive enclosure of C minus the maximal envelope is a box-exclusion witness.
`NOT_REFUTED_ON_PANEL` is not acceptance of every member or an asymptotic proof.
The configured examples include a broad box that must not be entirely excluded.

`verify_rational.py` is independent of the producer and Arb. For two fixed boxes
with delta>=0 it uses U**(-delta)<=1, then bounds S from above using exact rational
sixth-root inequalities. It pins input bytes, checks all20 group sums, and saves
strict positive rational margins. It does not trust producer output or rounded
numbers. Python and the short mathematical rules remain the trusted base; this
is not a Lean certificate.

From repository root (outputs must be fresh paths):

```sh
/tmp/cf22-pysr-venv/bin/python -m unittest discover -s experiments/cf22_pysr/pruning -p 'test_*.py' -v
/tmp/cf22-pysr-venv/bin/python experiments/cf22_pysr/pruning/prune.py --output /tmp/cf22-pruning-replay.json
python3 experiments/cf22_pysr/pruning/verify_rational.py --output /tmp/cf22-pruning-rational-replay.json
```

Actual outputs are `result.json` and `rational_verification.json`. Read the Russian
`RESULT.md` for the witnesses and limitations. Complete old mixed-mask and pair
data remain unchanged under `../nonunit/` and `../correlation/`.
