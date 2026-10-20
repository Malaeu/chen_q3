# Exact saved-pair gcd split

Main: all complete signed pair contributions with ideal gcd norm <=G.
Remainder: every other complete signed contribution. Thresholds: 1,7,13,19,31.
Every side retains RR, cross, AA, physical and subtracted raw contributions.
No arithmetic source evaluation, fitting, dependency installation or policy
changes are involved. Decimal displays in RESULT.md are illustrative; JSON
uses exact rational endpoints enclosing the saved source values.

`split.py` validates ideal factor identities and accumulates the two sides.
`verify_shells.py` independently recovers gcd norms by prime-ideal intersection,
accumulates exact gcd shells, then forms prefixes. Both use Python Fraction,
not floating-point comparisons. Inputs are SHA256 pinned. The old interval
source is trusted; interval overlap is compatibility, not exact equality of
independently evaluated irrational values. The partition identity itself is
an exact identity of finite sums.

Run from repository root with fresh output paths:

```sh
python3 -m unittest discover -s experiments/cf22_pysr/gcd_split -p 'test_*.py' -v
python3 experiments/cf22_pysr/gcd_split/split.py --output /tmp/cf22-gcd-replay.json
python3 experiments/cf22_pysr/gcd_split/verify_shells.py --output /tmp/cf22-gcd-shell-replay.json
```

Actual outputs: `result.json`, `shell_verification.json`; exact endpoint/count
comparison and implementation hashes: `VALIDATION.json`.
The diagnostic separation penalty is max(M,0)+max(R,0)-max(C,0), constrained
by its proven nonnegativity; it is not an optimized proof budget.
Empty remainders can be identified by their pair_count=0. A tiny nonempty
interval is not silently replaced by zero. No best asymptotic threshold or
CF22 improvement is established.
