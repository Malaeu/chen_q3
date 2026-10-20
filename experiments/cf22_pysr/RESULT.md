# CF22 PySR pilot — 2026-10-20

**Executed. Three generated upper-envelope candidates were refuted.**
No CF22 exponent improvement and no RH claim.

## What ran

- Source: complete CP.5–CP.6 finite sums, specialized to trivial `nu`,
  bad primes above 6, one fixed C-infinity bump, both character orientations.
- 48 configurations at U = 8, 12, 20, 32, 48, 64; both r endpoints
  and both L-window endpoints. 32 training and 16 heldout rows.
- Arb precision 192 bits. Maximum serialized q-interval width: `2.6e-55`,
  below the preregistered `1e-35` tolerance.
- E_M evaluated both directly and through Omega. C evaluated both by
  full subtraction and by the off-diagonal pair sum. Every row passed
  both interval-overlap checks.
- One PySR 2.7.2 fit: 20-iteration budget, 60-second search cap, serial,
  seed 20261020, no batching or warm start. Julia 1.13.2, Python 3.12.15.
  The cap does not bound initial package installation/precompilation.
- Eleven tests passed, including lattice completeness, character
  multiplicativity/zeros, mask hash mutation, precision stability,
  delayed-spike refutation, denominator holes and scale-split isolation.
- Independent read-only code review found no remaining material issue
  for this stated finite specialization after corrections.

The table contains genuine signed source values: q ranges approximately
from -0.0383274198374 to +0.0258267273154. These are not prescribed bounds.

## Frozen candidates and discriminator

Here `ell = log(L)/log(U)`; every displayed decimal literal means its exact
decimal rational value. Full interval results for all train and heldout rows
are in `results/search/results.json`.

| Candidate | Complexity | Heldout accepted/refuted | Largest heldout shortfall |
|---|---:|---:|---:|
| `0.008393425576270878` | 1 | 8 / 8 | 0.0174333017392 |
| `0.020864296433712338 / logU` | 3 | 8 / 8 | 0.0208099244827 |
| `ell * 0.046712812821380935 / logU^2` | 7 | 8 / 8 | 0.0227748923829 |

All three also have training violations. Thus **zero usable
EMPIRICAL_CANDIDATEs** were obtained. The finite penalty in the objective
does not enforce a hard upper bound; the separate interval checker rejected
the violations as intended.

The maximum shortfall occurs at U=64, r=113/100, L=U^r (both orientations).
There q is enclosed around 0.025826727315439297.
Every candidate is accepted on U=48 and refuted on U=64.
The training-maximum constant baseline, approximately 0.00841324684373,
is also refuted. It was an empirical baseline, not an analytic CF22 bound.

## Evidence and limits

- Dataset SHA-256:
  `276f5d60eca837e0d03be590ddcd2299fa912b9465a8d421875158d02839d211`
- Frozen candidates SHA-256:
  `89c88d3b037e4b12daa98a63f665929e7ae65db1c742525ba8425e8534cc5b50`
- Runtime Julia manifest hash matches the saved
  `results/environment/Manifest.toml`.
- Original source files, evaluator and preregistered plan are hashed in
  the dataset provenance.

Amplifier count is **one in every row**. The finite supports contain
18–228 original u elements, 72–804 raw w elements and 4–33 good column
ideals. Orientation pairs are conjugate computations for this real profile,
not independent evidence.

These scales exercise the complete arithmetic and falsification pipeline,
but do not sample nontrivial amplifier behavior or the full fixed-profile,
character and height quantifiers. The requested October 19 attachment
was not available locally; source definitions were recovered from the
existing pinned Q07/Q03 documents instead.

No claim is made that a short envelope cannot exist. Only these three
frozen formulas and this empirical baseline have been refuted.
No second fit, post-validation coefficient adjustment or global theorem
was performed. The next mathematical task is to explain the actual U=64
increase and obtain a source-derived envelope; merely raising the constants
after seeing this cell would consume the heldout set.

AUTOPSY: dropped=BOUNDEDNESS; note=The frozen finite search produced three envelopes, all refuted at U64; no arithmetic exponent gain.
