# Track B B2b: Smooth Quadrature Probe

Status: RP4/B2 diagnostic.  This is not a proof of E5p, not a proof of RH,
and not a Lean proof file.

This note follows `docs/trackB/b2b_correction_structure_probe.md`.  The
previous probe found the right structural target:

```text
B_R = (P(M^+) - P(1_I)) - (P0(M^+) - P0(1_I))
```

is small because the smooth prime correction and smooth continuum correction
nearly match as operators.  The next theorem candidate is therefore a smooth
prime-continuum quadrature estimate for the full receiver error.

## D2 Normalization

Raw variable:

```text
a = r * log p,
x = exp(a),
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

For a packet vector `v`, write:

```text
E_delta(a) = M^+_[2K,4K],delta(a) - 1_[2K,4K](a),
H_v(a)     = E_delta(a) * F_v(a),
phi_v(x)   = x^(-1/2) * H_v(log x).
```

Then the raw correction residual is:

```text
sum_n Lambda(n)n^(-1/2) H_v(log n)
  - integral exp(a/2) H_v(a) da

= integral phi_v(x) d(psi(x)-x).
```

This is the D2-safe partial-summation doorway.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV receiver formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Stieltjes partial summation for the Chebyshev function
  `psi(x)=sum_{n<=x} Lambda(n)`.
- `UNCONDITIONAL`: explicit Chebyshev/PNT error bounds.  The diagnostic uses
  the Fiori--Kadiri--Swidinsky shape:

  ```text
  |psi(x)-x| < 9.22106*x*(log x)^(3/2)*exp(-0.8476836*sqrt(log x))
  ```

  for `x>2`, as recorded on arXiv.  Source:
  https://arxiv.org/abs/2204.02588
- `UNCONDITIONAL / finite-dimensional linear algebra`: projected generalized
  eigenvectors and packet profiles for the current Step13 packet model.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap conclusions.

## Local Search Synthesis

Local `q3_docs` searches for:

```text
Chebyshev psi partial summation prime term variation bound von Mangoldt
AFP Chebyshev Prime Bounds psi theta Q3 prime heat bucket
partial summation Stieltjes psi(x)-x smooth prime sum explicit formula edge defect
```

returned:

- Q3 prime-term Lipschitz bridge material;
- PrimeCert / bucket-envelope machinery;
- AFP `Chebyshev_Prime_Bounds` references in older notes;
- prime-cap and heat-window finite certificate paths.

These are relevant formalization ingredients, but no local theorem currently
states the needed smooth quadrature estimate for `E_delta(a)*F_v(a)`.

## The Variation Bound Shape

If `|psi(x)-x| <= U(x)` on the support of `phi`, then integration by parts
gives the schematic bound:

```text
| integral phi(x) d(psi(x)-x) |
  <= U(A)|phi(A)| + U(B)|phi(B)|
     + integral_A^B U(x) |phi'(x)| dx.
```

In raw `a` coordinates:

```text
phi(x) = exp(-a/2) H(a),

integral |phi'(x)| dx
  = integral exp(-a/2) |H'(a) - H(a)/2| da.
```

So the theorem target becomes:

```text
U-weighted variation of E_delta(a)*F_v(a)
  <= epsilon_K * <v,Gv>.
```

The current probe computes this quantity for the correction eigenvectors.

## Probe Mode

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvquad \
  --K 3.5 --ell 1.375 --schedule fixed \
  --receiver-delta 1 \
  --p0-na 401 --quad-na 4001
```

The mode reports, for the lower/upper/opnorm directions:

- matrix correction eigenvalue;
- direct prime sum and direct continuum quadrature for
  `E_delta(a)*F_v(a)`;
- empirical-grid variation bound using exact sampled `psi(exp(a))-exp(a)`;
- explicit-PNT variation bound using the Fiori--Kadiri--Swidinsky error shape;
- variation in `x`:

  ```text
  integral exp(-a/2)|H'(a)-H(a)/2| da.
  ```

The empirical `psi` bound is diagnostic, not a theorem.  The explicit-PNT
bound is the allowed theorem-input proxy.  The implementation also takes the
minimum with the trivial positive fallback `x*(log x+1)` on the grid; since
the resulting bound is still far too large, this only strengthens the negative
diagnostic.

## Detailed K = 3.5 Result

At:

```text
K = 3.5,
ell = 1.375,
delta = 1,
p0_na = 401,
quad_na = 4001,
```

for the opnorm direction:

```text
matrix correction opnorm             ~= 0.2381603793
direct smooth residual               ~= 0.2232963920
matrix/direct abs mismatch           ~= 0.014864

exact-grid weighted variation bound  ~= 0.6126315280
explicit-PNT weighted variation      ~= 764.3713293

actual / exact-grid bound            ~= 0.36449
actual / explicit-PNT bound          ~= 0.000292
explicit-PNT bound / matrix opnorm   ~= 3209.48

variation_x                          ~= 0.10703
sup exact |psi-x| on grid            ~= 439.82436
sup explicit PNT bound on grid       ~= 1.3814690e7
max |H|                              ~= 0.99627
```

Interpretation:

- The partial-summation form is aligned with the object: the empirical
  `psi`-variation bound is only a small constant factor above the measured
  residual.
- The published explicit PNT bound is far too large at this scale.

## Four-K Schedule

Using the same stable packet widths and receiver bandwidths as the previous
Track B schedule, with `p0_na=401` and `quad_na=4001`:

```text
K=2.0, ell=0.75, delta=0.5:
  matrix opnorm ~= 0.101963946
  direct residual ~= 0.109199342
  exact-grid variation bound ~= 0.791832519
  explicit-PNT variation bound ~= 98.6338978
  explicit-PNT / matrix opnorm ~= 967.3

K=2.5, ell=1.375, delta=1.0:
  matrix opnorm ~= 0.419464375
  direct residual ~= -0.425840589
  exact-grid variation bound ~= 0.950942811
  explicit-PNT variation bound ~= 187.349516
  explicit-PNT / matrix opnorm ~= 446.6

K=3.0, ell=0.75, delta=0.5:
  matrix opnorm ~= 0.113324380
  direct residual ~= -0.143624266
  exact-grid variation bound ~= 0.310783442
  explicit-PNT variation bound ~= 314.934080
  explicit-PNT / matrix opnorm ~= 2779

K=3.5, ell=1.375, delta=1.0:
  matrix opnorm ~= 0.238160379
  direct residual ~= 0.223296392
  exact-grid variation bound ~= 0.612631528
  explicit-PNT variation bound ~= 764.371329
  explicit-PNT / matrix opnorm ~= 3209
```

The empirical-grid variation bound is plausible as a structural explanation.
The off-the-shelf explicit PNT error term is not a B3 closure bound for the
current small-K packet schedule.

## Interpretation

This probe kills the naive version of the smooth quadrature route:

```text
Use a global explicit PNT bound for |psi(x)-x|
and a total-variation bound for phi_v.
```

The theorem is unconditional, but it is too crude by factors from hundreds to
thousands in the tested schedule.  It would not give

```text
epsilon_K <= C*K^(-c)
```

at the current B3 scale.

But the route is not dead.  The empirical `psi` variation bound is close enough
to say the formula is looking at the right object.  What is missing is a
localized/frequency-aware prime quadrature theorem, not a new Selberg receiver
identity.

Surviving next shapes:

1. **Finite psi ledger for small K**:
   Use exact Chebyshev staircase data on the finite range and prove the
   variation inequality by certified interval arithmetic.  This is a
   computation route, but much smaller than raw edge chunks.

2. **Localized smooth PNT**:
   Replace the global `sup |psi-x|` input by a localized bound matched to the
   support and oscillation of `E_delta(a)*F_v(a)`.

3. **Return to zero-side PSD / explicit formula**:
   The correction weight is smooth enough that the full explicit formula may
   give a sharper zero-side/arch-side estimate than Chebyshev total variation.

## Verdict

`PARTIAL(partial-summation theorem shape matches the correction)`.

`GAP(global explicit-PNT variation bound is too large)`.

`FATAL(plain Fiori--Kadiri--Swidinsky sup-error + total variation as B3 closure)`.

This is not fatal for Track B.  It says the next proof attempt must be
localized, certified-finite, or zero-side/PSD-aware.

Follow-up:

- `docs/trackB/b2b_fourier_psd_probe.md` tests the zero-side/PSD-aware option
  directly.  The profile `F_v` passes sampled Fourier-positivity sanity, but
  the correction product `E_delta*F_v` is strongly Fourier-sign-changing.  So
  the direct PSD shortcut is not available; a signed PD decomposition or finite
  Chebyshev staircase ledger is still needed.

## Proshka Audit Block

Claim:
The smooth correction can be written D2-safely as
`integral phi_v d(psi-x)` with
`phi_v(x)=x^(-1/2)E_delta(log x)F_v(log x)`.  Empirically, the variation bound
using exact sampled `psi-x` is within a small constant factor of the measured
residual.

Point of blockage:
The unconditional published global PNT error bound is too large on the current
small-K schedule.  At K=3.5, it gives a bound around `764`, while the correction
opnorm is about `0.238`.

What was tried:
Added `scripts/trackb_edge_operator_probe.py clvquad`; computed direct
prime-minus-continuum residuals for the correction eigenvectors; computed
Stieltjes variation bounds using exact-grid `psi-x` and explicit PNT
`psi-x` bounds; ran K=2,2.5,3,3.5.

Minimal example:
At `K=3.5`, `ell=1.375`, `delta=1`, `p0_na=401`, `quad_na=4001`,
the opnorm direction has matrix opnorm `~0.238160379`, direct smooth residual
`~0.223296392`, exact-grid variation bound `~0.612631528`, but explicit-PNT
variation bound `~764.371329`.

Question for Proshka:
Should Track B next build a certified finite Chebyshev staircase ledger for
the smooth receiver correction, or should it abandon Chebyshev variation and
use the full explicit formula/zero-side PSD route for this smooth test family?
