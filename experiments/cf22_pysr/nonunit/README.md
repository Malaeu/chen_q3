# Nonunit amplifier response: separate diagnostic

**OFF_SCHEDULE_MASK_DIAGNOSTIC.** P is varied independently of U. This is
not the production CF22 schedule and is never merged with its training table.
The original `../evaluate.py`, its safeguards and its frozen data are unchanged.
No PySR fit is part of this experiment.

`OWNER_REQUEST.txt` preserves the supplied request verbatim. Its linked sandbox
attachment was not supplied as a local file; the implementation here is derived
independently from the displayed formulas and the repository source. We do not
claim to have reproduced the author's separate 63 checks or unpublished code.

## Frozen panel and predictions

`plan.json` is written before the new evaluations. The common profile, trivial
nu, primes above 6, both orientations and L=U^(113/100) match the first pilot.
The main panel uses U=48,64 and P=P0(U),7,13. Heldout full-return configurations
are U=96 at P=P0(U),7,13 and U=48 at P=49. Always H=UP^6.

Two formulas are frozen, with zero allowed approximation error:

1. Zero response: C0 = A S_rho (F(1) - G_H).
2. Additive response:
   Cadd = S_rho [A(F(1)-G_H) + sum_p A(P/q_p) h(p)].

These are deliberately conditional diagnostic predictions. They retain the
actual F(1), G_H and (for the second formula) singleton h(p) at each configuration.
They test the missing mask terms; they do not independently predict those
retained inputs or all of C from U alone.

At P=7 and 13, no product of two distinct good prime ideals has norm at most P.
Consequently the additive formula is exact by its algebraic definition there;
agreement is a consistency check, not discovery. P=49 includes p*conjugate(p)
over 7, as well as the distinct ideals p^2 and conjugate(p)^2.

The request already reveals approximate h(p*conjugate(p)) at U=48 and 64.
Their interval verification is **not blind**. U=48,P=49 is a heldout check of
the full return, not an undisclosed coefficient. No coefficient is fitted or
adjusted after any heldout result.

## Why the mask reconstruction is exact

Let c_n = mu(n) W(q_n/L)/sqrt(L), and retain the zero-extended source characters.
For each good squarefree d,

```
Z_u[d] = |sum_n c_n chi_n(u)^eps 1_(n,d)=1|^2
         - sum_n |c_n|^2 1_(n,u*d)=1
F(d)   = sum_(sixthfree u) rho(q_u/U) Z_u[d] / S_rho
G_H    = sum_(0<q_w<=2H) Z_w[1] / N_H.
```

The sixth-power character identity is a coprimality mask, including at shared
primes. Thus the diagonal and energy both push through w=u*a^6 with precisely
the original masks. The total mass of Omega is A(P) S_rho, so

```
C = S_rho [sum_(q_a<=P) F(rad a) - A(P) G_H].
```

Finite Möbius inversion defines h(d)=sum_(e|d) mu(d/e) F(e) and gives
F(rad a)=sum_(d|rad a) h(d). For fixed squarefree d, d divides rad(a)
exactly when d divides a; a=d*b is a bijection with good ideals q_b<=P/q_d.
Hence its coefficient is the exact integer A(P/q_d). No density approximation,
coprimality condition between d and b, or loss of prime powers is allowed.

The omitted mixed contribution in the additive baseline is exactly
S_rho sum_(omega(d)>=2) A(P/q_d) h(d). A nonzero interval for this total
refutes exact additivity for that full configuration. A nonzero local h(d)
also refutes the corresponding local assertion; local signs alone do not
establish a sign for the full weighted sum in general.

## Exact periodic raw sum

For a column pair use the **full lcm ideal**, not only a reduced conductor.
For a principal generator a+b*omega its lattice basis is
(a,b),(-b,a-b). Put h2=gcd(a,b), h1=(a^2-a*b+b^2)/h2.
Choose integers s,t with s*b+t*(a-b)=h2; the other HNF coordinate is
b0=(a*s-b*t) mod h1.

The fundamental table uses representatives (x,j), 0<=x<h1, 0<=j<h2.
At y=j+k*h2 the correct table coordinate is (x-k*b0 mod h1,j).
This translation must also be applied for negative y.

For integer B=floor(2H), a horizontal section satisfies

```
t = floor_sqrt(4B - 3y^2)
ceil((y-t)/2) <= x <= floor((y+t)/2).
```

Exact integer prefixes sum the periodic table on this interval; subtract the
origin once. Tables contain 2 Re(chi_n conjugate(chi_m)), an integer for sixth
roots, with all zero masks retained. The disk count uses the constant table 1.
Floating approximations may initialize a square root but every returned floor
must be corrected by exact integer comparisons.

A nontrivial character on the six units has zero sum on each complete unit
orbit. This can eliminate that pair. It cannot eliminate arbitrary distinct
columns with the same unit character.

Cost per pair and radius is O(norm(lcm(n,m)) + sqrt(B)); this accelerates the
raw disk only. It is not a logarithmic-time production evaluator at U~10^39.

## Evidence discipline

Integer periodic counts are checked against direct lattice enumeration.
Arb encloses the profile weights and the final reconstruction.
The full energies, original diagonal, raw radius, counts, F, h, baseline
residuals and source hashes are retained, including uncertainty.
Source specialization and production CF22 status remain distinct.

A second disk-count check uses factorization: the number of Eisenstein ideals
of norm n is sum_(d|n) chi_-3(d), since the local counts are k+1 for split primes,
1/0 for even/odd inert exponents, and 1 for ramified exponents. Each principal
ideal has six generators. Thus N(B)=6 sum_(d<=B) chi_-3(d) floor(B/d).
`verify_outputs.py` evaluates this by quotient grouping, independently of HNF
and disk slices, and checks every saved radius including the largest one.

## Reproduce

Requirements: Python 3.12, python-flint 0.9.0 and clang++ with C++17 support.
The recorded run uses `/tmp/cf22-pysr-venv/bin/python`; another environment with
the same dependencies may be substituted. No PySR or Julia execution is needed.
From the repository root:

```sh
PY=/tmp/cf22-pysr-venv/bin/python
$PY -m unittest discover -s experiments/cf22_pysr/nonunit -p 'test_*.py' -v
$PY experiments/cf22_pysr/nonunit/evaluate_nonunit.py --plan experiments/cf22_pysr/nonunit/plan.json --stage main --output /tmp/cf22-nonunit-main-replay.json
$PY experiments/cf22_pysr/nonunit/evaluate_nonunit.py --plan experiments/cf22_pysr/nonunit/plan.json --stage heldout --output /tmp/cf22-nonunit-heldout-replay.json
```

Output paths must not already exist. The old evaluator and mathematical source
files must match their historical blobs at `plan.source_commit`. Execution HEAD
can be a later commit; it is recorded separately. Source and plan hashes are
checked again at the end of each run. Runtime and compiler metadata may differ
on replay; compare numerical rows and source hashes, not complete JSON bytes.
The native library is built from the saved C++ source in a content-addressed
`/tmp` directory. The integer radius and period caps fail explicitly rather
than truncating the source.

`main.json` and `heldout.json` contain all original components, outward Arb
intervals, mask coefficients and full exact raw pair matrices. Column order is the deterministic `n_rows`
order in the pinned evaluator (good squarefree ideals in the open W window). `heldout_freeze.json` records the code, plan and main-output hashes
before the heldout run. `summary.json` and `verification.json` are derived by
`summarize.py` and `verify_outputs.py`; these commands also refuse to replace
existing artifacts. `disclosed_coefficients.json` separately checks the
already disclosed U48/U64 coefficients and is not a new heldout panel.
