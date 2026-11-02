# DH source Rayleigh interval certificates

`DIAGNOSTIC_NEVER_A_PROOF`; Route B remains CHALLENGER / NOT_RH.

These are finite Arb interval certificates for two negative Rayleigh quotients
of the unchanged source operator, not interval certificates for entire
eigensystems, first onset, zero locations, or a cofinal claim.

Source: `dh_matrix.py` at `d26831357b6cb3b2b7d4a569d2031e454952b246`,
SHA-256 `9554c27549fc0970391c06026d8bfb402ab1cfa3b2f1db3c0db6deeb92a39f00`.
The script checks this hash before calculation and does not edit that file.
The archived 120-dps matrices supply only an approximate witness. Its 165-digit
decimal coordinates are frozen and interpreted as exact rationals with outward
Arb conversion; the certificate does not assume eigenvector accuracy.

At 600-bit Arb precision, the script evaluates the complete scalar quadratic
form rather than certifying the archived quadrature matrix:

    q(v) = c ||v||^2 + integral_0^L j_D(s)(2||v||^2-Q_vv(s)) ds
           + 2||v||^2 [atanh(exp(-L/2))-atan(exp(-L/2))]
           - sum_(2<=n<m) b_D(n) Q_vv(log n)/sqrt(n).

Here `c=log(5/pi)+psi(3/4)=-gamma+pi/2-3log(2)+log(5/pi)`.
All integer coefficients are rebuilt by the exact recurrence with Arb,
including non-prime powers. There is no pole functional. The birth endpoint
`n=m` has zero correlation and is omitted exactly, as in the unchanged source.

The finite archimedean integral is computed using rigorous `acb.integral`
on 16 subintervals. The removable endpoint is expressed through entire sinc:

    (2||v||^2-Q(s))/s
      = sum_n [C_n cos(omega_n s)/L
          + C_n omega_n^2 s sinc(omega_n s/2)^2/2
          - S_n omega_n sinc(omega_n s)],

with `Q(s)=sum C_n(1-s/L)cos(omega_n s)+S_n sin(omega_n s)` and
`C_n=2v_n^2`. Multiplication by `s*j_D(s)` uses
`exp(-s/2)/(2*sinhc(s))`; `sinhc(s)=sinc(i*s)`.
Thus no evaluation subtracts two divergent archimedean pieces at zero.
The infinite archimedean tail is the exact elementary expression above.
Arb encloses all constants, coefficients, trigonometric moments, normalization,
and integration errors. The JSON files retain the full interval output.

| m | Coarse enclosing interval for Rayleigh quotient | Strict upper < 0 |
|---:|---|---|
| 51 | `[-1.326858e-47, -1.326857e-47]` | yes |
| 55 | `[-0.663921, -0.663920]` | yes |

The full JSON intervals are substantially narrower: their radii are below
`5.89e-144` and `3.89e-142`, respectively. The decimal centers in the JSON
are retained at full returned precision; the coarse intervals above avoid
combining a truncated display center with an inappropriately tiny radius.

Reproduce from the repository after extracting the pinned source matrix archives:

```bash
uv run --with python-flint --with mpmath python cert/rayleigh.py 51
uv run --with python-flint --with mpmath python cert/rayleigh.py 55
```

Run those commands from `ledger_diff/`. By default, the input directory is the
parent `fake_worlds_2026-11-02/`; set `DH_INPUTS` to use a separately downloaded
copy. Witness coordinates, input hashes, flint version, and integration settings
are included in each result file.

The interval conclusion is only that a concrete unit-normalized carrier witness
has negative energy. It does not establish which earlier cells are positive,
prove that m=51 is the first onset, or certify the complement projection.
