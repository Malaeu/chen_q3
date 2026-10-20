# Full signed pair decomposition of the saved nonunit panel

Scope: owner-requested §6 of `OWNER_REQUEST.txt`. Reuse all 20 saved
configurations in `../nonunit/main.json` and `../nonunit/heldout.json` at
`f1993ec6a7933418c38c305a13a3221037b9447a`. No new raw disk summation or fit.
Only the small physical sums are recomputed. Old files remain unchanged.

## Definition and exact return

All source columns are good squarefree ideals with nonzero Möbius coefficient
in the same strict W support. Column order is reconstructed from the pinned
source enumerator and checked against the saved raw matrix dimensions.
Let c_i=mu(n_i)W(q_i/L)/sqrt(L), with the real fixed profile used in the pilot.
For each **unordered** pair i<j compute

```
V_ij = sum_(sixthfree u) rho(q_u/U) * 2 Re(chi_i(u) conjugate(chi_j(u)))
R_ij = saved pair_2re[i][j]
a_ij = #{good a: q_a<=P and (a,n_i*n_j)=1}
D_ij = c_i*c_j * [a_ij V_ij - A(P)*S_rho*R_ij/N_H].
```

The factor 2 accounts for the two ordered off-diagonal terms. The diagonal
has already been removed and is not added back. The sum of D_ij is the original
C: expanding each masked energy gives coefficient a_ij on its physical pair,
and the original raw mean has coefficient A(P). Every amplifier, including
prime powers, is counted separately. Inclusion-exclusion independently gives
`a_ij = sum_(d|rad(n_i*n_j)) mu(d) A(P/q_d)`.

A column is P-rough exactly when it has no prime ideal divisor of norm <=P.
The partition consists of rough/rough (RR), exactly one rough (RA, both orders
already included), and neither rough (AA). These disjoint classes exhaust all
unordered pairs. If a column is rough, all allowed amplifiers are coprime to it.
Hence a_ij=A on RR pairs. Their mask-induced physical correction
`c_i*c_j*(a_ij-A)*V_ij` is identically zero, but D_ij need not vanish.
The correction is measured at the same P,H; it is not a difference against P0,
which changes the raw radius and mean.

Each group's physical term, subtracted raw term, signed D and mask correction
are retained. Absolute pair sums are optional diagnostics, not replacements for
C and not claims about its asymptotic upper bound. Verification requires interval
overlap with the saved C and with its physical/raw off-diagonal components;
residual intervals must contain zero and meet the stated precision tolerance.
This is numerical agreement of certified enclosures, not an assertion that the
new enclosure must be a subset of an older narrower enclosure.

## Period, primitive conductor and shared zero factor

For these squarefree columns put g=gcd(n_i,n_j). The full zero-extended period
is lcm(n_i,n_j), norm Q=q_i*q_j/q_g. The primitive quotient character has local
exponent +1 on n_i/g, -1 on n_j/g (reversed for the other orientation), and zero
on g. Each remaining local character is nontrivial modulo a good prime ideal,
so its primitive conductor is (n_i/g)*(n_j/g), norm q_i*q_j/q_g^2.
The canceled common primes still impose the zero factor g. Thus
`Q = norm(primitive conductor) * norm(shared zero factor)`.

This conductor description is restricted to the squarefree source used here;
it is not a formula for arbitrary higher exponents. Distinct columns imply a
nontrivial quotient conductor. The primitive character must not replace the
full zero-extended pair in a sum. Each saved pair retains the three ideal
factorizations, not just their norms.

H/Q is recorded for each pair using the actual H of its configuration. A
large H/Q diagnostic and a production configuration with small H/Q are distinct
regimes; decomposing this panel does not create a sample with both nonunit
amplification and production-scale long periods. CF22 remains unproved.

## Reproduce and inspect

Use the existing Python 3.12 / python-flint 0.9.0 environment. From repo root:

```sh
PY=/tmp/cf22-pysr-venv/bin/python
$PY -m unittest discover -s experiments/cf22_pysr/correlation -p 'test_*.py' -v
$PY experiments/cf22_pysr/correlation/decompose.py --output /tmp/cf22-pair-replay.json.gz
$PY experiments/cf22_pysr/correlation/verify_groups.py --decomposition /tmp/cf22-pair-replay.json.gz --output /tmp/cf22-pair-verification-replay.json
```

Output files must not already exist. The historical source/data pin is checked
against Git blobs; execution HEAD may be later. Input and implementation hashes
are checked for changes during calculation. No Julia, PySR, clang or native raw
counter execution is needed. `decomposition.json.gz` is deterministic compressed
JSON containing every pair, not a sample. `summary.json` provides compact group
intervals without per-pair expansion; `RESULT.md` provides the Russian report.

`verify_groups.py` independently computes masked group energies: |R|² and |A|²
minus their respective diagonals, and |R+A|²-|R|²-|A|² for the cross term.
It does not reuse the producer's physical pair assembly. It then subtracts each
group's saved raw contribution. `verification.json` retains every comparison.
`check_mask_return.py` compares the full correction against the old mask result
and checks the exact unit-phase distinction behind the U48/P7,P13 cross zeros.
`summarize.py` creates the compact summary. Derived-output scripts refuse to
replace existing files; preserve the shipped outputs when replaying.

The owner attachment is preserved verbatim, including its original Markdown
spacing and links. The linked sandbox-only full analysis was not available in
this local task. This implementation follows §6 of the supplied text and the
pinned source; it does not claim an independent audit of that full attachment.
