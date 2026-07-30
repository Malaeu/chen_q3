# RouteB.038 — generic-m Jacobi lift break list

```yaml
status: BREAK_LOCALIZED
replay_outcome: FINITE_NAMED_BREAK_LIST
algebraic_kernel: PASS
parametric_profile_identity: NOT_PROVED
primary_stop: SCALED_JACOBI_COFINAL_LIFT_GAP
sign_estimates_run: false
terminal_term_dropped: false
```

## What replayed exactly

The source-locked crosswalk survives the scaled substitution:

```text
z = a/m = a/lambda_m^2
sqrt(z/lambda_m) = sqrt(a)/lambda_m^(3/2)

E_star(h_{lambda_m},a/lambda_m)
  = -C_m * sqrt(a)/lambda_m^(3/2) * S_scaled_m(a),
  C_m = I0_m*I4_m/D_m > 0.
```

The checker also replays, with exact rational arithmetic, the common
three-term recurrence, the divided difference

```text
L_Theta4(delta) = ((Theta4-Theta0)/2) * b0,
```

the symmetrizer `omega_q=1/(4q+1)`, and the complete finite-`Q` Green ledger.
The terminal term is present and nonzero as a formal boundary monomial.

## Finite break list

| ID | File and line | Exact term | Why the generic profile replay stops |
|---|---|---|---|
| B038-1 | `coupled_full_sum_response_certificate.py:43-52`, `:691-698` | `M = 257`, `BANDS=(256,255)`, `scope.m=M`, `not_cofinal=True` | The only exact Ψ/δ coefficient backend is a finite `m=257` object. Replacing the label by symbolic `m` does not supply coefficient rows, spectral inputs, bands, or tail data for a cofinal family. |
| B038-2 | `priority_band_positive_part_certificate.py:224-227` | `if (L_Theta4 Y)_q=A_(r,q)(z)/omega_q` | The adjoint receiver `Y_{m,a}` is a conditional premise, not a source-locked construction for generic `m,a`. |
| B038-3 | `priority_band_positive_part_certificate.py:224-229` | `S_r=c<Y,b0>_omega+B` | The certificate never materializes a named exact `D_m(a)` whose whole expression includes forcing, normalization, lower boundary, and terminal boundary. Defining it from the desired sign is forbidden. |
| B038-4 | `031_priority_band_positive_part.answer.md:86-100` | finite-`Q` terminal `a_Q[Y_Q delta_(Q+1)-delta_Q Y_(Q+1)]` | The ledger is exact for every finite `Q`, but there is no source theorem coupling `Q→∞` to the sampled response while retaining or enclosing the live terminal remainder. |
| B038-5 | `check_priority_band_positive_part_certificate.py:211-237` | exact test values `g,Theta0,Theta4,last_q` | The checker verifies the algebraic identity at exact specializations. It does not source-lock `Theta4_m-Theta0_m>0` for the admissible cofinal family. |

Thus the algebraic Jacobi kernel is reusable, but

```text
S_scaled_m(a)
  = ((Theta4_m-Theta0_m)/2) * D_m(a)
```

does not replay as a current source-locked cofinal theorem.
`REPLAY_HOLDS_SYMBOLICALLY` and
`PARAMETRIC_SCALED_JACOBI_PROFILE_IDENTITY_PROVED` are not emitted.

## Live zero-consistent blocker

The exact unresolved whole-expression term is

```text
T_Q(m,a)
  = a_Q * (Y_Q*delta_(Q+1) - delta_Q*Y_(Q+1)),
  a_Q = omega_Q*r_(2Q).
```

With lower boundary coefficient `a_-1=omega_0*p_0=0`, the finite ledger gives
`B_Q=-T_Q`.  No source-locked generic enclosure or limiting identity fixes
the sign of `T_Q`; zero remains compatible.  Therefore the required
discriminator

```text
Gamma_m(4/3)
  = essInf_{a in [4/3,m]} D_m(a)
```

cannot be evaluated from the current certificate.

## Source-wording discrepancy

The 038 directive says the lower boundary is proved zero only from both
`a_minus_one=0` and `delta_0=0`.  The exact 031 displayed ledger has the
whole lower bracket multiplied by `a_-1=omega_0*p_0=0`; that factor alone
annihilates it.  The `delta_0=0` normalization remains true and essential
elsewhere, but it is redundant for this displayed lower-boundary product.
This discrepancy does not repair any generic-m break and does not authorize
dropping the terminal term.
