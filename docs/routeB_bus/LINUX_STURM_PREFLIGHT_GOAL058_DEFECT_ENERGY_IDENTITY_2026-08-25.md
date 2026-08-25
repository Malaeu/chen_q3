# STATUS: STURM_PREFLIGHT — EXACT ENERGY IDENTITY PRODUCTIVE; TARGET REACHED IN WEIGHTED FORM; RESIDUAL COMPRESSED TO ONE SLIVER INPUT

```yaml
ARTIFACT_CLASS: LINUX_STURM_PREFLIGHT
GOAL: GOAL_058
GAP: W5_PACKET_DEFECT_DERIVATIVE_L2_RATE
PARENT_VERDICT: dee1ec4d (L2/Sturm selected primary)
DISCRIMINATOR: STURM_FROM_COMMITTED_C0_AND_EIGENVALUE_DEFECT
DISCRIMINATOR_OUTCOME: PARTIAL_PASS_WEIGHTED / literal unweighted lambda^-4 NOT reached
P_DERIV_STURM_1_ADJUDICATION: CONFIRMED (improvement is lambda^2-scale, far beyond sqrt(lambda); the obstruction isolates to one exact edge object)
AUTHOR_BODY: LINUX_CLAUDE (LINUX_STANDING_GRANT_2026-08-25)
RH_CLAIM: false
```

## 1. Exact operator identity (from the committed eigenrelation)

Committed (`normalizedPhysicalMode_prolateWaveExpression_eigenrelation`):
on the open window, `-((lam^2 - x^2) phi')' + (2 pi lam x)^2 phi = theta * phi`,
`theta = Lambda + mode4JacobiG(m)`.  Dividing by `lam^2` and using
`-lam^2 phi'' + (x^2 phi')' = -((lam^2 - x^2) phi')'` EXACTLY:

```
(1/lam^2) L_prol = L_cyl + (1/lam^2) * d/dx (x^2 * d/dx),
L_cyl := -d^2/dx^2 + 4 pi^2 x^2.
```

The cylinder target `W(x) = D_n(sqrt(4 pi) x)` satisfies `L_cyl W = mu_n W`
with `mu_n = 4 pi (n + 1/2)` (exact rescaling of the parabolic cylinder ODE).

## 2. The defect equation with the transport moved LEFT

`delta := phi - W`, `eps := theta / lam^2 - mu`.  Splitting `phi' = delta' + W'`:

```
-(1/lam^2) * ((lam^2 - x^2) delta')' + (4 pi^2 x^2 - mu) delta
    = eps * phi - (1/lam^2) * (x^2 W')'.
```

The left side is EXACTLY the (1/lam^2)-scaled prolate-weighted operator on
delta: the source-faithful move — the defect inherits the degenerate weight.

## 3. The energy identity (test with conj(delta), window (-lam, lam))

```
(1/lam^2) INT (lam^2 - x^2) |delta'|^2
  + INT (4 pi^2 x^2 - mu)_+ |delta|^2
  = INT_core (mu - 4 pi^2 x^2)_+ |delta|^2
    + eps * INT phi conj(delta)
    - (1/lam^2) * INT (x^2 W')' conj(delta)
    + FLUX,
FLUX = (1/lam^2) * [(lam^2 - x^2) delta' conj(delta)] at +-lam = 0
```

**The flux vanishes IDENTICALLY**: the prolate weight degenerates at the
window edge.  No endpoint slope, no periodic trace, no seam hypothesis —
the C13-shadow is carried by the weight itself.  (Only local boundedness of
delta' at the edge is used, which the finite Ferrers truncation has per k.)

## 4. Ledger with committed data

* Core term: `(mu - 4 pi^2 x^2)_+` is supported on `|x| <= sqrt(mu)/(2 pi) = O(1)`;
  with the committed uniform C0 rate `|delta| <= C/lam^2`:
  `<= mu * 2 x_mu * C^2 / lam^4 = O(lam^-4)`.  The sign of the cylinder
  potential pays the WHOLE bulk — my registered fork (potential bulk as
  lambda^-1 culprit) is retracted: that scaling was an artifact of ignoring
  the sign.
* eps-term: `|eps * INT phi conj(delta)| <= |eps| * ||phi||_L1 * C / lam^2`;
  `||phi||_L1 = O(1)` from F72.6 (`|phi| <= |D_n(proj)| + C/lam^2` integrated);
  with the F72.3B eigenvalue-defect rate `|eps| <= C_eps / lam^2` (typed,
  committed input family): `O(lam^-4)`.
* W-transport: `(1/lam^2) * ||(x^2 W')'||_L1(R) * C/lam^2 = O(lam^-4)`;
  `W` is the EXPLICIT cylinder profile — its `L^1` constant is absolute and
  Lean-ready by exactly the technique of the closed H-node (17d7a5a8).

## 5. Output and the honest gap

**Weighted defect-energy rate (conditional on C0 + F72.3B only):**

```
INT_{-lam}^{lam} (lam^2 - x^2) * |delta'(x)|^2 dx <= C_E^2 / lam^2.
```

Consequences: on `|x| <= lam - 1/lam` this already gives
`INT (lam - |x|) |delta'|^2 <= C/lam^3` and `INT_{|x| <= lam - 1} |delta'|^2 <= C/lam^3`.
The LITERAL target `||delta'||_2^2 <= C/lam^4` (unweighted, whole window) is
NOT produced: the weight vanishes exactly on the edge sliver.

## 6. Consumer re-examination (the decisive part)

The Cauchy–Schwarz consumer map should consume the WEIGHTED energy, not the
unweighted norm.  Splitting the defect comb `sum (n u) delta'(n u)` with the
weight `(lam^2 - y^2)`: the companion factor
`sum n^2 u^2 / (lam^2 - n^2 u^2) ~ (lam/u) * log(lam/u)`, and the budget
integral closes UP TO the single topmost lattice point per u
(`y_top in (lam - u, lam]`).  Iterating the weight down to the last
`1/lam`-neighborhood: everything except the final sliver
`(lam - 1/lam, lam]` is paid by the weighted energy with room to spare
(the sliver-free part contributes `O(sqrt(log lam / lam))` to the budget).

**The entire derivative wall therefore compresses to ONE new named input:**

```
W5_DEFECT_EDGE_SLIVER_SLOPE:
  sup_{y in (lam - 1/lam, lam]} |delta'(y)| <= C_s / sqrt(lam).
```

Compare with the killed uniform C1 candidate (`C/sqrt(lam)` on the WHOLE
window): same rate but required only on an `O(1/lam)`-length sliver at the
window edge — dramatically weaker.  On that sliver the mode is a finite
even-Legendre truncation; its edge slope is exactly the signed second-moment
row `sum a_q * q(2q+1)`-type object, and the F72.6 machinery may already
constrain it near the edge via the same Gaussian-target smallness that paid
the seam ledger (H'(y) is Gaussian-small at y ~ lam, so the sliver slope of
delta equals the sliver slope of phi up to O(exp(-c lam^2))).

## 7. Proposed node order (for ratification)

1. STURM_ENERGY_NODE (Lean): the identity of Section 3 + ledger of Section 4,
   output = the weighted energy rate; inputs: F72.6 C0, F72.3B eigenvalue
   rate.  No new analytic supplier.
2. W_TRANSPORT_L1_NODE (Lean, unconditional): `||(x^2 W')'||_L1 <= const`,
   H-node technique.
3. WEIGHTED_CONSUMER_NODE (Lean): the weighted Cauchy–Schwarz comb map of
   Section 6, consuming (1) and emitting the defect budget up to the sliver
   term.
4. The sliver input: either judge sources it (edge behaviour of the Fuchs /
   Ferrers solution near the turning point), or it stays the single named
   open supplier of the whole derivative wall.

CLOSES: STURM_FROM_COMMITTED_C0_AND_EIGENVALUE_DEFECT (adjudicated: weighted
PASS), MY_REGISTERED_POTENTIAL_BULK_FORK (retracted — sign pays it).
OPENS: W5_DEFECT_EDGE_SLIVER_SLOPE (single residual input).
