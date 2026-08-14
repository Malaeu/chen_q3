# Goal 058 G3 - DLMF 30.16/30.3 strict order and literal-root audit

Date: 2026-08-14

Repository: `/Users/emalam/GitHub/rh_lean_01_2026`

Branch: `rh_clean`

Audited pin: `a55e8839c324ceeabb43f1654409094624568352`

Lane: `CHALLENGER / NOT_RH`

Verdict:

```text
FINITE_LIMIT_IDENTITY_SOURCE_CONTRACT_LOCKED
STRICT_ORDER_AND_MIDPOINT_WINDOWS_SOURCE_CONTRACT_LOCKED
LITERAL_ROOT_CROSSWALK_MISSING
```

Success code for this packet:

```text
GOAL058_G3_STRICT_ORDER_WINDOW_SOURCE_PACKET_LOCKED
```

This is a source-acquisition and object-match packet.  It does not add a
production Lean declaration.

## 1. Primary-source locks

### DLMF

Live source checked against NIST DLMF Version 1.2.7, release date 2026-06-15.

| Source | Exact role | Fetched TeX SHA-256 |
|---|---|---|
| DLMF 30.2.1 | differential equation and `lambda` units | `6180ae03f7ce5e4b6836fd36b5de5aac32b20d7a35aef43cf4b9630e54294cd4` |
| DLMF 30.3.1 | strict differential eigenvalue order | `a65fff15dd2dad3b8b3ad3d146f81c57e569c85d94f9ac769cc6a60d7cef2a02` |
| DLMF 30.16.1a | finite matrix diagonal | `5ded12f503ce3a658a73687976926264d51aae185838993f0bc27b9cd1326f22` |
| DLMF 30.16.1b | finite matrix upper entry | `146c9d584200e12850b5bfa7cb2fea7b2e515aa63993080730da31070141506a` |
| DLMF 30.16.1c | finite matrix lower entry | `d194f48cbc8f81930dbf9546864a5e2041307f21024093a33a7091d40feffb5e` |
| DLMF 30.16.2 | depth monotonicity | `c0e5f1b968b4bcb1b61a6d72dcb739f6b8228c3934987b992595bc4168854cbd` |
| DLMF 30.16.3 | same-index finite-to-differential limit | `35b0b61b184dd56ecd3b17a20de6f9e13f00533b56fbfa0b4a6e544820629e4d` |
| DLMF 30.3.5 | classical continued-fraction equation | `f8cb8ef56617c5c4ecfa99749aaf1867b706825ab8162d414eb592b1dcce171a` |

Stable source links:

- <https://dlmf.nist.gov/30.2.E1>
- <https://dlmf.nist.gov/30.3.E1>
- <https://dlmf.nist.gov/30.16.E1>
- <https://dlmf.nist.gov/30.16.E2>
- <https://dlmf.nist.gov/30.16.E3>
- <https://dlmf.nist.gov/30.3.E5>

The selector attached to 30.16.3 is

```text
pDLMF = floor((n-m)/2) + 1.
```

DLMF 30.16 says that the matrix eigenvalues are real and arranged in
ascending order before giving 30.16.2 and 30.16.3.  The project does not rely
on the page's potentially ambiguous word `magnitude`: the Lean finite family
is independently constructed in ascending by-value order from the Hermitian
similar matrix.

### Bonami-Karoui alternate explicit separator

Local file:
`docs/routeB_bus/litreview/pdfs/1405.3676.pdf`

SHA-256:
`9fe8dc39e4440200a29ff94bb640b693c06a176d28b7e38a468dce98afa7d7b8`

Visual verification:

- PDF page 5 / printed page 5: equation (8), Theorem 1, equation (12);
- PDF page 6 / printed page 6: equation (13).

Theorem 1 gives, for `c>0` and `n>=2`, an explicit strict two-sided enclosure
for `sqrt(chi_n(c))` through the increasing elliptic-integral function.  It is
a valid stronger alternate source for explicit endpoints.  It is not needed
for the minimal midpoint construction below.  Equation (8) gives
`chi_4(c)-c^2 <= 20`, consistent with the project `Lambda <= 20` domain.

DLMF 30.16.4 is explicitly excluded as a certified separator: its
constant-free `O(...)` estimate does not supply the current formal bound.

## 2. Exact object dictionary

Use the following dictionary and no shifted substitute:

```text
DLMF order m                = 0
DLMF differential index n  = 2 * pLean
DLMF one-based selector     = pLean + 1
DLMF gamma^2                = G
project Lambda              = DLMF lambda
Bonami-Karoui chi           = Lambda + G
project Lambda              = chi - G
```

The unit conversion follows directly from DLMF 30.2.1 at `mu=0`:

```text
-((1-x^2) w')' + G*x^2*w = (lambda_DLMF + G)*w.
```

The project's literal finite matrix already uses `G=gamma^2` and
`Lambda=lambda_DLMF`; no additional `+G` belongs in its scalar shift.

The zero-based Lean row `q` corresponds to the DLMF one-based row `j=q+1`
and even Legendre degree `2q`.  This is recorded literally in
`D0Mode4DLMFEvenFiniteMatrix.lean`.  The file proves positive diagonal
similarity to the forward Hermitian matrix.  The full-carrier crosswalk proves
that the actual finite truncation has the same characteristic polynomial.

## 3. Finite-limit identity contract

DLMF 30.16.3 states

```text
lambda_n^m(gamma^2) = lim_(d -> infinity) alpha_(pDLMF,d).
```

At `m=0`, `n=2*pLean`, `gamma^2=G`, its selector is `pLean+1`.  The Lean
definition

```text
mode4ClassicalEvenEigenvalue G pLean
```

is the `iInf`, and hence the proved limit, of the same zero-based finite
eigenvalue family.  The exact external source contract is therefore

```text
mode4ClassicalEvenEigenvalue G p
  = DLMF lambda_(2*p)^0(G).
```

This contract is not circular because the right side is independently
defined by DLMF 30.3 as the bounded/entire solution spectrum of the
differential equation.  It must not be implemented by defining a new
`dlmfLambda` alias to the Lean `iInf`.

Formal Lean status: `NOT_READY`.  There is no independent differential
spectrum object in the current imports, so the source identity has not yet
been materialized as a kernel-checked equality theorem.

## 4. Strict order and arithmetic windows

DLMF 30.3.1 gives strict order of the classical differential eigenvalues.
Restricting to `m=0` and the even subsequence yields

```text
lambda_0^0(G) < lambda_2^0(G) < lambda_4^0(G) < lambda_6^0(G) < ... .
```

Combined with the source identity, this is the exact contract

```text
StrictMono (mode4ClassicalEvenEigenvalue G).
```

Finite strict ordering alone is insufficient: strict inequalities may
collapse under a limit.  The independent DLMF identity plus 30.3.1 is the
load-bearing source step.

Once that step and the already proved `carrier 2 < 20` are available, define

```text
c p = mode4ClassicalEvenEigenvalue G p
LambdaLower = (c 1 + c 2) / 2
LambdaUpper = (c 2 + min (c 3) 20) / 2.
```

Strict order and `c 2 < 20` imply

```text
c 0, c 1 < LambdaLower < c 2
c 0, c 1, c 2 < LambdaUpper < c 3
LambdaUpper < 20.
```

H5 then derives eventual finite counts `2` and `3`.  Those counts are outputs,
not assumptions.  The midpoint construction is source-independent ordered
field arithmetic once strict order exists.

## 5. Literal-root avoidance audit

Requested discriminator:

```text
LITERAL_ROOT_CROSSWALK_MISSING
```

What is already kernel checked:

1. `det_mode4HermitianSchurMatrix_eq_schurContinuant` identifies the literal
   Hermitian Schur determinant with the scalar Schur continuant.
2. `mode4SchurContinuant_eq_upperProd_mul_rootFunction` factors that
   continuant as a strictly positive upper product times
   `mode4RootFunction` in the production domain.
3. Hence `det Schur = 0 <-> mode4RootFunction = 0` is locally derivable.
4. `mode4DLMF3084_3085_degreeFour_coefficients_force_root` proves only a
   one-way statement from an already supplied normalized classical
   coefficient row to the project root.

What is absent:

```text
mode4RootFunction mProject K Lambda = 0
  <-> exists p,
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p = Lambda.
```

In particular, the tree has no converse extracting an independently indexed
DLMF mode from an arbitrary project root, and it does not construct the
classical coefficient row consumed by the existing one-way bridge.

DLMF 30.3.5 is a promising primary-source pin: its even continued-fraction
equation has exactly the classical values
`lambda_(m+2j)^m(gamma^2)` as solutions.  However the current tree does not
prove that the project's Legendre/Jacobi root function is exactly that DLMF
30.3.5 continued fraction.  Their coefficient presentations are different,
so this identification cannot be asserted by notation alone.

Therefore endpoint inequalities do not yet imply the required `hdet`.  The
missing noncircular source bridge is an exact equivalence between the project
recessive-tail matching equation and the independent even differential
spectrum, followed by the already local determinant factorization.

## 6. Mandatory falsifiers

| Plant | Rejected mutation | Stop code |
|---|---|---|
| P1 | define the classical spectrum as the same finite `iInf` | `G3_CLASSICAL_CARRIER_TAUTOLOGICAL_REDEFINITION` |
| P2 | replace project `Lambda` by `chi` or `Lambda+G` | `G3_DLMF_PROJECT_SHIFT_MISMATCH` |
| P3 | infer strict limit order from finite strict order alone | `G3_FINITE_STRICT_ORDER_LIMIT_COLLAPSE` |
| P4 | infer `hdet` only from endpoint inequalities | `G3_SEPARATOR_DOES_NOT_YET_SUPPLY_LITERAL_NONSINGULARITY` |
| P5 | use DLMF 30.16.4 big-O without an explicit constant | `G3_CONSTANT_FREE_ASYMPTOTIC_NOT_CERTIFICATE` |

## 7. Exact next boundary

The source contract for finite-limit identity, strict order, and midpoint
windows is locked.  The next production theorem is still `NOT_READY` because
the current Lean graph has neither an independent differential spectrum
carrier nor the project-root/DLMF-spectrum equivalence.

Typed stop:

```text
G3_DLMF_STRICT_ORDER_SOURCE_LOCKED_LITERAL_ROOT_CROSSWALK_MISSING
```

Nonclaims:

```text
G1 OPEN
G3 OPEN
NO ENDPOINT COUNTS IN LEAN YET
NO ROOT EXISTENCE
NO INDEX4 IDENTIFICATION
NO ARISTOTLE
NO ROUTE PROMOTION
NO RH CLAIM
```
