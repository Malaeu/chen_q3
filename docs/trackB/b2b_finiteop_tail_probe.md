# Track B B2b: Finite-Op + CLV-Tail Probe

Status: B2 numerical/theorem-shape probe.  This is not a proof certificate and
does not close E5p.  It tests the fallback branch left after the
cost-controlled admissible-lift wall:

```text
compact edge defect -> direct finite projected operator certificate,
tail / continuum leakage -> CLV-Selberg control only where cone structure is
already preserved.
```

## D2 Normalization

Raw variable:

```text
a = r * log p,
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

The probe stays in raw-log coordinates and reports `xi` only as a diagnostic.
No extra factor `2` is inserted into the Step13 raw prime weights.

## Allowed Inputs

- `UNCONDITIONAL / finite-dimensional linear algebra`: for a fixed projected
  packet model, the symmetric generalized eigenvalue bound certifies

  ```text
  lambda_min * G <= P_edge - P0_edge <= lambda_max * G.
  ```

  This is only a finite projected model certificate, not a theorem-level E5p
  proof.

- `UNCONDITIONAL`: Selberg/Vaaler/CLV extremal-function tools from
  `docs/trackB/clv_pair.md`.  In this branch they are reserved for tail,
  leakage, or continuum transfer terms.  They are not used to claim Loewner
  order for the signed edge kernel.

Forbidden inputs remain unchanged: no RH/GRH, no FQ-transfer, no de Branges
positivity, and no RH-conditional prime-gap theorem as a theorem input.

## Local Search Synthesis

`q3_docs` search before this probe pointed to three reusable constraints:

1. Finite certificates are acceptable only as corrected-cone / projected
   packet certificates; broad-cone scalar positivity is already rejected.
2. Old grid-to-continuum material is useful as a transfer pattern, but it
   cannot be imported blindly because Track B is about the edge defect on the
   structured cross-correlation cone.
3. The local finite-cap notes support separating a compact finite object from
   tail/leakage terms.  That matches this branch better than another scalar
   majorant dictionary.

The external source check did not add a new theorem input.  It only reconfirmed
the safe background:

- CLV Gaussian subordination is unconditional.
- Vaaler/Selberg interval extremals are unconditional.
- Autocorrelation positive-definiteness is the square-modulus Fourier
  mechanism.

## Probe

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py finiteop \
  --K 2 --p0-na 8001 --top 12
```

The new `finiteop` mode computes

```text
A_K = G^{-1/2} N^T(P_edge - P0_edge)N G^{-1/2}
```

and reports `lambda_min(A_K)`, `lambda_max(A_K)`, plus a Rayleigh breakdown of
the upper and lower worst eigenvectors by prime-power shift.

For fixed `K` this gives the exact finite projected inequality

```text
lambda_min(A_K) * <v,Gv>
  <= <v,(P_edge-P0_edge)v>
  <= lambda_max(A_K) * <v,Gv>
```

inside the Step13 projected model.

## K=2 Result

With Step13 packet parameters

```text
ell = 0.35,
grid delta = 0.5,
k_spline = 5,
kerQ_dim = 14,
edge shifts = 441,
```

the finite projected certificate is

```text
lambda_min = -0.4416718760986586
lambda_max =  0.43707976289804495
two_sided_epsilon = 0.4416718760986586
```

The Rayleigh reconstruction checks close numerically:

```text
upper lambda check error ~= 1.1e-16
lower lambda check error ~= 9.4e-16
```

Prime-power concentration:

```text
upper worst:
  r=1 ordinary primes carry 97.314% of absolute prime-shift mass;
  top 12 shifts carry 18.748% of absolute mass.

lower worst:
  r=1 ordinary primes carry 97.372% of absolute prime-shift mass;
  top 12 shifts carry 17.850% of absolute mass.
```

So the K=2 finite defect is not caused by a tiny exceptional set of prime
powers.  It is already a distributed ordinary-prime phenomenon.

Representative upper-worst shifts:

```text
p=89,  a=4.4886363697, contribution=-0.3780994932
p=59,  a=4.0775374439, contribution=-0.3609532583
p=83,  a=4.4188406078, contribution=-0.3077261213
p=97,  a=4.5747109785, contribution=-0.3049598075
p=61,  a=4.1108738642, contribution=-0.2876321571
```

## K=1..3 Scale Snapshot

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py finiteop \
  --K 1 2 3 --p0-na 2001 --top 5
```

Result:

```text
K=1:
  edge shifts = 19
  two_sided_epsilon ~= 0.232991
  top 5 absolute shifts carry ~= 81.3% of upper-worst prime mass
  r=1 primes carry ~= 84.9%

K=2:
  edge shifts = 441
  two_sided_epsilon ~= 0.441671
  top 5 absolute shifts carry ~= 10.1% of upper-worst prime mass
  r=1 primes carry ~= 97.3%

K=3:
  edge shifts = 14942
  two_sided_epsilon ~= 0.498476
  top 5 absolute shifts carry ~= 0.535% of upper-worst prime mass
  r=1 primes carry ~= 99.4%
```

Interpretation:

- At K=1 the finite defect is still small enough to look local.
- By K=2 and K=3 the defect is spread across the ordinary prime comb.
- Therefore a finite certificate that removes only a handful of bad shifts is
  not the right theorem shape.
- The measured `two_sided_epsilon` is not showing the desired
  `C*K^{-c}` decay in this raw Step13 model.

Follow-up:

- `docs/trackB/b2b_packet_scale_sweep.md` checks whether this is merely a
  fixed-packet-width artifact.  Increasing `ell` from `0.35` to about
  `0.5..1.0` substantially lowers the finite epsilon for K=2 and K=3, but the
  non-degenerate values plateau near `0.10..0.11`.  Very wide packets can force
  smaller values only by collapsing `kerQ_dim` or by producing nearly singular
  projected Gram matrices under refinement.

## Verdict

`PARTIAL(finite projected certificate exists)`.

But this branch does not yet close E5p:

```text
B2-GAP(normalized packet theorem or uniform finite-op prime-mean estimate)
```

The useful wall has moved again:

```text
old wall: find a cost-controlled admissible lift.
new wall: find a stable normalized packet family with finite epsilon decay,
          or turn the finite eigenvalue certificate into a uniform structured
          ordinary-prime mean estimate.
```

## Proshka Update

Claim:
The direct finite projected operator certificate exists for each fixed Step13
packet model, but the K=2 and K=3 worst eigenvectors are distributed over the
ordinary prime comb, not concentrated on a few removable shifts.

Point of blockage:
`FINITE-OP + CLV-tail` needs a uniform theorem controlling the whole
ordinary-prime mean on the structured cross-correlation cone.  A finite
exception-list certificate will not scale.

What was tried:
- Added `finiteop` mode to `scripts/trackb_edge_operator_probe.py`.
- Computed exact projected eigenvalue certificates for K=1,2,3.
- Decomposed upper/lower worst eigenvectors by prime-power shifts.

Minimal example:
`K=2`, raw edge `[4,8]`, Step13 parameters `ell=0.35`, grid `0.5`,
`k_spline=5`.  The finite certificate gives
`two_sided_epsilon≈0.4416718761`; ordinary primes (`r=1`) carry about `97%`
of the absolute prime-shift mass, while the top 12 shifts carry only about
`18-19%`.

Question for Proshka:
Should the next theorem shape be a structured ordinary-prime mean estimate on
the cross-correlation cone, or should Track B first change the packet
normalization/family so the finite projected epsilon has visible `K^{-c}`
decay before trying a CLV-tail transfer?
