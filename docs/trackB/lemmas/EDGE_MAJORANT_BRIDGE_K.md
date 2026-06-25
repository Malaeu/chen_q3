# Track B E5p Lemma Audit: `edge_majorant_bridge_K`

Status: `KERNEL_MISMATCH`.

This file is the requested proof attempt for the edge-majorant bridge.  It is
not a Lean proof file, not an E5p closure claim, and not a use of tiny-B
`c_arch` JSON as a `mu_K` source.

Final verdict:

```text
edge_majorant_bridge_K is NOT proved.
Exact failure: KERNEL_MISMATCH.
Advisory route review: CHOSEN: B, replace the scalar-majorant route by a
direct interval/rational projected PSD certificate in Track B units.
```

The scalar Selberg/CLV majorant can be defined and gives the required
pointwise majorization on prime nodes.  The proof fails at line 3: the current
majorant is not proved to be admissible for the Q3 A3 / Toeplitz bridge, and
local Track B evidence shows that pointwise majorants do not transport to the
packet operator order.

Browser/Proshka advisory review on 2026-06-24 independently selected route B:
pointwise majorization does not transport to projected B-spline packet Loewner
order, so continuing to tune scalar `Psi_K` is the wrong patch.  The recommended
next proof object is a direct interval/rational projected PSD certificate in the
Track B `G_K` / `ker(Q_K)` normalization.  This advisory output is not proof
evidence; it only confirms the local route choice already supported below.

---

## Target Lemma

For each active Track B cell

```text
K_TB in {2, 3, 3.5},
```

prove a lemma of the form:

```text
edge_majorant_bridge_K:
  alpha_K * R_K - Loss_K >= mu_cert,K
```

where:

```text
mu_cert,2   = 0.45
mu_cert,3   = 0.51
mu_cert,3.5 = 0.75.
```

The requested proof chain was:

1. define `Psi_K`;
2. prove `Psi_K(xi_n) >= 1_[K/pi,2K/pi](xi_n)`;
3. prove `Psi_K` is admissible for Q3 A3 / Toeplitz bridge;
4. compute Arch reserve `R_K` for `Psi_K`;
5. prove norm transfer to `G_K`:

   ```text
   ||J_K v||^2 >= alpha_K v^T G_K v;
   ```

6. subtract all losses;
7. prove:

   ```text
   alpha_K * R_K - Loss_K >= 0.45 / 0.51 / 0.75.
   ```

The first failing line is line 3.

---

## Sources Checked

Commands used:

```bash
rg -n "edge_majorant|Psi_K|majorant|Toeplitz|Q3A3|crosswalk|J_K|norm transfer|alpha_K" \
  docs/trackB trackB scripts Q3 q3.lean.aristotle \
  /Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/sections \
  /Users/emalam/Documents/GitHub/RH_2025_V3_October/cert/bridge

./scripts/research_oracle.py query \
  "Track B E5p edge majorant bridge Psi K norm transfer J_K" -c q3_docs

./scripts/research_oracle.py query \
  "Selberg CLV edge majorant cone transport Track B E5p" -c q3_docs

./scripts/research_oracle.py query \
  "Q3 A3 Toeplitz bridge Fejer heat admissible edge interval majorant" -c q3_docs

./scripts/research_oracle.py query \
  "B spline packet G norm Toeplitz norm transfer Track B" -c q3_docs
```

Most relevant local files read:

| File | Relevance |
| --- | --- |
| `docs/trackB/clv_pair.md` | Defines the Selberg/Vaaler interval majorant and proves pointwise `M^- <= chi_I <= M^+`. |
| `docs/trackB/b2b_explicit_formula_route_gap.md` | Shows ordinary Selberg pointwise majorant is not a cone/operator proof. |
| `docs/trackB/b2b_admissible_lift_audit.md` | Isolates the missing admissible lift, not just pointwise majorization. |
| `docs/trackB/b2_psd_gaussian_majorant_probe.md` | Shows even a pointwise positive Gaussian PSD-friendly majorant fails finite packet operator order. |
| `docs/trackB/b2_cone_transport_probe.md` | Shows ordinary Selberg transport only survives an ultra-low-band window, not the current packet cone. |
| `docs/trackB/TRACKB_E5P_MATH_APPARATUS.md` | Defines the C0--C5 crosswalk and the required `J_K` norm transfer. |
| `q3.lean.aristotle/Q3/Proofs/P_A_Toeplitz_bridge_defs.lean` | Q3 A3 bridge is Fourier Toeplitz with `P_A`, not a scalar edge majorant. |
| `q3.lean.aristotle/Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` | One-scale A3 bridge consumes `P_A(B_min,t)` and `T_P_comp_real`, not Track B B-spline packets. |
| `q3.lean.aristotle/Q3/Proofs/A1_density.lean` | Shows Q3 admissible atom cone is built from Fejer-heat atoms. |
| `/Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/sections/A3/local_positivity.tex` | A3 local positivity assumes a Toeplitz symbol and compatible trigonometric polynomial support. |
| `/Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/sections/Main_closure.tex` | Q3 A3 participates in the Fejer-heat / Toeplitz / RKHS compact chain. |

No web result is used as proof evidence.

---

## 1. Definition Of `Psi_K`

The only local unconditional edge-majorant object found is the Selberg/Vaaler
interval majorant from `docs/trackB/clv_pair.md`.

For an interval `I=[a,b]` and bandwidth `delta>0`, define:

```text
M^+_{I,delta}(z)
  =  1/2 * H0(delta*(z-a))
   - 1/2 * H0(delta*(z-b))
   + 1/2 * K0(delta*(z-a))
   + 1/2 * K0(delta*(z-b)).
```

The Track B raw-log edge is:

```text
I_TB^a(K) = [2K, 4K].
```

The corresponding Q3 node interval is:

```text
I_TB^xi(K) = [K/pi, 2K/pi].
```

Define the one-sided candidate:

```text
Psi_K^+(xi) := M^+_{[K/pi, 2K/pi], delta}(xi).
```

If an even Q3 test is required, define the evenized scalar candidate:

```text
Psi_K^sym(xi)
  := M^+_{[K/pi, 2K/pi], delta}(xi)
     + M^+_{[-2K/pi, -K/pi], delta}(xi).
```

This satisfies line 1 as a scalar function definition.  It does not yet say
that `Psi_K` is a Q3 A3 admissible Fejer-heat / Toeplitz object.

---

## 2. Pointwise Majorization On Prime Nodes

The Selberg/Vaaler theorem recorded in `docs/trackB/clv_pair.md` proves:

```text
M^-_{I,delta}(x) <= chi_I(x) <= M^+_{I,delta}(x)
```

for every real `x`.

Therefore, for Q3 nodes:

```text
xi_n = log n / (2*pi),
```

we get:

```text
Psi_K^+(xi_n) >= 1_[K/pi, 2K/pi](xi_n).
```

The active intervals are:

| `K_TB` | raw-log edge `[2K,4K]` | Q3 node interval `[K/pi,2K/pi]` | first integer Q3 window covering it |
| ---: | --- | --- | ---: |
| 2 | `[4,8]` | `[0.6366197723675814, 1.2732395447351628]` | 2 |
| 3 | `[6,12]` | `[0.954929658551372, 1.909859317102744]` | 2 |
| 3.5 | `[7,14]` | `[1.1140846016432675, 2.228169203286535]` | 3 |

Line 2 passes for the scalar majorant.

---

## 3. Q3 A3 / Toeplitz Admissibility

This line fails.

Q3 A3 does not consume an arbitrary scalar interval majorant.  The local Lean
and paper artifacts show that A3 is a Fourier Toeplitz bridge with an
Archimedean symbol `P_A` and a compatible prime operator:

```text
RayleighQuotient
  (ToeplitzMatrix_Fourier_real (...) (P_A B_min t_sym)
   - T_P_comp_real K K t M) v
>= c_star / 4.
```

The Q3 admissible atom/cone layer is built from Fejer-heat atoms, not from an
arbitrary Selberg interval majorant:

```text
Fejer_heat_atom B t tau
AtomCone_K
```

The old Q3 2025 paper says the same thing in paper form: local positivity
requires a Lipschitz Toeplitz symbol `P_A` and a trigonometric polynomial
supported compatibly with the window defining the positive arc.

No local artifact proves:

```text
Psi_K^+ or Psi_K^sym is a Q3 A3 admissible Fejer-heat / Toeplitz symbol
```

or:

```text
Q3 A3 applied to Psi_K yields a Track B edge-majorant budget.
```

Worse, Track B already has negative evidence against treating pointwise
majorants as operator majorants:

1. `docs/trackB/b2b_explicit_formula_route_gap.md` records that the ordinary
   symmetric Selberg majorant for K=2 has sign-changing Fourier transform:

   ```text
   min hat(M^+_sym) ~= -7.5273 near u ~= -0.07852.
   ```

2. `docs/trackB/b2_cone_transport_probe.md` records that the ordinary Selberg
   transport band survives only at about:

   ```text
   |u| < 1/(12K),
   ```

   while the current Step13 packet spectrum is not concentrated there.

3. `docs/trackB/b2_psd_gaussian_majorant_probe.md` shows that even a
   pointwise Gaussian majorant with nonnegative Fourier transform does not
   imply the required finite packet operator order.  For K=2, the projected
   matrix `N^T(P_W-P_edge)N` has generalized eigenvalue minimum:

   ```text
   -3.477462109260e+05.
   ```

This is exactly the distinction the current E5p apparatus warns about:

```text
pointwise edge majorant != Track B packet operator majorant
```

Therefore line 3 fails with:

```text
KERNEL_MISMATCH
```

---

## 4. Arch Reserve `R_K`

Not reached as a proof step.

The Q3 A3 lock constants are not `R_K` for this `Psi_K`.  They belong to the
Q3 Toeplitz/RKHS chain and become usable for Track B only after proving the
operator/norm/ledger crosswalk.

The conservative lock data from the previous audit are:

| Q3 K | lock `c0` | Validity |
| ---: | ---: | --- |
| 2 | `0.9028668493703329` | candidate source only |
| 3 | `0.9043681970359332` | candidate source only |
| 4 | `0.9050660039059131` | candidate source only |

These are not used here as `mu_K`, and the larger raw floor values near `5.37`
are not used at all.

Current status:

```text
R_K(Psi_K) = GAP because Psi_K is not proved A3-admissible.
```

---

## 5. Norm Transfer To `G_K`

Not reached as a proof step, and currently absent in the repository.

The required theorem would be:

```text
exists J_K, exists alpha_K > 0,
  ||J_K v||^2 >= alpha_K * v^T G_K v
```

for the same vectors `v` used by the Track B B-spline packet backend.

The local search found no theorem, certificate, or script output defining a
map:

```text
J_K : TrackB B-spline packet space -> Q3 Toeplitz polynomial space
```

with a proof-grade lower norm bound.  If line 3 were repaired, this would be
the next likely blocker:

```text
NORM_TRANSFER_GAP
```

But the exact current failure remains earlier:

```text
KERNEL_MISMATCH
```

---

## 6. Loss Ledger

Not reached.

A valid loss ledger would need to subtract, in the same units:

```text
Loss_K =
  kernel/admissibility loss
  + coordinate/weight transfer loss
  + basis/norm transfer loss
  + nonedge support loss
  + tail loss
  + boundary loss
  + already-spent reserve loss.
```

No local file supplies this loss table for the `Psi_K` defined above.

---

## 7. Threshold Comparison

Not reached.

The requested final inequalities are:

```text
K=2:   alpha_K R_K - Loss_K >= 0.45
K=3:   alpha_K R_K - Loss_K >= 0.51
K=3.5: alpha_K R_K - Loss_K >= 0.75
```

They cannot be evaluated, because:

```text
R_K is not defined for an A3-admissible Psi_K,
alpha_K is not proved,
Loss_K is not available.
```

This is not `CONSTANT_THRESHOLD_FAIL`; the comparison has not reached same-unit
constants.

---

## K-by-K Verdict

| `K_TB` | line 1 define `Psi_K` | line 2 node majorant | line 3 A3 admissible | final verdict |
| ---: | --- | --- | --- | --- |
| 2 | PASS with Selberg/Vaaler scalar `M^+` | PASS pointwise | FAIL: not Q3 A3 Fejer-heat / Toeplitz admissible; prior finite evidence rejects pointwise-to-operator shortcut | `KERNEL_MISMATCH` |
| 3 | PASS with Selberg/Vaaler scalar `M^+` | PASS pointwise | FAIL: same structural mismatch | `KERNEL_MISMATCH` |
| 3.5 | PASS with Selberg/Vaaler scalar `M^+` | PASS pointwise | FAIL: same structural mismatch | `KERNEL_MISMATCH` |

---

## What Would Repair The Lemma

One of the following is required:

1. Construct `Psi_K` inside the Q3 Fejer-heat / Fourier Toeplitz admissible
   class and prove it majorizes the Track B edge operator, not merely the edge
   indicator pointwise.  Current route status: not recommended; local evidence
   and advisory review both classify this as the scalar-majorant swamp.

2. Prove a direct projected finite operator majorant:

   ```text
   N^T(P_Psi - P_edge)N >= 0
   ```

   in the Track B `G_K` normalization, with interval/rational certificate
   quality.  Current route status: recommended next patch.

3. Construct and certify the norm-transfer map:

   ```text
   J_K : V_K -> P_M
   ```

   plus:

   ```text
   ||J_K v||^2 >= alpha_K v^T G_K v.
   ```

Only after one of these repairs can `R_K`, `Loss_K`, and the threshold
comparison be meaningful.

The exact next patch should therefore be a certificate generator and audit for
the direct projected PSD object, not a new Lean theorem stub.  The expected
gap label for that patch is:

```text
TRACKB_E5P_EDGE_PROJECTED_PSD_CERT_GAP
```

---

## Decision

```text
[TRACK B BLOCKER]
claim: edge_majorant_bridge_K proves analytic mu_K from a scalar edge majorant
node: Track B / E5p / mu-normalization
obstruction: pointwise majorization does not imply Q3 A3 admissibility or Track B packet operator domination
file/theorem: docs/trackB/lemmas/EDGE_MAJORANT_BRIDGE_K.md / edge_majorant_bridge_K
normalization: raw edge [2K,4K] maps to xi interval [K/pi,2K/pi]; weights still require operator-level bridge
tried: Selberg/Vaaler M^+ as Psi_K; Q3 A3 artifacts; prior Selberg/Gaussian cone-transport probes
witness/numbers: K=2 Selberg symmetric majorant Fourier min about -7.5273; Gaussian K=2 projected operator min about -3.477e5; xi intervals listed above
repairs: build A3-admissible Psi_K, or direct projected finite operator majorant, then prove J_K norm transfer
decision: KERNEL_MISMATCH
```
