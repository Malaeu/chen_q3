# Q3 — GOAL057_SOURCE_WEIL_EVEN_SECTOR_SPECTRAL_CUT_PREFLIGHT — result for review

```yaml
scope: read-only experimental; not a route claim; not RH; not finite-to-global
route: CHALLENGER_NOT_RH
commit: 133908a (branch claude/ricci-flows-proof-search-emucjh)
evidence_sha256:
  results_spectral_cut.json: 3aa0dbf1988bab0b9ce371ade5389502cd273b062e77d31d8c712f95feb0fa47
  PRECOMMIT.md:               02a39bf81853cd4294436cda3cbcba03529110fa5265d1d129ef0ea52b3e4373
```

## What was asked

Your prior verdict (V0 navigator killed; V0.1 quarantined) selected
`RUN_GOAL057_SOURCE_WEIL_EVEN_SECTOR_SPECTRAL_CUT_PREFLIGHT`: build the exact
finite CCM source matrix `K = ccmWeilMatFinite(m,N)`, reduce to the even
sector via the exact reversal involution `J`, use a Fiedler min-conductance
graph cut as a **candidate generator only**, and judge every candidate by the
true signed cross-block operator norm `epsilon = ||E||_op`, spectral
separation `delta = dist(a, Spec B)`, `rho = epsilon/delta`,
`s = epsilon^2/delta`, at control cell `(m,N)=(13,60)`, stopping immediately
if it fails there.

All thresholds, instrument pins, plants and the stop rule were frozen in
`PRECOMMIT.md` and committed **before** the first real-matrix run (git-provable
ordering: commit `22a4575` precedes the result commit `133908a`).

## What ran

Independent Python/mpmath transcription of the literal Lean formulas
(`ccmWeilTauN1 = W02 - WR - Prime`, PSWF pair `(psi0,psi4)` via Legendre
diagonalization, `E*` summation, `kTrial_m_N` normalization), source-locked
to 8 Lean files by sha256, spot-checked bit-for-bit against the literal
Lean formula (12 random pairs, rel diff ~6e-33).

**Plants — all PASS**, run before interpreting the real matrix:
block-diagonal recovery, one-bridge control, prime-sign mutation (rejected by
the source-lock gate), label permutation, ±1 diagonal sign conjugation.

**Phase-0 gates — all PASS**: mode order, symmetry residual, `J`-commutation
residual (both at floor ~1e-15..1e-30), PSWF ODE residual (~5e-13), psi0⊥psi4
orthogonality, `int hTrial = 0` exactly, `||kTrial|| = 1` exactly.

## Result at (13,60) — dim=61 even sector

```text
Fiedler candidate (min-conductance sweep):
  phi (graph conductance) = 0.0313   <= 0.25 "meaningful": PASS
  mu  (retained trial mass) = 1.0    >= 0.95: PASS
  epsilon = ||E||_op       = 0.6955
  delta   = dist(a,SpecB)  = 0.4940
  rho     = epsilon/delta  = 1.408   <= 0.25 required: FAIL (~5.6x over)
  s       = epsilon^2/delta = 0.9793

frozen baselines:
  contiguous_half:  s = 1.3415   (candidate beats it, ~1.37x, but bar is 2x)
  lowhigh_split:    s = 2,133,885  (delta~4.9e-7, degenerate cut)

criteria: not_parity_only=T mass=T rho=F schur_2x=F phi_meaningful=T
STOP CODE: GOAL057_SPECTRAL_CUT_LOW_CONDUCTANCE_WITHOUT_SCHUR_POWER
```

This is exactly your own "Likeliest failure" prediction: the affinity graph
found a genuinely low-conductance, non-parity cut, and it directionally beats
both frozen elementary splits — but `rho > 1` means the cross-block coupling
*exceeds* the spectral gap, so not even a first-order Schur/Neumann argument
is licensed yet. Per your directive's own instruction on this outcome: not
"try another clustering algorithm" — kill this representation at the
finite-cell level. Stop rule fired; `N=90,120` were not evaluated.

## One open anomaly — flagged, not used as a premise

`a = <q_even, K+ q_even> = 2.89e-32` (numerically zero at the dps=30 floor),
while `Spec(B)` sits entirely in `[0.494, 5.019]` — nowhere near zero. For a
generic unit vector this Rayleigh value would be expected at the scale of the
spectrum (~O(1)), not 32 digits below it. This is *why* `delta` came out
small relative to `epsilon`, i.e. it's the proximate cause of the `rho`
failure.

Two open readings, checked against the knowledge base (`ask.sh`: no prior
record of this under `sourceCCMFiniteRayleigh` value, `ccmWeilMatFinite null
vector`, or `trial nullity kernel spectral`):

1. **Structural**: `hTrial = (I4*h0 - I0*h4)/norm` is source-locked as *the*
   unique (up to scalar) combination with vanishing integral
   (`PEN_3_3_G04_OBJECT_DICTIONARY.md`); if that vanishing transports through
   `E*`/projection into near-exact orthogonality to the leading mode of `K+`,
   the canonical trial is, by construction, close to a null vector of the
   finite CCM operator. If real, this could matter beyond this preflight.
2. **Instrumental**: independent, non-Lean-exported Python numerics. Every
   structural gate that passed (symmetry, `J`-commutation, PSWF ODE residual,
   `psi0/psi4` orthogonality, `int hTrial=0`, literal-formula spot-check) is a
   *necessary* condition for correctness, none is *sufficient* — a systematic
   sign/convention error reproduced identically in both my internal check
   paths would pass all of them and still be wrong.

Cheapest discriminator (not run — out of scope for this precommitted,
single-run protocol): a second, independently-coded PSWF solver (e.g.
shooting-method ODE integration instead of Legendre-basis diagonalization) at
a small cell `(m=3,N=4)`, checking whether the same near-null anomaly appears
relative to that cell's own `Spec(B)`.

## Question

Given the directive's own instruction to kill the finite-cell spectral-cut
representation on this failure (not retune the clustering), the actual
decision point is what comes *after* the kill. Two options, no strong Codex
preference yet:

- **A.** Register the kill (`GOAL057_SPECTRAL_CUT_LOW_CONDUCTANCE_WITHOUT_SCHUR_POWER`),
  close this representation, and return to the frozen mainline
  (`H-bridge`/`H1^f` ladder) with no further spectral-geometry work pending.
- **B.** Before closing, spend one small independent-implementation check on
  the `a~0` anomaly (cell `(3,4)`, cheap, read-only) *specifically because* it
  is what caused the `rho` failure — if the anomaly is structural (reading 1),
  it may be a genuine fact about the canonical trial worth a named theorem
  target later; if instrumental (reading 2), it retracts silently and A
  proceeds unchanged either way.

Which — and if B, does the anomaly (if it survives an independent check)
belong in `knowledge.db` as a `dossier` (open question) rather than a `kill`
detail?
