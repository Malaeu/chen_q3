# LOCALIZE audit: tight oscillatory controls and paid off-edge return

Status: bounded independent PAPER audits PASS; T/RH remain OPEN.
Original verdict preserved, GitHub commit e8fb58544c69ddf8559a4fa1c793c355c965a5f6.
All 691 lines read. Verdict SHA256:
356ab75dd0e8bdd4ff03220e8058e6f62ccc42f46e2642afa21531c7f366f414.
Request SHA256: f380d5b774022c76814d68c3eb9c3eac3662cd046aee5dc72caba5afafb4fb79;
5828 bytes, 98 lines, final LF. Same living phase and literal N=m source.
Appendix copied verbatim to ../thetagrade_2026-10-28/localize_proshka_algebra.py.
Root replay with `uv run --with sympy python` passed all four exact checks.
This checks algebra only, not the cofinal construction or an eigenpair.

## Accepted new source results

For a fixed compact smooth cutoff, split at Fourier index m-ceil(sqrt(m)).
The full mixed projection pairing of the interior part is smaller than every
fixed inverse power, uniformly over unit input vectors. Formula (2.4) retains
endpoint traces, arch tail, every supported prime power and poles. Only the
narrow spectral-edge contribution E remains unpaid; no bound on it is assumed.

The compensated discrepancy separates into a uniformly bounded short-shift
part and the directly defined far pairing F_far in (3.2). Its prime atoms and
continuous reference remain together. Thus (3.3) pays everything except
E+F_far, rather than claiming either sign. This is a quantitative reduction,
not a supplied bound on exact bottoms.

The main new control is a sequence of unit real-even original-carrier q_m:
all fixed-jet overlaps, full residual, top-edge mass and full cutoff-return
costs are superpolynomially small, while mass in [-1,1] tends to one and
local arch/source energy, joint expression (*) and F_far tend to +infinity.
The proof first establishes density of finite theta derivatives in each fixed
unweighted H^s, with exact finite-jet annihilation. Modulated compact bumps
are approximated in H^1 by finite radical seeds. Each seed is fixed before
its source return constants are paid. Increasing thresholds then give a
single sequence on ALL sufficiently late original cells. No uniform estimate
in increasing derivative order or effective threshold is claimed.

Small exterior L2 tails can therefore have unbounded compensated source
coupling to the fixed interior. A uniform unweighted exterior operator bound
on arbitrary carrier inputs cannot be substituted for the selected estimate.

## Exact limitation and minimum-selection input

The controls are NOT asserted to be exact bottoms. For a trial of energy rho,
its genuine excess epsilon=rho-lambda_min remains in
N_rho>=-epsilon||P chi q||². Residual smallness does not bound that excess.
The cutoff raises the controls' energies; it is not their improving direction.
Only the larger-class assertion “escape + tiny residual + tight mass + tiny
edge supplies uniform local regularity” is refuted. Selected-bottom local
regularity, variational descent, NOESCAPE and RH remain unproved.

A nonzero nonnegative cutoff has nonzero returned vector by analyticity of
finite trigonometric synthesis. We independently recovered this same shelf
observation while LOCALIZE ran. It pays existence of normalization, not a
uniform denominator bound or energy sign.

Local regularity plus positive fixed local mass implies T by Fourier-tail
compactness and fixed-jet density. Both source estimates are still unpaid.
Spatially translating controls defeat mass; the new oscillatory controls
defeat regularity even with mass. Neither is a theorem about exact minima.

## Independent verification

Read-only reviewer localize_budget_audit checked L1-L4 and L10: residual and
excess signs, majorant constants, convolution/trace factors, narrow-edge
exponents, the far pairing and conditional compactness. PASS, inherited
CONFINE interfaces retained; the guard w<m is eventual (m>=3).
Read-only reviewer localize_radical_audit checked L5-L9 and CONFINE §3:
Sobolev density, normalization, exact annihilation, all-m diagonal thresholds,
full weighted prime/pole tails and divergence. PASS at PAPER scope only.
Root read the entire verdict and rechecked the inherited source interfaces.
No new Lean theorem, interval cofinal proof or RH claim is made.

## Next concrete test and input correction

Do not repeat the decomposition or treat small edge mass as its missing bound.
A finite discriminator must evaluate E, F_far and near contribution DIRECTLY,
not recover one by subtracting the others from the local energy identity.
Maintain actual minimum/excess status and complete norm/return budgets.
The old noescape_m16_eigenpair.json saves coordinate boxes for INDEX 1,
the second even eigenvector, although it records the ground eigenvalue too.
It must not be relabelled a saved bottom. Cache the already-computed ground
coordinates separately before any exact-bottom channel calculation; preserve
the old F/X cache and its provenance. A finite result remains diagnostic and
cannot settle the cofinal source bound.

At the23:24UTC check the verdict was on GitHub, while the live chat still
showed Thinking/Stop. No interruption or second question was sent. Await the
final accompanying message at the next scheduled check before treating the
transport lifecycle as complete; this does not prevent auditing saved bytes.

The ground-input correction is now implemented by extending the existing cache
script with --output and a separately labelled ground block. One original
m=N=16 run saved noescape_m16_ground_eigenpair.json with raw and interval-
normalized index0 coordinates; the old index1 JSON is byte-identical to HEAD.
Root verified 17 even/33 Fourier coordinates, separated first/second/third
balls, norm enclosure containing1, and script hash agreement. Ground lambda
is enclosed near5.4561380117056876e-38; this is finite input, not cofinal proof.
Command: uv run --with python-flint --with mpmath python
 docs/routeB_bus/thetagrade_2026-10-28/noescape_m16_eigenpair.py --output
 docs/routeB_bus/thetagrade_2026-10-28/noescape_m16_ground_eigenpair.json.
New artifact SHA256: 922dde3153bec0c3dd3bab58d1152fff778dcbf34e74766a3c9a8441ae9fe1c8.
Componentwise residual containment is only a consistency check, not a
standalone existence proof. Direct localized channel enclosures are NOT yet run.
