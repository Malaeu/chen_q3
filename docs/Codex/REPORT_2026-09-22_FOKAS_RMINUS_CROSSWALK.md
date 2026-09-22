# Paired window remainder is the existing lower Mellin tail

2026-09-22. PAPER derivation; no new Lean proof or production admission.
Base: 82bd8329be545b18597119cb1da7eefb12b87cb3.
Independent calculation check: /root/recovery_review, same-turn read-only review.

## Exact statement

Let m≥2 be an integer, λ=√m. Let H:[0,1]→ℂ be Lipschitz, with
∫_0^1 H(v)dv=0; extend H by zero above 1. Let h(u)=H(u/λ) for
0≤u≤λ, zero for u>λ. A symmetric extension on negative u has no effect below.
Write S_H(t)=Σ_{k≥1}H(kt), a finite sum for every t>0.
For Re s=σ>0:

    R_m(s;H) = ∫_0^(1/m) t^(s−1) S_H(t) dt
             = λ^(−s) Rminus h λ (s−1/2).

R_m is the paired Hurwitz/Mellin expression in the reviewed Fokas note;
at s=1 its separated pole is removed using zero mass. Also Rplus h λ=0.
Complex powers of positive real numbers use the real logarithm.

## Proof and hypotheses

For σ>1 the series of absolute integrals is bounded by
||H||∞ Σ k^(−σ)/σ, so sum and integral may be exchanged. In each term
v=kt gives k^(−s)∫_0^min(k/m,1)H(v)v^(s−1)dv. Splitting k≤m and k>m
is exactly the two-term R_m definition. No contour asymptotic is needed.

Let A=Lip(H), M=sup|H|, N=floor(1/t), 0<t≤1/m. The right-rectangle error is

    |t Σ_{k=1}^N H(kt) − ∫_0^(Nt) H(v)dv| ≤ A N t²/2.

Zero mass implies |∫_0^(Nt)H|=|∫_(Nt)^1H|≤M(1−Nt)≤Mt.
Since Nt≤1, division by t gives |S_H(t)|≤A/2+M=:B.
The integral therefore converges absolutely for every σ>0, locally uniformly
with all logarithmic derivative weights, and is holomorphic on that half-plane.
The paired zeta expression has only the possible pole s=1 there; its residue
is ℋ(1)=0. Analytic continuation proves the displayed identity throughout σ>0.

Literal Core.lean defines
Rminus h λ(z)=∫_0^(1/λ) sqrt(u) Σh(ku) u^(z−1)du.
Set z=s−1/2 and u=λt: powers and measure give λ^s, and upper endpoint
becomes 1/m. Rplus vanishes because u>λ puts every ku outside support.

## Quantified bound; what it does not buy

    |R_m(s;H)| ≤ B / (σ m^σ).

For fixed H this gives compact-uniform decay inside Re s>0. For actual H_m,
B=B_m depends on m and is NOT bounded by this argument. On coefficient lattice
Re s_n=1/2, the unnormalized coefficient contribution is bounded by

    m^(1/4)/sqrt(log m) |R_m(s_n;H_m)|
      ≤ 2 B_m m^(−1/4)/sqrt(log m).

This is not yet a bound on normalized rows (Z_mN is still required), not
cache error, not spectral residual (K−aI)q, and not ground tracking.
One must derive any link to those quantities and account for operator norms,
row size, normalization, spectral selection/separation and compact-domain gain.
No all-m bound for the selected Ferrers pair is asserted.

## Exact negative control

H=P2=(3v²−1)/2 has zero mass and ℋ(s)=(s−1)/(s(s+2)). At s=1,
lim ζ(s,m+1)ℋ(s)=1/3, and direct finite summation yields

    R_m(1;P2)=1/(4m)+1/(12m²)>0.

Hence zero mass and Lipschitz regularity do not make the remainder vanish.
This does not refute special cancellation for the selected prolate pair.

## Existing Lean suppliers, candidate scope

- [Core](../../q3.lean.aristotle/Q3/Proofs/RouteB/MuntzV3/Core.lean):
  literal Gwin, Rminus, Rplus, Mellin definitions.
- [ExactClassClosure](../../q3.lean.aristotle/Q3/Proofs/RouteB/MuntzV3/ExactClassClosure.lean):
  continued_window_identity_v3Class discharges the four analytic inputs retained
  in Unconditional.lean. Requires support, Lipschitz, measurability and zero mass.
- [ProlateCombinationReceiver](../../q3.lean.aristotle/Q3/Proofs/RouteB/MuntzV3/ProlateCombinationReceiver.lean):
  continued_window_identity_prolateCombination_v3Class_of_modeLipschitz applies
  the continued identity to the actual ProlatePair expression; mode Lipschitz
  inputs remain explicit. It neither constructs the selected modes nor supplies
  positivity, ground identification or a cofinal family estimate.

These declarations were read, not rebuilt or admitted in this turn. The exact
new R_m↔Rminus scale crosswalk is PAPER, not a claimed existing Lean theorem.

Shelf query ./ask.sh --defer-external Rminus Mellin Hurwitz Ferrers returned
INCOMPLETE: semantic-index freshness validation failed; foreign shelf deferred.
Positive exact-source hits were inspected. This is not an absence result.
Raw output is saved beside this report in the existing session-protocol area.

## Consequence for the Hermes directive

Correct Δ multiplication to division, but Δ→0 alone does not force residual/Δ
→∞. Spectral selection and appropriate separation hypotheses remain necessary.
Replace 'prove R_m cancels to transfer cache coercivity' with: derive cancellation
or surviving tail and show the exact inequality/identity it supplies to the
same-source consumer. R_m is not automatically source-minus-cache or (K−aI)q.

Next bounded move: inspect selected mode regularity and the existing small-window
bounds, seeking family control of B_m/Z_mN or a sharper structural bound. Compare
that output with the actual cofinal ground consumer before a Proshka dispatch.
CHALLENGER_NOT_RH. PX_RH_CLAIM: NOT_MADE.


## Stronger signed summation bound (independently checked)

PAPER ONLY. For H in C²[0,1], zero integral, define periodic
B₂(x)={x}²−{x}+1/6 and f={1/t}. The sum includes the upper endpoint
with full weight when 1/t is integral. Cellwise integration by parts gives

    S_H(t) = −H(0)/2 + (1/2−f)H(1)
      + (t/2)[B₂(1/t)H′(1)−B₂(0)H′(0)]
      − (t/2)∫₀¹ B₂(v/t)H″(v)dv.

Proof: integrate on each interval between lattice points. The periodic
sawtooth B₁(x)={x}−1/2 has jump −1 at each lattice point; its derivative
between jumps is 1. The first integration gives the sum, integral/t and
endpoint terms. B₂ is continuous across these points, with derivative 2B₁
away from them; the second integration gives the displayed correction.
Use the left-limit upper endpoint in the first step when it is a lattice
point, and then add its full H(1) contribution. Values of the periodic
functions at finitely many integration points do not affect the integral.

Because |B₂|≤1/6, let A_H=|H(0)|+|H(1)| and
D_H=|H′(0)|+|H′(1)|+∫₀¹|H″|. Then

    |R_m(s;H)| ≤ A_H/(2σ m^σ) + D_H/[12(σ+1)m^(σ+1)].

This keeps the center and support-edge defects; neither is set to zero.
For the physical packet H_m(v)=h_m(λv), λ=√m, define

    A_m = |h_m(0)| + |h_m(λ)|,
    D_m = |h_m′(0)| + |h_m′(λ)| + ∫₀^λ |h_m″(u)|du.

Derivatives are interior one-sided endpoint derivatives of the packet,
not distributional derivatives of its zero extension. The extension can
jump at λ; that jump has already been paid by the H(1) term. Substitution
in the bound gives

    |R_m(s;H_m)| ≤ A_m/(2σ m^σ)
                    + D_m/[12(σ+1)m^(σ+1/2)].

On the full coefficient lattice σ=1/2, write
b_n=m^(1/4)/√log(m) · ζ(s_n)ℋ_m(s_n), a_n=α_mn(H_m).
For every |n|≤N, a_n=b_n−m^(1/4)/√log(m) R_m(s_n;H_m), hence

    ||a−b||₂ ≤ E_mN
      := √(2N+1)/√log(m) · [A_m m^(−1/4)+(D_m/18)m^(−3/4)].

Both signs of n and n=0 are included. If A_m=O(m⁻¹), D_m=O(1),
and N=O(m), this is O(m⁻¹/⁴/√log(m)) → 0. More generally, the exact
sufficient rate is the displayed E_mN→0; no particular schedule is imposed.
These are CONDITIONAL family hypotheses, not established Ferrers estimates.

For normalization set Z=||a||₂. If E_mN<Z, then ||b||₂≥Z−E_mN>0 and

    ||a/Z − b/||b||₂||₂ ≤ 2E_mN/Z.

Proof: write the difference as (a−b)/Z+b(1/Z−1/||b||₂), and apply
| ||a||₂−||b||₂ |≤||a−b||₂. Thus the required relative rate is E_mN/Z→0;
Z>0 for each m alone is insufficient. b is the zeta/Mellin bulk vector,
NOT the decimal cache, finite ground, or Ξ itself. No spectral conclusion
or cache coercivity transfer follows without a further exact bridge.

Independent reviewer /root/recovery_review checked the identity, endpoint
convention, all constants and physical scaling; 56 exact Fraction polynomial
checks. Parent independently ran 888 Fraction checks, degrees 1..8 and
rational meshes, with both lattice and nonlattice endpoints: all passed.
These checks test algebra and are not Ferrers-family certificates.

## Existing family suppliers and remaining interface

Read at HEAD 6abd36e1cc1bc41af2016e785340ce46e9f2e58d; not rebuilt here:

- G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean:
  selectedPacket_lipschitz_on_window (private) proves Lipschitz for each k,
  via weighted Ferrers summability. It does not provide a uniform D_m bound.
- G6N1SelectedFerrersPaperParameterDictionary.lean already fixes
  gamma=2π(k+2), λ=√(k+2), modes 0/4. No Lean bandwidth repair is needed.
- G6N1SelectedFerrersEStarWindowMainError.lean:
  selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates takes uniform
  full-window mode and chi rates as hypotheses, not conclusions.
- G6N1SelectedFerrersFirstOrderBudgetApplication.lean:123:
  selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget requires
  an eventual exact production-family crosswalk, mode and chi O(λ⁻²)
  rates, bounded selectedFerrersAbelLogDerivativeBudget, bounded inverse
  SourceScale, and cofinal physical bandwidth. It proves projection-tail
  decay under those inputs, not the finite-ground bridge.
- G6N1ExplicitHDerivativeCombBudget.lean treats the explicit Gaussian limit
  profile. Its derivative bound cannot be substituted for the actual
  selected Ferrers packet without a derivative-error transfer theorem.

Optional Euler-remainder branch obstruction: for the SAME scaled selected Ferrers packet, obtain
A_m and D_m estimates (or a sharper signed substitute) from its mode equations,
then bound E_mN/Z. Pointwise convergence or C⁰ mode rates cannot silently be
differentiated. Compare resulting bulk row with the exact Goal058 consumer
before any claim of ground tracking. This strengthens the available paper
estimate; it does not close any production node.


## Stronger existing assembly found on continuation (corrects next-step choice)

Source inspection at c2781655 found a stronger supplier than the first-order
receiver cited above. The independent derivative budget is NOT a mandatory
new premise of the existing projection-tail route:

- `G6N1SelectedFerrersW5RateAssembly.lean:5640`,
  `selectedProjectionTailDecay_of_selectedFerrersW5RateLedger`, assumes
  hFamily plus hmode, hχ and hθ. It internally derives the required budget,
  inverse source scale and bandwidth limit. No separate hD/hScale/hBandwidth
  arguments remain. Quantitative export at line 6016 permits a growing
  Fourier-decay budget O(m^(1/4) sqrt(log(m)+2)); uniform boundedness is not
  necessary for that receiver.
- `G6N1SelectedFerrersTrialNormalizerClosure.lean:1209`,
  `selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger`, supplies
  the bounded inverse projected norm under the same inputs and family match.
  Its subsequent normalized Galerkin residual theorem uses this together
  with projection-tail decay. This residual is a projection error, NOT
  automatically (K−aI)q.
- `G6N1SelectedFerrersN2CompactDecayAssembly.lean:1110`,
  `selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates`,
  already states locally uniform convergence on centeredCriticalStrip for
  its explicitly constructed selectedFerrersCofinalShell, conditional on
  hmode/hχ/hθ. It does not assert this family consists of finite ground states
  or is zero-free off the critical line.

Thus the next efficient route audit is to locate actual suppliers for the
three shared rates and the exact production-family identification. Do not
commission a new uniform second-derivative theorem merely to reproduce a
projection-tail conclusion already available conditionally. The Euler/Fokas
row estimate remains a valid optional mechanism, not an additional required
axiom of Goal058. These files were read, not rebuilt or admitted in this turn.
