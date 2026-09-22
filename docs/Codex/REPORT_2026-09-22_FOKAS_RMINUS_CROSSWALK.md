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


## Audit of the shared rate inputs (HEAD 3e3a79cf)

The inspected transfer declarations do not discharge their raw asymptotic
premises. This is a statement audit, not a repository-wide absence theorem:

- `G6N1SelectedFerrersDirectCylinderRate.lean:272` consumes two source
  families at the selected project eigenvalues, nonzero scale functions,
  and eventual FULL-window raw bounds hraw0/hraw4 by rawC/gamma. Its outputs
  have constants 2 rawC0/pi and 94 rawC4/(3 pi) at lambda^(-2). These are
  explicit transfer constants, not witnesses for hraw0/hraw4.
- `G6N1FuchsSelectedEigenvalueDefectRate.lean:139` consumes positive mu0/mu4,
  exact paper Fourier eigenrelations on the rescaled selected modes and
  concentration defects |1-mu²/(2pi)|≤C/a². The proven output has Cchi=C0+C4.
  Positive phase and raw defect estimates remain inputs.
- `G6N1SelectedFerrersCenterIntegralRate.lean:49` derives integral rates
  FROM hchi. Using that result to obtain hchi would be circular. Its header
  explicitly records the lost power from integrating only a sup-error over
  an expanding physical window.
- `G6N1Satz9SourcePackageInterface.lean` states that a payload inhabitant
  alone cannot enforce source provenance or supply Satz9 asymptotics.
  A source-only theorem and separate eigenvalue identification are needed.

The existing Meixner-Schaefke usage card records both a raw O(gamma^(-3/4))
mode remainder (becoming O(gamma^(-1)) after the leading scale) and eigenvalue
asymptotics. It is historical paper evidence, not newly verified book bytes
or a Lean proof of the selected rates. Do not confuse these raw exponents.

Decision: follow the exact raw Satz9 source theorem and its eigenvalue bind
before adding another rate-composition wrapper. The Fokas Euler mechanism
remains optional. The current browser still displayed the original Fokas
VERDICT preview; no new request was sent and no new response was claimed.


## Source-pinned exploratory alias brief: raw fixed-mode asymptotics

Target: hraw0/hraw4 of G6N1SelectedFerrersDirectCylinderRate.lean:272
at HEAD 3e3a79cf, read above. For each fixed degree n=0,4, lambda=√m,
gamma=2pi m, need nonzero scale a_m and source solution p_m at the selected
separation eigenvalue, with sup_{|x|≤lambda}|a_m p_m(x)−D_n(2√pi x)|≤C/gamma
eventually, C independent of m. Source/project matching must precede spending
this bound. Existing composition supplies its consequence, not this input.

Negative control: same ODE and regularity alone allow arbitrary scalar
multiples. Replacing a center-normalized degree-zero candidate f_m by 2f_m
leaves a center error 1, incompatible with C/gamma→0. A theorem only on fixed
physical compact sets is also insufficient for the expanding full window.

Search dictionaries: (1) spheroidal wave, fixed degree, parabolic cylinder;
(2) Sturm-Liouville, coalescing turning points, uniform error bounds;
(3) semiclassical harmonic oscillator, low eigenstates, expanding interval.
UNVERIFIED rewrites: harmonic-oscillator localization plus exterior decay;
Weber uniform asymptotics with source normalization. Preserve both endpoint
and center control. Worked existing mechanism: centerNormalizedSatz9Rate
transfers an already-proved raw rate after a denominator guard; it cannot
create the raw rate. Stop after inspecting one primary proof source and
recording its domain, normalization, and exact unmatched hypotheses.
Status INCOMPLETE_NO_CONSUMABLE_TARGET: production theorem/consumer edge is
still unbound; this is bounded exploratory discovery, not supplier admission.


## Alias result and a compact-test reduction of the theta input

The registered shelf query `Satz9 spheroidal parabolic-cylinder` finished
exit 2, INCOMPLETE (semantic freshness), with positive local Lean hits.
No absence claim. An exact-name shelf pass found the already stored primary
source Dunster, arXiv:1601.00699v3, "Asymptotics of Prolate Spheroidal Wave
Functions": https://arxiv.org/abs/1601.00699v3 . Landing metadata verified live.

Local source: docs/routeB_bus/litreview/pdfs/survey_2026-09-03_sources/
pswf_asym_1601.00699.pdf; SHA256
29dcb15d2b9d30ecd983e8fd2b835c6ab3e35224df5e7f0e56b0f5ac08144452.
Extracted text SHA256
1401c793807d9aa986a9c81016c9f4a840fc932cdb788b9cf77e7842c039f9e0.
Read section 5, printed pp16–18, equations (5.2), (5.9)–(5.19).
Precise domain quote after (5.19): "uniformly for 0 ≤ x ≤ 1 − δ0".

Classification: source-verified PARTIAL mechanism, not exact hraw fit.
Paper order m=0, fixed degree n=0 or4, gamma=2pi*m_project,
paper x=y/sqrt(m_project). The fixed-mode expansion uses a perturbed Weber
coordinate and O(gamma^(-1) log gamma) envelope error on a truncated interval.
Thus endpoints, envelope-to-absolute conversion, parameter/coordinate shift,
normalization and log loss prevent immediate use as the required full-window
C/gamma bound. The paper's eigenvalue asymptotic also needs exact branch
identification. Center-normalization is essential for the scalar negative
control. Do not relabel (5.19) as Satz9's stronger raw statement.

### New PAPER implication: compact mode rate implies eigenvalue defect bound

This implication is independently derived from the physical ODE; it does not
import Dunster's asymptotic theorem. Let m→∞, e∈R fixed. On (-sqrt(m),sqrt(m)),
f_m∈C² solves

    −((1−y²/m) f_m′)′ + 4pi² y² f_m = (theta_m/m) f_m.

Let real D satisfy L∞D=eD, L∞=−d²/dy²+4pi²y². On a fixed [-R,R], assume
sup |f_m−D|≤C/m eventually, C≥0. Even full-window mode rates are unnecessary
for this implication. Choose fixed φ∈C_c²(−R,R) and J=∫Dφ≠0. Set

    Tφ=(y²φ′)′=y²φ″+2yφ′,
    A=||L∞φ−eφ||₁, B=||Tφ||₁, P=||φ||₁,
    M=sup_supp(φ)|D|.

All these constants are finite and independent of m. Twice integrating by
parts, with φ and φ′ zero at the integration endpoints, gives the EXACT
identity

    (theta_m−em)∫f_mφ
      = m∫(f_m−D)(L∞φ−eφ) + ∫f_m Tφ.

Indeed L_mφ=L∞φ+Tφ/m, and self-adjoint integration for D gives
∫D(L∞φ−eφ)=0. This uses bilinear complex integrals consistently; D and φ
can be real in the actual application. It never differentiates f_m−D.

For m≥1, m>R² and m≥2CP/|J|, with the mode bound valid,

    |∫f_mφ| ≥ |J|−CP/m ≥ |J|/2,
    |theta_m−em| ≤ (2/|J|)[C A+(M+C)B].

For n=0,4 take D=D_n(2sqrt(pi)y), e=2pi(2n+1). One explicit admissible
choice is φ(y)=(1−y²)^3 D(y) on [-1,1], zero outside, using any fixed R>1.
This zero extension is C², J=∫_(−1)^1(1−y²)^3D(y)²dy>0 since D(0)=1 or3.
No unspecified bump-function or nonzero-overlap hypothesis remains.

The project's physical prolate equation has theta=Lambda+mode4JacobiG m
and lambda²=m; division by m gives exactly the displayed equation. Multiplying
a mode by its center-anchor scalar preserves it on the interior. Hence the
two hmode bounds, once supplied for these actual modes, imply a common htheta
by taking the maximum of the two finite constants. This is PAPER, not yet a
Lean theorem. It does NOT supply hmode, hchi, ground identification or RH.

Independent /root/recovery_review confirmed identity, constants, complex
pairing and eventual thresholds. Parent independently checked both oscillator
identities by exact integer polynomial arithmetic: for P0=1 and
P4=16t^4−24t²+3, −P″+4tP′−4nP=0, t=sqrt(pi)y.
An attempted optional SymPy check found the package unavailable; no install
was made; the integer calculation provides the stated algebra check.

Decision effect: htheta need not be commissioned as a separate asymptotic
supplier if hmode is proved without assuming htheta. The remaining shared
analytic entrances are then hmode and hchi; hFamily/finite-ground matching is
still separate. Next: inspect hmode proof dependencies before formalizing this
compact-test bridge, and seek a same-source hchi supplier. Do not use this
implication to justify an hmode proof that already assumes htheta.


## New PAPER implication: full-window mode rate implies chi defect rate

Let F use exp(+2pi ixy), exactly ProlateSourceRegularity.lean:18–27.
Let f_lambda be integrable, supported on I=[−lambda,lambda], and satisfy
F f_lambda=chi_lambda f_lambda on I. Let D be real, F D=D, and define

    L=∫|D|, M2=∫x²|D(x)|, Q2=∫x²D(x)², J0=∫D(x)²>0.

Assume all four numbers finite and, eventually,

    sup_I |f_lambda−D| ≤ C/lambda², C≥0.

No positivity of chi is assumed. With J_lambda=∫f_lambda D, absolute
Fubini applies because ∫∫|f(y)D(x)|dxdy=||f||₁ L<∞. Kernel symmetry and
self-Fourier D yield ∫(Ff)D=∫f(FD)=J_lambda. Split at I and use the
Fourier eigenrelation only on I:

    (1−chi_lambda) J_lambda = ∫_(outside I) (Ff_lambda)(x) D(x) dx.

This is a bilinear pairing; it is intentional, with D real. Since |Ff|≤||f||₁,

    ||f||₁ ≤ L+2C/lambda,
    |J_lambda−J0| ≤ (C L+Q2)/lambda²,
    |∫_(outside I)(Ff)D| ≤ (L+2C/lambda) M2/lambda².

The last two inequalities use x²≥lambda² on the exterior. Therefore for
lambda≥1 and lambda²≥2(C L+Q2)/J0,

    |1−chi_lambda| ≤ [2(L+2C) M2/J0] / lambda².

No derivative-error estimate, Plancherel theorem, or external Fuchs
concentration asymptotic is needed. The denominator is a nonzero overlap,
not the value of f at a point. The input is the full-window mode rate;
a fixed-compact mode approximation alone would not supply ||f||₁ control.

### Exact project correspondence

Use f_lambda = centerAnchorScalarZero*h0 or centerAnchorScalarFour*h4,
with lambda=selectedFerrersPaperLambda k. Scalar multiplication preserves
the exact finite-Fourier eigenrelation, and zero extension makes finite and
whole-line actions agree. Both eigenrelations and support are carried by
selectedFerrersPreAnchorPair_spec (G6N1SelectedFerrersPreAnchorDataInhabitant,
lines123–143) and its selected normalized modes. The same chi0/chi2 are used.

D0=e^(−pi x²), D4=(16pi²x⁴−24pi x²+3)e^(−pi x²).
All required moments are finite Gaussian moments and J0>0 because D0(0)=1,
D4(0)=3. The identity D4=16*explicitCCMLimitH+3*D0 and the existing
fourier_explicitCCMLimitH (D0PstarExplicitCCMLimitFourier.lean:253), together
with the Gaussian transform, supply self-Fourier D4 at PAPER scope. If using
Mathlib's minus-sign integral convention, explicitly apply evenness:
Fplus D(x)=Fminus D(−x)=D(−x)=D(x). Do not infer the sign from a docstring.

Negative control: for degree2, Fourier phase is −1. The same calculation
would control |−1−chi|, not |1−chi|. Thus the mechanism retains the phase
information lost by a squared concentration eigenvalue.

Combined with the preceding compact-test ODE lemma, hmode implies BOTH
hchi and htheta for the actual two selected modes, conditional on their
exact stored ODE/Fourier relations. This reduces the independent analytic
entrance of W5/N2 to hmode on PAPER; it does not prove hmode, construct a
source-independent Satz9 theorem, identify finite ground states, establish
off-line zero-freeness, or give Lean admission. Audit for circular dependence
before spending this reduction: hmode must not be obtained using these same
conclusions. Next concrete formal target is the generic Fourier-overlap
lemma with this explicit moment budget, followed by same-source instantiation.

Independent recovery_review checked the Fourier-overlap identity, moment constants,
phase negative control and full-window eigenrelation requirement; PAPER approval.


## Lean candidate: exact overlap identity and tail bound

Isolated candidate retained as research evidence, NOT imported into production:
`docs/session_protocols/fourier_overlap_candidate_20260922.lean`.
SHA256 cc6935a9e2993939fe791465c1f1864bd0bdd2f3d236cb1e699d61e81b15df8d.
Canonical narrow check `scripts/q3_check.sh /tmp/Q3FourierOverlap.lean`
finished exit0; archived exact check log beside candidate. Retained bytes
match the checked temporary file. No sorry or new axiom; printed dependencies
for overlap and overlap_bound are propext, Classical.choice, Quot.sound.

`F_eq_inverse` fixes the plus phase by kernel-checked equality with Mathlib's
inverse Fourier transform. `swap` supplies actual Fourier reciprocity;
`product_integrable` discharges the integral splitting hypothesis. `overlap`
proves (1-chi) integral(fD)=exterior integral(Ff D) for measurable window,
integrable f,D, support, full-window eigenrelation and self-Fourier D.
`overlap_bound` proves

    |1-chi| |integral(fD)| <= ||f||_1 integral_outside |D|.

No Fubini identity or product integrability is smuggled in as an assumption.
Actual Ferrers instantiation, profile self-Fourier transport, moment estimates,
overlap lower bound, and the eventual hchi theorem remain to formalize.
Independent reviewer checked the exact identity candidate; final extended
candidate review tracked separately. Kernel success is not production admission.

Final extended candidate approved by recovery_review on the exact SHA256 above;
no mathematical changes requested. Scope is isolated helper evidence only.


## Lean extension: second moment and conditional chi bound

Candidate updated to SHA256
b2945659247fc54ffbd45ef5f40c4d48678bbd62204f446387518734fc2aba74.
`exterior_moment_bound` proves the exterior norm integral is at most the
second absolute moment divided by lam². `chi_bound_of_overlap_floor`
combines this with the exact overlap estimate and an explicit J/2 floor:

    ||1−chi|| <= 2 ||f||_1 M2(D) / (J lam²).

q3_check exit0, all four printed theorem dependencies standard only;
independent recovery_review approved this exact hash. No production import.
The overlap floor and uniform family L1 bound are STILL INPUTS, not yet
derived from hmode in Lean. This is a pointwise quantitative inequality;
it is not a claimed uniform asymptotic if those constants vary freely.
Next: derive both missing bounds from the full-window C/lam² approximation
and the fixed target moments, then instantiate actual selected Ferrers modes.


## Lean generic mode-error to chi-rate theorem

Final candidate SHA256:
ef36d9bffc0a2df2ab5ea12e4775bf95ba4b2b7a37bd2cec3e0e6962c7305fa9.
q3_check exit0; all eight printed dependencies contain standard axioms only.
`source_l1_uniform` derives ||f||1≤||D||1+2C from support and full-window
C/lam² error. `source_product_integrable` derives product integrability.
`overlap_error_bound` derives

    |integral(fD)−integral(D²)| ≤ (C L+Q2)/lam².

`chi_bound_from_mode_error` combines these with Fourier reciprocity and
moment tails. Inputs: lam≥1, C≥0, fixed D with finite L1, square and two
weighted moments, self-Fourier D, integrable supported f, full-window
Fourier-eigenrelation and approximation, J=|integral(D²)|>0, and explicit
threshold 2(C L+Q2)≤J lam². Output:

    |1−chi| ≤ [2(L+2C)M2/J]/lam².

No independent overlap floor, uniform L1 source hypothesis, or assumed
Fourier defect bound remains. The generic theorem is kernel-checked; an
actual-source hchi instance still requires matching D0/D4 self-Fourier,
nonzero square integrals, moments and selected Ferrers eigenrelations.
The input hmode remains unproved; no claim of cofinal ground tracking.

Independent recovery_review recompiled and approved final ef36d9bf bytes;
no circular chi assumption; actual-source and production boundaries retained.


## Lean exact selected-mode Fourier connection

Candidate SHA256
344f7eacf946cf20cfc003880d9c6e8e123e0ca2d812c590c8dac5ea86c7d0e1.
`F_eq_finiteFourierAction` expands the actual project kernel, fixes its plus
phase and converts whole-line to window integral using support.
`scaled_finite_eigen` proves scalar transport. `selected_anchored_eigen`
instantiates the actual stored selected pair and precommitted center anchors:
mode0 with chi0, mode4 with chi2. Full-window eigenrelations come from
selectedFerrersPreAnchorPair_spec, support from the pair's fields; neither
is a new hypothesis of the selected-mode theorem.

q3_check exit0, ten printed theorem dependencies standard only, including
the selected-source theorem. Independent recovery_review approved exact
bytes. Builds use the repository's current available dependency oleans;
this is a narrow candidate check, not a fresh-clone production admission.
Remaining: target D0/D4 self-Fourier/moments/nonzero square integral,
source integrability and exact window dictionary, eventual assembly, and
actual hmode supplier. No complete selected-family chi rate claimed yet.

## Concrete cylinder target Fourier self-duality

Candidate SHA256 ca7aa7a17f20cf51cc61345a9a835c4e98ae3970423d65d27cf4d96effa8f6fb.
The candidate now defines cylinderTarget n using the actual parabolicCylinderD
and projectCylinderArgument. target_zero_fixed and target_four_fixed prove
Fplus D0=D0 and Fplus D4=D4. The minus-sign Mathlib transform is converted
through fourierInv_eq_fourier_neg and evenness, explicitly.

target_four_decomposition proves D4=16 explicitCCMLimitH+3 D0.
target_zero_moment proves integrability of x^n smul D0 for every natural n;
ccm_integrable follows from its degree2/4 moments. No self-Fourier premise
or circular chi input was added.

Canonical q3_check exit0; thirteen printed theorem dependencies standard only.
Independent recovery_review compiled and approved the exact hash above.
One unnecessarySeqFocus style warning remains; dependency UnicodeBasic had
preexisting local changes. This uses current dependency oleans, not a fresh
clone check or production admission.

Remaining target obligations: D4 and squared weighted moments, nonzero square
integrals; then source integrability, lambda dictionary and eventual selected
family chi assembly. hmode remains unproved, htheta reduction PAPER only,
finite-ground identification and off-line zero-freeness separate and open.
PX_RH_CLAIM: NOT_MADE.

## Actual target moment and nonzero-square inputs discharged

Candidate SHA256 978b2d4ba64bd49edeb11f79a04a7c8f27193ffcd91ff3fd3cd3a447f03ce8d2.
target_four_moment proves all natural polynomial moments of D4; square
moments of D0 and D4 follow from the double Gaussian. D4 squared polynomial
coefficients are 256pi^4, -768pi^3, 672pi^2, -144pi, 9 in degrees8,6,4,2,0.
target_square_positive uses continuity, integrability, nonnegativity and
D0(0)=1 / D4(0)=3 to prove strict positivity of the real square integral.

The combined target_analytic_inputs theorem for n=0 or4 now supplies exactly
hD, hDD, hM, hQ, hJ of chi_bound_from_mode_error: integrability of the complex
target, its bilinear square, x^2 times the target norm, x^2 times square norm,
and positive norm of the complex square integral. The real-to-complex
integral equality is proved explicitly, not an additional hypothesis.
selected_anchored_integrable also supplies integrability of both actual
selected modes after the precommitted center scalars, from the pair fields.

Canonical q3_check exit0; 21 printed dependency lists standard only.
Independent recovery_review approved final source and hash. Existing dependency
oleans were used, with the preexisting UnicodeBasic local-change warning;
style-only linter warnings remain. No fresh-clone or production admission.

Next is the actual eventual selected-family chi assembly using the exact
lambda dictionary and hmode. Window dictionary pointers already exist:
selectedFerrersPreAnchorPair_lambda_eq_paperLambda and
selectedFerrersPreAnchorPair_lambda_eq. No new source integrability premise
is needed. hmode remains unproved, htheta reduction remains PAPER, and
finite-ground identification/off-line zero-freeness remain separate.
PX_RH_CLAIM: NOT_MADE.

## Selected hchi derived and consumed in W5 without an independent hchi premise

Candidate SHA256 6f5effebbe5b0a263c6cd10122a360135700737027647e50cd6fb0e1d44e4abc.
scheduled_chi_rate combines the concrete target facts with the generic
Fourier-overlap inequality. A fixed threshold follows from exists_nat_ge and
lambda_k^2=k+2; the resulting constant is independent of k. No assumed
overlap floor, concentration defect, source L1 bound or chi rate is added.

selected_chi_rate_of_mode_rate uses the actual selected anchored mode0/h0
and mode4/h4, their exact eigenrelations with chi0 and chi2, and the exact
paper-window dictionary. It concludes existence of a single nonnegative Cchi
with eventual real bounds |1-chi0|,|1-chi2| <= Cchi/lambda_k^2, assuming only
the two nonnegative mode constants and the same eventual hmode statement
consumed by the W5 theorem. The max of two fixed constants supplies Cchi.

selected_projection_tail_of_mode_theta then calls the EXISTING
selectedProjectionTailDecay_of_selectedFerrersW5RateLedger directly. This
kernel-checked consumer bridge retains S, hFamily, C0,C4,Ctheta, their signs,
hmode and htheta; its signature has no independent hchi argument. This is a
conditional implication, not a proof of its remaining premises. It neither
changes production source nor admits a Goal058 node.

Canonical q3_check exit0; all 24 printed dependency lists standard only.
Independent recovery_review checked exact hypothesis fit, finite threshold,
real/complex conversion, common constant and direct consumer connection, and
approved the final hash. Current dependency oleans used; preexisting
UnicodeBasic warning and style-only linter warnings remain. Not fresh-clone
production validation.

The previous PAPER hmode->hchi reduction is now Lean-checked for the actual
selected source family in this isolated candidate. hmode itself remains
unproved; hmode->htheta is still PAPER. Next investigate the exact hmode donor
or formalize the compact-test htheta reduction, without using either output
circularly to prove hmode. Finite-ground matching and off-line zero-freeness
remain separate open requirements. PX_RH_CLAIM: NOT_MADE.

## Compact Green mechanism and literal target oscillator equations

Candidate SHA256 d2225b8d0fdc8aa8c7c9e8c6b32ff6aa69d8c3e3fc788c56b5e3ee0a4757a2db.
compact_flux_green derives integral(phi*dflux)=integral(f*dtestflux) on a
compact oriented interval by two interval integration-by-parts applications.
Explicit assumptions are continuity of f, phi, flux and testflux on uIcc;
interior derivative formulas; integrability of the four derivatives;
flux=p*df and testflux=p*dphi; zero phi and testflux at both endpoints.
These are regularity/boundary premises, not error bounds on df-dD. The
identity is bilinear over complex values and retains the same weight p.

The literal parabolicCylinderD(projectCylinderArgument) targets now satisfy
kernel-checked real oscillator equations via target_zero_oscillator and
target_four_oscillator, e=2pi and18pi. They reuse public ctW0/ctW4 derivative
and oscillator theorems from G6N1SturmWeightedEnergyIdentity, proving the
exact function dictionary rather than relying on notation similarity.

Source audit located actual-source suppliers:
- D0Mode4FerrersNormalizedActualModeLocalFields.lean:122,
  normalizedPhysicalMode_prolateWaveExpression_eigenrelation;
- G6N1SturmDefectEnergyModePlumbing.lean:34,
  sturm_mode_flux_hasDerivAt, with derivative
  ((2pi*sqrt(m)*x)^2-(Lambda+mode4JacobiG m))*physicalMode.
The latter assumes the Ferrers solution, m>=2 and an interior point, with no
spectral-separation or derivative-error estimate. Normalization/scalar
transport and compact-test instantiation remain. Existing
sturm_weighted_energy_identity is quadratic/full-window, not this arbitrary
bilinear compact-test identity; bounded independent source review found no
ready equivalent in the inspected import chain (not a global absence claim).

Canonical q3_check exit0; all27 printed dependency lists standard only.
Independent recovery_review reviewed the final candidate scope and bytes.
Current dependency oleans used; preexisting UnicodeBasic and style warnings
remain. No fresh-clone production admission.

Next exact joint: instantiate p=m-x^2 and a fixed test phi=(1-x^2)^3D on
[-1,1], derive the signed theta defect identity before taking norms, then
apply hmode to its overlap denominator and two numerator integrals.
The selected hmode->htheta implication remains PAPER until this connection
and quantitative estimates are checked. hmode itself, finite-ground matching
and off-line zero-freeness remain open. PX_RH_CLAIM: NOT_MADE.

## Signed weak theta identity and quantitative pairing bound

Candidate SHA256 42f590750f457d759c95c86f91952717d9964c93f1f4930a7aa9dcebc3edbccf.
compact_theta_defect_identity proves, over complex bilinear interval integrals,

  (theta-e*m) integral(f*phi)
    = m integral((f-D)*(-ddphi+(V-e)*phi)) + integral(f*T).

Its premises are continuous f,D,phi,ddphi,V,T on the compact interval, the
weak ODE identity integral(phi*(m*V-theta)*f)=integral(f*(m*ddphi-T)),
and target orthogonality integral(D*(-ddphi+(V-e)*phi))=0. Both signs and
scaling are explicit; all integral linearity premises follow from continuity.
ddphi is an arbitrary supplied function at this level, not silently declared
to be a derivative. For p=m-x^2 the intended T is x^2*phi''+2*x*phi'.

The separate theta_defect_bound_from_weak_pairing proves
|theta-e*m| <= 2*(A+B)/J from m>0,J>0, the signed pairing identity,
J/2<=norm(I), norm(U)<=A/m and norm(V)<=B. I,U,V may be complex;
no real-phase assumption is made. A,B nonnegativity need not be extra
premises because the norm upper bounds already imply it. The denominator
floor remains explicit until obtained from hmode and the fixed test.

Canonical q3_check exit0; all29 printed dependency lists standard only.
Independent recovery_review approved signs/scaling, denominator conditions,
absence of circular theta estimate, final source and hash. Current dependency
oleans used; preexisting UnicodeBasic and style warnings remain. No production
admission or fresh-clone proof claim.

Remaining actual-source obligations: construct the fixed test, discharge its
boundary/derivative facts and target orthogonality from Green and oscillator
ODE, instantiate the normalized selected-mode weak ODE, and derive the
uniform numerator estimates/overlap floor from hmode. The eventual selected
htheta statement is NOT yet proved. hmode, finite-ground connection and
off-line zero-freeness remain open. PX_RH_CLAIM: NOT_MADE.

## Concrete test: boundary cancellation, positive overlap and target orthogonality

Candidate SHA256 ed5784b00c4d5cac76a8b3cfaffc1325ed42a9899b61d402851e0a50a6b16f25.
compactTest n x=(1-x^2)^3*parabolicCylinderD n(projectCylinderArgument x).
For n=0 or4, kernel-checked facts now include C-infinity smoothness, its exact
first derivative, zero value and derivative at both -1 and1, and strictly
positive integral of D_n*compactTest over [-1,1]. The test is defined globally
as polynomial times Gaussian, NOT zero-extended or claimed compactly supported;
the compact interval and endpoint zeros are sufficient for the two IBPs.

The overlap integrand equals (1-x^2)^3 D_n^2, nonnegative on the interval and
positive at zero, where D0=1 and D4=3. No constant sign of D4 is assumed.
oscillator_test_orthogonality derives the signed test integral from two real
IBPs and an exact oscillator equation. compactTest_orthogonality instantiates
literal D0/D4 and e=2pi(2n+1), concluding

 integral D_n*(-phi''+(4pi^2*x^2-e)*phi) = 0.

Complex versions compactTest_complex_orthogonality and
compactTest_complex_overlap_positive explicitly transport these real integrals
using intervalIntegral.integral_ofReal. These discharge the target-side
orthogonality and fixed nonzero overlap requirements without added assumptions.
The overlap FLOOR for a varying source still must follow from hmode.

Canonical q3_check exit0; all36 printed dependency lists standard only.
Independent recovery_review checked endpoints, sign, correct degree4 behavior,
C-infinity scope, and real-to-complex transport, approving the final hash.
Current dependency oleans used; preexisting UnicodeBasic and style warnings
remain. No fresh-clone validation or production admission.

Next: normalize/scalar-transport actual selected-mode flux on [-1,1], obtain
its weak identity through compact_flux_green, and derive uniform numerator
bounds and the eventual overlap floor from hmode. This turn does NOT prove
the selected htheta rate. hmode and finite-ground/off-line-zero-free bridges
remain open. PX_RH_CLAIM: NOT_MADE.

## Actual anchored selected modes supply the concrete weak ODE

Candidate SHA256 ebb3cd2a325ba5a5174b09068bd56263720b03bf0b1fb3d59761226ee316103e.
prolateFlux=(lambda^2-x^2)*deriv f is C1 on the open source window from
ContDiffOn2 f; prolateFlux_hasDerivAt converts the literal project
prolateWaveExpression to its exact flux derivative. The normalized Ferrers
instance uses committed regularity and ODE, not a new source equation premise.

prolate_compact_weak applies compact_flux_green on [-1,1]. lambda>1 places
the entire closed test interval inside the regular source window, so no
singular source endpoint estimates are needed. Test flux derivative is
(lambda^2-x^2)*phi''-2*x*phi'; all required local integrability follows from
continuity. Arbitrary constant complex alpha is transported through both
integrals without division or nonzero assumptions.

CompactWeakODE records exact potential m*(4pi^2*x^2)-theta and test flux
m*phi''-x^2*phi''-2*x*phi'. normalized_mode_weak_ode proves this dictionary
using sqrt(m)^2=m. selected_anchored_weak_ode instantiates the actual stored
solutions0/4 and center scalars, with theta=classicalEigenvalue(index0/2)+g.
The mode labels, normalization and shifted eigenvalue are not changed.

selected_anchored_concrete_test_weak has only k as input: the mode0 equation
uses complex compactTest0 and the mode4 equation uses complex compactTest4.
Their smoothness and derivative boundary conditions are supplied internally.
complex_compactTest_derivatives proves both first/second complex derivatives
equal the corresponding cast real derivatives globally, closing the exact
interface with compactTest_complex_orthogonality.

Canonical q3_check exit0; all44 printed dependency lists standard only.
Independent recovery_review checked domain inclusion, signs, source/scalar
identity, specific test pairing, derivative transport and final hash.
Current dependency oleans used; preexisting UnicodeBasic and style warnings
remain. Saved log has trailing whitespace normalized; proof bytes unchanged.
No fresh-clone validation or production admission.

Next: combine this actual weak identity with target orthogonality and signed
defect identity; bound its two numerator integrals and source overlap from
hmode, uniformly in k, and conclude eventual htheta. No hmode or derivative-
error premise was needed for the weak ODE itself. The selected htheta RATE
is still unproved; hmode, finite-ground and off-line-zero-free bridges remain
open. PX_RH_CLAIM: NOT_MADE.

## Compact quantitative estimates and uniform scheduled theta bound

Candidate SHA256 5a2581b17a5e14100d20dbbbe87ecaa8bd5bf91780c806332841c88e966c245d.
For continuous f,D,g on [-1,1], compact_product_error_bound proves
norm(integral((f-D)*g)) <= epsilon*integral(norm g) from the sup error.
compact_overlap_floor derives the actual source overlap floor J/2 when
J=norm(integral(D*phi)) and epsilon*integral(norm phi)<=J/2.
compact_source_pairing_bound controls integral(f*T) by the fixed target
pairing plus epsilon*integral(norm T). No derivative-error estimates used.

compact_theta_bound_of_mode_error combines these with the previously checked
signed identity. For m>=1,C>=0,J>0, sup error<=C/m and
2*C*integral(norm phi)<=J*m, its conclusion is

 |theta-e*m| <= 2*(C*integral(norm A) + norm(integral(D*T))
                    + C*integral(norm T))/J.

The source-overlap floor is derived, not an independent premise. Continuity
provides all compact integrability. The identity itself remains an explicit
input until the actual-source/target lemmas are assembled.

scheduled_theta_bound fixes e,C,J,D,phi,A,T BEFORE quantification over k.
With m=k+2, eventual mode error and eventual signed identity imply existence
of one nonnegative B bounding |theta_k-e*(k+2)| eventually. exists_nat_ge and
J>0 discharge the finite overlap threshold; max(0,B) ensures output sign.
Thus independence of k is part of the theorem signature, not prose.

Canonical q3_check exit0; all49 printed dependency lists standard only.
Independent recovery_review checked constants, denominator threshold and fixed
family quantifiers, and approved final hash. Current dependency oleans used;
preexisting UnicodeBasic/style warnings remain. Saved log whitespace normalized.
No production admission or fresh-clone proof claim.

Next exact joint: instantiate the signed identity for the actual anchored
mode0/test0 and mode4/test4 from checked weak ODE, orthogonality and derivative
dictionary; feed the fixed target/test inputs and hmode to scheduled_theta_bound,
then combine constants for the actual htheta port. This actual selected
instantiation is NOT yet claimed. hmode, finite-ground matching and off-line
zero-freeness remain open. PX_RH_CLAIM: NOT_MADE.

## Actual selected theta rate and direct mode-only W5/N2 consumers

Candidate SHA256: 83a4bb5ee70b2b523aeccedf6f482a8b8887b7f95f30a3d4eb563be915adcfbd.
selected_theta_rate_of_mode_rate now derives the actual shared nonnegative
eventual htheta constant from exactly the center-anchored full-window hmode
used by the existing W5/N2 ports. The construction uses fixed compact tests,
the proved actual weak ODE and target orthogonality, restricts hmode to [-1,1],
and uses lambda_k^2=k+2. The spectral indices are 0 and 2, both with +g shift;
the target coefficients are 2*pi and 18*pi. No derivative-error hypothesis.

Together with selected_chi_rate_of_mode_rate, this removes two independent
analytic rate premises. selected_projection_tail_of_mode_rate invokes the
existing W5 rate assembly from hmode AND the explicit hFamily crosswalk.
selected_locally_uniform_xi_of_mode_rate invokes the existing N2 assembly and
returns local uniform convergence of the exact constructed
selectedFerrersCofinalShell.centeredPstar to centeredXi on centeredCriticalStrip.
It existentially supplies the actual Cchi/hCchi/hchi used to construct that shell.

Validation: scripts/q3_check.sh /tmp/Q3FourierOverlap.lean, exit0, q3_check ok;
all printed theorem dependencies are propext, Classical.choice, Quot.sound.
Independent recovery_review audited actual indices, constants, quantifiers and
consumer connections. Current dependency oleans used; preexisting UnicodeBasic
and style warnings remain; no fresh-clone validation or production admission.

This is a conditional theorem about the analytic selected family, NOT RH.
hmode remains unproved. Full-window uniform O(1/(k+2)) approximation, with the
exact selected branches and center anchoring, is now the one remaining rate
supplier for these two analytic consumers. It is not the only remaining premise
of Route B: production-family matching, finite-ground tracking/coercivity and
off-line zero-freeness are separate. Production theorem/consumer binding remains
unselected. Next work: exact hmode supplier audit/proof, without circularly
assuming either derived spectral rate. PX_RH_CLAIM: NOT_MADE.

## Source recheck and corrected quasimode route to the remaining hmode

Primary source re-read locally: Meixner-Schaefke (1954),
`docs/routeB_bus/litreview/pdfs/978-3-662-00941-3.pdf`, SHA256
f56225d83e49ea439e28ab85c7f59942c3d3a3ddba913026ade59c8bfe85604d.
Printed pp241-243, especially Satz9 on printed243/PDF255 (render inspected,
not just OCR); mechanism reference §2.333, printed143-144. Precise short quote:
"gleichmäßig in [-1, 1]".
The rendered remainder is O(gamma^(-3/4)) with prefactor (4gamma/pi)^(1/4).
Dividing by the leading scale produces O(gamma^(-1)), as CCM(7.10) reports.
The older card's source-availability and unresolved-binding statements are
historical: this PDF is present here, and current DirectCylinderRate already
proves the conditional centered bind. It still assumes both raw rate inputs.

The book's mechanism is more informative than its asymptotic statement:
construct a finite Weber combination with high-order residual, use spectral
separation to control the orthogonal error, then an integral eigenrelation
upgrades the mean estimate to a uniform estimate. §2.333 uses bounded cosine
kernels; its direct application to this prolate normalization is not assumed.
No new unchanged semantic query was issued: prior registered query is still
INCOMPLETE on freshness with positive hits, not a no-hit receipt.
Classification remains exploratory INCOMPLETE_NO_CONSUMABLE_TARGET.

### Exact first correction in the project's physical equation

Let t=sqrt(pi)*x, m>0, and
L_m = -d_x^2 + 4*pi^2*x^2 + m^(-1)*(x^2*d_x)' .
For n=0,4, put e_n=pi*(4*n+2), beta_n=-((2*n+1)^2+5)/8,
D_n(x)=exp(-t^2)*P_n(t), and
u_nm(x)=exp(-t^2)*(P_n(t)+Q_n(t)/(pi*m)).
The polynomials are

 P0=1,
 Q0=3*t^2/8-t^4/4,
 P4=3-24*t^2+16*t^4,
 Q4=129*t^2/8-183*t^4/4+28*t^6-4*t^8.

Thus beta0=-3/4, beta4=-43/4, and both corrections vanish at the center.
For T(P)=t^2*P''+(2*t-4*t^3)*P'+(4*t^4-6*t^2)*P,
the exact identities are

 -Q_n''+4*t*Q_n'-4*n*Q_n = beta_n*P_n-T(P_n),
 (L_m-e_n-beta_n/m)u_nm = exp(-t^2)*R_n(t)/(pi*m^2),
 R_n=T(Q_n)-beta_n*Q_n.

R0=81*t^2/32-167*t^4/16+7*t^6-t^8.
R4=8643*t^2/32-26121*t^4/16+2548*t^6-1354*t^8+264*t^10-16*t^12.
The accompanying Fraction checker solves and verifies the exact polynomial
identity for each n; no floating point, no fitted coefficients. This is PAPER
algebra evidence, not Lean certification. Gaussian-polynomial integrability
then bounds the L2 residual on every [-sqrt(m),sqrt(m)] by A_n/m^2, where A_n
is pi^(-5/4)*||exp(-t^2)*R_n(t)||_L2(dt) on the whole line. The physical
flux coefficient 1-x^2/m vanishes at both endpoints for this smooth function;
membership in the project's particular spectral operator domain must still
be established, not inferred solely from this flux observation.

### Why the stronger residual matters, and the exact remaining entrance

Suppose a separately proved spectral theorem supplies, on the same window,
a rank-one spectral projection onto the intended selected even branch, and
uniform distance delta>0 from e_n+beta_n/m to every OTHER eigenvalue of L_m.
Projection of u_nm then has L2 error O(m^(-2)). This is a CONDITIONAL mechanism;
the isolation and branch match are not proved here and may not be imported
from htheta, which was itself derived from hmode.

A naive Fourier upgrade of the O(m^(-1)) difference from D loses sqrt(lambda),
where lambda=sqrt(m), and gives only O(m^(-3/4)). Instead split the projected
function as u_nm plus its O(m^(-2)) projection error. The latter contributes
O(m^(-7/4)) by Cauchy-Schwarz on a window of length 2*sqrt(m); the explicit
Q_n correction contributes O(m^(-1)) because its whole-line L1 norm is finite.
The omitted Gaussian-polynomial tails are exponentially small. A Fourier
pairing with D_n, using its nonzero squared norm, gives chi=1+O(m^(-1)) from
L2 closeness, so division by chi is eventually legal; it does not need hchi
as an extra premise. Uniform control at the center then permits the existing
center-normalization transfer. This is a proposed PAPER completion route,
not an established hmode theorem.

Negative controls: no spectral separation leaves the projection error
uncontrolled; the wrong eigenvalue index does not identify our selected mode;
an arbitrary scalar multiple violates the fixed center target. The corrected
quasimode discriminates these issues but does not solve them.

Next bounded joint: inspect existing classical even Jacobi/Ferrers spectral
results for the uniform scaled isolation and branch identification, with the
trial u_nm's operator-domain membership explicit. Do not add further wrappers
that merely assume hmode. Finite CCM ground is a different object from this
analytic prolate spectral branch. PX_RH_CLAIM: NOT_MADE.

Independent recovery_review approved the exact algebra and residual bound,
and explicitly retained operator-domain, spectral-branch, normalization and
Fourier-defect obligations. The quasimode itself is not a Fourier eigenfunction.
Checker SHA256: fa623ef35c66cd778b35400318bcdde502941c9b5b9090f64be09a7aebc8c1cf.
