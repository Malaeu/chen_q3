TO: MAT

# ADVICE DENSITYSD — the DENSITY law has a name: self-decomposable (class L), OU-type stationary law, T = (π/2)·S₂ of Pitman–Yor (observer, 2026-09-12 01:40)

Owner's word (2026-09-12 ~01:15): «запустить наш скилл на поиск литературы по нашему вчерашнему протоколу». Object taken from
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DENSITY_2026-09-11.md` (DN2, DN11, DN12, DN13, DN20, DN22). Alias-hunt contract
(`.agents/skills/alias-hunt/SKILL.md`) followed by hand: shelf first, three dictionaries, numbers before agents, no proof admission.
Shelf before this note: `./ask.sh` for Biane / perpetuity / Vervaat / Bondesson / «smoothing transform» — no source match (shelf INCOMPLETE in the
cloud container: q3_docs freshness failed, zeta23 unresolved). `git grep` over origin/rh_clean: «self-decomposable» appears once, as a dictionary
word in the Codex 11.09 protocol (line 3745), never as a source-backed statement; GGC named in SLACK_INDEPENDENT_CHECK line 357 as «not excluded».
BPY (arXiv math/9912170) IS on the shelf, LFS sha256 04a444275e5522cef9a1ba9f7d1b9f20a752764d3548f9c48be6dbc055bb12ea, and DENSITY reads it.

## Verified by the observer (rule 13; script `docs/routeB_bus/density/theta_law_sd_check.py`, log `theta_law_sd_check_20260912.log`)

Notation as in DENSITY: Z = Σ_{n≥2} Γ(2,1)/(π(n²−1)), L_Z(z)=Π_{n≥2}(1+z/(π(n²−1)))^{-2}; T = shifted-rate law of DN2 with
L_T(z) = 4π² L_Z(z+π)/(z+π)²; θ(x)=Σ_{n∈ℤ} e^{−πn²x}.

(I1) **L_T(z) = Π_{n≥1}(1+z/(πn²))^{−2} = (√(πz)/sinh√(πz))².** Proof: the factor (z+π)^{-2}·π² is the n=1 term, Π_{n≥2} n²/(n²−1)=2 absorbs the 4;
     then Π_{n≥1}(1+w/n²)=sinh(π√w)/(π√w) with w=z/π. Numerically: relative difference equals the truncation bound 2z/(πN) at z=0.3, 1, 5.
     Hence **T = (π/2)·S₂** in the notation of Pitman–Yor 2003 (E e^{−λS_t}=(√(2λ)/sinh√(2λ))^t), i.e. DENSITY's full object is the
     t=2 member of the hyperbolic «S» family, the same S₂ that BPY tie to ξ. Every closed formula of PY03 for S_t (Lévy measure, moment/cumulant
     recursions, Mellin recursion, ODE for the Laplace transform) applies to T verbatim after the scale π/2.

(I2) **T (and Z) are self-decomposable.** DN11–DN12 (ρZ′+Y_ρ ~ μ for every ρ∈(0,1), Y_ρ an honest law) is exactly the definition of class L.
     For sums of gammas this is classical (GGC ⊂ SD, Bondesson 1992). The background driving Lévy process (BDLP) L of T is explicit:
     κ_L(z) = z·κ_T′(z) = −2 Σ_{n≥1} z/(πn²+z) = ∫₀^∞ (e^{−zx}−1)·(−θ′(x)) dx, so **the Lévy density of L on x>0 is −θ′(x) = 2π Σ_{n≥1} n² e^{−πn²x}**
     (infinite activity: ∫₀^∞ −θ′ = ∞). Checked at z=2 to 1e−10 between the series and the Lévy-integral form; z·κ_T′ by finite difference agrees to 6e−6.
     Each gamma component alone has a compound-Poisson BDLP (rate 2, Exp(πn²) jumps), which is the «Bernoulli-exponential» of DN11.

(I3) **The half-thinning of DN11 at ρ=1/2 is the OU-type flow over time log 2:** log L_T(z) − log L_T(z/2) = ∫₀^{log 2} κ_L(e^{−u}z) du,
     i.e. Y_{1/2} = ∫₀^{log 2} e^{−u} dL_u in law, and X_{log 2} = ½X₀ + Y_{1/2} is one step of the stationary Markov process
     dX = −X dt + dL_t with invariant law T. Checked at z=1, 3, 10 to the truncation error.

Z-versions of (I2)–(I3) follow from the shift DN2 (rate π removed, n=1 term removed); not separately tabulated.

## What the literature says (cards: `docs/routeB_bus/litreview/DENSITY_SELFDECOMPOSABLE_HUNT_USAGE_CARDS.md`)

- SD ⟺ stationary law of an OU-type process driven by a Lévy process: Wolfe 1982 (ℝ), Jurek–Vervaat 1983 (Banach, DOI 10.1007/BF00538800, OA),
  Sato–Yamazato 1984 (DOI 10.1016/0304-4149(84)90312-0), Sato 1999 Thm 17.5. Relay via OA secondary statements quoted in the card; primaries not read here
  (PDF egress blocked in the cloud container; `./paper.sh <doi>` from the workstation pulls them).
- Gamma marginal ⇒ compound-Poisson BDLP with exponential jumps: Barndorff-Nielsen–Shephard 2001 (DOI 10.1111/1467-9868.00282), OA restatement in
  Nicolato–Venardos 2003. Independently rederived above (κ_L = zκ′_X), so this line does not rest on the relay.
- Perpetuity / fixed point Y = AY′ + B: Vervaat 1979 (DOI 10.2307/1426858, abstract quoted in the card) — DN12 is this equation with A=ρ deterministic.
- Hyperbolic family, S₂ ↔ ξ: Pitman–Yor 2003 (DOI 10.4153/CJM-2003-014-x, OA), BPY 2001 (on shelf).

## What this changes and what it does not (my reading, marked as mine)

- It does NOT pay DN20. Nothing found gives positivity of a form averaged over μ⊗μ for an SD law.
- It NAMES the wall. In OU language the two «conditioning states» of DN13/DN22 are values of the stationary process; the half-thinned copies are
  P_{log 2}-images. The one classical source of free positive-definiteness for a Markov semigroup is μ-symmetry (reversibility): then P_t is
  self-adjoint and ⪰ 0 on L²(μ). A Lévy-driven OU-type process is NOT μ-reversible unless Gaussian — this is your own «nonreversible stationary
  law» remark (protocol 11.09 line 3742) now with a theorem-shaped reason. So the negative odd direction of DN8/DN10 should live in the
  antisymmetric part of P_{log 2} on span{φ(i+·)}. If it does, DN22 is measuring nonreversibility, and no amount of thinning repairs it.
- What it OPENS with a name: the symmetrised semigroup ½(P_t + P_t*) on L²(T) and its spectral positivity on the finite subspaces of DN22;
  the excursion representation of T (Lévy/BPY: S₂ = law tied to the maximum of a Bessel-3 bridge), which turns μ-integrals into expectations of
  excursion functionals; PY03's Lévy measure of S₂ for the odd-parity remainder in DN20.

## Probe (cheapest, no new grids) and branches

P1. On the saved DN22 data (a=0.7, ρ=1/2, nodes 1,2): write M_{ij} = V_φ(i,j) − V_φ(i,−j) as ⟨F_i, (P_{log 2} + P*_{log 2}) F_j⟩_{L²(T)} plus the
    explicitly known first term, using (I3). Decide by exact algebra whether the identity holds; one afternoon, no Proshka.
P2. If P1 holds: split P_{log 2} = S + A (symmetric/antisymmetric in L²(T)). Compute the DN10 negative odd direction's Rayleigh quotients on S and on A.
IF_A (negativity sits in A): the wall is nonreversibility of the theta OU-type process; record it as the exact obstruction, stop thinning repairs,
    and the next object is a reversible surrogate with the same marginal T (does one exist with the arithmetic coupling? that is the Proshka question).
IF_B (negativity already in S): the OU dictionary is a rename; record, keep DN22 as the discriminator.
Observer's numbers: (I1)–(I3) correct 0.95 (three-line proofs plus numerics); dictionary pays DN20: 0.15; dictionary names the wall precisely: 0.5.
Three attempts, at most one Proshka request, PAPER scope. Not a proof, not an admission, PX_RH_CLAIM: NOT_MADE.
