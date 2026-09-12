# DENSITY law under other names — alias hunt 2026-09-12 (observer, cloud container)

Object: the θ-probability law of DENSITY (verdict 2026-09-11): Z = Σ_{n≥2} Γ(2,1)/(π(n²−1)) with the thinning fixed point ρZ′+Y_ρ ~ μ (DN11–DN12),
and the shifted-rate law T with L_T(z)=4π²L_Z(z+π)/(z+π)² (DN2). Negative control (from the verdict): DN8 (conditional positivity false on a
positive-measure box) and DN10 (every symmetrised finite-gamma approximant has a negative odd direction). Consumer: DN20 / DN22.
Three dictionaries used: probability (self-decomposable, class L, OU-type stationary law, BDLP, perpetuity), special functions (hyperbolic
Laplace transforms, Pitman–Yor S_t, GGC/Thorin, HCM), operator (Markov semigroup P_t on L²(μ), reversibility). Tools reachable from the
container: Scite, Scholar Gateway, `./ask.sh` (INCOMPLETE here). arXiv API and publisher PDFs are blocked by the egress proxy (CONNECT 403), so
no external file was hashed; every DOI below is an intake candidate for `./paper.sh <doi>` from the workstation.

Observer-verified mathematics (numbers by hand, `docs/routeB_bus/density/theta_law_sd_check.py` + log): T = (π/2)·S₂ (PY03 notation);
BDLP Lévy density of T is −θ′(x); half-thinning at ρ=1/2 = OU increment over time log 2. See ADVICE_2026-09-12_DENSITYSD.md.

## Cards (all external sources: metadata via Scite/Scholar Gateway; primary text NOT read here unless stated)

### PITMANYOR-2003 — Pitman & Yor, "Infinitely Divisible Laws Associated with Hyperbolic Functions", Canad. J. Math. 55 (2003) 292–330, DOI 10.4153/CJM-2003-014-x, OA (bronze)
VERBATIM (abstract, via Scite): "The infinitely divisible distributions on R+ of random variables C_t, S_t and T_t with Laplace transforms
(1/cosh√2λ)^t, (√2λ/sinh√2λ)^t and (tanh√2λ/√2λ)^t respectively are characterized for various t > 0 … by corresponding relations between the
distributions and their Lévy measures, by recursions for their Mellin transforms, and by differential equations satisfied by their Laplace
transforms. … The distributions of C_1 and S_2 are also known to appear in the Mellin representations of two important functions in analytic
number theory, the Riemann zeta function and the Dirichlet L-function associated with the quadratic character modulo 4."
Mapping: our L_T(z) = (√(πz)/sinh√(πz))² = E e^{−(πz/2)S₂}, so T = (π/2)S₂ exactly (observer, I1). Their t = our shape 2 per gamma term.
Gives: closed Lévy measure, moment/cumulant recursions, Mellin recursion and Laplace ODE for T. Does not give: any sign for DN20. Not read: body.
Smart-citation snippet (via Scite, section "poisson interpretations"): "S_2 is the sum of two independent random variables with the same
distribution as S_1 and T_1(R_3)" — the excursion/Bessel-3 reading of T.

### JUREKVERVAAT-1983 — Jurek & Vervaat, "An integral representation for selfdecomposable Banach space valued random variables", Z. Wahrsch. verw. Geb. 62 (1983) 247–262, DOI 10.1007/BF00538800, OA (bronze)
VERBATIM (Smart-citation snippet from the paper, section "introduction and notations"): "This is the major result of the present paper. It
generalizes results of Wolfe (1982) for E=ℝ, but also gives completely new proofs." The result: X selfdecomposable ⟺ X = ∫₀^∞ e^{−t} dL_t for a
Lévy process L with E log⁺|L_1| < ∞. Mapping: DN12 with all ρ ⟺ this representation; the BDLP of T is the L with Lévy density −θ′ (observer I2).
Strength: exact fit for the dictionary (theorem), no sign content. Not read: text.

### SATOYAMAZATO-1984 — Sato & Yamazato, "Operator-selfdecomposable distributions as limit distributions of processes of Ornstein-Uhlenbeck type", Stoch. Proc. Appl. 17 (1984) 73–100, DOI 10.1016/0304-4149(84)90312-0, closed
Metadata only (Scite; 202 citing publications). Content relayed through OA secondary sources below (Sato 1999 Thm 17.5 is the textbook form).
Relay, not verified from the primary.

### VERVAAT-1979 — Vervaat, "On a stochastic difference equation and a representation of non-negative infinitely divisible random variables", Adv. Appl. Prob. 11 (1979) 750–783, DOI 10.2307/1426858, closed
VERBATIM (abstract, via Scite): "The present paper considers the stochastic difference equation Y_n = A_n Y_{n−1} + B_n with i.i.d. random pairs
(A_n, B_n) and obtains conditions under which Y_n converges in distribution. This convergence is related to the existence of solutions of
[Y =d AY + B] … A second subject is the series Σ C_n f(T_n) with (C_n) i.i.d., (T_n) the points of a Poisson process … The resulting random
variable turns out to be infinitely divisible, and its Lévy–Hinčin representation is obtained."
Mapping: DN12 is Y =d ρY′ + B with deterministic A=ρ; the series subject is the shot-noise form of the same object. Strength: exact fit for the
fixed-point dictionary; no sign content.

### BARNDORFFNIELSENSHEPHARD-2001 — Barndorff-Nielsen & Shephard, JRSS-B 63 (2001) 167–241, DOI 10.1111/1467-9868.00282, closed
Metadata only. The needed fact (gamma marginal ⇒ compound-Poisson BDLP with exponential jumps; κ_L(z)=zκ_X′(z)) is restated in OA form by
NICOLATOVENARDOS-2003 and rederived by the observer (I2), so nothing here rests on the relay.

### NICOLATOVENARDOS-2003 — Nicolato & Venardos, "Option Pricing in Stochastic Volatility Models of the Ornstein-Uhlenbeck type", Math. Finance 13 (2003) 445–466, DOI 10.1111/1467-9965.t01-1-00175 (secondary, via Scholar Gateway)
VERBATIM (§2): "It is well known that for any selfdecomposable law D there exists a Lévy process Z such that the process of the OU type driven by
Z has invariant distribution given by D (see Sato 1999, Sec. 17). Moreover, the cumulant function of D … and the cumulant function of Z_1 are
related through the formula (2.7) (see Barndorff-Nielsen 2001). … the stationary distribution of σ² is a gamma law Γ(ν,α). It follows from (2.7)
that such a process can be obtained when the BDLP has cumulant function given by (2.10). The BDLP of a Γ-OU process is in fact a compound Poisson
process since its Lévy density is given by (2.11)." Use: OA quotable statement of the two facts above; formulas (2.7)/(2.11) not reproduced in
the excerpt, observer's own derivation stands in.

### BONDESSON-1992 — Bondesson, "Generalized Gamma Convolutions and Related Classes of Distributions and Densities", LNS 76, Springer, DOI 10.1007/978-1-4612-2948-3, closed
Metadata only (331 citing publications). Needed facts: GGC ⊂ SD ⊂ ID; HCM ⊂ GGC. Codex's HCM exclusion for the θ-density (commit b7bf286e) is
consistent: T is a GGC (sum of gammas with summable rates) that is not HCM. Not read.

### Already on the shelf, re-found
PBIANEANDJPITMANANDMYOR-1999 (arXiv math/9912170, `pdfs/math_9912170.pdf`, LFS sha256 04a444275e5522cef9a1ba9f7d1b9f20a752764d3548f9c48be6dbc055bb12ea):
the S₂ ↔ ξ Mellin identities that DENSITY already uses (their (14)–(25), Prop. 1).

## Rejected / not pursued
- Lindner–Sato 2011 (generalized OU, quasi-infinite divisibility): different object (random A), noted only.
- Widder/Bernstein k(x+y)-kernel criteria: V_f is not Hankel (SL20 card); unchanged.
- No Deitmar / Hallouin–Perret search repeated here: that hunt is the observer's Sonin card, currently uncommitted on the workstation.

## Intake manifest for the owner (separate authorized actions)
`./paper.sh 10.4153/CJM-2003-014-x`, `./paper.sh 10.1007/BF00538800`, optionally 10.2307/1426858, 10.1016/0304-4149(84)90312-0,
10.1111/1467-9868.00282, 10.1007/978-1-4612-2948-3. Then this card gets file hashes and the primary quotes replace the relays.
