# Catalogue of local zero invariants — zero side, prime side, symmetries, and what flips exactly at the line (2026-09-08)

Status: observer's paper catalogue (Linux-Claude), UNVERIFIED by a second channel except where a locator says so.
Owner's frame: «everyone looks at a zero and sees a zero; we look at a zero as the place where the global system left
its imprint». Question: does a combination of local invariants exist whose sign / phase / reality changes EXACTLY
when ρ leaves the critical line, and which has a prime-side representation?

Conventions: ξ(s) = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s); Ξ(t) = ξ(½+it) real for real t; centred λ = ρ − ½; the two symmetries
are s ↦ 1−s (λ ↦ −λ) and s ↦ s̄ (λ ↦ λ̄); their composite j: λ ↦ −λ̄ fixes exactly the critical line. The zero set is
closed under both. The signed explicit formula (KERNEL (K16), checked to 34–41 digits): Q(f,g) = Σ_λ m_λ conj(F_f(jλ)) F_g(λ).

## A. The catalogue

| # | Invariant at a zero ρ (λ = ρ−½) | Zero-side form | Prime-side representation | Under λ ↦ −λ | Under λ ↦ λ̄ | Exact flip at the line? |
|---|---|---|---|---|---|---|
| 1 | Re λ | itself | none directly; only through sums Σ_ρ f(ρ) (row 6) | −Re λ | Re λ | trivially: Re λ = 0 ⟺ on line; not prime-side |
| 2 | Multiplicity m_λ = Res_{s=ρ} ξ′/ξ | residue | Σ_ρ m_ρ F(ρ) = explicit formula (von Mangoldt side) | invariant | invariant | no; m is real > 0 on and off the line |
| 3 | ξ′(ρ) | derivative | none local; ξ′ is the global function | ξ′(1−ρ) = −ξ′(ρ) | conj | PARTIAL: on the line ξ′(ρ) is purely imaginary (Ξ real ⇒ ξ′(½+iγ) = −iΞ′(γ)); off the line Re ξ′(ρ) ≠ 0 generically but not necessarily (no exact flip) |
| 4 | Phase arg ξ′(ρ), the local «direction» of the zero | ξ′(ρ)/|ξ′(ρ)| | none | rotates by π | conjugates | no exact flip; on the line the phase is ±π/2 exactly, off it wanders continuously |
| 5 | The jump of S(t) = π^{−1} arg ζ(½+it) at t = γ | +m at each on-line zero | S(t) has a prime-side expression (Selberg: smoothed −π^{−1} Σ Λ(n)n^{−½−it}/log n + error) | — | — | YES for on-line zeros (jump), NO for off-line ones (the pair leaves a smooth dip on the line, no jump). But the prime-side formula for S(t) is only asymptotic/smoothed; the jump itself is Ξ-side |
| 6 | Zero moments Σ_ρ f(ρ) for entire f (e.g. Li: λ_n = Σ_ρ[1 − (1−1/ρ)^n]) | sum over zeros | explicit formula: archimedean + Σ_n Λ(n)(…) (Bombieri–Lagarias for Li) | pair-symmetric | real for real f | NO exact flip for any fixed f: an off-line pair contributes 2Re f(λ) which varies continuously in Re λ; the FLIP lives in positivity of the whole family (Li: λ_n ≥ 0 ∀n ⟺ RH) |
| 7 | Oscillation exponent of ψ(x) − x carried by ρ: the term x^ρ/ρ | Landau/Littlewood: a zero with Re ρ = θ forces ψ(x) − x = Ω_±(x^{θ−ε}) | this IS the prime side (ψ counts prime powers) | x^ρ ↔ x^{1−ρ}: amplitudes x^{θ}, x^{1−θ} | conj | NO exact flip: the pair merges into a single amplitude √x at θ = ½ continuously; what changes exactly is the NUMBER of distinct amplitudes (2 → 1) |
| 8 | Reality of Ξ at the zero: Ξ(γ) = 0 with Ξ real | sign change of a real function | none (Ξ real is the functional equation + reflection, not a prime statement) | — | — | YES: N₀(T) (sign changes of Ξ) vs N(T) (argument principle, prime-side via Riemann–von Mangoldt + S): N(T) − N₀(T) = 2·#{off-line pairs below T}. The flip is exact and integer; the prime side computes N, never N₀ |
| 9 | The local block of the Weil form at the zero (KERNEL (K16), (K23a)) | on line: rank-1 term m|F(λ)|² (signature (1,0)); off line: pair term m[conj F(jλ)F(λ) + c.c.] (signature (1,1)) | Q is prime-side computable for every test | — | — | YES, EXACT and DISCRETE: local signature (1,0) → (1,1) the instant λ ≠ jλ. This is the imprint. But it is an invariant of a FORM (needs the whole family of tests), not a scalar |
| 10 | Isotropy of the separating test h_λ (KERNEL (K21)–(K22): F_{h_λ}(λ) ≠ 0, = 0 at every other distinct zero) | Q[h_λ] = m_λ |F_{h_λ}(λ)|² if λ = jλ; Q[h_λ] = 0 if λ ≠ jλ | Q[h_λ] is computable from primes + archimedean part once h_λ is built; h_λ needs λ (integral division of Φ) | h_λ ↔ h_{−λ} | h_λ ↔ h_{λ̄} | YES, EXACT: the scalar r(λ) := Q[h_λ]/‖h_λ‖²_ℰ is > 0 on the line and EXACTLY 0 off it. The one scalar in this table with an exact flip and a prime-side evaluation — at the price of knowing λ to build the test |
| 11 | Sign of the hyperbolic pairing Q(h_λ, h_{jλ}) | = m_λ conj F_{h_λ}(jλ)... (nonzero iff λ ≠ jλ) | prime-side computable given λ | — | — | complementary to row 10: nonzero exactly off the line |
| 12 | Local Rayleigh quotient of the null family: Q[g_k] = 0 (ALIGN) | 0 for all zeros, on or off | prime-side computable (checked to 1e−16) | — | — | NO: the null family is blind to the line by construction; it is the radical, not a detector |
| 13 | Our window operators: λ_a (lowest eigenvalue of A_a on [−a,a]) and n₋(a) | λ_∞ = 0 (RH) / −∞ (¬RH), SCREW (S24) | A_a is built from the screw function (primes inside) | — | — | YES in the limit and discretely (n₋(a) integer), but only through the exhausting family; no single window decides, and the first-touch a_* (H17) is where the imprint would first show |
| 14 | de Bruijn–Newman parameter Λ | Λ = 0 (RH) vs Λ > 0 | theta/Fourier side; no Euler product for t ≠ 0 (shelf 05.09) | — | — | YES (Λ ≥ 0 proved, RH ⟺ Λ = 0) but global, not local to one zero |

## B. What the table says
1. **Every invariant with an EXACT flip is a reality/signature statement** (rows 5, 8, 9, 10, 11, 13): «Ξ is real», «the local block is (1,0) not (1,1)», «h_λ is not isotropic». They are all the same fact: λ = jλ. None of them has a prime-side representation that does not pass through Ξ or through an object built with knowledge of λ.
2. **Every invariant with a prime-side representation independent of λ varies CONTINUOUSLY in Re λ** (rows 2, 6, 7): moments, oscillation exponents, counts N(T). An off-line pair leaves a continuous imprint (amplitude x^θ, moment 2Re f(λ)), never a sign flip at θ = ½. The discrete flip appears only when one quantifies over a family (Li ∀n, Weil ∀f): the family converts «continuous in θ» into «some member goes negative iff θ ≠ ½».
3. So the owner's «imprint of the global system» is exactly right and exactly located: the imprint is the local SIGNATURE of the Weil form at the zero, (1,0) versus (1,1). It is prime-side computable test by test, and it is discrete. What does not exist is a single prime-side scalar, computable without knowing λ, that flips. This is not a theorem of impossibility; it is what the fourteen rows show, and rows 6–7 show why (continuity in θ).
4. **The one scalar that flips exactly, row 10:** r(λ) = Q[h_λ]/‖h_λ‖²_ℰ. Positive on the line, zero off it. It costs knowing λ. Its use is not as a detector but as a CONTROL for any proposed positive representation: any candidate square ‖Xf‖² with the right kernel must give ‖Xh_λ‖² = 0 for off-line λ — impossible to test on ζ (no off-line zero known) but testable on a function that HAS off-line zeros: Davenport–Heilbronn.

## C. Candidate and probe (rule 19)
CANDIDATE (p = 0.5 that it survives a fresh check): row 10 is a correct, exact, prime-side-evaluable local invariant; rows 1–14 exhaust the natural local invariants up to the four symmetries; no λ-free prime-side scalar flips.
PROBE (cheapest decisive, hours): the Davenport–Heilbronn control. The DH function has a functional equation, no Euler product, and known off-line zeros. Build its signed «Weil form» Q_DH from its explicit formula (Dirichlet-coefficient side + archimedean), its theta-type null test Φ_DH, the separating tests h_λ, and compute r_DH(λ) at (i) an on-line zero, (ii) an off-line zero. ЕСЛИ_A: r > 0 at (i), r = 0 at (ii) to precision — row 10 is honest, and the catalogue's «flip = signature» conclusion is verified on a function where the flip actually happens; the same code then measures how any proposed square X of ours behaves at a real off-line zero. ЕСЛИ_B: r_DH ≠ 0 at (ii) or ≤ 0 at (i) — a bookkeeping error in the catalogue (conjugation/j-convention), to be found before anything else.

Locators: KERNEL (K16), (K19)–(K23a) and its check; ALIGN (A22)–(A28) and its check; SCREW (S24) and its check; Davenport–Heilbronn 1936 (Titchmarsh §10.25); Landau/Littlewood Ω-theorems (Ingham ch. V); Li 1997 / Bombieri–Lagarias 1999 (relay, from the literature map); de Bruijn–Newman: Rodgers–Tao 1801.05914 (shelf).

## D. Executed on the owner's «го» (2026-09-08): the decisive step turned out to be a lemma, not a run
Before building the Davenport–Heilbronn instrument I asked what number it would decide. Its stated purpose — «r_DH > 0 on
an on-line zero, = 0 on an off-line zero» — is a tautology of the definition of h_λ (its transform vanishes at every
other zero by construction), and the conjugation bookkeeping it would exercise is already verified on ζ by the KERNEL
checker ((K16) to 34–41 digits, (K20)–(K22) to 1e−17). A run would have confirmed arithmetic, not decided anything.
The substantive claim of §B.2 («no λ-free prime-side scalar flips exactly at the line») is instead a five-line lemma:

**Lemma (no exact flip for zero-moment invariants).** Let f be entire with f(−z̄) = conj f(z) (equivalently f real on
the imaginary axis), and let S_f(λ) := f(λ) + f(jλ) be the contribution of the j-orbit of a centred zero λ to the
zero-moment Σ_ρ f(ρ − ½). Then (i) S_f(λ) = 2 Re f(λ) is REAL for every λ, on or off the line — no reality or phase
flip is possible; (ii) S_f is real-analytic in Re λ, so its sign cannot change exactly at Re λ = 0 unless S_f(iβ) = 0
for the on-line value, i.e. f(iβ) = 0; (iii) if S_f vanishes at every on-line point iβ then f ≡ 0 on iℝ, hence f ≡ 0.
Proof: (i) f(jλ) = f(−λ̄) = conj f(λ); (ii) analyticity of f; (iii) identity theorem. ∎
Consequence: every prime-side representable invariant of the form Σ_ρ f(ρ) (moments, Li coefficients, smoothed counts,
ψ-oscillation amplitudes, which are Σ_ρ x^ρ/ρ) is blind to the line pointwise; the only way such invariants see the
line is through a FAMILY (Li ∀n, Weil ∀ tests), where «some member changes sign» is a discrete event. The exact-flip
invariants (rows 5, 8, 9, 10, 11, 13) are all statements «λ = jλ» in disguise and need λ or Ξ. This is the owner's
«imprint»: it is real, it is the local signature of the Weil form, and it is visible from the prime side only as a
property of the whole test family, never as one number. Observer's paper lemma, UNVERIFIED by a second channel.

DH instrument: DEFERRED, not cancelled. Its genuine use is as a test bed for a PROPOSED square X (KERNEL (K1)-type or
any future one): evaluate ‖X h_λ‖² at a real off-line zero of the DH function, where ζ offers no such zero. It is
worth building the day a candidate X exists; today none does.

## E. Corrections from Prošhka's SIGNATURE/CLOSURE supplement (d6243e9f, 2026-09-08)
- Multiplicity is a WEIGHT, not a dimension: the pair block is m_λ[[0,1],[1,0]] of inertia (1,1) for every m; sig(Q̄) = (∞, r) with r = number of DISTINCT off-line j-orbits (SC4)–(SC5); an off-line quartet gives (2,2). Rows 9 and 13 above are to be read with this count.
- The pole summand P has signature (1,1) as a summand, but is NOT an intrinsic hyperbolic plane of the full Q: Q[Φ] = 0 while P[Φ] = 2|ξ(1)|² > 0 (SC10)–(SC11). The fibre-class analogy is a picture, not a theorem.
- Window index n₋(a) is finite, nondecreasing, and sup_a n₋(a) = r (SC13): negative directions are visible on a FINITE window; RH ⟺ n₋(a) = 0 ∀a. My «the wrong limit is born only at infinity» holds only for nonzero locally uniform limits of the real-zero bricks, not for the inertia of the form.
- Under ¬RH what must fail is target IDENTIFICATION (Rouché defect (SC26)), not convergence as such.
