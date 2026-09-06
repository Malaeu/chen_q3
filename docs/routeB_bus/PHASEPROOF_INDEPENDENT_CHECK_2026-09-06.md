# PHASEPROOFCHECK — independent re-derivation of PROSHKA_VERDICT_GOAL058_PHASE_CLASS_INEQUALITY_AND_MOLLIFIER_CROSSWALK_2026-09-06

Items 1–12, re-derived from the two verdicts' own definitions and re-computed here (python3
numpy/sympy/mpmath/scipy; scripts `c1.py c2.py c3.py c4.py c5d.py c6.py c8b.py c8c.py`). Sources
opened: the verdict, parent [ST], `zeta23/full.txt`, `2403.01247.pdf` (→ `ccm.txt`). Nothing else.
Constants: a = log2 = 0.69314718, r = 2^(−1/2), w = ar = 0.49012907, δ = (log3−log2)/8 = 0.05068314,
a+2δ = 0.79451346 < log3 = 1.09861229, c_A = γ+log(8π)+π/2 = 4.42744401.

## 1. Lemma 1 (pole-null parametrization) — **CORRECT**
K(y)=2sinh(y/2) has K(0)=0, K′(0)=1, so η″ = h + η/4 identically. Numerics (σ = δ/2):
- h = (∂²−¼)η: A±(h) = 5.9e−17 (machine zero); η reconstructed to 1e−10 on supp η and
  |η_rec| ≤ 3e−18 outside — compactly supported.
- h = η (not pole-null): A− = A+ = 0.011251643; η_rec outside supp equals
  e^{x/2}A−(h) − e^{−x/2}A+(h) to 10 digits (x = 1.5σ, 2σ, 5σ). So compact support ⟺ A± = 0.
Support ⊆ conv(supp h) ⊆ I; injectivity from {e^{x/2},e^{−x/2}} having no compact member; realness
and parity preserved. The open-Fourier-gap remark is standard Paley–Wiener and correct.

## 2. Lemma 2, (4)–(5) — **CORRECT**
Hν_a = Re⟨Z,U_aZ⟩; U_a=(I−B)/r gives (4); ‖(I−U_a)Z‖² = 2‖Z‖²−2Re⟨Z,U_aZ⟩ gives the first form of
(5); B*B = (1+r²)I−r(U_a+U_a*) gives the second. Random complex 6×6 tests (Z arbitrary, U_a Haar
unitary, B = I−rU_a), 3 trials: (4) and both forms of (5) agree to 1e−14.
Caveat (not an error): n(v_θ) = n₀+ν_a cosθ needs the mixed HS product real (real h, as [ST] states);
for generic complex Z a −Im(·)sinθ term appears. θ = 0 and π are exact regardless and only θ = π is
used, so nothing downstream is affected. Norm bounds give only 0 ≤ n₀−ν_a ≤ 2n₀ — confirmed.

## 3. Lemma 3, (6)–(8) — **CORRECT**
(6) Gram(V₀) = [[I,C],[C,I]] because F_∞ is a self-adjoint involution; P_ran = V₀Gram^{−1}V₀*.
Finite model (n=12, m=4, F random ±1 spectral involution, J isometry, ‖C‖ = 0.863): P₀ from (6)
equals the reference orthoprojection onto (ran J + ran FJ)^⊥ to 5e−15, idempotent and self-adjoint.
The ‖C‖<1 argument (attainment would give f and F_∞f both supported in (0,1)) is valid and needed.
(7) e_j^± are orthonormal (⟨·,·⟩ = 2δ_ij(1±α_j), cross terms (α_i−α_j)δ_ij = 0) and I−Σ|e_j^±⟩⟨e_j^±|
reproduces (6) exactly. (8a–c) V = BP₀G^{−1/2} is an isometry, VV* = S₂ (S₂²=S₂=S₂*, rank 9), Φ_j
orthonormal. Circulant/shift model (N=16, U_a cyclic shift, random rank-9 P₀, random circulant T_h):
n₂ = Σ|ĥ|²k₂ (20.876556265557458 vs …447), Hν_a = Σcos(aξ)|ĥ|²k₂ (−7.768123822890354 vs …349),
n₀−ν_a = Σ(1−cos aξ)|ĥ|²k₂ — all to 1e−14; k₂ invariant under a random unitary change of basis of
H₀. Normalisation self-consistent: ĥ(ξ)=∫he^{−iξx}dx, F = (2π)^{−1/2}ĥ, F(T_hΦ)=ĥ·FΦ.

## 4. (9)–(10) sandwich — **CORRECT**
G = (1+r²)(I−qA), q = 2r/(1+r²) = 0.94280904 (verified to 1e−15). Scalar remainder
(1+r²)^{−1}(qx)^{2d+2}/(1−qx) on [−1,1] is ≥0 and ≤ q^{2d+2}/(1−r)² = ε_d because 1−q = (1−r)²/(1+r²);
eigenvalues of G^{−1}−R_d land in [7e−13, 2.1] ⊂ [0,ε_d]. ZZ* = C_hG^{−1}C_h*, so ‖(I−U_a)Z‖²/2 =
Tr(D_hG^{−1}D_h*) (28.644680088447814 both sides). Sandwich (10) holds for d = 0,1,2,3,5, and the
minus-phase cancellation is indeed performed inside D_h before the inverse is replaced.
Practical note (not an error): ε_d < 1 only from d ≥ 20 (ε_0 = 10.36, ε_20 = 0.983).

## 5. (12) exact remainder identity — **CORRECT**, and the 3.927236 value reproduces
For ‖v‖=1, ‖v‖²−C_v(t) = ∫(1−cos tξ)|Fv|²dξ, hence D(v)−c_A‖v‖² = ∫q_∞(ξ)|Fv(ξ)|²dξ with exactly
the verdict's q_∞. Summing a_∞(t)=Σ_j e^{−(2j+1/2)t} gives the **closed form**
q_∞(ξ) = Re ψ(¼+iξ/2) − log π (using ψ(1/4) = −γ−3log2−π/2, c_A = γ+log8π+π/2) — the standard Weil
archimedean multiplier, an independent confirmation of the c_A/q_∞ normalisation. Quadrature vs
closed form: ξ = 0, 0.5, 2 to 12 digits; ξ = 7, 25 to 8 digits (tail).
|Fv₋|² = (1−cos aξ)|ĥ|²/(2πH) and C_{v₋}(a) = −½ give
L₂(v₋) = w + (1/H)∫(1−cos aξ)|ĥ|² q_∞/(2π) dξ, while (8c) gives n₂(v₋) = (1/H)∫(1−cos aξ)|ĥ|²k₂.
Subtracting is exactly (12). Two-channel numerical check for h = (∂²−¼)η_σ:

| σ | H | L₂(v₋) Fourier channel | L₂(v₋) time channel (D(v₋)−c_A+w) | A₀+J_a+w | J_a |
|---|---|---|---|---|---|
| δ   | 8.32205e4 | 3.927236130 | 3.927236130 | 3.927236130 | 4.5962e−7 |
| δ/2 | 6.65740e5 | 4.620430907 | 4.620431080 | 4.620431080 | 1.4088e−8 |

The σ = δ row reproduces the reported L₂(v₋) = **3.927236** to all printed digits. J_a > 0 strictly,
confirming [ST]'s correction of the "identical archimedean energy" claim. The inequality half of
(12) is of course not checked — it is the declared open sign.

## 6. (13), (13a), 2×2 leakage — **CORRECT**
Exact (sympy): G = 3/2, G^{−1} = 2/3, P₀(B*B)^{−1}P₀ = ½[(1−r)^{−2}+(1+r)^{−2}] = **6**, ratio
exactly **9**. (13a) re-derived: B*K_vB = B*BK_v; insert P₀+Q₀; P₀B*BP₀ = G cancels G^{−1} leaving
n_∞(v); P₀B*BQ₀ = −rP₀(U_a+U_{−a})Q₀. General 14-dim shift model: n₂−n_∞ = 1.065803244159964 vs
RHS 1.065803244159958. 2×2 model gives exactly √2(k₂−k₁)/3 = (2r/3)(k₂−k₁), sign-indefinite as
claimed. (13b) is consistent: L₂(v₋) = L_∞(v₋)+w, so n₂ ≤ L₂ ⟺ e_∞(v₋)+leak ≤ w.

## 7. §3.2 vs CCM 2403.01247 — **CORRECT** (measure, matrix and inference all check out)
Quoted from `ccm.txt`: Thm 6.6 — "Let p be a prime, and dµ be the measure on R given by dµ(s) =
|1/(1−p^{−1/2−is}) · Γ(1/4+is/2)|² ds" (the verdict's (14) up to the stated scalar normalisation;
§3.2: L_∞(½−is) = π^{−1/4}Γ(¼+½is), dµ_S = |∏_{v∈S}L_p(½−is)|² ds). §2.2 — "We assume that the
measure dµ is even… The moments c(n) are 0 for odd n… X P_n = a_{n−1}P_{n−1}+a_nP_{n+1}, a_n ≠ 0",
with the displayed X having **zero diagonal** (eq. (3)). Prop 3.1 — "The moment problem … is
determinate."
The density is even (|Γ(¼+is/2)|² and |1−p^{−1/2−is}|² = 1+p^{−1}−2p^{−1/2}cos(s log p) both even), so
the zero-diagonal form applies; it is strictly positive and locally integrable on R, so supp µ = R
and (determinacy ⇒ essential self-adjointness) σ(X) = R: unbounded, indefinite. **The argument is
valid.** The 2×2 compression [[0,a₀],[a₀,0]] has eigenvalues ±a₀, so ⟨Xv,v⟩ < 0 for some polynomial
v, while G ≥ (1−r)²I = 0.0858·I > 0 and ‖G‖ ≤ (1+r)²; unitary equivalence preserves spectrum and
positivity, so no literal identification is possible. The verdict's own limitation ("a relation
through a new function of the Jacobi operator and a projection is not excluded") is correctly
stated, and the integrality claim really is about q-series coefficients of the Jacobi /
orthogonal-polynomial data, not about Sonin projections, G^{−1}, or traces of smooth bumps.

## 8. (20)–(21) — **CORRECT**
Zero lattices of M₂(s) = (1−2^{3/4−s})(1−2^{−1/4+s}): s = ¾−2πik/a and s = ¼+2πik/a, i.e.
γ = ∓id+2πk/a with d = ¼. Poisson over each lattice gives Σ_ρ f̂(γ_ρ) = aΣ_n f(na)(e^{−dna}+e^{dna})
= 2a‖v‖²+4aΣ_{j≥1}cosh(dja)C_v(ja) — the verdict's (20). Explicit bump (σ = 0.3, f(ja)=0 for j≥1):
partial zero-sums K=0: 0.0355150622 → K=20: 0.0553489599 → K≥50: **0.0553489617** = 2a f(0) = RHS,
10 digits. (An earlier run of mine showing a sign flip was quadrature aliasing, not a defect.)
For v₋: Q_M(v₋) = 2a − 2a cosh(a/4) = **−0.020866177122** = −δ_M, δ_M = 2a(cosh(a/4)−1) > 0. ✔
(21): log 3 = 1.09861 > a+2δ = 0.79451, so every C_v(j log3) = 0 and Q_{M₃}(v) = 2log3·‖v‖² =
2.1972245773·‖v‖² > 0. ✔ Consistency with [ST](14): 𝔪_♯ = 𝔪 − δ_M ⟺ e_♯ = e + δ_M. ✔

## 9. (24)–(27) three-lobe matrix — **CORRECT**
Polarising L₂₃−n₂₃ on v_z = Σ z_iU_{c_i}h, c = (0,a,b), disjoint lobes, reproduces (24)–(25) term by
term: diagonals give A₀−n₀²³; the (0,1) cross term collects −J_a, −w₂ = −a/√2, −ν_a²³; likewise
(0,2) with w₃ = b/√3 and (1,2) with no prime atom at b−a = log(3/2). Cross-distances are ≥ 0.2877
apart, above the correlation width 2δ = 0.10137, so the weights in (24) are exact. (23)'s weights
are the standard (log p)p^{−j/2}: a/√2, b/√3, a/2. b+2δ = 1.2000 < log4 = 1.38629, so C_v(2a)=0 for
this family while (23) still needs the 4-term in general — as the verdict says.
sympy: RᵀDR = [[2d₀−2d₀₁, d₀−d₀₁−d₀₂+d₁₂],[·, 2d₀−2d₀₂]] (exactly (26)); det = 3d₀²−2d₀d₀₁−2d₀d₀₂
−2d₀d₁₂−d₀₁²+2d₀₁d₀₂+2d₀₁d₁₂−d₀₂²+2d₀₂d₁₂−d₁₂², which is exactly 4(d₀−d₀₁)(d₀−d₀₂)−(d₀−d₀₁−d₀₂+d₁₂)²
— condition (27). Plant [[1,2],[2,1]]: eigenvalues 3, −1; value on (1,−1) is **−2**. ✔

## 10. (30)–(31) — **CORRECT**
(30) expands to Σ_{i,j}B(u_i,u_j)conj(B(u_i,u_j)) = Σ|W_ij|² = ‖W‖²_HS; finite algebraic identity, no
positivity or completion used. (31) is the parallelogram law (41.602504165704 both sides, random
5×5 complex). W_t = diag(1,t): ‖W_t‖²_HS = 1+t², centered second difference 2s²; W_t(v,v) =
|v₁|²+t|v₂|² is affine, second difference 0. At s=1: **2 vs 0**. ✔
Cross-check of the window dictionary (28) against `full.txt` §2.2–2.3: ψ ∈ C²([−½,½]), ψ>0,
ψ_MT(s)=cos(√2 s)1_{[−1/2,1/2]} (2.6); ϕ(u)=χ(L/2+u)χ(L/2−u)ψ(u/L)^{1/2} (2.7); α_k = T+2πk/L;
a := ‖ϕ‖²₂/L; supp(ϕ∗ϕ) ⊂ [−L,L] = [−log X, log X]; G̃, Ẽ as in (2.10) with prefactor (aL²)^{−1} and
(2.11) (G̃+Ẽ)_{kk'} = (aL²)^{−1}∫ϕ̂(τ−α_k)ϕ̂(τ−α_{k'})ν_X(τ)dτ. So s_ψ = (a_ψL²)^{−1} and
(29) G̃ + Ẽ_height = s_ψ W match the paper. ✔

## 11. (33)–(34) — **CORRECT**
W = N_S−E_S+Π is the polarisation of [ST]'s Q(v) = L₂(v)+P₀₂(v) with e = n−L₂; Π has the right
diagonal 2Re(A₊conj(A₋)) and rank ≤ 2; contact term ℓ = log(TW) = 0 at cutoffs 1. (34) is the
correct HS expansion, all three cross-term signs right: 159.395587133637 = 159.395587133637 (random
complex 5×5). (35) |∫_T^{2T}e^{it log(n/m)}dt| ≤ min(T, 2/|log(n/m)|) ✔; and |n−m| ≍ X/T with n ≍ X
gives |log(n/m)| ≍ 1/T, i.e. no oscillation — the stated regime is correct.

## 12. (36)–(37), R(ψ) — **CORRECT**
`full.txt`, Lemma 5.6 (Window constant), verbatim: "R(ψ) := [∫_{−1/2}^{1/2}ψ² + ∫∫|u−v|ψ(u)ψ(v)dudv]
/ (∫_{−1/2}^{1/2}ψ)²… Then R(ψ₀) = 4/3 and R(ψ_MT) = ½ + (1/√2)cot(1/√2) = c_MT^{−1}." The
verdict's (36)/(37) reproduce this exactly, including the derivation G := ψ+Kψ, G″ = ψ″+2ψ = 0 for
ψ_MT = cos(√2u), G ≡ G(0) = cos s + sin s/√2 (s = 1/√2), ∫ψ = √2 sin s, R = G(0)/∫ψ.
Numbers (mpmath, 30 dps): R(ψ_MT) = 1.3274992963205884; **2 − R(ψ_MT) = 0.67250070367941165**,
matching the paper's "2 − c_MT^{−1} = 0.67250…"; ½(3−c_MT^{−1}) = 0.83625035183970582 matching
"0.83625…"; c_MT = 1/R = 0.75329606785607068 = √2 tan(1/√2)/(1+(1/√2)tan(1/√2)) (the paper's
displayed c_MT, radical restored after pdftotext loss). R(ψ₀) = 4/3 exactly; 2−4/3 = 2/3, the
Theorem A constant. Direct 400-node quadrature of (36) gives 1.3333316 and 1.3274975 (slow
convergence — the |u−v| kernel is only Lipschitz), consistent.
The verdict's repair "the request has an extra factor ½ in the cotangent term" is consistent with
the paper's cot(1/√2); the request itself was not opened.

## Verdict
**No mathematical error found in items 1–12.** Every identity I could test independently reproduces
exactly, several through a second channel (time-domain vs Fourier for (12); direct HS trace vs
kernel sum for (8a–c); Poisson-lattice sum vs autocorrelation form for (20); closed digamma form vs
quadrature for q_∞; the paper's printed decimals for R(ψ_MT)). §3.2's inference against the q-series
Jacobi identification is valid on the PDF's own statements. **Consequences for the RESULT codes:
none — no code needs to change.** In particular
`Q2a: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE`, `SCOPED_REFUTATIONS`
(CCM_QSERIES…, DROP_PROJECTION_FROM_INVERSE, SOURCE_LINEAR_SINGLE_TEST…) and
`REMAINING_SIGN: SEMITABLE_R1_MINUS_AT_FIXED_CUTOFF_1 / UNRESOLVED` are all supported by what I
verified; the boxed inequality in (12) is genuinely untouched by any of these identities.

**UNVERIFIABLE within the permitted reading set** (flagged, not faults):
1. §6.4's Lamzouri dictionary — [L26] was not opened. Its internal algebra does check: under the 2π
   convention (f″)^ = −4π²z²f̂, so (32)'s multiplier is 1+π²z²/(log T)²; and with ρ−ρ′ = i(γ−γ′),
   z = (γ−γ′)L/2π, w^{−1} = 1+(γ−γ′)²/4 = 1+π²z²/L². Consistent.
2. §4.3's reading of `NoFiniteStencilMinorant`'s quantifiers (the theorem file was not opened).
3. §4.2's characterisation of [AF] §1.4 on Davenport–Heilbronn robustness (not located in the
   17-page text I have; the conclusion drawn — no native split supplied — is a negative claim I
   cannot falsify from these sources).
4. "The reported margin near 0.34" and the A/B table values — outside the permitted files.
5. Nothing here is a kernel certificate: paper algebra plus float/30-dps numerics, exactly the
   status the verdict itself assigns (`NEW_DERIVATIONS: VERIFIER: PAPER`).

**Two presentational nits** (no consequence):
- Lemma 2 omits the reality hypothesis under which n(v_θ)=n₀+ν_a cosθ holds for all θ ([ST] states
  it); (4), (5), (8b), (8c) and everything used downstream are unconditional, so nothing breaks.
- ε_d ≥ 1 for all d ≤ 19 (ε_0 = 10.36), so the upper leg of (10)/(17) carries no information until
  d ≥ 20; §3.3's instruction to report the inverse tail separately already covers this.
