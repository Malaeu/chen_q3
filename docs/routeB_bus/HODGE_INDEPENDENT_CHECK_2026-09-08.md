# HODGE_PRIMITIVE_SIGN_DEPENDENCY_AUDIT — independent check

Target: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_HODGE_2026-09-08.md`
Auditor: fresh Claude checker, own derivations. Scripts: `chk1.py` (envelope/countermodel/fibre),
`chk2.py` (H7 exterior algebra, H9 block, H14 symbolic), `chk3.py` (H10 mechanism, H14 float),
`chk4.py` (H14 at 50 digits). Extracted sources: `S26.txt`, `CC22.txt`, `CC20.txt`.
No repository file touched, no commit, no subagent.

## Verdict per item

**(1) §1.2 curve bound, (H1)–(H4) — CORRECT, and Hodge-free.**
- Curve bound `h⁰_H(L) ≤ max(0,e+1)`: correct. Reconstructed argument: if `h⁰ > e+1`, the e+1
  point-vanishing conditions leave a nonzero section whose divisor is effective of degree ≥ e+1 > e
  on the integral curve H — contradiction. Needs H integral and ≥ e+1 distinct closed points
  (free over an algebraically closed field). The verdict's phrase "leaves negative degree" is a
  compression of exactly this; sound.
- (H1)/(H2): restriction `0→O(L−H)→O(L)→O_H(L)→0` gives `h⁰_X(L) ≤ h⁰_X(L−H)+h⁰_H(L|_H)`,
  `deg(L|_H)=L·H`. Iterating `k=⌊d/h⌋+1` times ends in negative H-degree, where effective-degree
  positivity kills the surface term. I recomputed the resulting sum independently for all
  `h∈[1,8]`, `d∈[−5,60)` and it equals `B_H(d)` of (H1) on every cell. **Direction correct**
  (upper bound), uniform in L at fixed degree.
- (H3): `nD·H=0 ⇒ h⁰(nD) ≤ B_H(0)=1`; `(K−nD)·H = K·H` (n-independent, because `D·H=0`) so
  `h²(nD)=h⁰(K−nD) ≤ B_H(K·H)`. `C_H` is n-free. Correct.
- (H4): `χ ≤ h⁰+h²` uses only `h¹≥0`; RR gives `n²D²/2 − nD·K/2 + χ(O) ≤ C_H`, hence
  `D² ≤ (D·K)/n + 2(C_H−χ(O))/n² → 0`. All inequality directions correct. Checked the
  contrapositive numerically: `D²=+1` breaks the constant bound for large n on 2000 random
  `(D·K, C_H, χ₀)`. Ingredients used: RR for surfaces, Serre duality, `h^i ≥ 0`, ampleness of H.
  **No Hodge index / Hodge–Riemann positivity enters.** Confirmed.
- (H5): `h¹(nD) = n²q/2 + n(D·K)/2 + h⁰ + h² − χ(O)` with `q=−D²` — sympy residual exactly 0.
  The weakening `h⁰+h² = o_D(n²)` does suffice; the verdict's insistence that this envelope, not
  `h⁰≥0`, is the load-bearing content is correct.

**(2) Countermodel (H6) — CORRECT and VALID.**
Exhaustive check on `x=(a,b)`, `|a|,|b| ≤ 12`: `h⁰−h¹+h² = χ₀ + B(x,x)/2` holds on every cell;
`h²(x)=h⁰(K−x)=h⁰(−x)` holds; all dimensions are nonnegative integers. `H=(1,0)`: `H²=2>0`,
`H·D=0`, `D²=2>0`. `h⁰(nD)=1+n²` is exactly the o(n²) envelope failing. So "nonnegative counts
+ RR + Serre duality alone" does **not** force `D²≤0`. The refutation is of the abstract
implication only — the model has no effectivity/restriction, which the verdict states plainly.
Valid as written.

**(3) §1.3 equality case and fibre computation — CORRECT.**
`(D+tE)² = 2t(D·E)+t²E² ≤ 0` for all real t forces `D·E=0` (linear term dominates near t=0, both
signs available). With `D·H=0` and `h=H²>0`, any class splits as `F=(F·H/h)H+E`, `E·H=0`, so
`D·F=0` for all F: D numerically trivial. Negative-definiteness on the primitive quotient follows.
Rational extension by clearing denominators (`(mD)²≤0 ⇒ D²≤0`) and real extension by continuity
are both legitimate.
Fibre computation: with `a=D·F₁`, `b=D·F₂`, `D₀=D−bF₁−aF₂`, sympy gives `D₀·F₁=D₀·F₂=0` and
`D₀² − (D²−2ab) = 0`. Since `H=F₁+F₂` is ample (`H²=2`) and `D₀·H=0`, (H4) applies. Correct.

**(4) §1.5 (H7) — CORRECT (pointwise algebra); its global input is imported, not derived.**
Explicit exterior-algebra computation in the orthonormal coframe `x¹,y¹,x²,y²`, complex
orientation `vol = x¹∧y¹∧x²∧y²`, `ω₁=x¹∧y¹`, `ω₂=x²∧y²`:
`α = r(ω₁−ω₂)`, `ω = ω₁+ω₂`:  `α∧ω = 0` (primitive), `*α = −α`, `α∧α = −2r²·vol`,
`α∧*α = +2r²·vol = ‖α‖²·vol`. So `−∫α∧α = ∫α∧*α = ‖α‖²_{L²} ≥ 0`, with equality iff `α≡0`.
I also checked the *general* real (1,1) form (diagonal a,b plus both off-diagonal real types):
`α∧ω ∝ a+b`, so primitivity ⟺ `a+b=0`, and then `α∧α = (−2a²−2p²−2q²)vol ≤ 0` — the normal
form used by the verdict is not a loss of generality. Correct.
The step "a primitive class admits a *pointwise* primitive representative" is [DN, Prop. 2.4],
cited, not derived here and not verifiable in this audit — see ASSERTED-NOT-DERIVED below.

**(5) §2.3 (H9)–(H10) — CORRECT, with one unstated (true) hypothesis and one sketched passage.**
From (K16) `Q(f,g)=Σ_λ m_λ conj(F_f(jλ))F_g(λ)` and separators with `F_{e_λ}(μ)=δ_{λμ}` over
distinct zeros, one gets `Q(e_μ,e_λ)=m_λ·[μ=jλ]`. j-fixed zero → `(m_λ)`, positive 1×1.
Two-element orbit → `m[[0,1],[1,0]]`: eigenvalues `±m`, rank 2, inertia (1,1). `Q[e_λ]=0`,
`Q(e_{jλ},e_λ)=m`, `Q[e_λ−e_{jλ}]=−2m` — reproduces KERNEL (K23a). Multiplicity scales the block
and does not add coordinates: correct, and consistent with supplement (SC1)–(SC4) (which states
the same inertia `(s,r)` and the same quartet accounting `(2,2)`).
*Unstated hypothesis:* the single symbol `m_λ` in the 2×2 block presumes `m_λ = m_{jλ}`. That is
true (`Λ_ξ(z)=Λ_ξ(−z)` and `Λ_ξ(conj z)=conj Λ_ξ(z)` give equal orders at λ and `−conj λ`), but it
is not written down. WORDING-class. Likewise "for every m" should read "for every `m ≠ 0`".
*Index counting:* the upper bound mechanism is sound and I re-derived it: `2m Re(conj(b)a)` with
`a=F_f(λ)`, `b=F_f(jλ)` equals `(m/2)(|a+b|²−|a−b|²)`, so imposing the k complex conditions
`F_f(λ_i)=F_f(jλ_i)` leaves every surviving term nonnegative; 20 000 random draws with k=3
off-line and s=6 on-line coordinates produced no negative value. k complex functionals cannot
annihilate a subspace of complex dimension > k, so `ind₋ ≤ k`; the separator span gives `ind₋ ≥ k`.
`ind₊=∞` from (K14) on the infinite-dimensional `(∂²−1/4)C_c^∞(I)` is legitimate but is KERNEL's
result, inherited.

**(6) §3.1 (H11)–(H13a) — CORRECT; source reading confirmed verbatim.**
`T=A_a−τ`, `‖f‖²_T = Q_W^a[f] − τ‖f‖²₂`, so `Q = ‖f‖²_T + τ‖f‖²₂` (H12) is an identity, not a
theorem — which is exactly the verdict's point: when `τ<0` it is not a sum of nonnegative terms.
(H13): `A_a=diag(−1,1)`, `τ=−2 < λ_a=−1` (admissible), `T_a=diag(1,3)>0`, `Q[e₁]=−1`. Refutes the
abstract inference "positive shifted metric ⇒ positive unshifted form". Correct.
(H13a): `A_{a,c}−τ_c I = A_a−cI−(τ−c)I = A_a−τI = T_a` — exact, so `T_a`, its completion, the
derivative realisation `D_a`, the deficiency spaces and `W` are literally unchanged, while
`Q_c[f]=Q[f]−c‖f‖²<0` for `c>Q[f]/‖f‖²`. The logic is valid, and the verdict itself labels it a
falsifier of a structure-only inference rather than a replacement of zeta's Q. Confirmed.

**(7) §4 (H14) — CORRECT. This is the load-bearing reduction and it stands.**
Antilinear-first, `Q(f,g)=f*Mg`, M Hermitian. Symbolic (general 2×2 with complex off-diagonal):
`Q(u,w)=0`; `Q[w]−(Q[v]−|Q(u,v)|²/Q[u]) = 0`; `Q[f]−(Q[u]+s²Q[w]) = 0`, so at
`s=√(Q[u]/−Q[w])` we get `Q[f]=0`; `Q(u,f)−Q[u]=0`. All residuals identically zero.
Numerically: 3910 admissible random 3×3 Hermitian indefinite cases at 50 digits — **0 violations**
(a single float-precision hit at double precision vanished at 50 digits).
Converse: `Q≥0`, `Q[f]=0` ⇒ `Q[f+tg] = 2Re(t Q(f,g)) + |t|²Q[g] ≥ 0` for all complex t; choosing
`t = −ε·conj(Q(f,g))/|Q(f,g)|` gives `−2ε|Q(f,g)| + ε²Q[g] ≥ 0`, impossible for small ε unless
`Q(f,g)=0`. So nonnegative ⇒ null rigidity, and (H14) gives the converse under a positive anchor.
The anchor is genuinely needed (without it, `Q ≤ 0` trivially satisfies null rigidity); the
verdict supplies it from (K14) and says so.

**(8) (H15) — CORRECT.** `⟨g,Af⟩=Q(g,f)` and Riesz give `sup_{‖g‖=1}|Q(g,f)|² = ‖Af‖²`, vanishing
exactly on `ker A = 𝒩_pt`. Taking `g=e_{jλ}/‖e_{jλ}‖` on an off-line block gives
`Δ(e_λ) ≥ m_λ²/‖e_{jλ}‖²_ℋ > 0` while `Q[e_λ]=0`. Correct, and it is a genuine discriminator:
it separates "zero energy" from "annihilated by every pairing".

**(9) Reading claims — all three READ.**
- **CC22 arXiv:2205.01391 — READ** (26 pp., "Riemann-Roch for Spec Z"). Thm 1.1:
  `dim_{S[±1]}H⁰(D) − dim H¹(D) = ⌈deg′D + log′2⌉′ − 1_L`. Thm 1.2:
  `H⁰(K−D) ≃ Hom_{ΓT*}(H¹(D), U(1)_{1/4})`, `K=−2{2}`. The verdict's two claims are exactly right:
  genuine integer dimensions and Serre-type duality **do** exist, and the Euler characteristic is a
  rounded *degree* — hence **linear** in n along nD, not a quadratic intersection coefficient.
- **Suzuki arXiv:2606.09096v1 — READ** (30 pp.). (1.9) verbatim: "Choose λ such that `λ_a > λ`,
  and define `T_a = T_{a,λ} := A_a − λI`. Since `T_a` is positive, `‖v‖²_{T_a} := ⟨T_a v,v⟩_{L²} =
  Q_W^a(v) − λ‖v‖²_{L²}`" — i.e. (H11) is quoted correctly, with τ = λ. (1.10) domain
  `C_c^∞(−a,a)`; deficiency indices (1,1) (Lemmas 6.1–6.2); (1.11) and Thm 1.5 (all zeros of
  `W(a,θ;z)` real, unconditionally) as described. (1.12) target is `z²ξ(1/2−iz)/ξ′(1/2−iz)` —
  meromorphic, matching the verdict's `z²ξ/ξ′` and its v1/32-page-version caution. Thm 1.4 is
  "for sufficiently small a>0", so the verdict's warning against reading it as positivity on a
  whole interval is right. §7: "Section 7 proceeds under the assumption `A_a>0`" (which the paper
  derives from RH) — the verdict's "opening of §7 assumes RH" is accurate in substance.
  **Independent corroboration of the verdict against its own prediction:** the paper states that
  failure of RH ⟺ `λ_a < 0` for some `a>0`. So the sign defect is visible at a *finite* window,
  which is precisely why `P_SUZUKI_REALISES_ONLY_WINDOW` is correctly marked REFUTED_AS_STATED.
  The paper also says control of `λ (< λ_a)` "is expected to require a detailed analysis of the
  arithmetic contribution coming from the prime terms" — the same gap (H13a) names.
- **CC20 arXiv:2006.13771v1, App. C, Prop. C.1 (155) — READ**: `RH ⟺ Σ_v W_v(g*ḡ^7) ≤ 0` for all
  `g∈C_c^∞(ℝ*₊)` with `g̃` vanishing on a finite `F ⊇ {0,1}`. Locator, statement and the two Mellin
  conditions are as the verdict describes; the sign flip relative to the project's Q is stated
  openly, not hidden.
- DN (math/0501449, Prop. 2.4) not fetched in this audit — NOT VERIFIED here.

## First asserted-not-derived step

**§1.5, the pointwise-primitive representative [DN, Prop. 2.4].** (H7) itself is pure pointwise
linear algebra and I verified it, but the passage from a cohomologically primitive class to a
representative that is primitive *at every point* is imported wholesale, and it carries the entire
compatibility burden of the analytic route. The verdict flags this itself in §9 ("that theorem can
hide the entire compatibility burden"), so it is a labelled import rather than a concealed gap.

Second, and inside the registered strip: **§2.3's one-sentence "Continuity and compact-core
approximation transfer this bound to ℋ"** for (H10). It is a sketch, and it sits next to the
verdict's own refusal to assume absolute convergence of the two-variable zero series for every
pair in ℋ. It is repairable and I supply the repair: the functionals `ℓ_i(f)=F_f(λ_i)−F_f(jλ_i)`
are ℋ-continuous by (K15)/(K9); approximate `f∈ℋ` by compact smooth pole-null `f_n`, correct each
`f_n` by a vanishing multiple of the separators to enforce `ℓ_i=0` exactly, apply (K16) on the
compact core to get `Q[f_n']≥0`, then use boundedness of Q (`‖A‖≤65/3`) to pass to the limit.
Also unstated-but-true: `m_λ = m_{jλ}` in (H9).

## Adjudication

**`P_HODGE_STRIP_SURVIVES_INDEPENDENT_AUDIT` (0.90) — CONFIRMED / TRUE.**
(H2), (H9) and (H14) all survive, each re-derived here from scratch, and **no new positivity
assumption was needed at any point**. (H2) uses only RR, Serre duality, `h^i≥0` and ampleness of
H. (H9) uses only (K16) plus separator existence. (H14) is elementary Hermitian algebra and needs
only the pre-existing (K14) anchor. Nothing in the strip was repaired to make it pass.

**Is the countermodel (H6) valid? Yes.** All three named identities (nonnegative integer
dimensions, RR with `χ₀+B(x,x)/2`, duality `h²(x)=h⁰(K−x)`) hold on the whole lattice, while
`H²=2>0`, `H·D=0` and `D²=+2`. "Nonnegative counts + RR + duality alone" therefore do not force
the sign. It refutes the abstract implication as stated, and nothing more — which is what the
verdict claims.

**Does (H14) "null rigidity + positive anchor ⇒ Q ≥ 0" stand? Yes.** Symbolically exact and
numerically exact to 50 digits; the converse holds too, so null rigidity is *equivalent* to
nonnegativity given the anchor — an honest reformulation, not a weakening. What it does not do is
make the arithmetic easier, and the verdict says so in §5 in exactly those terms: the passage from
null rigidity to the sign is easy, and proving null rigidity for the source is the unpaid work.

**No defect found.** Findings are WORDING-class only: "for every m" should exclude m=0; `m_λ=m_{jλ}`
should be stated; the ℋ-transfer in (H10) deserves the four-line argument above instead of one
clause. Every UNKNOWN cell I inspected in the §2.2 table reads as an unproved supplier, not as a
claimed absence theorem, and no analytic RH supplier is marked closed.
