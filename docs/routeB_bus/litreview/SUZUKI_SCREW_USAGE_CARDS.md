# Suzuki, Weil's Quadratic Form via the Screw Function (arXiv:2606.09096) — verified usage cards

Source PDF: pdfs/2606.09096.pdf

Author: Masatoshi Suzuki. Version of June 9, 2026 (arXiv:2606.09096v1, math.NT, 8 Jun 2026). 30 pages.
MSC 2020: 11M26 42A82 46E22 47B25.

Scope note for the reader (not a quote): the paper's global claim is that Theorems 1.1, 1.3, 1.4, 1.5
are all obtained **without assuming RH**; Corollary 1.6 is a **conjecture** whose truth would imply RH;
Section 7 (de Branges isomorphism) is an explicitly **heuristic** discussion carried out **under RH**.
No RH closure is claimed by this worker.

---

## 1. Screw function definition + main object (operator / quadratic form) — Eq. (1.3) p.3; Thm 1.2 [13] cited p.3–4; Eqs. (1.4)–(1.6) p.4; Eq. (1.1) p.2

VERBATIM (the screw function g, Eq. (1.3), p.3):
"Let g(t) be a continuous real-valued even function on ℝ, defined by
g(t) = −4(e^{t/2} + e^{−t/2} − 2) + Σ_{n≤exp(|t|)} (Λ(n)/√n)(|t| − log n) − (|t|/2)(ψ(1/4) − log π) − (1/4)(Φ(1,2,1/4) − e^{−|t|/2}Φ(e^{−2|t|},2,1/4)),
where ψ(s) is the digamma function and Φ(z,s,a) = Σ_{n=0}^∞ (n+a)^{−s} z^n is the Hurwitz–Lerch zeta function."

VERBATIM (screw-function property + RH link, p.3–4):
"A function g on ℝ satisfying g(t) = \overline{g(−t)} is called a screw function on the real line if the kernel g(t−u) − g(t) − g(−u) + g(0) is nonnegative for all t,u ∈ ℝ. As shown in [13, Theorem 1.2], the above function g is a screw function in the sense of Krein–Langer [8, Section 5] if and only if RH holds. For this reason, we shall refer to it as the screw function associated with ζ(s)."

VERBATIM (integral operators built from g, Eqs. (1.4)–(1.6), p.4):
"We define the integral operator G by (Gu)(x) := ∫_{−∞}^∞ g(x − y)u(y) dy. ...
G_a := P_a G P_a : L²_0(−a,a) → L²_0(−a,a). ...
B_a := D* G_a D : L²(−a,a) → L²(−a,a), 𝔇(B_a) = H¹_0(−a,a)."

VERBATIM (the primary object — the self-adjoint operator realizing Weil's form, Eq. (1.1), p.2):
"Q_W^a(v) = ⟨A_a v, v⟩_{L²} for v ∈ 𝔇(A_a) ⊂ 𝔇(Q_W^a) ⊂ L²(−a,a)."

K7-TAG: CONVENTION (definition) + THEOREM (Thm 1.2 of ref [13], cited, gives the RH-iff-screw property)
MAPS TO Q3: α-Gate / truncated-Weil / canonical-systems (g is the continuous integral kernel that realizes the localized Weil form Q_W^a on [−a,a])
PROVED-OR-OPEN: g's definition proved/constructive here; "g is a screw function ⇔ RH" is cited from [13, Thm 1.2], not re-proved here.

---

## 2. Unified framework claim (Yoshida / Bombieri / Connes–Consani / CCM) — Abstract p.1; Section 1.1 pp.2–3 (esp. p.3 lines "unify these various results…" and "unified perspective")

VERBATIM (Abstract, p.1):
"We establish a unified framework for understanding the results on the Weil quadratic form obtained by Yoshida (1992), Bombieri (2001, 2003), Connes–Consani (2023), and Connes–Consani–Moscovici (2025+) from the perspective of the screw function introduced in Suzuki (2023)."

VERBATIM (Section 1.1, p.3):
"First, we aim to unify these various results through the framework of the screw function associated with ζ(s), which was introduced in [13]. This approach not only provides transparent re-derivations of previous results, but also leads to more refined results presented below. ... Indeed, [13] reinterpreted some of the results by Yoshida [17], Bombieri [1, 2], and Connes–Consani [3] from the viewpoint of screw functions. However, these earlier works had not yet been placed within a fully unified framework."

VERBATIM (culmination of the unification, Section 1.1, p.3):
"This line of investigation led to a unified perspective on the earlier works mentioned above and ultimately to Corollary 1.6, which constitutes the main conjectural statement of the present paper."

K7-TAG: CONVENTION / program statement (framework/perspective), NOT a single stated "unification theorem"
MAPS TO Q3: α-Gate / canonical-systems (positions Yoshida localization, Bombieri Rayleigh-min, Connes–Consani operator A_a, and CCM zeta-spectral-triple all as facets of the one screw-function/Weil-form picture)
PROVED-OR-OPEN: The unification is a **program / re-derivation framework**, NOT proved as one theorem. Individual re-derivations (e.g. new proof of Yoshida's equivalence via Thm 1.3, and the explicit A_a via Thm 1.1) are proved; the culminating unified object (limit formula, Cor. 1.6) is **conjectural**.

---

## 3. Limit of nonlocal operators on [−a,a] as a→∞ (→ C3 / roof convergence) — Eq. (1.2) p.3; Corollary 1.6 / Eq. (1.12) p.6; Theorem 1.3 p.5

VERBATIM (conjectural limiting formula, Eq. (1.2), p.3):
"lim_{a→∞} c_a \hat{v_a}(z) = ξ(1/2 + iz).   (1.2)"

VERBATIM (Corollary 1.6, Eq. (1.12), p.6):
"Corollary 1.6. If one can choose θ = θ(a) and φ(a,z) (≠ ∞ for any a > 0 and z ∈ ℂ) such that
lim_{a→∞} e^{φ(a,z)} W(a,θ;z) = z² ξ(1/2 − iz) / ξ'(1/2 − iz),   (1.12)
holds uniformly on every compact subset K ⊂ ℂ, then RH holds."

VERBATIM (Abstract statement of the a→∞ conjecture, p.1):
"we formulate a conjecture stating that a self-adjoint operator whose eigenvalues are the imaginary parts of the nontrivial zeros of the Riemann zeta function can be obtained as the limit, as a → ∞, of self-adjoint operators arising from nonlocal realizations of the first-order differential operator on the finite interval [−a,a]."

VERBATIM (what IS proved about the a-family limit — continuity, Theorem 1.3, p.5):
"Theorem 1.3. The lowest eigenvalue λ_a is continuous in a."

K7-TAG: CONJECTURE (Cor. 1.6 / Eq. (1.2), Eq. (1.12)) + THEOREM (Thm 1.3, continuity, proved)
MAPS TO Q3: C3 / ROOF (the a→∞ limit of the truncated [−a,a] operators is exactly our roof-convergence analogue; the target ξ(1/2+iz) is the Ξ approximant limit)
PROVED-OR-OPEN: The a→∞ limit formula (1.2)/(1.12) is **OPEN / conjectural** (Cor. 1.6 is stated "If one can choose … then RH holds"). Continuity of λ_a in a (Thm 1.3) is **proved unconditionally**.

---

## 4. Weil positivity / RH criterion (α-Gate) — Weil criterion p.1 (cited [15]); Yoshida localization p.1–2; Theorem 1.3 corollary p.5; Corollary 1.6 p.6

VERBATIM (Weil's positivity criterion, p.1, attributed to Weil [15]):
"A fundamental result due to Weil [15] states that RH is equivalent to the condition that
Q_W(v) ≥ 0   for all v ∈ C_c^∞(ℝ),
a property known as Weil's positivity criterion for RH."

VERBATIM (localized equivalence, Yoshida, p.1–2):
"The study of the localization of the Weil quadratic form Q_W was pioneered by Yoshida [17], who established that RH is equivalent to the positive definiteness of Q_W on the space C_c^∞(−a,a) := {v ∈ C_c^∞(ℝ) | supp(v) ⊂ [−a,a]} for every a > 0."

VERBATIM (this paper's re-derivation of the equivalence via continuity, p.5):
"Since the continuity of λ_a can be established without assuming RH, Theorem 1.3 immediately yields, as a corollary, another proof of Yoshida's result [17] that RH is equivalent to the nondegeneracy of Q_W^a for every a > 0. Indeed, the failure of RH is equivalent to the existence of some a > 0 for which λ_a < 0."

K7-TAG: THEOREM (Weil criterion, cited from [15]; Yoshida equivalence, cited [17] and re-proved via Thm 1.3) + CONJECTURE (Cor. 1.6 sufficient condition)
MAPS TO Q3: α-Gate (Q_W ⪰ 0 ⇔ RH is exactly the α-Gate; the localized λ_a ≥ 0 form and Cor. 1.6 are the interval-truncated / limit forms of it)
PROVED-OR-OPEN: Weil criterion (equivalence) cited from Weil [15]; Yoshida localized equivalence cited [17] and additionally re-proved here (via Thm 1.3, unconditional). Corollary 1.6 gives only a **sufficient condition** (limit formula ⇒ RH), and is **conjectural / open**, not an equivalence and not proved.

---

## 5. Real-zero / de Branges / canonical-system statement for the ROOF — Theorem 1.5 / Eq. (1.11) p.6; Theorem 1.4 p.5; Section 7.2 pp.23–24

VERBATIM (Theorem 1.5, unconditional real zeros, p.6):
"Theorem 1.5. Let a > 0 and θ ∈ [0,2π). Let v_±(a,x) be eigenfunctions of the adjoint operator 𝒟_a^* corresponding respectively to the eigenvalues ±i, normalized so that ‖v_+(a,·)‖_{T_a} = ‖v_−(a,·)‖_{T_a}. Then the function
W(a,θ;z) := (z − i) ∫_{−a}^a v_+(a,x)e^{izx}dx + e^{iθ}(z + i) ∫_{−a}^a v_−(a,x)e^{izx}dx   (1.11)
is entire in z. The eigenvalues of the self-adjoint operator \overline{𝒟}_{a,θ} are precisely the zeros of W(a,θ;z). Furthermore, all zeros of W(a,θ;z) are real."

VERBATIM (unconditionality emphasized, p.6):
"whereas the result in [4] requires strong assumptions, such as the simplicity of λ_a and the evenness of the corresponding eigenfunction, our Theorem 1.5 has the advantage of being proved unconditionally. In fact, its proof does not require detailed information about the arithmetic terms appearing in the Weil form Q_W^a."

VERBATIM (evenness of the ground state, Theorem 1.4, p.5):
"Theorem 1.4. For sufficiently small a > 0, the lowest eigenvalue λ_a is positive, simple, and satisfies
λ_a = log(1/a) + μ_1 − log(2π) + ψ(2) − 1 + O(a)
as a → 0+, for some constant μ_1 > 0. Furthermore, the corresponding eigenfunction is even."

VERBATIM (de Branges isomorphism, Section 7.2, pp.23–24 — under RH):
"7.2. Isomorphism with a de Branges space. We now recall the isometric isomorphism between H(A∞) (denoted by H_W in [14]) and a certain de Branges space B established in [14]. ... the self-adjoint extension M_{π/2} has purely discrete spectrum Γ, the set of zeros of ξ(1/2−iz) in Section 3, and one can choose an orthonormal basis of B consisting of the corresponding eigenfunctions F_γ for γ ∈ Γ [14, Section 6]."

K7-TAG: THEOREM (Thm 1.5 real zeros, proved unconditionally; Thm 1.4 evenness, proved for small a) + THEOREM (de Branges isomorphism, cited from [14], invoked under RH in §7)
MAPS TO Q3: ROOF / canonical-systems (entire approximants W(a,θ;z) with all-real zeros converging toward ξ is precisely the ROOF's real-zero entire-approximant → Ξ frame; the de Branges space B and multiplication operator M_{π/2} are Suzuki's canonical-system realization)
PROVED-OR-OPEN: Thm 1.5 (W(a,θ;z) entire, self-adjoint spectrum = zeros, ALL zeros real) **proved here, unconditionally**. Thm 1.4 (positivity/simplicity/evenness for small a) **proved here**. The de Branges isomorphism H(A∞) ≅ B is **cited from [14]** and used only inside the RH-conditional heuristic of §7.

---

## 6. What is PROVED vs OPEN/conjectural — Abstract p.1; Theorem statements pp.4–6; Section 7 opening p.22

VERBATIM (global "no RH assumed" claim, Abstract, p.1):
"All these results are obtained without assuming the Riemann Hypothesis. This conjecture may be compared with the limit formula for the Riemann zeta function expressed in terms of zeta-regularized products proposed by Connes, Consani, and Moscovici, and it sheds new light on the spectral-theoretic interpretation of the nontrivial zeros of the Riemann zeta function."

VERBATIM (main results are RH-free, Section 1.2, p.3):
"Before presenting the main results, we emphasize that none of them depends on RH."

VERBATIM (Theorem 1.1, proved, p.4):
"Theorem 1.1. For each a > 0, the self-adjoint operator A_a defined by (1.1) is the Friedrichs extension of the symmetric operator B_a defined by (1.6)."

VERBATIM (Cor. 1.6 flagged as the conjectural apex, p.6):
"lim_{a→∞} e^{φ(a,z)} W(a,θ;z) = z² ξ(1/2 − iz) / ξ'(1/2 − iz),   (1.12) holds uniformly on every compact subset K ⊂ ℂ, then RH holds."
and (p.3): "ultimately to Corollary 1.6, which constitutes the main conjectural statement of the present paper."

VERBATIM (Section 7 is explicitly heuristic and assumes RH, p.22):
"7. Heuristic justification of the formula in Corollary 1.6
In this section, we assume RH. By Weil's positivity criterion, we have Q_W ≥ 0 and hence A_a > 0 for all a > 0."

K7-TAG: THEOREM (Thms 1.1, 1.3, 1.4, 1.5 — proved unconditionally) + CONJECTURE (Cor. 1.6 / Eq. (1.2), (1.12)) + heuristic (§7 under RH)
MAPS TO Q3: α-Gate / ROOF / C3
PROVED-OR-OPEN summary:
- PROVED here, unconditionally: Thm 1.1 (explicit A_a = Friedrichs ext. of B_a), Thm 1.3 (λ_a continuous in a), Thm 1.4 (λ_a positive/simple/even for small a), Thm 1.5 (W(a,θ;z) entire, all zeros real).
- Re-proved here: Yoshida's RH ⇔ nondegeneracy of Q_W^a (as corollary of Thm 1.3).
- CITED (not re-proved): Weil criterion [15]; screw ⇔ RH [13, Thm 1.2]; de Branges isomorphism [14].
- OPEN / conjectural: Corollary 1.6 (limit formula (1.12)/(1.2) ⇒ RH); the a→∞ Hilbert–Pólya limit operator. §7's de Branges/M_{π/2} justification is heuristic and assumes RH.

---

### Reference key (as used above, from the paper's bibliography)
- [1],[2] E. Bombieri (2001; 2003) — Weil quadratic functional / variational explicit formula.
- [3] A. Connes, C. Consani, Spectral triples and ζ-cycles, Enseign. Math. 69 (2023).
- [4] A. Connes, C. Consani, H. Moscovici, Zeta spectral triples, arXiv:2511.22755 ("CCM 2025+").
- [8] Krein–Langer.
- [13] Suzuki (2023) — screw function associated with ζ(s) (Thm 1.2: screw ⇔ RH; Prop. 3.1: Q_W ↔ screw).
- [14] Suzuki — Hilbert space H_W, de Branges space B, Hilbert–Pólya operator (§6).
- [15] A. Weil — Weil's positivity criterion.
- [17] H. Yoshida (1992) — Hermitian forms attached to zeta functions (localization; Prop.1, Lemmas 2–3, Thm 2).

All 6 requested items FOUND verbatim. No numerics treated as proof. No Q3 closure claimed.
