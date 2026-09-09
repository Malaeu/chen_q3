STATUS: SUPPLEMENT (RELAY — Prošhka's chat answer to point 5 of addendum SCHUR, pasted by the owner into the observer's session 2026-09-09; NOT committed by Prošhka; verbatim below, LaTeX doubled by the chat export; not verified except where the observer's probe says so)
REQUEST_ID: REQ-2026-09-09-DISTANCE
SUPPLEMENT_ID: SCHUR_POINT5
DATE: 2026-09-09
AUTHOR: Prošhka (chat «Adjudicate distance request», project RH_März_2026); transport Linux-Claude
PARENT: PROSHKA_ADDENDUM_GOAL058_DISTANCE_SCHUR_2026-09-09.md (16da282c; blob e456429ba1a55ca04d70d7c3e571979a14aa56aa)

---

SCHUR fetched at the pinned commit. Both hashes match: 37 lines, 4,248 bytes, including the final newline. The registered D37 threshold is satisfied by the reported diagnostics; that selects the directional Schur calculation, not a smallest-gap estimate.

Git blob: e456429ba1a55ca04d70d7c3e571979a14aa56aa
SHA-256:  7027bf2b5323f183b2e8af298230d68685c423fb31e4585d571f002626e80f04

Answer to point 5: prove a lower bound on the energy recovered by one full-source correction. You do not need an upper estimate for every complement vector. You also cannot assign the cancellation to the prime component of b alone.
There is one important quantifier repair: do not require positive full complements on every sufficiently large window just to define the inverse. Below I prove why that would already contain the global sign problem—and how to retain Schur without making that assumption.

1. The exact D24 lemma
Definitions — [ABSTRACT][PAPER]. Keep the full source form Q, including its pole terms, and the established form domain: V_a = closure of C_c^∞(−a,a) in E.
Set p_a = 1_(−a,a)Φ / ‖1_(−a,a)Φ‖_2,  K_a = {h ∈ V_a : ⟨p_a,h⟩_2 = 0},  r_a = Q[p_a],  b_a(h) = Q(h,p_a),  C_a = Q|_{K_a}.
In coefficient coordinates, this is G-orthogonality, not the unweighted dot product.
Define the complement floor without assuming its sign: β_a = inf_{0≠h∈K_a} Q[h]/‖h‖_2².
When β_a > 0, the Schur response is the unique y_a ∈ K_a satisfying  Q(h,y_a) = Q(h,p_a)  (h ∈ K_a).
That is the precise form-domain meaning of y_a = C_a^{-1} b_a. The universal h here defines the response; it is not the quantifier of the desired rate estimate. This is the response already used in D22–D24.
The source estimate to prove — Unpaid target [COFINAL_FAMILY][CONDITIONAL]:
  ∃M>0, ν≥0, a_*>0 ∀a≥a_*:  β_a > 0 ⟹ (r_a − b_a^* C_a^{-1} b_a)/(1+‖y_a‖_2²) ≤ M e^{νa} T(a)².     (1)
The constants M, ν, a_* are fixed before the universal a. A proof should supply them, not choose a new constant for every numerical row.
Why this yields an unconditional upper bound — [COFINAL_FAMILY][PAPER]. When β_a ≤ 0, inclusion of the complement gives λ_a ≤ β_a ≤ 0. The requested positive upper envelope already holds. When β_a > 0, use the single trial p_a − y_a: Q[p_a − y_a] = r_a − b_a^*C_a^{-1}b_a, ‖p_a − y_a‖_2² = 1 + ‖y_a‖_2². Then (1) gives the bound by the Rayleigh quotient. Thus the correct target is a conditional estimate on each positive-complement window, with the other branch handled separately. It is not a cofinal positivity assumption.

2. The first inequality I would try
Derivation — [ABSTRACT][PAPER]. Define the signed recovered energy  J_a(z) := 2 Re Q(z,p_a) − Q[z],  z ∈ K_a.
Exact identity, no positivity assumption:  Q[p_a − z] = r_a − J_a(z).     (2)
On the positive-complement branch, completing the square gives J_a(z) = b_a^*C_a^{-1}b_a − C_a[z − y_a]. Consequently sup_{z∈K_a} J_a(z) = b_a^*C_a^{-1}b_a.     (3)
The first sufficient inequality to attack is
  J_a(z_a) ≥ r_a − M e^{νa} T(a)²  for one explicitly constructed z_a ∈ K_a.     (4)
Its cofinal quantifiers are ∃M>0, ν≥0, a_*>0 ∀a≥a_* ∃z_a∈K_a: (4). This is a sufficient, slightly stronger interface than necessary. It proves Q[p_a − z_a] ≤ M e^{νa}T(a)², ‖p_a − z_a‖_2² = 1 + ‖z_a‖_2² ≥ 1. Hence it gives the upper bound directly, without any full-complement inverse. Where y_a exists, (3) shows that the same inequality also proves D24. No separate smallness bound for ‖z_a‖ is required for this implication. No normalization can collapse.
A concrete two-dimensional version. Choose one source-defined nonzero direction d_a ∈ K_a. Put u_a = Q[d_a], B_a = Q(d_a,p_a). If u_a ≤ 0, the direction itself gives λ_a ≤ 0. If u_a > 0, optimize only its scalar coefficient: z_a = (B_a/u_a) d_a. Direct calculation gives J_a(z_a) = |B_a|²/u_a. Therefore a sufficient implementation of (4) is
  |Q(d_a,p_a)|² ≥ Q[d_a] (r_a − M e^{νa}T(a)²),  Q[d_a] > 0.     (5)
This is a two-dimensional determinant estimate on span{p_a,d_a}, not a bound on all of K_a.
The remaining construction is genuine: the addendum supplies finite numerical response directions, but not yet a cofinal source formula for d_a or z_a, nor the remainder bound (4) or (5). I am not claiming that a fixed number of theta derivatives or a fixed Legendre degree supplies that formula.
Also, reflection preserves Q, and p_a is even. Thus b_a annihilates odd vectors; whenever the full positive response exists, it is even. Constructing one real-even trial is sufficient for an upper bound over the full complex class. There is no need to solve the odd sector to construct that trial.

3. Which source term carries the cancellation?
The full coupled expression does. Not the prime component alone.
Write Q = A − P_a + R, where A is the archimedean form including −c_A⟨·,·⟩; P_a is the unsigned prime-sum expression subtracted in Q; R is the pole form. Correspondingly b = b_A − b_P + b_R. On the positive-complement branch define S_ij = b_i^* C_a^{-1} b_j. Then the exact expansion is
  b^*C_a^{-1}b = S_AA + S_PP + S_RR − 2 Re S_AP + 2 Re S_AR − 2 Re S_PR.     (6)   [ABSTRACT][PAPER]
Moreover, C_a itself contains all three source pieces. The prime coefficients enter both the forcing and its inverse response. Bounding b_P alone does not control (6).
An exact abstract falsifier is already scalar: take C = 1, b_A = b_P = 1, b_R = 0. Then b = 0, so the recovered energy is zero, although b_P^*C^{-1}b_P = 1. Ignoring the mixed term fabricates a unit of cancellation. This rejects the abstract prime-only substitution, not the actual zeta source.
Two additional details matter: the mass term disappears from b_A on K_a, but not from r_a or C_a (⟨h,p_a⟩ = 0 only removes that cross pairing); the pole term cannot be discarded — the cut-theta trial is not pole-null; D20 retains both pole functionals.
Useful exact tail formulation. Let t_a = Φ − 1_(−a,a)Φ, N_a = ‖1_(−a,a)Φ‖_2. The radical identity Q(Φ,h) = 0 (D7) yields
  r_a = Q[t_a]/N_a²,  b_a(h) = −Q(h,t_a)/N_a.     (7)
Thus the object is the full tail-forced response, with every mixed contribution retained.
Support warning: the prime sum is finite through m ≤ e^{2a} when both arguments are window-supported. In the rewritten pairing Q(h,t_a) the tail is noncompact; its prime sum is infinite, though convergent in the established domain. Truncating that rewritten forcing at e^{2a} would introduce a new error.

4. The arithmetic input, stated explicitly
Although the answer is not "the prime piece of b", we can isolate the precise arithmetic obligation after choosing the trial. Let f_a = p_a − z_a and define its autocorrelation R_{f_a}(t) = Re⟨f_a, U_t f_a⟩_2. The upper bound Q[f_a] ≤ ε_a‖f_a‖_2² with ε_a = M e^{νa}T(a)² is exactly
  2 Σ_{2≤m≤e^{2a}} Λ(m)/√m · R_{f_a}(log m) ≥ D[f_a] − c_A‖f_a‖_2² + 2 Re(conj(M_+(f_a)) M_−(f_a)) − ε_a‖f_a‖_2².     (8)
That is the arithmetic input: a one-sided weighted von-Mangoldt correlation bound for the constructed trial family, including all prime powers. It is not a bound for every test, and it is not an upper bound for ‖b_P‖. [COFINAL_FAMILY][CONDITIONAL: required estimate, not proved here]
For smooth or piecewise-C¹ trials, its remaining integral can be exposed explicitly. Set X = e^{2a}, k_a(x) = x^{−1/2} R_{f_a}(log x), ψ(x) = Σ_{m≤x}Λ(m), D_ψ(x) = ψ(x) − (x − 1). Endpoint conditions k_a(X) = 0, D_ψ(1) = 0. Integration by parts gives
  Q[f_a] = A[f_a] + R[f_a] − 2∫_1^X k_a(x)dx + 2∫_1^X D_ψ(x) k_a'(x) dx.     (9)   [ABSTRACT][PAPER]
A proposed prime-counting theorem must pay the signed last integral together with the displayed main term at the required T² scale. An absolute error envelope |D_ψ| ≤ E_ψ helps only after showing that A[f_a] + R[f_a] − 2∫_1^X k_a + 2∫_1^X E_ψ(x)|k_a'(x)|dx ≤ ε_a‖f_a‖_2². Without that budget, invoking a prime-number asymptotic merely renames the missing estimate. Taking absolute values may destroy the relevant cancellation. For a general logarithmic form-domain response, retain the Stieltjes formulation unless the regularity needed for (9) is proved.

5. Why cofinal complement positivity is not a free preliminary lemma
Proposition — [COFINAL_FAMILY][PAPER]. If a_j → ∞ and Q[h] ≥ 0 (h ∈ K_{a_j}, j sufficiently large) (10), then Q[f] ≥ 0 for every complex compact smooth test f.
Proof. The theta tail estimates give p_{a_j} → n := Φ/‖Φ‖_2 in E, and n is radical: Q(n,g) = 0 (g ∈ E). The radical identity and legal sharp-cut domain are the source facts established in D7–D8. Fix a compact smooth f. Eventually its support lies in the window. Define α_j = ⟨p_{a_j},f⟩_2, h_j = f − α_j p_{a_j} ∈ K_{a_j}. The coefficients α_j are bounded. By source continuity, Q(f,p_{a_j}) → 0, Q[p_{a_j}] → 0. Therefore Q[h_j] = Q[f] − 2Re(α_j Q(f,p_{a_j})) + |α_j|²Q[p_{a_j}] → Q[f]. By (10), the left side is nonnegative. Hence Q[f] ≥ 0. ∎
The contrapositive is useful: a fixed compact negative witness produces a negative complement direction on every sufficiently large theta window.
So the repair is not to abandon Schur. It is to use the local branch structure in (1). A proof of cofinal full-complement positivity would be a substantive sign theorem, not routine inverse-existence bookkeeping. The registered 0.9 expectation is confirmed by this paper argument.

6. The next proof target
Keep D24 as the exact-response formulation, but attack it through (4):
  Construct one source-defined even z_a ⊥ p_a and prove 2 Re Q(z_a,p_a) − Q[z_a] ≥ r_a − M e^{νa}T(a)².
For a one-direction implementation, use (5). Its discriminator — the signed margin that tests that particular candidate — is
  𝔐_a = |Q(d_a,p_a)|² − Q[d_a](r_a − ε_a).
On Q[d_a] > 0, a rigorous lower enclosure L(𝔐_a) ≥ 0 accepts that sufficient inequality. A strict upper enclosure U(𝔐_a) < 0 rejects that direction and budget, not the source T² law. An enclosure containing zero remains unresolved.
ЕСЛИ_A: a cofinal proof of this inequality closes the upper-rate supplier. The lower-sign problem remains separate. ЕСЛИ_B: preserve the failing direction and signed margin, then inspect the coupled arithmetic expression (8)–(9); do not repair the attempt by assuming cofinal complement positivity.
The actual source T² estimate remains unproved here. What is now fixed is its quantifier, its admissible trial class, its inequality direction, and the full source expression that must pay the remainder.
Complete point-5 answer, proofs, source locks, and closeout. No repository file was changed. No Lean run or interval certification is claimed.
