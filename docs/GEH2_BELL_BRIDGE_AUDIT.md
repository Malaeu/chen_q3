# GEH2_BELL_BRIDGE_AUDIT.md
(Assume Q3 is proved/valid.)

## 0) One-line target
Twin primes are infinite ⇔ π₂(X) is unbounded. A sufficient analytic target is any power-saving lower bound for

S(X) := ∑_{n≤X} Λ(n)Λ(n+2)

that beats the “finite-twins ceiling” O(√X log²X).

## 1) Critical fix: “mod 4 parity lock” is not yet a proof
Fact (parity lock): for every twin prime p>3, χ₄(p)χ₄(p+2) = −1.
But this only fixes the sign of each *existing* twin contribution, not the *number* of twins.
So the step “T_{χ₄}(X) ~ X” is essentially as strong as Hardy–Littlewood for h=2; numeric scaling is evidence, not proof.

Correct takeaway:
If you can prove any growth lower bound for |T_{χ₄}(X)|, then (since |T_{χ₄}(X)| ≤ S(X)) you force S(X) → ∞ and hence infinitely many twins.

## 2) Rigorous ceiling under finite twins
Lemma (finite twins ⇒ ceiling).
If there exists N₀ such that for all n≥N₀, it is not the case that n and n+2 are both prime, then

S(X) = O(√X log²X).

Proof.
For n≥N₀, a term Λ(n)Λ(n+2) can be nonzero only if each of n, n+2 is a prime power.
Since (n,n+2) cannot be (prime,prime) for n≥N₀, at least one of them is a prime power p^k with k≥2.
The count of prime powers ≤X with exponent ≥2 is ≤ ∑_{k≥2} #{p : p^k≤X} ≤ ∑_{k≥2} X^{1/k} = O(√X).
Each nonzero term is ≤(log X)².
Hence S(X) ≤ O(√X)·(log X)². ∎

Corollary.
Any lower bound S(X) ≥ X^{1/2+δ} (δ>0) for arbitrarily large X contradicts “finite twins”.

## 3) PB-lemma: the clean analytic “parity-breaking” goal
PB(δ): There exists δ>0 and a nonnegative smooth cutoff W supported in [1,2] such that for all large X,

S_W(X) := ∑_{n≥1} Λ(n)Λ(n+2) W(n/X) ≥ X^{1/2+δ}.

Theorem (PB ⇒ TPC).
PB(δ) implies infinitely many twin primes.

Proof.
If twin primes were finite, then for all sufficiently large X the condition of Lemma 2 holds, so
S_W(X) ≤ S(2X) = O(√X log²X), contradicting S_W(X) ≥ X^{1/2+δ}. ∎

Remarks.
PB(δ) is vastly weaker than Hardy–Littlewood (which predicts S_W(X) ~ const·X).
PB(δ) is exactly the missing “parity break”: it rules out the scenario where all Λ(n)Λ(n+2) mass comes only from prime powers.

## 4) Bell/CHSH packaging (optional, but matches intuition)
For any bounded weight u(n) with |u(n)|≤1 define a twisted sum

T_{u,W}(X) := ∑ Λ(n)Λ(n+2) u(n) W(n/X).

Then |T_{u,W}(X)| ≤ S_W(X).
So a Bell-flavored PB can be stated as:

PB_Bell(δ): ∃ δ>0, W≥0, and some explicit ±1-valued u(n) (e.g. u(n)=χ₄(n)χ₄(n+2)) such that
|T_{u,W}(X)| ≥ X^{1/2+δ} for all large X.

This implies PB(δ), hence TPC.

## 5) Operator dictionary (RKHS/Hilbert form)
On ℓ²(ℕ) with basis |n⟩ define:
- g_X := ∑ Λ(n) W(n/X) |n⟩
- (U₂|n⟩)=|n+2⟩ (shift)
- (M_u|n⟩)=u(n)|n⟩ (diagonal multiplier)

Then T_{u,W}(X) = ⟨g_X, M_u U₂ M_u g_X⟩, and S_W(X)=⟨g_X, U₂ g_X⟩ up to boundary effects.
Thus PB is equivalent to one explicit matrix-element lower bound.

## 6) Where GEH-2 sits
A GEH-2-type hypothesis at level θ>1 for h=2 implies the HL asymptotic

S_W(X) = 𝔖(2)X + o(X),

hence it implies PB(δ) for every δ<1/2.
So PB is the “minimal” parity-breaking target; GEH-2 is a much stronger sufficient condition.

## 7) Where Q3 can enter without circularity
(Assuming Q3 true.)
If your commutator energy can be algebraically expanded into a positive combination of terms like |T_{u_i,W_i}(X)|²,
then Q3 gives a lower bound for that combination.
To get actual twins you need one extra extraction step: show at least one term corresponds to the shift U₂ (h=2)
with non-negligible coefficient. That extraction statement is precisely the parity-breaking bridge.
