import Q3.Proofs.RouteB.D0Mode4DLMF3035EvenCharacteristicSource

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

namespace Q3.RouteB

/-!
# W13.7B — the source interface for the regular even endpoint spectrum

The obligation this file discharges is the set equality the judge fixed in
`PROSHKA_VERDICT_REQ_2026_08_21_N_...` (commit `d7e6f060`): below the cutoff,
the reals satisfying the literal DLMF 30.3.5 even characteristic equation are
exactly the values of the even-degree source branches.

**The two inclusions have different provenance and are carried by different
fields.** They are never merged into one hypothesis, because the two sides start
from different kinds of object: the source classifies solutions of a
differential equation, while the project object is a root of a
continued-fraction characteristic equation. Collapsing them into a single
citation is exactly the `C04` same-coordinates-two-laws failure.

```text
branch -> characteristic   DLMF 30.3.5, one-way membership
characteristic -> branch   project root-to-regular-solution bridge
                           + Meixner-Schaefke §3.22 Satz 1 exhaustiveness,
                             reality, simplicity, and parity
```

`BookRegularEvenSpectrum` is a **typed hole**, not an axiom. Nothing here
asserts that the source facts hold; a term of this type exists only once
somebody exhibits a branch family together with proofs of the four fields. That
supplier does not exist yet and is named honestly in `OPENS`.

What this file does **not** claim:

* that the source theorem has been formalized — it has not;
* that the cutoff selects the production branches — it does not, it only lets
  them through, and higher even branches drop below it as the parameter grows;
* that the branch family is definitionally the project carrier — asserting that
  would be the `C10` surrogate kill.

LEDGER:
  CLOSES: [W13_7B_BOOK_REGULAR_SPECTRUM_TO_DLMF3035_CHARACTERISTIC_RANGE]
  OPENS:  [MEIXNER_SCHAEFKE_SATZ_1_TYPED_SUPPLIER]
-/

/-- The source-side facts about the regular even endpoint spectrum at one fixed
parameter, as a typed hole.

`branch n` is the source eigenvalue branch of degree `n` at the fixed parameter.
No field mentions a project object, and no field is proved here. -/
structure BookRegularEvenSpectrum (G : ℝ) (splitDegree : ℕ) where
  /-- The source branch family, indexed by degree at the fixed parameter. -/
  branch : ℕ → ℝ
  /-- **Forward inclusion, provenance DLMF 30.3.5.** An even-degree branch value
  below the cutoff satisfies the literal characteristic equation. This is the
  one-way membership the reference actually states. -/
  branch_characteristic :
    ∀ r : ℕ, branch (2 * r) < 20 →
      mode4DLMF3035EvenCharacteristicEquation G (branch (2 * r)) splitDegree
  /-- **Reverse inclusion, provenance Meixner-Schaefke §3.22 Satz 1 together
  with the project root-to-regular-solution bridge.** A characteristic root
  below the cutoff is a branch value at an even degree.

  The reference supplies exhaustiveness of the regular endpoint spectrum and
  parity by the parity of `n - m`; the project supplies that a root produces a
  nonzero even solution regular at both endpoints. Neither half suffices alone,
  which is why this is one field and not two citations. -/
  characteristic_branch :
    ∀ Λ : ℝ, Λ < 20 →
      mode4DLMF3035EvenCharacteristicEquation G Λ splitDegree →
      ∃ r : ℕ, branch (2 * r) = Λ
  /-- **Reality and simplicity**, in the shape the ordered-enumeration lock
  consumes. Simplicity is load-bearing: without it one eigenvalue could carry
  both an even and an odd solution and the parity step would not close. -/
  branch_strictMono : StrictMono branch

namespace BookRegularEvenSpectrum

variable {G : ℝ} {splitDegree : ℕ}

/-- **W13.7B.** Below the cutoff, the characteristic roots are exactly the
even-degree branch values.

Each direction is discharged by its own field, so the provenance split survives
into the proof term. -/
theorem characteristic_setOf_eq_even_branch_setOf
    (S : BookRegularEvenSpectrum G splitDegree) :
    {Λ : ℝ | Λ < 20 ∧ mode4DLMF3035EvenCharacteristicEquation G Λ splitDegree}
      = {Λ : ℝ | Λ < 20 ∧ ∃ r : ℕ, S.branch (2 * r) = Λ} := by
  ext Λ
  constructor
  · rintro ⟨hcut, hchar⟩
    exact ⟨hcut, S.characteristic_branch Λ hcut hchar⟩
  · rintro ⟨hcut, r, hr⟩
    refine ⟨hcut, ?_⟩
    have hbranch : S.branch (2 * r) < 20 := by rw [hr]; exact hcut
    have := S.branch_characteristic r hbranch
    rwa [hr] at this

/-- The forward inclusion alone, stated separately so a consumer that only needs
the reference direction does not silently acquire the reverse one. -/
theorem even_branch_subset_characteristic
    (S : BookRegularEvenSpectrum G splitDegree) :
    {Λ : ℝ | Λ < 20 ∧ ∃ r : ℕ, S.branch (2 * r) = Λ}
      ⊆ {Λ : ℝ | Λ < 20 ∧ mode4DLMF3035EvenCharacteristicEquation G Λ splitDegree} :=
  (S.characteristic_setOf_eq_even_branch_setOf).ge

/-- The reverse inclusion alone, likewise separate. This is the direction the
reference does **not** state and that the book plus the project bridge supply. -/
theorem characteristic_subset_even_branch
    (S : BookRegularEvenSpectrum G splitDegree) :
    {Λ : ℝ | Λ < 20 ∧ mode4DLMF3035EvenCharacteristicEquation G Λ splitDegree}
      ⊆ {Λ : ℝ | Λ < 20 ∧ ∃ r : ℕ, S.branch (2 * r) = Λ} :=
  (S.characteristic_setOf_eq_even_branch_setOf).le

/-- The even-degree subfamily is strictly increasing.  This is what the ordered
enumeration lock consumes at rank two; it follows from simplicity of the full
family and is stated here so the consumer does not re-derive it. -/
theorem evenBranch_strictMono (S : BookRegularEvenSpectrum G splitDegree) :
    StrictMono (fun r : ℕ => S.branch (2 * r)) := by
  intro a b hab
  exact S.branch_strictMono (by omega)

end BookRegularEvenSpectrum

#print axioms BookRegularEvenSpectrum.characteristic_setOf_eq_even_branch_setOf
#print axioms BookRegularEvenSpectrum.even_branch_subset_characteristic
#print axioms BookRegularEvenSpectrum.characteristic_subset_even_branch
#print axioms BookRegularEvenSpectrum.evenBranch_strictMono

end Q3.RouteB
