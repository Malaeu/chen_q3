# Goal 058 G3 post-inertia source crosswalk — Proshka verdict

Source: visible completed response in the existing Proshka/ChatGPT phase chat
on 2026-08-14 after the four requested exact UTF-8 files were attached. The
text below is line-normalized from the browser response; it is not represented
as a byte-exact downloaded artifact.

## PRIMARY

`REJECT_PLACEHOLDER_ENDPOINT_COUNTS_REQUIRE_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK`

All four SHA-256 values matched and Proshka declared the source lock restored.

The Mythos point about an absolute inertia anchor is conceptually correct:
ordering supplied roots gives only relative labels, so without a starting
count three roots could carry labels `5,6,7` rather than `0,1,2`. But the
proposed endpoint-count task is not an admissible current-tree theorem.

## Reasons

1. `sourceKWindow`, `windowBottomΛ`, `windowTopΛ`, and
   `d0Mode4SchurMatrix` do not exist. The literal object is

   ```lean
   mode4HermitianSchurMatrix
     (mProject : ℕ) (Λ : ℝ) (K : ℕ) :
     Matrix (Fin K) (Fin K) ℝ
   ```

   Materializing placeholder objects before the crosswalk would violate
   `[C04] SAME-COORDINATES-TWO-LAWS`: a similar Schur matrix would replace the
   exact infinite-tail Schur complement.

2. The upper point `20 + ε` is incompatible with the production receiver.
   `exists_mode4RootFunction_eq_zero_of_hermitianSchur_counts_two_three`
   requires `ΛUpper ≤ 20`, endpoint nonsingularity, lower negative count `2`,
   and upper negative count `3`. Mythos's `0/3` proposal changes the existing
   source-locked proof program instead of filling its supplier.

3. The elementary Bonami--Karoui bound gives only
   `Λ₄ = χ₄(c) - c² ≤ 20`; it does not prove

   ```text
   negativeCount (mode4HermitianSchurMatrix ...) = 3.
   ```

   The stronger `tildePhi` bounds give source-defined separators between
   differential indices `2,4,6`, but the repository has no theorem identifying
   the negative count of the literal exact-recessive-tail Schur complement
   with the classical Sturm--Liouville spectral counting function.

Importing the classical `χ_n` family is not itself circular. Circularity would
enter if

```text
χ_(2r) - c²  ↔  det (mode4HermitianSchurMatrix ...) = 0
```

were proved from already supplied Schur roots, coefficient rows, or endpoint
counts. An independent operator/recurrence equivalence is required. Literal
endpoint counts are therefore mathematically possible but currently not
source-legally available.

## Correct next object

`MODE4_CLASSICAL_EVEN_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK`

Its mathematical contract is

```text
negativeCount (A_(m,K)(Λ))
  = #{r : ℕ | χ_(2r)(c) - c² < Λ} + offset_(m,K),

A_(m,K)(Λ) = mode4HermitianSchurMatrix mProject Λ K,
c² = mode4JacobiG mProject.
```

The crosswalk must prove the exact offset; it may not silently set it to zero.
Only after this theorem may the Bonami--Karoui separators supply production
counts `2/3` at endpoints satisfying `ΛUpper ≤ 20`.

## Bounded directive

`GOAL058_G3_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_SOURCE_PACKET`:
read-only source acquisition and an exact theorem-contract report over the
literal Schur/order/simple-kernel/crossing/inertia-label and PSWF recurrence
files, the pinned index-source packet, and the three pinned PDFs. No
production Lean edit, placeholder declaration, commit, push, or Aristotle
submission was authorized.

`ARISTOTLE_SUBMISSION_AUTHORIZED` was **not** issued. G1 and G3 remain open;
Route B remains challenger/not-RH; no Route promotion or RH claim follows.
