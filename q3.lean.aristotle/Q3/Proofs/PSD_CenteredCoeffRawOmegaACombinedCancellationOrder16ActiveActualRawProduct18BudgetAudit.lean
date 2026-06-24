import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Source

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-!
Exact rational budget audit for the Step33A.1-A sub0 RawProduct18 source.

The source file closes the uniform `D^18 RawProductActual` estimate in `Real`.
This audit mirrors the same factor-majorant arrays in `Rat`, so the degree-0
budget generator can consume the full RawProduct18/ComponentProductActual
majorant instead of accidentally spending only the OmegaPrime order-17 factor.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- `Rat` mirror of `centeredTaylorDerivMajorant16`, deliberately using the
same `Fin 16`/`Fin 17` indexing as the real definition. -/
def primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
    (jetAbs : Fin 16 -> Rat) (order16Abs radius : Rat)
    (k : Fin 17) : Rat :=
  (∑ j : Fin 16,
      if k.1 <= j.1 then
        ((Nat.factorial j.1 : Rat) /
            (Nat.factorial (j.1 - k.1) : Rat)) *
          jetAbs j *
          radius ^ (j.1 - k.1)
      else
        0) +
    order16Abs * radius ^ (16 - k.1) /
      (Nat.factorial (16 - k.1) : Rat)

theorem primaryFiniteRow0Parent0Split100Sub0_order18_centeredTaylorDerivMajorant16Rat_cast
    (jetAbs : Fin 16 -> Rat) (order16Abs radius : Rat)
    (k : Fin 17) :
    (primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
        jetAbs order16Abs radius k : Real) =
      centeredTaylorDerivMajorant16
        (fun j : Fin 16 => (jetAbs j : Real))
        (order16Abs : Real) (radius : Real) k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
  unfold centeredTaylorDerivMajorant16
  rw [Rat.cast_add]
  congr 1
  · rw [Rat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hle : k.1 <= j.1
    · simp [hle]
    · simp [hle]
  · simp

/-- Exact rational mirror of the OmegaPrime derivative majorant through row 16. -/
def primaryFiniteRow0Parent0Split100Sub0Order18OmegaPrimeActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if hk : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
      (fun j : Fin 16 =>
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualCenterJetAbs j.1)
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert.order16Abs
      ((1 : Rat) / 20)
      ⟨k, hk⟩
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_order18_omegaPrimeActualDerivativeMajorantRat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0Order18OmegaPrimeActualDerivativeMajorantRat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Order18OmegaPrimeActualDerivativeMajorantRat
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
  by_cases hk : k < 17
  · simp [hk,
      primaryFiniteRow0Parent0Split100Sub0_order18_centeredTaylorDerivMajorant16Rat_cast]
  · simp [hk]

/-- Exact rational mirror of the OmegaActual derivative majorant through row
16. -/
def primaryFiniteRow0Parent0Split100Sub0Order18OmegaActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if hk : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
      (fun j : Fin 16 =>
        primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs j.1)
      (primaryFiniteRow0Parent0Split100Sub0Order18OmegaPrimeActualDerivativeMajorantRat
        15)
      ((1 : Rat) / 20)
      ⟨k, hk⟩
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_order18_omegaActualDerivativeMajorantRat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0Order18OmegaActualDerivativeMajorantRat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Order18OmegaActualDerivativeMajorantRat
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
  by_cases hk : k < 17
  · simp [hk,
      primaryFiniteRow0Parent0Split100Sub0_order18_centeredTaylorDerivMajorant16Rat_cast,
      primaryFiniteRow0Parent0Split100Sub0_order18_omegaPrimeActualDerivativeMajorantRat_cast]
  · simp [hk]

/-- Exact rational mirror of the OmegaActual derivative majorant through row
17. -/
def primaryFiniteRow0Parent0Split100Sub0Order18OmegaActualDerivativeMajorant17Rat
    (k : Nat) : Rat :=
  if _hk : k < 18 then
    if _hk16 : k <= 16 then
      primaryFiniteRow0Parent0Split100Sub0Order18OmegaActualDerivativeMajorantRat k
    else
      primaryFiniteRow0Parent0Split100Sub0Order18OmegaPrimeActualDerivativeMajorantRat
        16
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_order18_omegaActualDerivativeMajorant17Rat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0Order18OmegaActualDerivativeMajorant17Rat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17 k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Order18OmegaActualDerivativeMajorant17Rat
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17
  by_cases hk : k < 18
  · simp [hk]
    by_cases hk16 : k <= 16
    · simp [hk16,
        primaryFiniteRow0Parent0Split100Sub0_order18_omegaActualDerivativeMajorantRat_cast]
    · simp [hk16,
        primaryFiniteRow0Parent0Split100Sub0_order18_omegaPrimeActualDerivativeMajorantRat_cast]
  · simp [hk]

/-- Exact rational mirror of the OmegaActual derivative majorant through row
18. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
    (k : Nat) : Rat :=
  if _hk : k < 19 then
    if _hk17 : k <= 17 then
      primaryFiniteRow0Parent0Split100Sub0Order18OmegaActualDerivativeMajorant17Rat k
    else
      Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant18Rat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18 k := by
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18
  by_cases hk : k < 19
  · simp [hk]
    by_cases hk17 : k <= 17
    · simp [hk17,
        primaryFiniteRow0Parent0Split100Sub0_order18_omegaActualDerivativeMajorant17Rat_cast]
    · simp [hk17]
  · simp [hk]

/-- Exact rational mirror of the sharp ShapeSqDeriv derivative majorant through
row 16. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorantRat
    (k : Nat) : Rat :=
  if hk : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
      (fun j : Fin 16 =>
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs j.1)
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs
      ((1 : Rat) / 20)
      ⟨k, hk⟩
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActualSharpDerivativeMajorantRat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorantRat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant
        k := by
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorantRat
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant
  by_cases hk : k < 17
  · simp [hk,
      primaryFiniteRow0Parent0Split100Sub0_order18_centeredTaylorDerivMajorant16Rat_cast]
  · simp [hk]

/-- Exact rational mirror of the sharp ShapeSq derivative majorant through row
16. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorantRat
    (k : Nat) : Rat :=
  if hk : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
      (fun j : Fin 16 =>
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs j.1)
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorantRat
        15)
      ((1 : Rat) / 20)
      ⟨k, hk⟩
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorantRat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorantRat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant
        k := by
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorantRat
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant
  by_cases hk : k < 17
  · simp [hk,
      primaryFiniteRow0Parent0Split100Sub0_order18_centeredTaylorDerivMajorant16Rat_cast,
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActualSharpDerivativeMajorantRat_cast]
  · simp [hk]

/-- Exact rational mirror of the sharp ShapeSq derivative majorant through row
18 used by the RawProduct18 receiver. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
    (k : Nat) : Rat :=
  if _ : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorantRat k
  else if k = 17 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs
  else if k = 18 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqSharpOrder18Abs
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorant18Rat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18
        k := by
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18
  by_cases hk : k < 17
  · simp [hk,
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorantRat_cast]
  · simp [hk]
    by_cases hk17 : k = 17
    · simp [hk17]
    · simp [hk17]
      by_cases hk18 : k = 18
      · simp [hk18]
      · simp [hk18]

/-- Exact rational mirror of the generated RawProduct18 Leibniz majorant. -/
def primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantRat :
    Rat :=
  ∑ i ∈ Finset.range (18 + 1),
    (Nat.choose 18 i : Rat) *
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat i *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
        (18 - i)

theorem primaryFiniteRow0Parent0Split100Sub0_rawProductActualOrder18MajorantGenerated_eq_rat :
    primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantGenerated =
      (primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantRat :
        Real) := by
  unfold primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantGenerated
  unfold primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantRat
  unfold primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Rat.cast_mul, Rat.cast_mul]
  rw [primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant18Rat_cast]
  rw [primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorant18Rat_cast]
  norm_num

theorem primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_rat :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 18
          primaryFiniteRow0Parent0Split100Sub0RawProductActual eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantRat :
          Real) := by
  simpa [primaryFiniteRow0Parent0Split100Sub0_rawProductActualOrder18MajorantGenerated_eq_rat]
    using
      primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_generated

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_rat :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantRat :
          Real) := by
  simpa [primaryFiniteRow0Parent0Split100Sub0_rawProductActualOrder18MajorantGenerated_eq_rat]
    using
      primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_generated

end Step33
end PSDpd
end Q3
