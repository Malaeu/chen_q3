import Q3.Proofs.PSD_CenteredCoeffRawOmegaATailWindowGeneratedArithmeticHandoffSupport

set_option linter.mathlibStandardSet false
set_option autoImplicit false

/-!
Raw-Omega direct chunk-integral certificate landing surface.

This module keeps the generator-facing chunk-integral route separate from the
comparison-function routes.  The generated import may prove the fields below
by splitting the finite/tail windows into chunks and checking rational Arb
integral certificates.  This file only folds those checked bounds into the
existing direct raw-Omega finite/tail receiver.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport
open MeasureTheory
open scoped BigOperators

namespace RawOmegaAChunkIntegral

abbrev windowPart (k : Nat) (ell x L U : Real) : Real :=
  Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart
    k ell x L U

/-- Bounds for a raw Step22 positive-axis Omega window `(L,U]`.  This is the
small chunk-level object generated Arb certificates should prove before the
window is folded into the direct finite/tail receiver. -/
structure WindowPartBoundsCert
    (k : Nat) (ell x L U lower upper : Real) : Prop where
  hWindowLower : lower <= windowPart k ell x L U
  hWindowUpper : windowPart k ell x L U <= upper

/-- Glue two adjacent raw-Omega window certificates. -/
theorem windowPartBoundsCert_glue_adjacent
    (k : Nat) (ell x L U c lower upper leftLower leftUpper rightLower
      rightUpper : Real)
    (hint :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L U))
    (hLeft : L <= c) (hRight : c <= U)
    (left : WindowPartBoundsCert k ell x L c leftLower leftUpper)
    (right : WindowPartBoundsCert k ell x c U rightLower rightUpper)
    (hWindowLower : lower <= leftLower + rightLower)
    (hWindowUpper : leftUpper + rightUpper <= upper) :
    WindowPartBoundsCert k ell x L U lower upper := by
  let f : Real -> Real :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
      k ell x
  have hcover : Set.Ioc L U = Set.Ioc L c ∪ Set.Ioc c U := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      by_cases hyc : y <= c
      · exact Or.inl ⟨hy.1, hyc⟩
      · exact Or.inr ⟨lt_of_not_ge hyc, hy.2⟩
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      rcases hy with hleftMem | hrightMem
      · exact ⟨hleftMem.1, le_trans hleftMem.2 hRight⟩
      · exact ⟨lt_of_le_of_lt hLeft hrightMem.1, hrightMem.2⟩
  have hdisj : Disjoint (Set.Ioc L c) (Set.Ioc c U) := by
    rw [Set.disjoint_left]
    intro y hyleft hyright
    simp only [Set.mem_Ioc] at hyleft hyright
    exact not_lt_of_ge hyleft.2 hyright.1
  have hfintLeft : IntegrableOn f (Set.Ioc L c) := by
    exact hint.mono_set (by
      intro y hy
      exact ⟨hy.1, le_trans hy.2 hRight⟩)
  have hfintRight : IntegrableOn f (Set.Ioc c U) := by
    exact hint.mono_set (by
      intro y hy
      exact ⟨lt_of_le_of_lt hLeft hy.1, hy.2⟩)
  have hsum :
      windowPart k ell x L U =
        windowPart k ell x L c + windowPart k ell x c U := by
    calc
      windowPart k ell x L U = ∫ t in Set.Ioc L c ∪ Set.Ioc c U, f t := by
            rw [← hcover]
            rfl
      _ = (∫ t in Set.Ioc L c, f t) + ∫ t in Set.Ioc c U, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ = windowPart k ell x L c + windowPart k ell x c U := by
            rfl
  refine ⟨?_, ?_⟩
  · calc
      lower <= leftLower + rightLower := hWindowLower
      _ <= windowPart k ell x L c + windowPart k ell x c U := by
            exact add_le_add left.hWindowLower right.hWindowLower
      _ = windowPart k ell x L U := by
            rw [hsum]
  · calc
      windowPart k ell x L U =
          windowPart k ell x L c + windowPart k ell x c U := hsum
      _ <= leftUpper + rightUpper := by
            exact add_le_add left.hWindowUpper right.hWindowUpper
      _ <= upper := hWindowUpper

/-- Degenerate raw-Omega window certificate on an empty adjacent interval. -/
theorem windowPartBoundsCert_empty
    (k : Nat) (ell x L : Real) :
    WindowPartBoundsCert k ell x L L 0 0 := by
  refine ⟨?_, ?_⟩
  · simp [windowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart]
  · simp [windowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart]

/-- Fold adjacent raw-Omega chunks into one window certificate. -/
theorem windowPartBoundsCert_of_chunked_range
    (k : Nat) (ell x L step : Real)
    (chunkLower chunkUpper : Nat -> Real)
    (N : Nat)
    (hstep : 0 <= step)
    (hint :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L (L + step * (N : Real))))
    (chunkCert : ∀ i < N,
      WindowPartBoundsCert
        k ell x (L + step * (i : Real)) (L + step * ((i + 1 : Nat) : Real))
        (chunkLower i) (chunkUpper i)) :
    WindowPartBoundsCert k ell x L (L + step * (N : Real))
      (∑ i ∈ Finset.range N, chunkLower i)
      (∑ i ∈ Finset.range N, chunkUpper i) := by
  induction N with
  | zero =>
      simpa using windowPartBoundsCert_empty k ell x L
  | succ N ih =>
      have hRight :
          L + step * (N : Real) <=
            L + step * (((N + 1 : Nat) : Real)) := by
        have hN : (N : Real) <= (((N + 1 : Nat) : Real)) := by
          exact_mod_cast Nat.le_succ N
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (mul_le_mul_of_nonneg_left hN hstep) L
      have hprefixHint :
          IntegrableOn
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x)
            (Set.Ioc L (L + step * (N : Real))) := by
        exact hint.mono_set (by
          intro y hy
          exact ⟨hy.1, le_trans hy.2 hRight⟩)
      have hprefix :
          WindowPartBoundsCert k ell x L (L + step * (N : Real))
            (∑ i ∈ Finset.range N, chunkLower i)
            (∑ i ∈ Finset.range N, chunkUpper i) := by
        exact ih hprefixHint
          (fun i hi => chunkCert i (Nat.lt_trans hi (Nat.lt_succ_self N)))
      have hlast :
          WindowPartBoundsCert
            k ell x (L + step * (N : Real))
              (L + step * (((N + 1 : Nat) : Real)))
            (chunkLower N) (chunkUpper N) := by
        simpa using chunkCert N (Nat.lt_succ_self N)
      have hLeft : L <= L + step * (N : Real) := by
        have hN : (0 : Real) <= (N : Real) := by exact_mod_cast Nat.zero_le N
        nlinarith [mul_nonneg hstep hN]
      exact
        windowPartBoundsCert_glue_adjacent
          k ell x L (L + step * (((N + 1 : Nat) : Real)))
          (L + step * (N : Real))
          (∑ i ∈ Finset.range (N + 1), chunkLower i)
          (∑ i ∈ Finset.range (N + 1), chunkUpper i)
          (∑ i ∈ Finset.range N, chunkLower i)
          (∑ i ∈ Finset.range N, chunkUpper i)
          (chunkLower N) (chunkUpper N)
          hint hLeft hRight hprefix hlast
          (by rw [Finset.sum_range_succ])
          (by rw [Finset.sum_range_succ])

/-- Fold adjacent raw-Omega chunks and compare their endpoint sums to a target
window. -/
theorem windowPartBoundsCert_of_chunked_range_bounds
    (k : Nat) (ell x L step : Real)
    (chunkLower chunkUpper : Nat -> Real)
    (N : Nat) (windowLower windowUpper : Real)
    (hstep : 0 <= step)
    (hint :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L (L + step * (N : Real))))
    (chunkCert : ∀ i < N,
      WindowPartBoundsCert
        k ell x (L + step * (i : Real)) (L + step * ((i + 1 : Nat) : Real))
        (chunkLower i) (chunkUpper i))
    (hWindowLower : windowLower <= ∑ i ∈ Finset.range N, chunkLower i)
    (hWindowUpper : (∑ i ∈ Finset.range N, chunkUpper i) <= windowUpper) :
    WindowPartBoundsCert k ell x L (L + step * (N : Real))
      windowLower windowUpper := by
  have folded :=
    windowPartBoundsCert_of_chunked_range
      k ell x L step chunkLower chunkUpper N hstep hint chunkCert
  exact
    { hWindowLower := le_trans hWindowLower folded.hWindowLower
      hWindowUpper := le_trans folded.hWindowUpper hWindowUpper }

end RawOmegaAChunkIntegral

/-- Primary finite-window direct integral bounds produced by a chunk-integral
certificate generator. -/
structure PrimaryK11RawOmegaAFiniteWindowChunkIntegralBoundsCert where
  hLower : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
  hUpper : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff <=
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

/-- Primary tail-window direct integral and tail-remainder bounds produced by
a chunk-integral certificate generator. -/
structure PrimaryK11RawOmegaATailWindowChunkIntegralBoundsCert where
  hWindowLower : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd
  hWindowUpper : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd <=
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n
  hRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n

/-- Control finite-window direct integral bounds produced by a chunk-integral
certificate generator. -/
structure ControlK9RawOmegaAFiniteWindowChunkIntegralBoundsCert where
  hLower : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
  hUpper : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff <=
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

/-- Control tail-window direct integral and tail-remainder bounds produced by
a chunk-integral certificate generator. -/
structure ControlK9RawOmegaATailWindowChunkIntegralBoundsCert where
  hWindowLower : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd
  hWindowUpper : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd <=
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n
  hRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n

/-- Generated-facing primary finite-window chunk payload for the active
raw-Omega route.  The generator proves one scalar integral bound per
distance/chunk and two row-sum comparisons per distance. -/
structure PrimaryK11RawOmegaAFiniteWindowChunkedRangePayload where
  chunkLower : CoeffIndex23 -> Nat -> Real
  chunkUpper : CoeffIndex23 -> Nat -> Real
  chunkCert : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 ->
    RawOmegaAChunkIntegral.WindowPartBoundsCert
      11 primaryK11Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i : Real))
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
      (chunkLower n i) (chunkUpper n i)
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkLower n i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkUpper n i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

/-- Generated-facing primary tail-window chunk payload for the active
raw-Omega route. -/
structure PrimaryK11RawOmegaATailWindowChunkedRangePayload where
  chunkLower : CoeffIndex23 -> Nat -> Real
  chunkUpper : CoeffIndex23 -> Nat -> Real
  chunkCert : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 ->
    RawOmegaAChunkIntegral.WindowPartBoundsCert
      11 primaryK11Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real))
      (chunkLower n i) (chunkUpper n i)
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkLower n i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkUpper n i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n
  hRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n

/-- Generated-facing control finite-window chunk payload for the active
raw-Omega route. -/
structure ControlK9RawOmegaAFiniteWindowChunkedRangePayload where
  chunkLower : CoeffIndex23 -> Nat -> Real
  chunkUpper : CoeffIndex23 -> Nat -> Real
  chunkCert : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 ->
    RawOmegaAChunkIntegral.WindowPartBoundsCert
      9 controlK9Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i : Real))
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
      (chunkLower n i) (chunkUpper n i)
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkLower n i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkUpper n i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

/-- Generated-facing control tail-window chunk payload for the active
raw-Omega route. -/
structure ControlK9RawOmegaATailWindowChunkedRangePayload where
  chunkLower : CoeffIndex23 -> Nat -> Real
  chunkUpper : CoeffIndex23 -> Nat -> Real
  chunkCert : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 ->
    RawOmegaAChunkIntegral.WindowPartBoundsCert
      9 controlK9Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real))
      (chunkLower n i) (chunkUpper n i)
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkLower n i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkUpper n i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n
  hRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n

def primaryK11RawOmegaAFiniteWindowChunkIntegralBoundsCert_of_chunkedRangePayload
    (payload : PrimaryK11RawOmegaAFiniteWindowChunkedRangePayload) :
    PrimaryK11RawOmegaAFiniteWindowChunkIntegralBoundsCert := by
  refine ⟨?_, ?_⟩
  · intro n
    have hint :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4))
          (Set.Ioc (0 : Real) ((0 : Real) + (10 : Real) * (26 : Real))) := by
      have h0 :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioc_zero
          rawOmegaAFiniteTailCutoff n
      norm_num [rawOmegaAFiniteTailCutoff] at h0 ⊢
      exact h0
    have folded :=
      RawOmegaAChunkIntegral.windowPartBoundsCert_of_chunked_range_bounds
        11 primaryK11Ell ((n.1 : Real) / 4)
        (0 : Real) (10 : Real)
        (payload.chunkLower n) (payload.chunkUpper n) 26
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n)
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
        (by norm_num) hint (payload.chunkCert n)
        (payload.hLowerSum n) (payload.hUpperSum n)
    have h := folded.hWindowLower
    norm_num [RawOmegaAChunkIntegral.windowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated,
      rawOmegaAFiniteTailCutoff] at h ⊢
    exact h
  · intro n
    have hint :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4))
          (Set.Ioc (0 : Real) ((0 : Real) + (10 : Real) * (26 : Real))) := by
      have h0 :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioc_zero
          rawOmegaAFiniteTailCutoff n
      norm_num [rawOmegaAFiniteTailCutoff] at h0 ⊢
      exact h0
    have folded :=
      RawOmegaAChunkIntegral.windowPartBoundsCert_of_chunked_range_bounds
        11 primaryK11Ell ((n.1 : Real) / 4)
        (0 : Real) (10 : Real)
        (payload.chunkLower n) (payload.chunkUpper n) 26
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n)
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
        (by norm_num) hint (payload.chunkCert n)
        (payload.hLowerSum n) (payload.hUpperSum n)
    have h := folded.hWindowUpper
    norm_num [RawOmegaAChunkIntegral.windowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated,
      rawOmegaAFiniteTailCutoff] at h ⊢
    exact h

def primaryK11RawOmegaATailWindowChunkIntegralBoundsCert_of_chunkedRangePayload
    (payload : PrimaryK11RawOmegaATailWindowChunkedRangePayload) :
    PrimaryK11RawOmegaATailWindowChunkIntegralBoundsCert := by
  refine ⟨?_, ?_, payload.hRemainder⟩
  · intro n
    have hintIoi :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4))
          (Set.Ioi rawOmegaAFiniteTailCutoff) := by
      exact
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioi_of_nonneg
          rawOmegaAFiniteTailCutoff (by norm_num [rawOmegaAFiniteTailCutoff]) n
    have hint :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4))
          (Set.Ioc rawOmegaAFiniteTailCutoff
            (rawOmegaAFiniteTailCutoff + (10 : Real) * (26 : Real))) := by
      exact hintIoi.mono_set (by intro eta heta; exact heta.1)
    have folded :=
      RawOmegaAChunkIntegral.windowPartBoundsCert_of_chunked_range_bounds
        11 primaryK11Ell ((n.1 : Real) / 4)
        rawOmegaAFiniteTailCutoff (10 : Real)
        (payload.chunkLower n) (payload.chunkUpper n) 26
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n)
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
        (by norm_num) hint (payload.chunkCert n)
        (payload.hLowerSum n) (payload.hUpperSum n)
    have h := folded.hWindowLower
    norm_num [RawOmegaAChunkIntegral.windowPart,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated,
      rawOmegaAFiniteTailCutoff, rawOmegaATailWindowEnd] at h ⊢
    exact h
  · intro n
    have hintIoi :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4))
          (Set.Ioi rawOmegaAFiniteTailCutoff) := by
      exact
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioi_of_nonneg
          rawOmegaAFiniteTailCutoff (by norm_num [rawOmegaAFiniteTailCutoff]) n
    have hint :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4))
          (Set.Ioc rawOmegaAFiniteTailCutoff
            (rawOmegaAFiniteTailCutoff + (10 : Real) * (26 : Real))) := by
      exact hintIoi.mono_set (by intro eta heta; exact heta.1)
    have folded :=
      RawOmegaAChunkIntegral.windowPartBoundsCert_of_chunked_range_bounds
        11 primaryK11Ell ((n.1 : Real) / 4)
        rawOmegaAFiniteTailCutoff (10 : Real)
        (payload.chunkLower n) (payload.chunkUpper n) 26
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n)
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
        (by norm_num) hint (payload.chunkCert n)
        (payload.hLowerSum n) (payload.hUpperSum n)
    have h := folded.hWindowUpper
    norm_num [RawOmegaAChunkIntegral.windowPart,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated,
      rawOmegaAFiniteTailCutoff, rawOmegaATailWindowEnd] at h ⊢
    exact h

def controlK9RawOmegaAFiniteWindowChunkIntegralBoundsCert_of_chunkedRangePayload
    (payload : ControlK9RawOmegaAFiniteWindowChunkedRangePayload) :
    ControlK9RawOmegaAFiniteWindowChunkIntegralBoundsCert := by
  refine ⟨?_, ?_⟩
  · intro n
    have hint :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4))
          (Set.Ioc (0 : Real) ((0 : Real) + (10 : Real) * (26 : Real))) := by
      have h0 :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioc_zero
          rawOmegaAFiniteTailCutoff n
      norm_num [rawOmegaAFiniteTailCutoff] at h0 ⊢
      exact h0
    have folded :=
      RawOmegaAChunkIntegral.windowPartBoundsCert_of_chunked_range_bounds
        9 controlK9Ell ((n.1 : Real) / 4)
        (0 : Real) (10 : Real)
        (payload.chunkLower n) (payload.chunkUpper n) 26
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n)
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
        (by norm_num) hint (payload.chunkCert n)
        (payload.hLowerSum n) (payload.hUpperSum n)
    have h := folded.hWindowLower
    norm_num [RawOmegaAChunkIntegral.windowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated,
      rawOmegaAFiniteTailCutoff] at h ⊢
    exact h
  · intro n
    have hint :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4))
          (Set.Ioc (0 : Real) ((0 : Real) + (10 : Real) * (26 : Real))) := by
      have h0 :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioc_zero
          rawOmegaAFiniteTailCutoff n
      norm_num [rawOmegaAFiniteTailCutoff] at h0 ⊢
      exact h0
    have folded :=
      RawOmegaAChunkIntegral.windowPartBoundsCert_of_chunked_range_bounds
        9 controlK9Ell ((n.1 : Real) / 4)
        (0 : Real) (10 : Real)
        (payload.chunkLower n) (payload.chunkUpper n) 26
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n)
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
        (by norm_num) hint (payload.chunkCert n)
        (payload.hLowerSum n) (payload.hUpperSum n)
    have h := folded.hWindowUpper
    norm_num [RawOmegaAChunkIntegral.windowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated,
      rawOmegaAFiniteTailCutoff] at h ⊢
    exact h

def controlK9RawOmegaATailWindowChunkIntegralBoundsCert_of_chunkedRangePayload
    (payload : ControlK9RawOmegaATailWindowChunkedRangePayload) :
    ControlK9RawOmegaATailWindowChunkIntegralBoundsCert := by
  refine ⟨?_, ?_, payload.hRemainder⟩
  · intro n
    have hintIoi :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4))
          (Set.Ioi rawOmegaAFiniteTailCutoff) := by
      exact
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioi_of_nonneg
          rawOmegaAFiniteTailCutoff (by norm_num [rawOmegaAFiniteTailCutoff]) n
    have hint :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4))
          (Set.Ioc rawOmegaAFiniteTailCutoff
            (rawOmegaAFiniteTailCutoff + (10 : Real) * (26 : Real))) := by
      exact hintIoi.mono_set (by intro eta heta; exact heta.1)
    have folded :=
      RawOmegaAChunkIntegral.windowPartBoundsCert_of_chunked_range_bounds
        9 controlK9Ell ((n.1 : Real) / 4)
        rawOmegaAFiniteTailCutoff (10 : Real)
        (payload.chunkLower n) (payload.chunkUpper n) 26
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n)
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
        (by norm_num) hint (payload.chunkCert n)
        (payload.hLowerSum n) (payload.hUpperSum n)
    have h := folded.hWindowLower
    norm_num [RawOmegaAChunkIntegral.windowPart,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated,
      rawOmegaAFiniteTailCutoff, rawOmegaATailWindowEnd] at h ⊢
    exact h
  · intro n
    have hintIoi :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4))
          (Set.Ioi rawOmegaAFiniteTailCutoff) := by
      exact
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioi_of_nonneg
          rawOmegaAFiniteTailCutoff (by norm_num [rawOmegaAFiniteTailCutoff]) n
    have hint :
        IntegrableOn
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4))
          (Set.Ioc rawOmegaAFiniteTailCutoff
            (rawOmegaAFiniteTailCutoff + (10 : Real) * (26 : Real))) := by
      exact hintIoi.mono_set (by intro eta heta; exact heta.1)
    have folded :=
      RawOmegaAChunkIntegral.windowPartBoundsCert_of_chunked_range_bounds
        9 controlK9Ell ((n.1 : Real) / 4)
        rawOmegaAFiniteTailCutoff (10 : Real)
        (payload.chunkLower n) (payload.chunkUpper n) 26
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n)
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
        (by norm_num) hint (payload.chunkCert n)
        (payload.hLowerSum n) (payload.hUpperSum n)
    have h := folded.hWindowUpper
    norm_num [RawOmegaAChunkIntegral.windowPart,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated,
      rawOmegaAFiniteTailCutoff, rawOmegaATailWindowEnd] at h ⊢
    exact h

/-- Single generated-object target for the chunked range payloads. -/
structure RawOmegaAChunkedRangePayload where
  primaryFinite : PrimaryK11RawOmegaAFiniteWindowChunkedRangePayload
  primaryTail : PrimaryK11RawOmegaATailWindowChunkedRangePayload
  controlFinite : ControlK9RawOmegaAFiniteWindowChunkedRangePayload
  controlTail : ControlK9RawOmegaATailWindowChunkedRangePayload

/-- Single generated-object target for Louise route-A direct chunk-integral
certificates.  The generator should prove this structure, not reopen the
downstream hbox/Step33B/Step33C glue. -/
structure RawOmegaAChunkIntegralBoundsCert where
  primaryFinite : PrimaryK11RawOmegaAFiniteWindowChunkIntegralBoundsCert
  primaryTail : PrimaryK11RawOmegaATailWindowChunkIntegralBoundsCert
  controlFinite : ControlK9RawOmegaAFiniteWindowChunkIntegralBoundsCert
  controlTail : ControlK9RawOmegaATailWindowChunkIntegralBoundsCert

def RawOmegaAChunkedRangePayload.toChunkIntegralBoundsCert
    (payload : RawOmegaAChunkedRangePayload) :
    RawOmegaAChunkIntegralBoundsCert :=
  { primaryFinite :=
      primaryK11RawOmegaAFiniteWindowChunkIntegralBoundsCert_of_chunkedRangePayload
        payload.primaryFinite
    primaryTail :=
      primaryK11RawOmegaATailWindowChunkIntegralBoundsCert_of_chunkedRangePayload
        payload.primaryTail
    controlFinite :=
      controlK9RawOmegaAFiniteWindowChunkIntegralBoundsCert_of_chunkedRangePayload
        payload.controlFinite
    controlTail :=
      controlK9RawOmegaATailWindowChunkIntegralBoundsCert_of_chunkedRangePayload
        payload.controlTail }

def primaryK11RawOmegaADirectTailWindowAnalyticPayload_of_chunkIntegralBounds
    (hFinite : PrimaryK11RawOmegaAFiniteWindowChunkIntegralBoundsCert)
    (hTail : PrimaryK11RawOmegaATailWindowChunkIntegralBoundsCert) :
    PrimaryK11RawOmegaADirectTailWindowAnalyticPayload
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated :=
  { hProfileInt :=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioi
    hFiniteLower := hFinite.hLower
    hFiniteUpper := hFinite.hUpper
    hTailWindowLower := hTail.hWindowLower
    hTailWindowUpper := hTail.hWindowUpper
    hTailRemainder := hTail.hRemainder }

def controlK9RawOmegaADirectTailWindowAnalyticPayload_of_chunkIntegralBounds
    (hFinite : ControlK9RawOmegaAFiniteWindowChunkIntegralBoundsCert)
    (hTail : ControlK9RawOmegaATailWindowChunkIntegralBoundsCert) :
    ControlK9RawOmegaADirectTailWindowAnalyticPayload
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated :=
  { hProfileInt :=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioi
    hFiniteLower := hFinite.hLower
    hFiniteUpper := hFinite.hUpper
    hTailWindowLower := hTail.hWindowLower
    hTailWindowUpper := hTail.hWindowUpper
    hTailRemainder := hTail.hRemainder }

/-- Louise route-A folder theorem surface, adapted to the checked direct
raw-Omega receiver. -/
def rawOmegaADirectTailWindowInputs_of_generatedChunkIntegralBounds
    (hPrimaryFinite : PrimaryK11RawOmegaAFiniteWindowChunkIntegralBoundsCert)
    (hPrimaryTail : PrimaryK11RawOmegaATailWindowChunkIntegralBoundsCert)
    (hControlFinite : ControlK9RawOmegaAFiniteWindowChunkIntegralBoundsCert)
    (hControlTail : ControlK9RawOmegaATailWindowChunkIntegralBoundsCert) :
    RawOmegaADirectTailWindowInputs :=
  { primaryAnalytic :=
      primaryK11RawOmegaADirectTailWindowAnalyticPayload_of_chunkIntegralBounds
        hPrimaryFinite hPrimaryTail
    controlAnalytic :=
      controlK9RawOmegaADirectTailWindowAnalyticPayload_of_chunkIntegralBounds
        hControlFinite hControlTail }

/-- Fold a single generated chunk-integral certificate into the checked
raw-Omega direct finite/tail-window receiver. -/
def RawOmegaAChunkIntegralBoundsCert.toDirectTailWindowInputs
    (cert : RawOmegaAChunkIntegralBoundsCert) :
    RawOmegaADirectTailWindowInputs :=
  rawOmegaADirectTailWindowInputs_of_generatedChunkIntegralBounds
    cert.primaryFinite cert.primaryTail cert.controlFinite cert.controlTail

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
