import Mathlib

#check closure_mono

example (K : ℝ) (f : ℝ → ℝ) (h : Function.support f ⊆ Set.Icc (-K) K) : 
    HasCompactSupport f := by
  have h1 : tsupport f ⊆ Set.Icc (-K) K := by
    calc tsupport f = closure (Function.support f) := rfl
      _ ⊆ closure (Set.Icc (-K) K) := closure_mono h
      _ = Set.Icc (-K) K := IsClosed.closure_eq isClosed_Icc
  exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) h1
