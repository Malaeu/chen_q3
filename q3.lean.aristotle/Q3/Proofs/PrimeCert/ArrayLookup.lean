import Mathlib

/-!
Helpers for lookup tables stored as Arrays.

We use a fuelled binary search to avoid large match expressions.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Binary search for a key in a sorted `Array (Nat × α)`.
    Returns `some v` if `(n, v)` is present, otherwise `none`.
    The search is fuelled by `arr.size` to ensure termination. -/
def natArrayLookup {α} (arr : Array (Nat × α)) (n : Nat) : Option α :=
  let rec go (fuel lo hi : Nat) : Option α :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        if lo < hi then
          let mid := (lo + hi) / 2
          match arr[mid]? with
          | none => none
          | some (k, v) =>
              if n < k then
                go fuel lo mid
              else if k < n then
                go fuel (mid + 1) hi
              else
                some v
        else
          none
  go arr.size 0 arr.size

end Q3.Proofs.PrimeCert
