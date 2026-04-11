import Mathlib.Algebra.Star.Basic

/-!
# H-bridge PO3 shell

This file records the smallest algebraic handoff behind the `PO3` packet.
It does **not** formalize the analytic content of cross-sign boundary
cancellation. Instead, it formalizes the logical shell consumed by the
downstream Door-2 / upper-bridge notes:

- `PO2_shell`: the mixed block has only boundary-plus-cap remainder;
- `PO3a`: the cross-sign boundary term cancels;
- therefore `PO3b`: the mixed block is cap-only;
- and by symmetry `PO3c`: the mirrored cross-sign boundary also cancels.

The point is to freeze the executable reduction before attaching the genuine Q3
objects.
-/

namespace Q3
namespace HBridge

section PO3Shell

variable {A : Type*} [AddGroup A]

/-- Abstract `PO2` shell: the mixed block splits into boundary plus cap. -/
theorem po3_cap_only_of_po2_shell
    (D_N_pm D_partial_pm D_cap_pm : A)
    (hpo2 : D_N_pm = D_partial_pm + D_cap_pm)
    (hpo3a : D_partial_pm = 0) :
    D_N_pm = D_cap_pm := by
  calc
    D_N_pm = D_partial_pm + D_cap_pm := hpo2
    _ = 0 + D_cap_pm := by simp [hpo3a]
    _ = D_cap_pm := zero_add _

end PO3Shell

section PO3Symmetry

variable {A : Type*} [AddGroup A] [StarAddMonoid A]

/-- Abstract `PO3c`: if the `(-,+)` boundary channel is the star-symmetric
image of the `(+,-)` one, then `PO3a` forces the mirrored channel to vanish. -/
theorem po3_mirror_zero_of_symmetry
    (D_partial_pm D_partial_mp : A)
    (hsymm : D_partial_mp = star D_partial_pm)
    (hpo3a : D_partial_pm = 0) :
    D_partial_mp = 0 := by
  calc
    D_partial_mp = star D_partial_pm := hsymm
    _ = star (0 : A) := by simp [hpo3a]
    _ = 0 := by simp

end PO3Symmetry

end HBridge
end Q3
