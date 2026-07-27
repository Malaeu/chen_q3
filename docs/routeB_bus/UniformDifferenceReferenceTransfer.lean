import Mathlib

set_option linter.mathlibStandardSet false

open Filter Topology
open scoped Topology

noncomputable section
namespace Q3.RouteB

theorem tendstoUniformlyOn_of_difference_and_reference
    {ι α E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} (F G : ι → α → E) (X : α → E) (K : Set α)
    (hdiff : TendstoUniformlyOn
      (fun i z => F i z - G i z) (fun _ => 0) l K)
    (href : TendstoUniformlyOn G X l K) :
    TendstoUniformlyOn F X l K := by
  have h := hdiff.add href
  convert h using 1
  · ext i z
    simp
  · ext z
    simp

theorem tendstoLocallyUniformlyOn_of_difference_and_reference
    {ι α E : Type*} [TopologicalSpace α] [LocallyCompactSpace α]
    [NormedAddCommGroup E] {l : Filter ι}
    (F G : ι → α → E) (X : α → E) (U : Set α)
    (hU : IsOpen U)
    (hdiff : TendstoLocallyUniformlyOn
      (fun i z => F i z - G i z) (fun _ => 0) l U)
    (href : TendstoLocallyUniformlyOn G X l U) :
    TendstoLocallyUniformlyOn F X l U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at hdiff href ⊢
  intro K hKU hK
  exact tendstoUniformlyOn_of_difference_and_reference
    F G X K (hdiff K hKU hK) (href K hKU hK)

#print axioms tendstoUniformlyOn_of_difference_and_reference
#print axioms tendstoLocallyUniformlyOn_of_difference_and_reference

end Q3.RouteB
