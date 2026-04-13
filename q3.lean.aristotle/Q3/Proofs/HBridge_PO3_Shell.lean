import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Span.Basic

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

/-- Abstract finite-matrix receiver for `PO3a`: if the boundary channel is
represented by a finite cancellation packet `A + B + M`, and that packet
vanishes, then the boundary channel itself vanishes. -/
theorem po3_boundary_zero_of_matrix_receiver
    (D_partial_pm receiver A_mat B_mat M_mat : A)
    (hreceiver : D_partial_pm = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_partial_pm = 0 := by
  calc
    D_partial_pm = receiver := hreceiver
    _ = A_mat + B_mat + M_mat := hmatrix
    _ = 0 := hcancel

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

/-- Combined shell: `PO2` plus the finite-matrix receiver already implies the
cap-only mixed block conclusion. -/
theorem po3_cap_only_of_po2_and_matrix_receiver
    (D_N_pm D_partial_pm D_cap_pm receiver A_mat B_mat M_mat : A)
    (hpo2 : D_N_pm = D_partial_pm + D_cap_pm)
    (hreceiver : D_partial_pm = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_N_pm = D_cap_pm := by
  apply po3_cap_only_of_po2_shell
  · exact hpo2
  · exact po3_boundary_zero_of_matrix_receiver
      D_partial_pm receiver A_mat B_mat M_mat hreceiver hmatrix hcancel

end PO3Shell

section PO3WeakerBridge

variable {A : Type*} [AddGroup A]

/-- Abstract weaker bridge (`PO3a-A + PO3a-B`):
if the genuine boundary packet splits into a zero-endpoint part and an
endpoint-word part, and the zero-endpoint packet cancels globally, then only
the endpoint-word packet remains. -/
theorem po3_endpoint_packet_of_weaker_bridge
    (D_partial_pm zero_endpoint_packet endpoint_word_packet : A)
    (hsplit : D_partial_pm = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0) :
    D_partial_pm = endpoint_word_packet := by
  calc
    D_partial_pm = zero_endpoint_packet + endpoint_word_packet := hsplit
    _ = 0 + endpoint_word_packet := by simp [hzero]
    _ = endpoint_word_packet := zero_add _

/-- Once the weaker bridge lands and the surviving endpoint-word packet enters
the finite receiver, the boundary channel already vanishes. -/
theorem po3_boundary_zero_of_weaker_bridge_and_matrix_receiver
    (D_partial_pm zero_endpoint_packet endpoint_word_packet receiver A_mat B_mat M_mat : A)
    (hsplit : D_partial_pm = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0)
    (hreceiver : endpoint_word_packet = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_partial_pm = 0 := by
  calc
    D_partial_pm = endpoint_word_packet := by
      exact po3_endpoint_packet_of_weaker_bridge
        D_partial_pm zero_endpoint_packet endpoint_word_packet hsplit hzero
    _ = receiver := hreceiver
    _ = A_mat + B_mat + M_mat := hmatrix
    _ = 0 := hcancel

/-- `PO2` plus the weaker bridge plus the finite receiver already imply the
cap-only conclusion. This is the exact shell needed before plugging in the real
Volterra/endpoint packet. -/
theorem po3_cap_only_of_po2_and_weaker_bridge
    (D_N_pm D_partial_pm D_cap_pm zero_endpoint_packet endpoint_word_packet
      receiver A_mat B_mat M_mat : A)
    (hpo2 : D_N_pm = D_partial_pm + D_cap_pm)
    (hsplit : D_partial_pm = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0)
    (hreceiver : endpoint_word_packet = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_N_pm = D_cap_pm := by
  apply po3_cap_only_of_po2_shell
  · exact hpo2
  · exact po3_boundary_zero_of_weaker_bridge_and_matrix_receiver
      D_partial_pm zero_endpoint_packet endpoint_word_packet
      receiver A_mat B_mat M_mat hsplit hzero hreceiver hmatrix hcancel

end PO3WeakerBridge

section PO3AntiderivativeTransport

variable {A : Type*} [AddGroup A]

/-- `PO3a-A` shell: once the genuine boundary packet is transported to the
Volterra-antiderivative side and expanded into a zero-endpoint part plus an
endpoint-word part, the active weaker bridge reduces immediately to the
endpoint packet. -/
theorem po3_endpoint_packet_of_antiderivative_transport
    (D_partial_pm antiderivative_packet zero_endpoint_packet endpoint_word_packet : A)
    (htransport : D_partial_pm = antiderivative_packet)
    (hexpand : antiderivative_packet = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0) :
    D_partial_pm = endpoint_word_packet := by
  calc
    D_partial_pm = antiderivative_packet := htransport
    _ = zero_endpoint_packet + endpoint_word_packet := hexpand
    _ = 0 + endpoint_word_packet := by simp [hzero]
    _ = endpoint_word_packet := zero_add _

/-- Combined `PO3a-A -> PO3a-B -> finite receiver` shell: once the
antiderivative transport packet collapses to the endpoint-word packet, the
already frozen finite receiver kills the cross-sign boundary channel. -/
theorem po3_boundary_zero_of_antiderivative_transport_and_matrix_receiver
    (D_partial_pm antiderivative_packet zero_endpoint_packet endpoint_word_packet
      receiver A_mat B_mat M_mat : A)
    (htransport : D_partial_pm = antiderivative_packet)
    (hexpand : antiderivative_packet = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0)
    (hreceiver : endpoint_word_packet = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_partial_pm = 0 := by
  calc
    D_partial_pm = endpoint_word_packet := by
      exact po3_endpoint_packet_of_antiderivative_transport
        D_partial_pm antiderivative_packet zero_endpoint_packet endpoint_word_packet
        htransport hexpand hzero
    _ = receiver := hreceiver
    _ = A_mat + B_mat + M_mat := hmatrix
    _ = 0 := hcancel

end PO3AntiderivativeTransport

section PO3Witness

variable {𝕜 V W : Type*}
variable [DivisionRing 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

/-- If the boundary-cap subspace already contains `h` but does not contain `v`,
then `v` cannot lie on the line generated by `h`. -/
theorem not_mem_span_singleton_of_mem_submodule_of_not_mem
    {E : Submodule 𝕜 V} {h v : V}
    (hhE : h ∈ E) (hvE : v ∉ E) :
    v ∉ 𝕜 ∙ h := by
  intro hvh
  have hline : 𝕜 ∙ h ≤ E := (Submodule.span_singleton_le_iff_mem h E).2 hhE
  exact hvE (hline hvh)

/-- Collinearity with a single vector is reflected by an injective linear map. -/
theorem mem_span_singleton_of_mem_span_singleton_map
    {f : V →ₗ[𝕜] W} (hf : Function.Injective f) {h v : V}
    (hfv : f v ∈ 𝕜 ∙ f h) :
    v ∈ 𝕜 ∙ h := by
  rcases Submodule.mem_span_singleton.mp hfv with ⟨a, ha⟩
  refine Submodule.mem_span_singleton.mpr ?_
  refine ⟨a, ?_⟩
  apply hf
  simpa using ha

/-- Hence non-collinearity also survives after applying an injective linear map. -/
theorem not_mem_span_singleton_map_of_injective
    {f : V →ₗ[𝕜] W} (hf : Function.Injective f) {h v : V}
    (hv : v ∉ 𝕜 ∙ h) :
    f v ∉ 𝕜 ∙ f h := by
  intro hfv
  exact hv (mem_span_singleton_of_mem_span_singleton_map hf hfv)

/-- Dually, dependence of linear functionals also descends through a surjective
pullback. This is the minus-side outer-factor bridge behind `PO3a.4`. -/
theorem mem_span_singleton_of_comp_mem_span_singleton_of_surjective
    {V₁ V₂ : Type*}
    [Field 𝕜]
    [AddCommGroup V₁] [Module 𝕜 V₁]
    [AddCommGroup V₂] [Module 𝕜 V₂]
    {g : V₁ →ₗ[𝕜] V₂} (hg : Function.Surjective g)
    {φ ψ : V₂ →ₗ[𝕜] 𝕜}
    (hcomp : φ.comp g ∈ 𝕜 ∙ (ψ.comp g)) :
    φ ∈ 𝕜 ∙ ψ := by
  rcases Submodule.mem_span_singleton.mp hcomp with ⟨a, ha⟩
  refine Submodule.mem_span_singleton.mpr ?_
  refine ⟨a, ?_⟩
  ext y
  rcases hg y with ⟨x, rfl⟩
  have hx := LinearMap.congr_fun ha x
  simpa using hx

/-- Hence non-collinearity of functionals also survives pullback along a
surjective linear map. -/
theorem not_mem_span_singleton_comp_of_surjective
    {V₁ V₂ : Type*}
    [Field 𝕜]
    [AddCommGroup V₁] [Module 𝕜 V₁]
    [AddCommGroup V₂] [Module 𝕜 V₂]
    {g : V₁ →ₗ[𝕜] V₂} (hg : Function.Surjective g)
    {φ ψ : V₂ →ₗ[𝕜] 𝕜}
    (hφ : φ ∉ 𝕜 ∙ ψ) :
    φ.comp g ∉ 𝕜 ∙ (ψ.comp g) := by
  intro hcomp
  exact hφ (mem_span_singleton_of_comp_mem_span_singleton_of_surjective hg hcomp)

/-- Practical `PO3a.3` receiver: once `h` lives inside the finite boundary-cap
space `E` but `v` does not, any injective transport keeps them non-collinear. -/
theorem not_mem_span_singleton_map_of_mem_submodule_of_not_mem
    {E : Submodule 𝕜 V} {f : V →ₗ[𝕜] W} (hf : Function.Injective f)
    {h v : V} (hhE : h ∈ E) (hvE : v ∉ E) :
    f v ∉ 𝕜 ∙ f h := by
  apply not_mem_span_singleton_map_of_injective hf
  exact not_mem_span_singleton_of_mem_submodule_of_not_mem hhE hvE

/-- Dual-witness version: a single linear functional annihilating the whole
boundary-cap subspace but not `v` already proves `v ∉ E`. -/
theorem not_mem_submodule_of_linearForm
    {E : Submodule 𝕜 V} {v : V} {φ : V →ₗ[𝕜] 𝕜}
    (hEφ : E ≤ LinearMap.ker φ) (hvφ : φ v ≠ 0) :
    v ∉ E := by
  intro hvE
  exact hvφ (show φ v = 0 from hEφ hvE)

/-- Abstract projector criterion: if a linear projector `Π` has range `E`, then
membership in `E` is equivalent to being fixed by `Π`. -/
theorem mem_submodule_iff_projector_eq_self
    {E : Submodule 𝕜 V} {Pproj : V →ₗ[𝕜] V}
    (hPproj_idem : Pproj.comp Pproj = Pproj) (hPproj_range : LinearMap.range Pproj = E)
    {w : V} :
    w ∈ E ↔ Pproj w = w := by
  constructor
  · intro hwE
    rw [← hPproj_range, LinearMap.mem_range] at hwE
    rcases hwE with ⟨u, rfl⟩
    simpa using LinearMap.congr_fun hPproj_idem u
  · intro hw
    rw [← hPproj_range, LinearMap.mem_range]
    exact ⟨w, hw⟩

/-- Hence a nonzero projector residual already proves that `w` is outside the
boundary-cap subspace. -/
theorem not_mem_submodule_of_projector_residual_ne_zero
    {E : Submodule 𝕜 V} {Pproj : V →ₗ[𝕜] V}
    (hPproj_idem : Pproj.comp Pproj = Pproj) (hPproj_range : LinearMap.range Pproj = E)
    {w : V} (hres : w - Pproj w ≠ 0) :
    w ∉ E := by
  intro hwE
  have hfix : Pproj w = w :=
    (mem_submodule_iff_projector_eq_self hPproj_idem hPproj_range).1 hwE
  exact hres (sub_eq_zero.mpr hfix.symm)

/-- Projector-witness version of the `PO3a.3` receiver: once `h` lies in the
boundary-cap subspace `E`, a nonzero projector residual for `v` excludes
collinearity after any injective transport. -/
theorem not_mem_span_singleton_map_of_projector_residual_ne_zero
    {E : Submodule 𝕜 V} {Pproj : V →ₗ[𝕜] V} {f : V →ₗ[𝕜] W}
    (hPproj_idem : Pproj.comp Pproj = Pproj) (hPproj_range : LinearMap.range Pproj = E)
    (hf : Function.Injective f)
    {h v : V} (hhE : h ∈ E) (hres : v - Pproj v ≠ 0) :
    f v ∉ 𝕜 ∙ f h := by
  apply not_mem_span_singleton_map_of_mem_submodule_of_not_mem hf hhE
  exact not_mem_submodule_of_projector_residual_ne_zero hPproj_idem hPproj_range hres

/-- Combined witness packet: if `h` lies in the boundary-cap subspace `E`, a
single linear functional separates `v` from `E`, and the transport is
injective, then the transported vectors are still non-collinear. -/
theorem not_mem_span_singleton_map_of_linearForm_witness
    {E : Submodule 𝕜 V} {f : V →ₗ[𝕜] W} (hf : Function.Injective f)
    {h v : V} {φ : V →ₗ[𝕜] 𝕜}
    (hhE : h ∈ E) (hEφ : E ≤ LinearMap.ker φ) (hvφ : φ v ≠ 0) :
    f v ∉ 𝕜 ∙ f h := by
  apply not_mem_span_singleton_map_of_mem_submodule_of_not_mem hf hhE
  exact not_mem_submodule_of_linearForm hEφ hvφ

end PO3Witness

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
