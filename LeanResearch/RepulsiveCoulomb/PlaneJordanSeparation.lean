module

public import LeanResearch.RepulsiveCoulomb.Imported.Schoenflies.JordanClosed
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! Transport of Álvaro Begué's Jordan separation theorem to arbitrary spaces
homeomorphic to the Euclidean plane. Source and pinned import attribution are in
Imported/Schoenflies/PROVENANCE.md. No polygonal-crosscut theorem is used here. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- A continuous simple closed parametrized curve separates any topological plane.
The two sets are the actual connected components, and the first has compact closure. -/
theorem jordan_separation_of_homeomorph {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ Schoenflies.Plane) (f : ℝ → X)
    (hc : ContinuousOn f (Icc 0 1)) (hclose : f 0 = f 1)
    (hinj : InjOn f (Ico 0 1)) :
    ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (f '' Icc 0 1)ᶜ ∧
      frontier U = f '' Icc 0 1 ∧ frontier V = f '' Icc 0 1 ∧
      IsCompact (closure U) ∧
      (∀ x ∈ U, connectedComponentIn (f '' Icc 0 1)ᶜ x = U) ∧
      (∀ x ∈ V, connectedComponentIn (f '' Icc 0 1)ᶜ x = V) := by
  let C := (e ∘ f) '' Icc 0 1
  have hj : Schoenflies.IsJordanCurve C := by
    refine ⟨e ∘ f, ⟨e.continuous.comp_continuousOn hc, ?_, ?_⟩, rfl⟩
    · exact congrArg e hclose
    · intro s hs t ht h
      exact hinj hs ht (e.injective h)
  have hs := Schoenflies.jordan_curve_theorem hj
  let U := e ⁻¹' Schoenflies.inside C
  let V := e ⁻¹' Schoenflies.outside C
  have hpre : e ⁻¹' C = f '' Icc 0 1 := by
    change e ⁻¹' ((fun x => e (f x)) '' Icc 0 1) = _
    rw [← image_image (f := f) (g := e), preimage_image_eq _ e.injective]
  have hU : IsConnected U := e.isConnected_preimage.mpr hs.isConnected_inside
  have hV : IsConnected V := e.isConnected_preimage.mpr hs.isConnected_outside
  have hUV : U ∪ V = (f '' Icc 0 1)ᶜ := by
    change (e ⁻¹' Schoenflies.inside C) ∪ (e ⁻¹' Schoenflies.outside C) = _
    rw [← preimage_union, Schoenflies.inside_union_outside, preimage_compl, hpre]
  have hd : Disjoint U V := Schoenflies.disjoint_inside_outside.preimage e
  have hfu : frontier U = f '' Icc 0 1 := by
    rw [← e.preimage_frontier, hs.frontier_inside, hpre]
  have hfv : frontier V = f '' Icc 0 1 := by
    rw [← e.preimage_frontier, hs.frontier_outside, hpre]
  have hcompact : IsCompact (closure U) := by
    rw [← e.preimage_closure, ← e.image_symm]
    exact hs.isBounded_inside.isCompact_closure.image e.symm.continuous
  refine ⟨U, V, hs.isOpen_inside.preimage e.continuous,
    hs.isOpen_outside.preimage e.continuous, hU, hV, hd, hUV, hfu, hfv, hcompact, ?_, ?_⟩
  · intro x hx
    have he := e.image_connectedComponentIn (s := (f '' Icc 0 1)ᶜ)
      (show x ∈ (f '' Icc 0 1)ᶜ from hUV ▸ Or.inl hx)
    have hcim : e '' (f '' Icc 0 1)ᶜ = Cᶜ := by
      rw [e.image_compl, image_image]
      rfl
    rw [hcim, hs.connectedComponentIn_eq_inside hx] at he
    apply e.injective.image_injective
    simpa [U, image_preimage_eq _ e.surjective] using he
  · intro x hx
    have he := e.image_connectedComponentIn (s := (f '' Icc 0 1)ᶜ)
      (show x ∈ (f '' Icc 0 1)ᶜ from hUV ▸ Or.inr hx)
    have hcim : e '' (f '' Icc 0 1)ᶜ = Cᶜ := by
      rw [e.image_compl, image_image]
      rfl
    rw [hcim, hs.connectedComponentIn_eq_outside hx] at he
    apply e.injective.image_injective
    simpa [V, image_preimage_eq _ e.surjective] using he

end RepulsiveCoulomb
