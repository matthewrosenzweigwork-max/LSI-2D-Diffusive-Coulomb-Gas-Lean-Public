module

public import LeanResearch.RepulsiveCoulomb.AffineTriangleLevel
public import LeanResearch.RepulsiveCoulomb.TriangleSignAlternative

@[expose] public section

/-! Every nonvertex affine triangular level is empty or exactly the segment
between two actual incident-edge crossing points. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem triple_cyclic_set (p : Fin 3 → ℂ) (i : Fin 3) :
    ({p 0, p 1, p 2} : Set ℂ) = {p i, p (i + 1), p (i + 2)} := by
  fin_cases i <;> ext z <;> norm_num <;> tauto

theorem affine_triangle_level_empty_of_below (f : ℂ →ᵃ[ℝ] ℝ) (p : Fin 3 → ℂ) (t : ℝ)
    (h : ∀ i, f (p i) < t) :
    convexHull ℝ ({p 0, p 1, p 2} : Set ℂ) ∩ f ⁻¹' {t} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hs : ({p 0, p 1, p 2} : Set ℂ) ⊆ f ⁻¹' Iio t := by
    intro x hx
    rcases hx with rfl | rfl | rfl <;> exact h _
  have hh := convexHull_min hs ((convex_Iio t).affine_preimage f) hz.1
  change f z < t at hh
  have he : f z = t := hz.2
  linarith

theorem affine_triangle_level_empty_of_above (f : ℂ →ᵃ[ℝ] ℝ) (p : Fin 3 → ℂ) (t : ℝ)
    (h : ∀ i, t < f (p i)) :
    convexHull ℝ ({p 0, p 1, p 2} : Set ℂ) ∩ f ⁻¹' {t} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hs : ({p 0, p 1, p 2} : Set ℂ) ⊆ f ⁻¹' Ioi t := by
    intro x hx
    rcases hx with rfl | rfl | rfl <;> exact h _
  have hh := convexHull_min hs ((convex_Ioi t).affine_preimage f) hz.1
  change t < f z at hh
  have he : f z = t := hz.2
  linarith

theorem affine_triangle_regular_level (f : ℂ →ᵃ[ℝ] ℝ) (p : Fin 3 → ℂ)
    (hp : Function.Injective p) (t : ℝ) (ht : ∀ i, f (p i) ≠ t) :
    (convexHull ℝ ({p 0, p 1, p 2} : Set ℂ) ∩ f ⁻¹' {t} = ∅) ∨
      ∃ i : Fin 3,
        ((f (p i) < t ∧ t < f (p (i + 1))) ∨ (f (p (i + 1)) < t ∧ t < f (p i))) ∧
        ((f (p i) < t ∧ t < f (p (i + 2))) ∨ (f (p (i + 2)) < t ∧ t < f (p i))) ∧
        convexHull ℝ ({p 0, p 1, p 2} : Set ℂ) ∩ f ⁻¹' {t} =
          segment ℝ (affineLevelEdgePoint (p i) (p (i + 1)) (f (p i)) (f (p (i + 1))) t)
            (affineLevelEdgePoint (p i) (p (i + 2)) (f (p i)) (f (p (i + 2))) t) := by
  rcases triangle_regular_sign_alternative (fun i => f (p i)) t ht with h | h | ⟨i, h1, h2⟩
  · exact Or.inl (affine_triangle_level_empty_of_below f p t h)
  · exact Or.inl (affine_triangle_level_empty_of_above f p t h)
  · refine Or.inr ⟨i, h1, h2, ?_⟩
    rw [triple_cyclic_set p i]
    apply affine_triangle_slice_two_incident_edges f (p i) (p (i + 1)) (p (i + 2))
      (hp.ne (by fin_cases i <;> decide)) (hp.ne (by fin_cases i <;> decide))
      (hp.ne (by fin_cases i <;> decide)) h1 h2

end RepulsiveCoulomb
