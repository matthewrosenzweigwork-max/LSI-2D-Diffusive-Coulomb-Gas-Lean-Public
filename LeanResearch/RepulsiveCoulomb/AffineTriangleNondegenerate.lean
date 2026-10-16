import LeanResearch.RepulsiveCoulomb.AffineTriangleRegularLevel
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! The two contour endpoints of a genuine affine triangle are distinct. -/
noncomputable section
open Set AffineMap
open scoped BigOperators
namespace RepulsiveCoulomb

theorem affineIndependent_incident_lineMaps_ne {p₀ p₁ p₂ : ℂ}
    (hp : AffineIndependent ℝ ![p₀, p₁, p₂]) {r s : ℝ} (hr : r ≠ 0) :
    lineMap p₀ p₁ r ≠ lineMap p₀ p₂ s := by
  intro he
  let w₁ : Fin 3 → ℝ := ![1 - r, r, 0]
  let w₂ : Fin 3 → ℝ := ![1 - s, 0, s]
  have hs : ∑ i : Fin 3, w₁ i = ∑ i : Fin 3, w₂ i := by
    simp [w₁, w₂, Fin.sum_univ_succ]
  have hv : (∑ i : Fin 3, w₁ i • (![p₀, p₁, p₂] i)) =
      ∑ i : Fin 3, w₂ i • (![p₀, p₁, p₂] i) := by
    simpa [w₁, w₂, Fin.sum_univ_succ, lineMap_apply_module, add_assoc] using he
  have hh := hp.eq_of_sum_eq_sum hs hv (1 : Fin 3) (Finset.mem_univ _)
  have hz : r = 0 := by simpa [w₁, w₂] using hh
  exact hr hz

theorem affineIndependent_cyclic_triple {p : Fin 3 → ℂ}
    (hp : AffineIndependent ℝ p) (i : Fin 3) :
    AffineIndependent ℝ ![p i, p (i + 1), p (i + 2)] := by
  have h := hp.comp_embedding (Equiv.addLeft i).toEmbedding
  convert h using 1
  funext j
  fin_cases j <;> simp [Function.comp_def]

theorem affine_triangle_regular_level_nondegenerate (f : ℂ →ᵃ[ℝ] ℝ) (p : Fin 3 → ℂ)
    (hp : AffineIndependent ℝ p) (t : ℝ) (ht : ∀ i, f (p i) ≠ t) :
    (convexHull ℝ ({p 0, p 1, p 2} : Set ℂ) ∩ f ⁻¹' {t} = ∅) ∨
      ∃ q r : ℂ, q ≠ r ∧
        convexHull ℝ ({p 0, p 1, p 2} : Set ℂ) ∩ f ⁻¹' {t} = segment ℝ q r := by
  rcases affine_triangle_regular_level f p hp.injective t ht with h | ⟨i, h1, h2, hs⟩
  · exact Or.inl h
  · refine Or.inr ⟨_, _, ?_, hs⟩
    apply affineIndependent_incident_lineMaps_ne (affineIndependent_cyclic_triple hp i)
    exact (levelEdgeParameter_mem_Ioo h1).1.ne'

end RepulsiveCoulomb
