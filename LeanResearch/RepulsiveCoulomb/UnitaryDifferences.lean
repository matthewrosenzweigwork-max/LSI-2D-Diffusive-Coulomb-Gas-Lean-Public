module

public import LeanResearch.RepulsiveCoulomb.FiniteUnitaryAverage

@[expose] public section

/-! Positive differences of orthogonal involutions and commuting cross terms. -/
noncomputable section
open InnerProductSpace
namespace RepulsiveCoulomb
variable {G E : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitaryDifference (U : G →* (E →L[ℝ] E)) (g : G) : E →L[ℝ] E := 1 - U g

theorem unitaryDifference_apply (U : G →* (E →L[ℝ] E)) (g : G) (x : E) :
    unitaryDifference U g x = x - U g x := by simp [unitaryDifference]

theorem unitaryDifference_energy (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (g : G) (x : E) :
    2 * inner ℝ x (unitaryDifference U g x) = ‖unitaryDifference U g x‖ ^ 2 := by
  have hn := hU g x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hn
  rw [unitaryDifference_apply, inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real]
  linarith

theorem unitaryDifference_positive (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (g : G) (x : E) :
    0 ≤ inner ℝ x (unitaryDifference U g x) := by
  have h := unitaryDifference_energy U hU g x
  nlinarith [sq_nonneg ‖unitaryDifference U g x‖]

theorem unitaryDifference_selfAdjoint (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (g : G) (hg : g⁻¹ = g) (x y : E) :
    inner ℝ (unitaryDifference U g x) y = inner ℝ x (unitaryDifference U g y) := by
  simp only [unitaryDifference_apply, inner_sub_left, inner_sub_right, finiteUnitary_inner_flip U hU, hg]

theorem unitaryDifference_inner_product (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (g : G) (hg : g⁻¹ = g) (x y : E) :
    inner ℝ (unitaryDifference U g x) (unitaryDifference U g y) =
      2 * inner ℝ x (unitaryDifference U g y) := by
  simp only [unitaryDifference_apply, inner_sub_left, inner_sub_right]
  rw [hU, finiteUnitary_inner_flip U hU, hg]
  ring

theorem unitaryDifference_commute (U : G →* (E →L[ℝ] E)) (g h : G) (hgh : g * h = h * g) (x : E) :
    unitaryDifference U g (unitaryDifference U h x) = unitaryDifference U h (unitaryDifference U g x) := by
  have hu : U g (U h x) = U h (U g x) := by
    change (U g * U h) x = (U h * U g) x
    rw [← map_mul, ← map_mul, hgh]
  simp only [unitaryDifference_apply, map_sub]
  rw [hu]
  abel

theorem unitaryDifference_disjoint_cross_nonneg (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y)
    (g h : G) (hg : g⁻¹ = g) (hh : h⁻¹ = h) (hgh : g * h = h * g) (x : E) :
    0 ≤ inner ℝ (unitaryDifference U g x) (unitaryDifference U h x) := by
  have hp := unitaryDifference_positive U hU g (unitaryDifference U h x)
  rw [unitaryDifference_commute U g h hgh] at hp
  rw [unitaryDifference_inner_product U hU h hh] at hp
  rw [← unitaryDifference_commute U g h hgh,
    ← unitaryDifference_selfAdjoint U hU g hg] at hp
  linarith

end RepulsiveCoulomb
