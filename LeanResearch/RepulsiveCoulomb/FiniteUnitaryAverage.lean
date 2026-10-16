import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite averages of genuine orthogonal representations. -/
noncomputable section
open scoped BigOperators
open InnerProductSpace
namespace RepulsiveCoulomb
variable {G E : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finiteUnitaryAverage (U : G →* (E →L[ℝ] E)) : E →L[ℝ] E :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g, U g

theorem finiteUnitaryAverage_apply (U : G →* (E →L[ℝ] E)) (x : E) :
    finiteUnitaryAverage U x = (Fintype.card G : ℝ)⁻¹ • ∑ g, U g x := by
  simp [finiteUnitaryAverage]

theorem finiteUnitaryAverage_invariant (U : G →* (E →L[ℝ] E)) (a : G) (x : E) :
    U a (finiteUnitaryAverage U x) = finiteUnitaryAverage U x := by
  rw [finiteUnitaryAverage_apply, map_smul, map_sum]
  congr 1
  have hm (g : G) : U a (U g x) = U (a * g) x := by
    rw [map_mul]
    rfl
  simp_rw [hm]
  exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)

theorem finiteUnitaryAverage_idempotent (U : G →* (E →L[ℝ] E)) (x : E) :
    finiteUnitaryAverage U (finiteUnitaryAverage U x) = finiteUnitaryAverage U x := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [finiteUnitaryAverage_apply]
  simp_rw [finiteUnitaryAverage_invariant]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

theorem finiteUnitary_inner_flip (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (g : G) (x y : E) :
    inner ℝ (U g x) y = inner ℝ x (U g⁻¹ y) := by
  have h := hU g x (U g⁻¹ y)
  have he : U g (U g⁻¹ y) = y := by
    change (U g * U g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  simpa only [he, pow_two] using h

theorem finiteUnitaryAverage_selfAdjoint (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x y : E) :
    inner ℝ (finiteUnitaryAverage U x) y = inner ℝ x (finiteUnitaryAverage U y) := by
  rw [finiteUnitaryAverage_apply, real_inner_smul_left, sum_inner,
    finiteUnitaryAverage_apply, real_inner_smul_right, inner_sum]
  congr 1
  simp_rw [finiteUnitary_inner_flip U hU]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)

theorem finiteUnitaryAverage_inner_eq_norm_sq (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    inner ℝ x (finiteUnitaryAverage U x) = ‖finiteUnitaryAverage U x‖ ^ 2 := by
  have h := finiteUnitaryAverage_selfAdjoint U hU x (finiteUnitaryAverage U x)
  rw [finiteUnitaryAverage_idempotent, real_inner_self_eq_norm_sq] at h
  exact h.symm

theorem finiteUnitaryAverage_orthogonal_error (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    inner ℝ (finiteUnitaryAverage U x) (x - finiteUnitaryAverage U x) = 0 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm,
    finiteUnitaryAverage_inner_eq_norm_sq U hU, sub_self]

theorem finiteUnitaryAverage_norm_decomposition (U : G →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    ‖x‖ ^ 2 = ‖finiteUnitaryAverage U x‖ ^ 2 + ‖x - finiteUnitaryAverage U x‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (finiteUnitaryAverage U x) (x - finiteUnitaryAverage U x)
    (finiteUnitaryAverage_orthogonal_error U hU x)
  have he : finiteUnitaryAverage U x + (x - finiteUnitaryAverage U x) = x := by abel
  simpa only [he, pow_two] using h

end RepulsiveCoulomb

