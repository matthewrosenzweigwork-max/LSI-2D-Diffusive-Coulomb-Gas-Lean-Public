import LeanResearch.RepulsiveCoulomb.TranspositionKernel
import LeanResearch.RepulsiveCoulomb.FiniteBochnerGap

/-! The sharp finite-dimensional random-transposition gap, with its Bochner input proved. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem transpositionLaplacian_isPositive
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) :
    (transpositionLaplacian U).toLinearMap.IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact transpositionLaplacian_selfAdjoint U hU x y
  · intro x
    simpa only [RCLike.re_to_real, ContinuousLinearMap.coe_coe, real_inner_comm]
      using transpositionLaplacian_positive U hU x

theorem transposition_error_orthogonal_kernel
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    x - finiteUnitaryAverage U x ∈ (transpositionLaplacian U).toLinearMap.kerᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hy' : transpositionLaplacian U y = 0 := hy
  have ha := transpositionLaplacian_kernel_average U hU y hy'
  rw [inner_sub_right, ← finiteUnitaryAverage_selfAdjoint U hU y x, ha, sub_self]

theorem finite_transposition_gap [FiniteDimensional ℝ E] (hN : 2 ≤ N)
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    (N : ℝ) * ‖x - finiteUnitaryAverage U x‖ ^ 2 ≤ inner ℝ x (transpositionLaplacian U x) := by
  have hc : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h := finiteDimensional_gap_of_bochner (transpositionLaplacian U).toLinearMap
    (transpositionLaplacian_isPositive U hU) hc (transpositionLaplacian_bochner hN U hU)
    (x - finiteUnitaryAverage U x) (transposition_error_orthogonal_kernel U hU x)
  change (N : ℝ) * ‖x - finiteUnitaryAverage U x‖ ^ 2 ≤
    inner ℝ (x - finiteUnitaryAverage U x) (transpositionLaplacian U (x - finiteUnitaryAverage U x)) at h
  rw [map_sub, transpositionLaplacian_average, sub_zero, inner_sub_left] at h
  have hz : inner ℝ (finiteUnitaryAverage U x) (transpositionLaplacian U x) = 0 := by
    rw [← transpositionLaplacian_selfAdjoint U hU, transpositionLaplacian_average, inner_zero_left]
  simpa only [hz, sub_zero] using h

theorem finite_transposition_gap_norm [FiniteDimensional ℝ E] (hN : 2 ≤ N)
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    2 * (N : ℝ) * ‖x - finiteUnitaryAverage U x‖ ^ 2 ≤
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2, ‖x - U (edgeTransposition s) x‖ ^ 2 := by
  have h := finite_transposition_gap hN U hU x
  have he : 2 * inner ℝ x (transpositionLaplacian U x) =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2, ‖x - U (edgeTransposition s) x‖ ^ 2 := by
    rw [transpositionLaplacian_apply, inner_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => unitaryDifference_energy U hU _ x
  nlinarith

end RepulsiveCoulomb
