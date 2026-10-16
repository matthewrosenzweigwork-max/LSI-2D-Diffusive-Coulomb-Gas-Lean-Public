module

public import LeanResearch.RepulsiveCoulomb.CoulombDensityLocal

@[expose] public section

/-! Compact density upper bound retaining one actual collision exponent.
Other collisions, including intersections, require no separation. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombDensity_le_collision_power {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (p : Fin N × Fin N)
    (hp : p ∈ coulombPairs N) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K,
      coulombDensity N β z ≤ C * ‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) := by
  classical
  let F : CoulombConfig N → ℝ := fun z =>
    (∫ w : CoulombConfig N, coulombWeight β w)⁻¹ *
      Real.exp (-β * ‖z‖ ^ 2 / 2) *
        ∏ q ∈ (coulombPairs N).erase p, ‖z q.1 - z q.2‖ ^ (β / (N : ℝ))
  have hF : Continuous F := by
    apply Continuous.mul
    · fun_prop
    · apply continuous_finsetProd
      intro q _
      exact (Real.continuous_rpow_const (div_nonneg hβ (Nat.cast_nonneg N))).comp
        (((coulombCoordinate q.1).continuous.sub (coulombCoordinate q.2).continuous).norm)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro z hz
  have he : coulombDensity N β z = F z * ‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) := by
    dsimp [coulombDensity, coulombWeight, F]
    rw [← Finset.prod_erase_mul (coulombPairs N)
      (fun q => ‖z q.1 - z q.2‖ ^ (β / (N : ℝ))) hp]
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
  have hb := hC z hz
  rw [Real.norm_eq_abs] at hb
  linarith [le_abs_self (F z), le_abs_self C]

end RepulsiveCoulomb

