import LeanResearch.RepulsiveCoulomb.CoulombCollisionDensity

/-! Global Gaussian domination retaining one collision power. Constants may
depend on N and beta; no separation or collision exclusion is imposed. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombDensity_le_gaussian_collision_power {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (p : Fin N × Fin N) (hp : p ∈ coulombPairs N) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : CoulombConfig N,
      coulombDensity N β z ≤
        C * Real.exp (-(β / 4) * ‖z‖ ^ 2) * ‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) := by
  classical
  let A := ∑ _q ∈ (coulombPairs N).erase p, 2 * (β / (N : ℝ))
  let Z := ∫ w : CoulombConfig N, coulombWeight β w
  refine ⟨Z⁻¹ * Real.exp (A ^ 2 / β), mul_pos (inv_pos.mpr (coulombWeight_integral_pos hβ))
    (Real.exp_pos _), ?_⟩
  intro z
  have hprod : (∏ q ∈ (coulombPairs N).erase p, ‖z q.1 - z q.2‖ ^ (β / (N : ℝ))) ≤
      Real.exp (‖z‖ * A) := by
    calc
      _ ≤ ∏ _q ∈ (coulombPairs N).erase p, Real.exp (2 * ‖z‖ * (β / (N : ℝ))) :=
        Finset.prod_le_prod₀ (fun q _ => Real.rpow_nonneg (norm_nonneg _) _)
          (fun q _ => coulomb_pair_rpow_le_exp hβ.le z q.1 q.2)
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        simp only [A, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
  have hg := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-β * ‖z‖ ^ 2 / 2)).le
  rw [← Real.exp_add] at hg
  have hb := hg.trans (gaussian_linear_le β A ‖z‖ hβ)
  have he : coulombDensity N β z =
      Z⁻¹ * (Real.exp (-β * ‖z‖ ^ 2 / 2) *
        ∏ q ∈ (coulombPairs N).erase p, ‖z q.1 - z q.2‖ ^ (β / (N : ℝ))) *
          ‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) := by
    dsimp [coulombDensity, coulombWeight, Z]
    rw [← Finset.prod_erase_mul (coulombPairs N)
      (fun q => ‖z q.1 - z q.2‖ ^ (β / (N : ℝ))) hp]
    ring
  rw [he]
  have hZ : 0 ≤ Z⁻¹ := (inv_pos.mpr (coulombWeight_integral_pos hβ)).le
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hZ)
    (Real.rpow_nonneg (norm_nonneg (z p.1 - z p.2)) (β / (N : ℝ)))
  convert h using 1 <;> ring

end RepulsiveCoulomb

