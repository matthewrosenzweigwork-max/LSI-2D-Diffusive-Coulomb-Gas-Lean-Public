module

public import LeanResearch.RepulsiveCoulomb.PointConePhase

@[expose] public section

/-! Sharp small-sector lower bound from rotated C1 supporting functions. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

theorem cone_scaled_angle_window {N θ : ℝ} (hN : 1 ≤ N) (h : |N * θ| < Real.pi) :
    θ ∈ Ioc (-Real.pi) Real.pi := by
  have hn : 0 ≤ N := by linarith
  rw [abs_mul, abs_of_nonneg hn] at h
  have hθ : |θ| < Real.pi := (le_mul_of_one_le_left (abs_nonneg θ) hN).trans_lt h
  exact ⟨(abs_lt.mp hθ).1, (abs_lt.mp hθ).2.le⟩

theorem cone_projection_rotation_bounds {α β a : ℝ} (hα : 0 ≤ α)
    (hβ : |β| ≤ Real.pi / 2) (ha : |(α + 1) * a| < Real.pi / 2) :
    (-β / (α + 1)) ∈ Ioc (-Real.pi) Real.pi ∧
      (-β / (α + 1) + a) ∈ Ioc (-Real.pi) Real.pi ∧
      |(α + 1) * (-β / (α + 1) + a)| < Real.pi := by
  have hN : α + 1 ≠ 0 := by linarith
  have he : (α + 1) * (-β / (α + 1)) = -β := by field_simp
  have he' : (α + 1) * (-β / (α + 1) + a) = (α + 1) * a - β := by
    rw [mul_add, he]
    ring
  have hsmall : |(α + 1) * (-β / (α + 1) + a)| < Real.pi := by
    rw [he']
    exact (abs_sub _ _).trans_lt (by linarith)
  refine ⟨cone_scaled_angle_window (N := α + 1) (by linarith) ?_,
    cone_scaled_angle_window (N := α + 1) (by linarith) hsmall, hsmall⟩
  rw [he, abs_neg]
  linarith [Real.pi_pos]

theorem coneAngularBarrier_rotated_projection {α β : ℝ} (hα : 0 ≤ α)
    (hβ : |β| ≤ Real.pi / 2) {z : ℂ} (hz : z ≠ 0)
    (ha : |(α + 1) * Complex.arg z| < Real.pi / 2) :
    coneAngularBarrier α (conePhase (-β / (α + 1)) * z) =
      (conePhase (-β) * pointConeSectorMap α z).re := by
  obtain ⟨hθ, hsum, hsmall⟩ := cone_projection_rotation_bounds hα hβ ha
  have harg := conePhase_arg_mul hθ hz hsum
  rw [coneAngularBarrier_eq_sector_re (by rw [harg]; exact hsmall.le),
    pointConeSectorMap_phase hθ hz hsum]
  have he : (-β / (α + 1)) * (α + 1) = -β := div_mul_cancel₀ _ (by linarith)
  rw [he]

theorem standardCone_chord_lower {α : ℝ} (hα : 0 < α) {x z : ℂ}
    (hx : x ≠ 0) (hz : z ≠ 0)
    (hxa : |(α + 1) * Complex.arg x| < Real.pi / 2)
    (hza : |(α + 1) * Complex.arg z| < Real.pi / 2) :
    ENNReal.ofReal ‖pointConeSectorMap α z - pointConeSectorMap α x‖ ≤
      pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z := by
  obtain ⟨β, hβ, hproj⟩ := exists_cone_halfplane_projection
    (pointConeSectorMap α z - pointConeSectorMap α x)
  have h := coneAngularBarrier_metric_lower hα
    (conePhase (-β / (α + 1)) * x) (conePhase (-β / (α + 1)) * z)
  rw [standardCone_rotation_invariant (conePhase_norm _),
    coneAngularBarrier_rotated_projection hα.le hβ hz hza,
    coneAngularBarrier_rotated_projection hα.le hβ hx hxa] at h
  rw [← Complex.sub_re, ← mul_sub, hproj] at h
  exact h

end RepulsiveCoulomb
