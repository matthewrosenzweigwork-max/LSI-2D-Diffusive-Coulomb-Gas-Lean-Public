module

public import LeanResearch.RepulsiveCoulomb.PointConeChordLower

@[expose] public section

/-! Exact chord distance in a centered narrow sector, and then for any angular
separation smaller than pi after development. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointConeSectorMap_re_pos {α : ℝ} (hα : 0 ≤ α) {z : ℂ} (hz : z ≠ 0)
    (ha : |(α + 1) * Complex.arg z| < Real.pi / 2) :
    0 < (pointConeSectorMap α z).re := by
  have hpi : |(α + 1) * Complex.arg z| ≤ Real.pi := by linarith [Real.pi_pos]
  rw [← coneAngularBarrier_eq_sector_re hpi]
  unfold coneAngularBarrier coneClippedCos
  have ht : (α + 1) * Complex.arg z ∈ Icc (-Real.pi) Real.pi := abs_le.mp hpi
  rw [piecewise_eq_of_mem _ _ _ ht]
  exact mul_pos (div_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _) (by linarith))
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp ha))

theorem standardCone_centered_chord_distance {α : ℝ} (hα : 0 < α) {x z : ℂ}
    (hx : x ≠ 0) (hz : z ≠ 0)
    (hxa : |(α + 1) * Complex.arg x| < Real.pi / 2)
    (hza : |(α + 1) * Complex.arg z| < Real.pi / 2) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z =
      ENNReal.ofReal ‖pointConeSectorMap α z - pointConeSectorMap α x‖ := by
  have hxw : x ∈ pointConeSectorWindow α := by
    obtain ⟨h1, h2⟩ := abs_lt.mp hxa
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hzw : z ∈ pointConeSectorWindow α := by
    obtain ⟨h1, h2⟩ := abs_lt.mp hza
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact le_antisymm
    (standardCone_chord_upper hα.le hxw hzw (pointConeSectorMap_re_pos hα.le hx hxa)
      (pointConeSectorMap_re_pos hα.le hz hza))
    (standardCone_chord_lower hα hx hz hxa hza)

theorem standardCone_small_angle_nonzero {α : ℝ} (hα : 0 < α) {x z : ℂ}
    (hx : x ≠ 0) (hz : z ≠ 0) (hxa : Complex.arg x = 0)
    (hza : |(α + 1) * Complex.arg z| < Real.pi) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z =
      ENNReal.ofReal ‖pointConeSectorMap α z - pointConeSectorMap α x‖ := by
  let θ := -Complex.arg z / 2
  have hθs : |(α + 1) * θ| < Real.pi / 2 := by
    have he : (α + 1) * θ = -((α + 1) * Complex.arg z) / 2 := by dsimp [θ]; ring
    rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hsum : θ + Complex.arg z = -θ := by dsimp [θ]; ring
  have hsumS : |(α + 1) * (θ + Complex.arg z)| < Real.pi / 2 := by
    rw [hsum, mul_neg, abs_neg]
    exact hθs
  have hθ : θ ∈ Ioc (-Real.pi) Real.pi :=
    cone_scaled_angle_window (N := α + 1) (by linarith) (by linarith [Real.pi_pos])
  have hsz : θ + Complex.arg z ∈ Ioc (-Real.pi) Real.pi :=
    cone_scaled_angle_window (N := α + 1) (by linarith) (by linarith [Real.pi_pos])
  have hsx : θ + Complex.arg x ∈ Ioc (-Real.pi) Real.pi := by simpa [hxa] using hθ
  have hc : conePhase θ ≠ 0 := Complex.exp_ne_zero _
  have hargx := conePhase_arg_mul hθ hx hsx
  have hargz := conePhase_arg_mul hθ hz hsz
  have hx' : |(α + 1) * Complex.arg (conePhase θ * x)| < Real.pi / 2 := by
    rw [hargx, hxa, add_zero]
    exact hθs
  have hz' : |(α + 1) * Complex.arg (conePhase θ * z)| < Real.pi / 2 := by
    rw [hargz]
    exact hsumS
  have h := standardCone_centered_chord_distance hα (mul_ne_zero hc hx) (mul_ne_zero hc hz) hx' hz'
  rw [standardCone_rotation_invariant (conePhase_norm θ), pointConeSectorMap_phase hθ hz hsz,
    pointConeSectorMap_phase hθ hx hsx, ← mul_sub, norm_mul, conePhase_norm, one_mul] at h
  exact h

theorem pointConeSectorMap_zero {α : ℝ} (hα : 0 ≤ α) : pointConeSectorMap α 0 = 0 := by
  have hn : ((α + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show α + 1 ≠ 0 by linarith)
  unfold pointConeSectorMap
  rw [Complex.zero_cpow hn, zero_div]

theorem standardCone_distance_small_angle {α : ℝ} (hα : 0 < α) {x z : ℂ}
    (hxa : Complex.arg x = 0) (hza : |(α + 1) * Complex.arg z| < Real.pi) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z =
      ENNReal.ofReal ‖pointConeSectorMap α z - pointConeSectorMap α x‖ := by
  by_cases hx : x = 0
  · subst x
    rw [pointConeSectorMap_zero hα.le, sub_zero, standardCone_distance_from_apex hα,
      pointConeSectorMap_norm hα.le]
  · by_cases hz : z = 0
    · subst z
      rw [pointConeSectorMap_zero hα.le, zero_sub, norm_neg,
        pointSmoothConformalEDist_comm (standardConeExponents α) standardConeLocations x 0,
        standardCone_distance_from_apex hα, pointConeSectorMap_norm hα.le]
    · exact standardCone_small_angle_nonzero hα hx hz hxa hza

end RepulsiveCoulomb
