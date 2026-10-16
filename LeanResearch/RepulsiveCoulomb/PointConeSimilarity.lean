import LeanResearch.RepulsiveCoulomb.PointConformalRay
import LeanResearch.RepulsiveCoulomb.PointConeSectorMap

/-! Exact rotations and homotheties of the model cone's constructed metric. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointConformalEDist_le_of_smooth_path_bound {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (x z : ℂ) {D K : ℝ≥0∞} (hK0 : K ≠ 0) (hKt : K ≠ ∞)
    (h : ∀ γ : ℝ → ℂ, γ 0 = x → γ 1 = z → ContDiff ℝ 1 γ →
      D ≤ K * pointConformalPathELength a y γ 0 1) :
    D ≤ K * pointSmoothConformalEDist a y x z := by
  apply (ENNReal.div_le_iff' hK0 hKt).mp
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y hr
  exact ((ENNReal.div_le_iff' hK0 hKt).mpr (h γ h0 h1 hγ)).trans_lt hlen

theorem standardCone_path_mul {α : ℝ} {c : ℂ} (hc : c ≠ 0)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (s t : ℝ) :
    pointConformalPathELength (standardConeExponents α) standardConeLocations (fun u ↦ c * γ u) s t =
      ENNReal.ofReal (‖c‖ ^ (α + 1)) *
        pointConformalPathELength (standardConeExponents α) standardConeLocations γ s t := by
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hd (u : ℝ) : deriv (fun v ↦ c * γ v) u = c * deriv γ u :=
    ((hγ.differentiable one_ne_zero u).hasDerivAt.const_mul c).deriv
  unfold pointConformalPathELength
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  rw [hd, standardCone_density, standardCone_density, norm_mul, norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Real.rpow_add_one hn]
  simp only [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),
    ENNReal.ofReal_mul (norm_nonneg _)]
  ring

theorem standardCone_dist_mul_le {α : ℝ} {c : ℂ} (hc : c ≠ 0) (x z : ℂ) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations (c * x) (c * z) ≤
      ENNReal.ofReal (‖c‖ ^ (α + 1)) *
        pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z := by
  have hK : 0 < ENNReal.ofReal (‖c‖ ^ (α + 1)) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hc) _)
  apply pointConformalEDist_le_of_smooth_path_bound _ _ x z hK.ne' ENNReal.ofReal_ne_top
  intro γ h0 h1 hγ
  have hγ' : ContDiff ℝ 1 (fun u ↦ c * γ u) := contDiff_const.mul hγ
  have hd := pointSmoothConformalEDist_le_path (standardConeExponents α) standardConeLocations
    hγ'.contDiffOn (by norm_num : (0 : ℝ) ≤ 1)
  rw [h0, h1, standardCone_path_mul hc hγ] at hd
  exact hd

theorem standardCone_dist_mul {α : ℝ} {c : ℂ} (hc : c ≠ 0) (x z : ℂ) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations (c * x) (c * z) =
      ENNReal.ofReal (‖c‖ ^ (α + 1)) *
        pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z := by
  apply le_antisymm (standardCone_dist_mul_le hc x z)
  have hback := standardCone_dist_mul_le (α := α) (inv_ne_zero hc) (c * x) (c * z)
  simp only [inv_mul_cancel_left₀ hc, norm_inv, Real.inv_rpow (norm_nonneg c),
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hc) _)] at hback
  have h := mul_le_mul' (le_rfl : ENNReal.ofReal (‖c‖ ^ (α + 1)) ≤ ENNReal.ofReal (‖c‖ ^ (α + 1))) hback
  rw [← mul_assoc, ENNReal.mul_inv_cancel
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hc) _)).ne'
    ENNReal.ofReal_ne_top, one_mul] at h
  exact h

theorem standardCone_rotation_invariant {α : ℝ} {c : ℂ} (hc : ‖c‖ = 1) (x z : ℂ) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations (c * x) (c * z) =
      pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  rw [standardCone_dist_mul hc0, hc, Real.one_rpow, ENNReal.ofReal_one, one_mul]

end RepulsiveCoulomb
