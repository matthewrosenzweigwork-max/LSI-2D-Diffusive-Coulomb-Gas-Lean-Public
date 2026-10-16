import LeanResearch.RepulsiveCoulomb.PointConeInverseChart

/-! A Euclidean chord in the right half-plane pulls back to an actual admissible
smooth path, giving the small-sector upper bound. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem standardCone_zero_segment_length (u v : ℂ) :
    pointConformalPathELength (standardConeExponents 0) standardConeLocations
      (fun t : ℝ ↦ u + t • (v - u)) 0 1 = ENNReal.ofReal ‖v - u‖ := by
  have hd (t : ℝ) : deriv (fun s : ℝ ↦ u + s • (v - u)) t = v - u := by
    simpa using (((hasDerivAt_id t).smul_const (v - u)).const_add u).deriv
  unfold pointConformalPathELength
  simp only [standardCone_density, Real.rpow_zero, ENNReal.ofReal_one, one_mul, hd]
  simp

theorem standardCone_chord_upper {α : ℝ} (hα : 0 ≤ α) {x z : ℂ}
    (hx : x ∈ pointConeSectorWindow α) (hz : z ∈ pointConeSectorWindow α)
    (hxr : 0 < (pointConeSectorMap α x).re) (hzr : 0 < (pointConeSectorMap α z).re) :
    pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z ≤
      ENNReal.ofReal ‖pointConeSectorMap α z - pointConeSectorMap α x‖ := by
  let u := pointConeSectorMap α x
  let v := pointConeSectorMap α z
  let η : ℝ → ℂ := fun t ↦ u + t • (v - u)
  have hη : ContDiff ℝ 1 η := by fun_prop
  have hmap : MapsTo η (Icc (0 : ℝ) 1) {w : ℂ | 0 < w.re} := by
    intro t ht
    change 0 < (u + t • (v - u)).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero]
    have h1 : 0 ≤ t * v.re := mul_nonneg ht.1 hzr.le
    have h2 : 0 ≤ (1 - t) * u.re := mul_nonneg (sub_nonneg.mpr ht.2) hxr.le
    by_cases hzero : t = 0
    · simpa [hzero] using hxr
    · have : 0 < t * v.re := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hzero)) hzr
      nlinarith
  let γ := pointConeSectorInverse α ∘ η
  have hγ : ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1) :=
    analyticOnNhd_comp_smooth_path (pointConeSectorInverse_analyticOnNhd hα) hη.contDiffOn hmap
  have h0 : γ 0 = x := by simpa [γ, η, u] using pointConeSectorInverse_left hα hx
  have h1 : γ 1 = z := by simpa [γ, η, v] using pointConeSectorInverse_left hα hz
  have hF : ∀ w ∈ {w : ℂ | 0 < w.re}, AnalyticAt ℂ (pointConeSectorInverse α) w ∧
      pointConformalDensity (standardConeExponents α) standardConeLocations (pointConeSectorInverse α w) *
        ‖deriv (pointConeSectorInverse α) w‖ =
          pointConformalDensity (standardConeExponents 0) standardConeLocations w := by
    intro w hw
    refine ⟨pointConeSectorInverse_analyticOnNhd hα w hw, ?_⟩
    rw [pointConeSectorInverse_density_deriv hα hw, standardCone_density, Real.rpow_zero]
  have hlen := pointConformalPath_transport (standardConeExponents 0) standardConeLocations
    (standardConeExponents α) standardConeLocations hF hη.contDiffOn hmap
  have hd := pointSmoothConformalEDist_le_path (standardConeExponents α) standardConeLocations
    hγ (by norm_num : (0 : ℝ) ≤ 1)
  rw [h0, h1, ← hlen] at hd
  exact hd.trans_eq (standardCone_zero_segment_length u v)

end RepulsiveCoulomb
