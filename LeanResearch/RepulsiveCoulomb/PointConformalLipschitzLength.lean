import LeanResearch.RepulsiveCoulomb.PointConformalDistanceSlope
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Every Euclidean Lipschitz curve has physical weighted length at least the
actual smooth-path metric distance. This holds for arbitrary finite nonnegative
point configurations and includes curves passing through the punctures. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem rawPointBallFactor_segment_le_bounded {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {R : ℝ} {p z : ℂ}
    (hp : ‖p‖ ≤ R) (hz : ‖z‖ ≤ R) :
    rawPointBallFactor a y p ‖z - p‖ ≤ rawPointBallFactor a y 0 (3 * R) := by
  unfold rawPointBallFactor
  apply Finset.prod_le_prod₀
    (fun j _ ↦ Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _)
  intro j hj
  apply Real.rpow_le_rpow (add_nonneg (norm_nonneg _) (norm_nonneg _)) _ (ha j)
  simp only [zero_sub, norm_neg]
  linarith [norm_sub_le z p, norm_sub_le p (y j)]

theorem pointConformalDistance_lipschitzOn_ball {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) (R : ℝ) :
    LipschitzOnWith ⟨Real.sqrt (rawPointBallFactor a y 0 (3 * R)), Real.sqrt_nonneg _⟩
      (fun p ↦ (pointSmoothConformalEDist a y p c).toReal) (closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp z hz
  have hp' : ‖p‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hp
  have hz' : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hf := Real.sqrt_le_sqrt (rawPointBallFactor_segment_le_bounded ha y hp' hz')
  change |(pointSmoothConformalEDist a y p c).toReal -
      (pointSmoothConformalEDist a y z c).toReal| ≤ _
  calc
    _ ≤ (pointSmoothConformalEDist a y p z).toReal := pointConformalDistance_abs_sub_le ha y p z c
    _ ≤ Real.sqrt (rawPointBallFactor a y p ‖z - p‖) * ‖z - p‖ :=
      pointConformalDistance_segment_upper ha y p z
    _ ≤ Real.sqrt (rawPointBallFactor a y 0 (3 * R)) * ‖z - p‖ :=
      mul_le_mul_of_nonneg_right hf (norm_nonneg _)
    _ = _ := by rw [dist_eq_norm']; rfl

theorem pointConformalDistance_comp_lipschitzOn {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) {γ : ℝ → ℂ}
    {s t : ℝ} {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) :
    ∃ L : NNReal, LipschitzOnWith L
      (fun u ↦ (pointSmoothConformalEDist a y (γ u) c).toReal) (Icc s t) := by
  have hcompact := isCompact_Icc.image_of_continuousOn hγ.continuousOn
  obtain ⟨R, hR⟩ := hcompact.isBounded.exists_norm_le
  have hmap : MapsTo γ (Icc s t) (closedBall 0 R) := by
    intro u hu
    simpa only [mem_closedBall, dist_zero_right] using hR (γ u) ⟨u, hu, rfl⟩
  exact ⟨_, (pointConformalDistance_lipschitzOn_ball ha y c R).comp hγ hmap⟩

theorem lipschitzOn_Icc_ae_differentiableAt_complex {γ : ℝ → ℂ} {s t : ℝ}
    {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) :
    ∀ᵐ u ∂volume.restrict (Icc s t), DifferentiableAt ℝ γ u := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  have hdiff : ∀ᵐ u : ℝ, u ∈ Icc s t → DifferentiableWithinAt ℝ γ (Icc s t) u :=
    hγ.ae_differentiableWithinAt_of_mem
  filter_upwards [ae_restrict_of_ae hdiff, self_mem_ae_restrict measurableSet_Ioo] with u hu huI
  exact (hu ⟨huI.1.le, huI.2.le⟩).differentiableAt (Icc_mem_nhds huI.1 huI.2)

/-- The required lower bound for every Lipschitz parametrization; unlike an
arbitrary BV derivative integral, its physical integral is genuine arc length. -/
theorem pointSmoothConformalEDist_le_lipschitz_path {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {s t : ℝ}
    {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) (hst : s ≤ t) :
    pointSmoothConformalEDist a y (γ s) (γ t) ≤ pointConformalPathELength a y γ s t := by
  let f : ℝ → ℝ := fun u ↦ (pointSmoothConformalEDist a y (γ u) (γ s)).toReal
  obtain ⟨L, hf⟩ := pointConformalDistance_comp_lipschitzOn ha y (γ s) hγ
  change LipschitzOnWith L f (Icc s t) at hf
  have hac : AbsolutelyContinuousOnInterval f s t := by
    rw [← uIcc_of_le hst] at hf
    exact hf.absolutelyContinuousOnInterval
  have hint : (∫ u in Icc s t, deriv f u) = f t - f s := by
    have h := hac.integral_deriv_eq_sub
    rw [intervalIntegral.integral_of_le hst, restrict_Ioc_eq_restrict_Icc] at h
    exact h
  have hnorm : ENNReal.ofReal ‖∫ u in Icc s t, deriv f u‖ ≤
      ∫⁻ u in Icc s t, ENNReal.ofReal ‖deriv f u‖ := by
    simpa only [ofReal_norm] using
      (enorm_integral_le_lintegral_enorm (μ := volume.restrict (Icc s t)) (deriv f))
  have heq : ENNReal.ofReal ‖∫ u in Icc s t, deriv f u‖ =
      pointSmoothConformalEDist a y (γ s) (γ t) := by
    rw [hint]
    simp only [f, pointSmoothConformalEDist_self, ENNReal.toReal_zero, sub_zero,
      Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (pointSmoothConformalEDist_lt_top ha y (γ t) (γ s)).ne]
    exact pointSmoothConformalEDist_comm a y (γ t) (γ s)
  rw [heq] at hnorm
  apply hnorm.trans
  unfold pointConformalPathELength
  apply lintegral_mono_ae
  filter_upwards [lipschitzOn_Icc_ae_differentiableAt_complex hγ] with u hu
  rw [← ENNReal.ofReal_mul (pointConformalDensity_nonneg a y _)]
  exact ENNReal.ofReal_le_ofReal (pointConformalDistance_deriv_norm_le ha y (γ s) hu)

end RepulsiveCoulomb
