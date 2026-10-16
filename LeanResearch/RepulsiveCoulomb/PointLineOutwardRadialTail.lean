import LeanResearch.RepulsiveCoulomb.AffineLineTailTransport
import LeanResearch.RepulsiveCoulomb.PointMetricLineEscapeBounds
import LeanResearch.RepulsiveCoulomb.ContinuousLastLevelCrossing
import Mathlib.Tactic

/-! Apply the original-time finite tail theorem directly to a rescaled chunk of
 the actual complete line. This proves regularity, positive radial component,
 and radial tangency without passing any tangent through the subsequence. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem pointMetricLine_outward_tail_at
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ) (hc : Continuous c)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {A s t : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hstart : ‖c s‖ = A) (hout : ∀ u, s < u → A < ‖c u‖) (hst : s < t) :
    DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
      0 < physicalRadialProjection (c t) (deriv c t) ∧
      ‖deriv c t / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ)‖ ≤
        2 * tailSineEnvelope A (pointExteriorHalfMass a) (pointExteriorMoment a y) ‖c t‖ := by
  let l := s - 1
  let k := t - s + 2
  have hk : 0 < k := by dsimp [k]; linarith
  let ξ := (s - l) / k
  let η := (t - l) / k
  let u := (η + 1) / 2
  let γ : ℝ → ℂ := fun v => c (l + k * v)
  have hξeq : l + k * ξ = s := by dsimp [ξ]; field_simp [ne_of_gt hk] <;> ring
  have hηeq : l + k * η = t := by dsimp [η]; field_simp [ne_of_gt hk] <;> ring
  have hξpos : 0 < ξ := by apply div_pos _ hk; dsimp [l]; linarith
  have hξη : ξ < η := (div_lt_div_iff_of_pos_right hk).mpr (by linarith)
  have hη1 : η < 1 := by
    apply (div_lt_iff₀ hk).mpr
    dsimp [l, k]
    linarith
  have hηu : η < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hγc : Continuous γ := hc.comp (by fun_prop)
  have hγgeo := pointMetricLine_affine_segment_identity y c hd l hk
  have hγstart : ‖γ ξ‖ = A := by simpa only [γ, hξeq] using hstart
  have hγout : ∀ v ∈ Ioc ξ u, A < ‖γ v‖ := by
    intro v hv
    apply hout
    rw [← hξeq]
    linarith [mul_lt_mul_of_pos_left hv.1 hk]
  obtain ⟨θ, φ, hθ, hφ, hlift, hcos, hsine, _, _⟩ :=
    exists_pointConformal_actual_outward_tail_sine_bound ha y γ hγc k hk hγgeo
      hA hyA hB hD hξpos (hξη.trans hηu) hu1 hγstart hγout
  have hηcc : η ∈ Icc ξ u := ⟨hξη.le, hηu.le⟩
  have hηoo : η ∈ Ioo ξ u := ⟨hξη, hηu⟩
  have hη01 : η ∈ Ioo (0 : ℝ) 1 := ⟨hξpos.trans hξη, hη1⟩
  have hctpos : 0 < ‖c t‖ := hA.trans (hout t hst)
  have hγpuncture : γ η ∉ pointPunctures a y := by
    rintro ⟨j, _, hj⟩
    have hy : 2 * ‖y j‖ ≤ ‖c t‖ := (hyA j).trans (hout t hst).le
    apply pointExterior_sub_ne_zero hctpos hy
    have he : γ η = c t := by simp only [γ, hηeq]
    rw [← he, hj, sub_self]
  have hγD := (pointConformal_geodesic_analyticAt ha y γ hγc k hγgeo hη01 hγpuncture).differentiableAt
  have hγV := pointConformal_geodesic_deriv_ne_zero ha y γ hγc k hk hγgeo hη01 hγpuncture
  have hcD := hasDerivAt_of_positive_affine_pullback (c := c) (l := l) (u := η) hk hγD.hasDerivAt
  rw [hηeq] at hcD
  have hcV : deriv c t ≠ 0 := by
    rw [hcD.deriv]
    exact smul_ne_zero (inv_ne_zero (ne_of_gt hk)) hγV
  have hunit : deriv c t / (‖deriv c t‖ : ℂ) = deriv γ η / (‖deriv γ η‖ : ℂ) := by
    rw [hcD.deriv]
    exact normalized_positive_real_smul k⁻¹ (inv_pos.mpr hk) (deriv γ η)
  have hθt : Complex.exp ((θ η : ℂ) * Complex.I) = deriv c t / (‖deriv c t‖ : ℂ) :=
    (hlift η hηcc).1.trans hunit.symm
  have hφt : Complex.exp ((φ η : ℂ) * Complex.I) = c t / (‖c t‖ : ℂ) := by
    simpa only [γ, hηeq] using (hlift η hηcc).2
  have hradial : 0 < physicalRadialProjection (c t) (deriv c t) := by
    rw [physicalRadialProjection_polar_lifts (norm_pos_iff.mp hctpos) hcV hθt hφt]
    exact mul_pos (mul_pos hctpos (norm_pos_iff.mpr hcV)) (hcos η hηoo)
  refine ⟨hcD.differentiableAt, hcV, hradial, ?_⟩
  rw [← hθt, ← hφt]
  apply (norm_angle_chord_le_two_abs_sin (hcos η hηoo).le).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [tailSineEnvelope, γ, hηeq] using hsine η hηcc

theorem exists_pointMetricLine_outward_radial_tail
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ) (hc : Continuous c)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {A : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hinside : ‖c 0‖ < A) :
    ∃ s : ℝ, 0 < s ∧ ‖c s‖ = A ∧ (∀ t, s < t → A < ‖c t‖) ∧
      ∀ t, s < t → DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
        0 < physicalRadialProjection (c t) (deriv c t) ∧
        ‖deriv c t / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ)‖ ≤
          2 * tailSineEnvelope A (pointExteriorHalfMass a) (pointExteriorMoment a y) ‖c t‖ := by
  have hescape := pointMetricLine_norm_tendsto_atTop ha y c hd
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hescape.eventually (eventually_gt_atTop A))
  let T := max T₀ 1
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hfar : ∀ t, T ≤ t → A < ‖c t‖ := fun t ht => hT₀ t ((le_max_left _ _).trans ht)
  obtain ⟨s, hs, hsA, hout⟩ := exists_last_level_crossing hc.norm hT hinside (hfar T le_rfl)
  have houtAll : ∀ t, s < t → A < ‖c t‖ := by
    intro t ht
    by_cases htT : t ≤ T
    · exact hout t ⟨ht, htT⟩
    · exact hfar t (le_of_not_ge htT)
  refine ⟨s, hs.1, hsA, houtAll, ?_⟩
  intro t ht
  exact pointMetricLine_outward_tail_at ha y c hc hd hA hyA hB hD hsA houtAll ht

theorem pointMetricLine_outward_tangent_radial_limit
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ) (hc : Continuous c)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {A : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hinside : ‖c 0‖ < A) :
    Tendsto (fun t => deriv c t / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ)) atTop (𝓝 0) := by
  obtain ⟨s, _, _, _, htail⟩ := exists_pointMetricLine_outward_radial_tail
    ha y c hc hd hA hyA hB hD hinside
  have hbound : ∀ᶠ t in atTop,
      ‖deriv c t / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ)‖ ≤
        2 * tailSineEnvelope A (pointExteriorHalfMass a) (pointExteriorMoment a y) ‖c t‖ := by
    filter_upwards [eventually_gt_atTop s] with t ht
    exact (htail t ht).2.2.2
  have hzero := ((tailSineEnvelope_tendsto_zero_atTop A (pointExteriorMoment a y) hB).comp
    (pointMetricLine_norm_tendsto_atTop ha y c hd)).const_mul 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound (by simpa using hzero)

end RepulsiveCoulomb
