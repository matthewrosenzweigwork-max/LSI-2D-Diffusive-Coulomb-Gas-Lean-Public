module

public import LeanResearch.RepulsiveCoulomb.PointRadialC1BigonSimplicity
public import LeanResearch.RepulsiveCoulomb.PointRadialGermNoncuspidality

@[expose] public section

/-! Actual half-open simplicity suffices for noncuspidality at every cyclic
join, including a two-edge loop whose full closed arcs share two endpoints. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem radial_corner_not_positive_multiple_of_halfOpen_disjoint
    {F G : ℝ → ℂ} {H : ℂ → ℂ} {u v : ℂ}
    (hdisj : Disjoint (F '' Ico (0 : ℝ) 1) (G '' Ico (0 : ℝ) 1))
    (hF : F =ᶠ[𝓝 (1 : ℝ)] (fun t : ℝ => H ((1 - t) • u)))
    (hG : G =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => H (t • v))) :
    ¬ ∃ c : ℝ, 0 < c ∧ v = c • u := by
  rintro ⟨c, hc, hv⟩
  have hmap : Tendsto (fun t : ℝ => 1 - c * t) (𝓝 0) (𝓝 1) := by
    have h : Continuous (fun t : ℝ => 1 - c * t) := by fun_prop
    simpa only [mul_zero, sub_zero] using h.tendsto 0
  have hsame : (fun t : ℝ => F (1 - c * t)) =ᶠ[𝓝 0] G := by
    filter_upwards [hF.comp_tendsto hmap, hG] with t hFt hGt
    simp only [Function.comp_def, sub_sub_cancel] at hFt
    rw [hFt, hGt, hv, smul_smul, mul_comm c t]
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hsame
  let t := min (δ / 2) (min (1 / 2) (1 / (2 * c)))
  have ht : 0 < t := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have htδ : t ≤ δ / 2 := min_le_left _ _
  have ht1 : t ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htc : t ≤ 1 / (2 * c) := (min_le_right _ _).trans (min_le_right _ _)
  have hct1 : c * t ≤ 1 := by
    have h := (le_div_iff₀ (show 0 < 2 * c by positivity)).mp htc
    nlinarith
  have hct : 0 < c * t := mul_pos hc ht
  have htI : t ∈ Ico (0 : ℝ) 1 := ⟨ht.le, by linarith⟩
  have hFtI : 1 - c * t ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have he : F (1 - c * t) = G t := hδsub (by
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]
    linarith)
  exact disjoint_left.mp hdisj ⟨1 - c * t, hFtI, rfl⟩ ⟨t, htI, he.symm⟩

theorem radial_chart_halfOpen_corner_derivative_ratio_mem_slitPlane
    {F G : ℝ → ℂ} {H : ℂ → ℂ} {u v : ℂ}
    (hdisj : Disjoint (F '' Ico (0 : ℝ) 1) (G '' Ico (0 : ℝ) 1))
    (hF : F =ᶠ[𝓝 (1 : ℝ)] (fun t : ℝ => H ((1 - t) • u)))
    (hG : G =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => H (t • v)))
    (hH : DifferentiableAt ℂ H 0) (hFr : deriv F 1 ≠ 0) (hGr : deriv G 0 ≠ 0) :
    deriv G 0 / deriv F 1 ∈ Complex.slitPlane := by
  have hpF : HasDerivAt (fun t : ℝ => (1 - t) • u) (-u) 1 := by
    simpa only [id_eq, Pi.sub_apply, zero_sub, neg_one_smul] using
      ((hasDerivAt_const 1 (1 : ℝ)).sub (hasDerivAt_id 1)).smul_const u
  have hpG : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hHF : HasDerivAt H (deriv H 0) (((1 : ℝ) - 1) • u) := by
    simpa only [sub_self, zero_smul] using hH.hasDerivAt
  have hHG : HasDerivAt H (deriv H 0) ((0 : ℝ) • v) := by
    simpa only [zero_smul] using hH.hasDerivAt
  have hdF : deriv F 1 = -(deriv H 0 * u) := by
    have h := (hHF.comp 1 hpF).congr_of_eventuallyEq hF
    simpa only [mul_neg] using h.deriv
  have hdG : deriv G 0 = deriv H 0 * v := (hHG.comp 0 hpG).congr_of_eventuallyEq hG |>.deriv
  have hu : u ≠ 0 := by intro he; apply hFr; rw [hdF, he, mul_zero, neg_zero]
  have hv : v ≠ 0 := by intro he; apply hGr; rw [hdG, he, mul_zero]
  have hD : deriv H 0 ≠ 0 := by intro he; apply hGr; rw [hdG, he, zero_mul]
  have hs := neg_ratio_mem_slitPlane_of_not_positive_multiple hu hv
    (radial_corner_not_positive_multiple_of_halfOpen_disjoint hdisj hF hG)
  rw [hdF, hdG]
  have he : (deriv H 0 * v) / -(deriv H 0 * u) = -(v / u) := by field_simp [hD, hu]
  rwa [he]

/-- The constructed chosen charts provide the common differentiable H at
an actual cyclic join. No noncuspidal corner hypothesis is introduced. -/
theorem PointRadialC1PlaneArc.corner_ratio_mem_slitPlane {m : ℕ} {a : Fin m → ℝ}
    {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ} (e f : PointRadialC1PlaneArc ha y)
    (hjoin : e.finish = f.start)
    (hdisj : Disjoint (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1)) :
    deriv f.curve 0 / deriv e.curve 1 ∈ Complex.slitPlane := by
  obtain ⟨R, hR, hep, hsource, hInv, _, _⟩ := pointChosenSmoothRadialChart_spec ha y (e.curve 1)
  have htarget : (0 : ℂ) ∈ (pointChosenSmoothRadialChart ha y (e.curve 1)).target :=
    hep ▸ (pointChosenSmoothRadialChart ha y (e.curve 1)).mapsTo hsource
  have hG := f.left_radial
  change e.curve 1 = f.curve 0 at hjoin
  rw [← hjoin] at hG
  exact radial_chart_halfOpen_corner_derivative_ratio_mem_slitPlane hdisj e.right_radial hG
    (hInv 0 htarget).differentiableAt (e.regular 1 (by norm_num)) (f.regular 0 (by norm_num))

end RepulsiveCoulomb
