import LeanResearch.RepulsiveCoulomb.PointSmoothJoinTangents
import LeanResearch.RepulsiveCoulomb.JordanConformalTurnTransport

/-! Noncuspidality at an actual radial-chart corner follows from genuine
endpoint-only intersection. A positive coincidence of the two outgoing rays
would force overlapping small arc points. No corner-angle premise is input. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

/-- Two outgoing common-chart germs with actual one-endpoint intersection
cannot be positive real multiples of the same ray. -/
theorem radial_germs_not_positive_multiple {F G : ℝ → ℂ} {H : ℂ → ℂ} {u v : ℂ}
    (hFi : InjOn F (Icc (0 : ℝ) 1))
    (hmeet : F '' Icc (0 : ℝ) 1 ∩ G '' Icc (0 : ℝ) 1 ⊆ {F 0})
    (hF : F =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => H (t • u)))
    (hG : G =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => H (t • v))) :
    ¬ ∃ c : ℝ, 0 < c ∧ v = c • u := by
  rintro ⟨c, hc, hv⟩
  have hscale : Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun t : ℝ => c * t) := by fun_prop
    simpa only [mul_zero] using h.tendsto 0
  have hsame : (fun t : ℝ => F (c * t)) =ᶠ[𝓝 0] G := by
    filter_upwards [hF.comp_tendsto hscale, hG] with t hFt hGt
    simp only [Function.comp_def] at hFt
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
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.le, by linarith⟩
  have hctI : c * t ∈ Icc (0 : ℝ) 1 := ⟨(mul_pos hc ht).le, hct1⟩
  have he : F (c * t) = G t := hδsub (by
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]
    linarith)
  have hcommon : F (c * t) ∈ F '' Icc (0 : ℝ) 1 ∩ G '' Icc (0 : ℝ) 1 :=
    ⟨⟨c * t, hctI, rfl⟩, ⟨t, htI, he.symm⟩⟩
  have htime : c * t = 0 := hFi hctI (by norm_num) (hmeet hcommon)
  exact (mul_pos hc ht).ne' htime

/-- The algebraic short-angle criterion follows from the geometric absence
of coincident positive rays. -/
theorem neg_ratio_mem_slitPlane_of_not_positive_multiple {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hno : ¬ ∃ c : ℝ, 0 < c ∧ v = c • u) :
    -(v / u) ∈ Complex.slitPlane := by
  by_contra hnot
  have hfail : ¬ (0 < (-(v / u)).re ∨ (-(v / u)).im ≠ 0) := hnot
  have hre : 0 ≤ (v / u).re := by
    have h := not_lt.mp (not_or.mp hfail).1
    simp only [Complex.neg_re] at h
    linarith
  have him : (v / u).im = 0 := by
    have h : (-(v / u)).im = 0 := not_not.mp (not_or.mp hfail).2
    simpa only [Complex.neg_im, neg_eq_zero] using h
  have he : v / u = ((v / u).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hcne : (v / u).re ≠ 0 := by
    intro hc
    have hz : v / u = 0 := by rw [he, hc, Complex.ofReal_zero]
    exact (div_ne_zero hv hu) hz
  apply hno
  refine ⟨(v / u).re, lt_of_le_of_ne hre (Ne.symm hcne), ?_⟩
  calc
    v = (v / u) * u := (div_mul_cancel₀ v hu).symm
    _ = ((v / u).re : ℂ) * u := congrArg (fun z : ℂ => z * u) he
    _ = (v / u).re • u := Complex.real_smul.symm

/-- Reversing the incoming actual arc turns the common-chart corner into
outgoing germs. The chart chain rule then gives the genuine slit-plane ratio
of its oriented endpoint derivatives, including straight passages. -/
theorem radial_chart_corner_derivative_ratio_mem_slitPlane
    {F G : ℝ → ℂ} {H : ℂ → ℂ} {u v : ℂ}
    (hFi : InjOn F (Icc (0 : ℝ) 1))
    (hmeet : F '' Icc (0 : ℝ) 1 ∩ G '' Icc (0 : ℝ) 1 ⊆ {F 1})
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
  let Fᵣ : ℝ → ℂ := fun t => F (1 - t)
  have hFir : InjOn Fᵣ (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    have h := hFi (show 1 - s ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hs.1, hs.2])
      (show 1 - t ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2]) he
    linarith
  have hmeetR : Fᵣ '' Icc (0 : ℝ) 1 ∩ G '' Icc (0 : ℝ) 1 ⊆ {Fᵣ 0} := by
    rintro z ⟨⟨t, ht, htz⟩, hGz⟩
    have hmem : z ∈ F '' Icc (0 : ℝ) 1 :=
      ⟨1 - t, by constructor <;> linarith [ht.1, ht.2], htz⟩
    simpa only [Fᵣ, sub_zero] using hmeet ⟨hmem, hGz⟩
  have hFrev : Fᵣ =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => H (t • u)) := by
    have ht : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 1) := by
      have h : Continuous (fun t : ℝ => 1 - t) := by fun_prop
      simpa only [sub_zero] using h.tendsto 0
    simpa only [Fᵣ, Function.comp_def, sub_sub_cancel] using hF.comp_tendsto ht
  have hs := neg_ratio_mem_slitPlane_of_not_positive_multiple hu hv
    (radial_germs_not_positive_multiple hFir hmeetR hFrev hG)
  rw [hdF, hdG]
  have he : (deriv H 0 * v) / -(deriv H 0 * u) = -(v / u) := by
    field_simp [hD, hu]
  rwa [he]

end RepulsiveCoulomb
