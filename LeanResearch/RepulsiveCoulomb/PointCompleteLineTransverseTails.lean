module

public import LeanResearch.RepulsiveCoulomb.PointCompleteLineEndDirections
public import LeanResearch.RepulsiveCoulomb.PointLineOutwardRadialTail
public import Mathlib.Tactic

@[expose] public section

/-! Both actual outward tails of the constructed complete line. Local
 regularity, radial signs and tangent radiality are derived from the line's
 exact metric identity, separately from endpoint-direction retention. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem hasDerivAt_of_negated_parameter
    {c : ℝ → ℂ} {V : ℂ} {t : ℝ}
    (h : HasDerivAt (fun u => c (-u)) V (-t)) : HasDerivAt c (-V) t := by
  have hh := h.scomp t (hasDerivAt_id t).neg
  simpa only [Function.comp_def, neg_neg, neg_one_smul] using hh

theorem exists_pointMetricLine_transverse_radial_tails
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a)
    (c : ℝ → ℂ) (hc : Continuous c)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t, T < t → DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
        0 < physicalRadialProjection (c t) (deriv c t)) ∧
      (∀ t, t < -T → DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
        physicalRadialProjection (c t) (deriv c t) < 0) ∧
      Tendsto (fun t => deriv c t / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ))
        atTop (𝓝 0) ∧
      Tendsto (fun t => (-deriv c t) / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ))
        atBot (𝓝 0) := by
  let A := ‖c 0‖ + pointExteriorPenetrationRadius a y + 1
  obtain ⟨hP, hyP, hDP, _⟩ := pointExteriorPenetrationRadius_bounds ha y hB
  have hA : 0 < A := by dsimp [A]; positivity
  have hPA : pointExteriorPenetrationRadius a y ≤ A := by
    dsimp [A]
    linarith [norm_nonneg (c 0)]
  have hyA : ∀ j, 2 * ‖y j‖ ≤ A := fun j => (hyP j).trans hPA
  have hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A :=
    hDP.trans_le (mul_le_mul_of_nonneg_left hPA (by linarith))
  have hinside : ‖c 0‖ < A := by dsimp [A]; linarith
  let cr : ℝ → ℂ := fun t => c (-t)
  have hcr : Continuous cr := hc.comp continuous_neg
  have hdr : ∀ s t, (pointSmoothConformalEDist a y (cr s) (cr t)).toReal = dist s t := by
    intro s t
    simpa only [cr, Real.dist_eq, neg_sub_neg, abs_sub_comm] using hd (-s) (-t)
  have hinsideR : ‖cr 0‖ < A := by simpa only [cr, neg_zero] using hinside
  obtain ⟨sp, hsp, _, _, hp⟩ := exists_pointMetricLine_outward_radial_tail
    ha y c hc hd hA hyA hB hD hinside
  obtain ⟨sn, hsn, _, _, hn⟩ := exists_pointMetricLine_outward_radial_tail
    ha y cr hcr hdr hA hyA hB hD hinsideR
  have hreverse (t : ℝ) (ht : t < -sn) :
      HasDerivAt c (-deriv cr (-t)) t :=
    hasDerivAt_of_negated_parameter (hn (-t) (by linarith)).1.hasDerivAt
  have hnegative (t : ℝ) (ht : t < -sn) :
      DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
        physicalRadialProjection (c t) (deriv c t) < 0 := by
    have h := hn (-t) (by linarith)
    refine ⟨(hreverse t ht).differentiableAt, ?_, ?_⟩
    · rw [(hreverse t ht).deriv]
      exact neg_ne_zero.mpr h.2.1
    · have hproj := h.2.2.1
      rw [(hreverse t ht).deriv]
      have he : physicalRadialProjection (c t) (-deriv cr (-t)) =
          -physicalRadialProjection (cr (-t)) (deriv cr (-t)) := by
        simp only [cr, neg_neg, physicalRadialProjection, Complex.neg_re, Complex.neg_im]
        ring
      rw [he]
      linarith
  have hposlim := pointMetricLine_outward_tangent_radial_limit
    ha y c hc hd hA hyA hB hD hinside
  have hneglimR := pointMetricLine_outward_tangent_radial_limit
    ha y cr hcr hdr hA hyA hB hD hinsideR
  have hneglim0 : Tendsto
      (fun t => deriv cr (-t) / (‖deriv cr (-t)‖ : ℂ) - c t / (‖c t‖ : ℂ))
      atBot (𝓝 0) := by
    simpa only [Function.comp_def, cr, neg_neg] using hneglimR.comp tendsto_neg_atBot_atTop
  have hneglim : Tendsto
      (fun t => (-deriv c t) / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ))
      atBot (𝓝 0) := by
    apply hneglim0.congr'
    filter_upwards [eventually_lt_atBot (-sn)] with t ht
    rw [(hreverse t ht).deriv, neg_neg, norm_neg]
  let T := max sp sn + 1
  have hT : 0 < T := by dsimp [T]; linarith [le_max_left sp sn]
  refine ⟨T, hT, ?_, ?_, hposlim, hneglim⟩
  · intro t ht
    have hst : sp < t := by dsimp [T] at ht; linarith [le_max_left sp sn]
    exact ⟨(hp t hst).1, (hp t hst).2.1, (hp t hst).2.2.1⟩
  · intro t ht
    apply hnegative
    dsimp [T] at ht
    linarith [le_max_right sp sn]

theorem exists_pointConformal_complete_line_with_actual_radial_tails
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) ∧
      Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)) ∧
      Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ)) ∧
      ∃ T : ℝ, 0 < T ∧
        (∀ t, T < t → DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
          0 < physicalRadialProjection (c t) (deriv c t)) ∧
        (∀ t, t < -T → DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
          physicalRadialProjection (c t) (deriv c t) < 0) ∧
        Tendsto (fun t => deriv c t / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ))
          atTop (𝓝 0) ∧
        Tendsto (fun t => (-deriv c t) / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ))
          atBot (𝓝 0) := by
  obtain ⟨c, hc, hd, hpos, hneg⟩ :=
    exists_pointConformal_complete_line_with_opposite_end_directions ha y hB
  exact ⟨c, hc, hd, hpos, hneg, exists_pointMetricLine_transverse_radial_tails ha y hB c hc hd⟩

end RepulsiveCoulomb
