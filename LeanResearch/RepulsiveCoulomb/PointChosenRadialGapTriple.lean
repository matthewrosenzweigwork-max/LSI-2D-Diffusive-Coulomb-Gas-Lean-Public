import LeanResearch.RepulsiveCoulomb.PointChosenRadialCollars
import LeanResearch.RepulsiveCoulomb.PointSmoothGapJoinTangents
import LeanResearch.RepulsiveCoulomb.PointGeodesicSmoothInteriorSubarc

/-! Constructed three-piece data for each actual puncture gap. Both endpoint
collars retain the once-per-vertex chart, exact power law and analytic radial
formula. The two artificial joins have proved positive tangent alignment. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

structure PointChosenRadialGapTriple {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) (s t : Icc (0 : ℝ) 1) where
  leftCut : Icc (0 : ℝ) 1
  rightCut : Icc (0 : ℝ) 1
  left_lt : s < leftCut
  middle_lt : leftCut < rightCut
  right_lt : rightCut < t
  leftArc : PointSmoothArcPiece γ
  middleArc : PointSmoothArcPiece γ
  rightArc : PointSmoothArcPiece γ
  left_start : leftArc.start = s
  left_finish : leftArc.finish = leftCut
  middle_start : middleArc.start = leftCut
  middle_finish : middleArc.finish = rightCut
  right_start : rightArc.start = rightCut
  right_finish : rightArc.finish = t
  chain : PointSmoothArcChain γ s t [leftArc, middleArc, rightArc]
  left_power : ∀ u ∈ Icc (0 : ℝ) 1,
    IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ (s.1 + u * (leftCut.1 - s.1)) =
      leftArc.curve (u ^ (coalescedPointExponent a y (γ s) / 2 + 1)⁻¹)
  middle_affine : ∀ u ∈ Icc (0 : ℝ) 1, middleArc.curve u =
    IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
      (leftCut.1 + u * (rightCut.1 - leftCut.1))
  right_power : ∀ u ∈ Icc (0 : ℝ) 1,
    IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ (t.1 + u * (rightCut.1 - t.1)) =
      rightArc.curve (1 - u ^ (coalescedPointExponent a y (γ t) / 2 + 1)⁻¹)
  left_radial : ∀ u ∈ Icc (0 : ℝ) 1, leftArc.curve =ᶠ[𝓝 u] (fun v : ℝ =>
    (pointChosenSmoothRadialChart ha y (γ s)).symm
      (v • (pointChosenSmoothRadialChart ha y (γ s)) (γ leftCut)))
  right_radial : ∀ u ∈ Icc (0 : ℝ) 1, rightArc.curve =ᶠ[𝓝 u] (fun v : ℝ =>
    (pointChosenSmoothRadialChart ha y (γ t)).symm
      ((1 - v) • (pointChosenSmoothRadialChart ha y (γ t)) (γ rightCut)))
  leftSpeed : ℝ
  rightSpeed : ℝ
  leftSpeed_pos : 0 < leftSpeed
  rightSpeed_pos : 0 < rightSpeed
  left_jet : deriv middleArc.curve 0 = leftSpeed • deriv leftArc.curve 1
  right_jet : deriv rightArc.curve 0 = rightSpeed • deriv middleArc.curve 1

/-- Every nonempty actual geodesic interval without an interior positive
puncture has a constructed triple retaining compatible charts and all jets. -/
theorem exists_pointConformal_chosen_radial_gap_triple {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal)
    (s t : Icc (0 : ℝ) 1) (hst : s < t)
    (hgap : ∀ u ∈ Ioo s t, γ u ∉ pointPunctures a y) :
    Nonempty (PointChosenRadialGapTriple ha y γ s t) := by
  obtain ⟨Rs, hRs, hleft⟩ := exists_pointChosenRadial_start_collar ha y hpq γ hd s
  obtain ⟨Rt, hRt, hright⟩ := exists_pointChosenRadial_finish_collar ha y hpq γ hd t
  let D := (pointSmoothConformalEDist a y p q).toReal
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  have hst' : s.1 < t.1 := hst
  let ε := min ((t.1 - s.1) / 4) (min Rs Rt / (D + 1))
  have hε : 0 < ε := lt_min (by positivity) (div_pos (lt_min hRs hRt) (by linarith))
  have hεgap : ε ≤ (t.1 - s.1) / 4 := min_le_left _ _
  have hεR : ε * (D + 1) ≤ min Rs Rt :=
    (le_div_iff₀ (show 0 < D + 1 by linarith)).mp (min_le_right _ _)
  have hεDs : ε * D ≤ Rs := by nlinarith [min_le_left Rs Rt]
  have hεDt : ε * D ≤ Rt := by nlinarith [min_le_right Rs Rt]
  let l : Icc (0 : ℝ) 1 := ⟨s.1 + ε, by constructor <;> nlinarith [s.2.1, t.2.2]⟩
  let r : Icc (0 : ℝ) 1 := ⟨t.1 - ε, by constructor <;> nlinarith [s.2.1, t.2.2]⟩
  have hsl : s < l := by change s.1 < s.1 + ε; linarith
  have hlr : l < r := by change s.1 + ε < t.1 - ε; nlinarith
  have hrt : r < t := by change t.1 - ε < t.1; linarith
  have hl0 : 0 < l.1 := by change 0 < s.1 + ε; linarith [s.2.1]
  have hr1 : r.1 < 1 := by change t.1 - ε < 1; linarith [t.2.2]
  have hl1 : l.1 < 1 := lt_trans hlr hr1
  have hr0 : 0 < r.1 := lt_trans hl0 hlr
  have hdls : (pointSmoothConformalEDist a y (γ l) (γ s)).toReal = ε * D := by
    rw [hd]
    change |s.1 - (s.1 + ε)| * D = ε * D
    rw [show s.1 - (s.1 + ε) = -ε by ring, abs_neg, abs_of_pos hε]
  have hdrt : (pointSmoothConformalEDist a y (γ r) (γ t)).toReal = ε * D := by
    rw [hd]
    change |t.1 - (t.1 - ε)| * D = ε * D
    rw [sub_sub_cancel, abs_of_pos hε]
  obtain ⟨eL, heLs, heLl, hLpower, hLgerm⟩ := hleft l hsl (hdls.trans_le hεDs)
  obtain ⟨eR, heRr, heRt, hRpower, hRgerm⟩ := hright r hrt (hdrt.trans_le hεDt)
  have hmiddle : ∀ u ∈ Icc l r, γ u ∉ pointPunctures a y := by
    intro u hu
    exact hgap u ⟨hsl.trans_le hu.1, hu.2.trans_lt hrt⟩
  obtain ⟨η, hη, hηi, hηr, hη0, hη1, hηparam, hηimage⟩ :=
    exists_pointConformal_smooth_interior_subarc ha y hpq γ hd l r hlr hl0 hr1 hmiddle
  let eM : PointSmoothArcPiece γ := ⟨l, r, hlr, η, hη, hηi, hηr, hη0, hη1, hηimage⟩
  let g := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  have hMaffine : ∀ u ∈ Icc (0 : ℝ) 1, η u = g (l.1 + u * (r.1 - l.1)) := by
    intro u hu
    rw [hηparam ⟨u, hu⟩]
    change γ (pointGeodesicIntervalMap l r hlr.le ⟨u, hu⟩) =
      IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
        (pointGeodesicIntervalMap l r hlr.le ⟨u, hu⟩).1
    exact (IccExtend_of_mem _ _ (pointGeodesicIntervalMap l r hlr.le ⟨u, hu⟩).2).symm
  have hc := pointConformal_geodesic_continuous ha y γ hd
  have hgl : DifferentiableAt ℝ g l.1 :=
    (pointConformal_geodesic_extension_analyticAt ha y γ hc hd ⟨hl0, hl1⟩
      (hmiddle l ⟨le_rfl, hlr.le⟩)).differentiableAt
  have hgr : DifferentiableAt ℝ g r.1 :=
    (pointConformal_geodesic_extension_analyticAt ha y γ hc hd ⟨hr0, hr1⟩
      (hmiddle r ⟨hlr.le, le_rfl⟩)).differentiableAt
  have hβs : 0 < (coalescedPointExponent a y (γ s) / 2 + 1)⁻¹ :=
    inv_pos.mpr (by have h := coalescedPointExponent_nonneg a y (γ s); positivity)
  have hβt : 0 < (coalescedPointExponent a y (γ t) / 2 + 1)⁻¹ :=
    inv_pos.mpr (by have h := coalescedPointExponent_nonneg a y (γ t); positivity)
  obtain ⟨cL, hcL, hjetL⟩ := power_collar_affine_join_positive_tangent hsl hlr hβs
    hgl (eL.smooth.differentiable (by simp) 1) (hη.differentiable (by simp) 0) hLpower hMaffine
  obtain ⟨cR, hcR, hjetR⟩ := affine_middle_power_finish_join_positive_tangent hlr hrt hβt
    hgr (hη.differentiable (by simp) 1) (eR.smooth.differentiable (by simp) 0) hMaffine hRpower
  have hL : PointSmoothArcChain γ s l [eL] := by
    rw [← heLs, ← heLl]
    exact .cons eL (.nil eL.finish)
  have hM : PointSmoothArcChain γ l r [eM] := .cons eM (.nil r)
  have hR : PointSmoothArcChain γ r t [eR] := by
    rw [← heRr, ← heRt]
    exact .cons eR (.nil eR.finish)
  exact ⟨⟨l, r, hsl, hlr, hrt, eL, eM, eR, heLs, heLl, rfl, rfl, heRr, heRt,
    (hL.append hM).append hR, hLpower, hMaffine, hRpower, hLgerm, hRgerm,
    cL, cR, hcL, hcR, hjetL, hjetR⟩⟩

end RepulsiveCoulomb
