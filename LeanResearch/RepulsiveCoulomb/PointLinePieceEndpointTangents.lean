module

public import LeanResearch.RepulsiveCoulomb.OrientedClockEndpointTangents
public import LeanResearch.RepulsiveCoulomb.PointLineCapNatFamily
public import LeanResearch.RepulsiveCoulomb.PointLineCapAngleLimits
public import LeanResearch.RepulsiveCoulomb.AffineLineTailTransport
public import LeanResearch.RepulsiveCoulomb.PointGeodesicOrientedClock
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Uncompiled records-only successor. Actual line representatives retain the
oriented endpoint tangent direction. Their clock is constructed from literal
point-metric distance; differentiability of that clock is never assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- A complete metric line is physically regular at every nonpuncture, by
restricting a genuine affine unit window around that time. -/
theorem pointMetricLine_regular_at_nonpuncture
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {t : ℝ} (ht : c t ∉ pointPunctures a y) :
    DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 := by
  have hc := (pointMetricLine_isClosedEmbedding ha y c hd).continuous
  let γ : ℝ → ℂ := fun u => c ((t - 1) + 2 * u)
  have hγ : Continuous γ := hc.comp (by fun_prop)
  have hgeo := pointMetricLine_affine_segment_identity y c hd (t - 1) (by norm_num : (0 : ℝ) < 2)
  have hmid : (t - 1) + 2 * (1 / 2 : ℝ) = t := by ring
  have hpun : γ (1 / 2) ∉ pointPunctures a y := by simpa only [γ, hmid] using ht
  have hD := (pointConformal_geodesic_analyticAt ha y γ hγ 2 hgeo (by norm_num) hpun).differentiableAt
  have hV := pointConformal_geodesic_deriv_ne_zero ha y γ hγ 2 (by norm_num) hgeo (by norm_num) hpun
  have h := hasDerivAt_of_positive_affine_pullback (c := c) (l := t - 1)
    (u := (1 / 2 : ℝ)) (by norm_num : (0 : ℝ) < 2) hD.hasDerivAt
  rw [hmid] at h
  exact ⟨h.differentiableAt, by rw [h.deriv]; exact smul_ne_zero (by norm_num) hV⟩

/-- The source clock for an actual retained representative is globally
continuous and strictly increasing on its original closed parameter interval. -/
theorem PointRadialC1ArcPiece.exists_actual_line_clock
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {tm tp : ℝ} (ht : tm < tp)
    (e : PointRadialC1ArcPiece ha y (lineCapSegment c tm tp)) :
    ∃ T : ℝ → ℝ, Continuous T ∧ StrictMonoOn T (Icc (0 : ℝ) 1) ∧
      T 0 = tm + e.start.1 * (tp - tm) ∧ T 1 = tm + e.finish.1 * (tp - tm) ∧
      EqOn e.curve (c ∘ T) (Icc (0 : ℝ) 1) := by
  have hi := (pointMetricLine_isClosedEmbedding ha y c hd).injective
  have hpq : c tm ≠ c tp := fun h => ht.ne (hi h)
  let τ := pointGeodesicMetricClock a y (c tm) (c tp) e.curve
  obtain ⟨_, hmono, hτ0, hτ1, hmaps, hparam⟩ :=
    pointConformal_equal_image_oriented_clock ha y hpq (lineCapSegment c tm tp)
      (lineCapSegment_zero c tm tp) (lineCapSegment_metric y c hd tm tp)
      e.start e.finish e.increasing e.smooth.continuous.continuousOn
      e.injective e.at_zero e.at_one e.image
  have hτ : Continuous τ :=
    ((pointConformal_real_distance_continuous ha y (c tm)).comp e.smooth.continuous).div_const _
  let T : ℝ → ℝ := fun u => tm + τ u * (tp - tm)
  have hT : Continuous T := continuous_const.add (hτ.mul_const (tp - tm))
  have hTmono : StrictMonoOn T (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    simpa only [T, τ, add_comm] using
      add_lt_add_left (mul_lt_mul_of_pos_right (hmono hu hv huv) (sub_pos.mpr ht)) tm
  refine ⟨T, hT, hTmono, ?_, ?_, ?_⟩
  · change tm + pointGeodesicMetricClock a y (c tm) (c tp) e.curve 0 * (tp - tm) = _
    rw [hτ0]
  · change tm + pointGeodesicMetricClock a y (c tm) (c tp) e.curve 1 * (tp - tm) = _
    rw [hτ1]
  · intro u hu
    have hτ01 : τ u ∈ Icc (0 : ℝ) 1 :=
      ⟨e.start.2.1.trans (hmaps hu).1, (hmaps hu).2.trans e.finish.2.2⟩
    have hp := hparam u hu
    rw [IccExtend_of_mem _ _ hτ01] at hp
    exact hp

/-- Endpoint tangent transport for an arbitrary original radial macro-piece.
The endpoint nonpuncture assumptions are precisely the regular-point case;
positive atoms remain radial-link corners rather than differentiable points. -/
theorem PointRadialC1ArcPiece.actual_line_endpoint_tangents
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {tm tp : ℝ} (ht : tm < tp)
    (e : PointRadialC1ArcPiece ha y (lineCapSegment c tm tp)) :
    (e.curve 0 ∉ pointPunctures a y →
      deriv e.curve 0 / (‖deriv e.curve 0‖ : ℂ) =
        deriv c (tm + e.start.1 * (tp - tm)) /
          (‖deriv c (tm + e.start.1 * (tp - tm))‖ : ℂ)) ∧
    (e.curve 1 ∉ pointPunctures a y →
      deriv e.curve 1 / (‖deriv e.curve 1‖ : ℂ) =
        deriv c (tm + e.finish.1 * (tp - tm)) /
          (‖deriv c (tm + e.finish.1 * (tp - tm))‖ : ℂ)) := by
  obtain ⟨T, hT, hmono, hT0, hT1, hparam⟩ := e.exists_actual_line_clock hd ht
  constructor
  · intro hp
    have hbase : e.curve 0 = c (T 0) := hparam (by norm_num)
    have hreg := pointMetricLine_regular_at_nonpuncture ha y c hd (by rwa [← hbase])
    have h := oriented_clock_initial_tangent hT hmono hparam
      (e.smooth.differentiable (by norm_num) 0) hreg.1 (e.regular 0 (by norm_num)) hreg.2
    simpa only [hT0] using h
  · intro hp
    have hbase : e.curve 1 = c (T 1) := hparam (by norm_num)
    have hreg := pointMetricLine_regular_at_nonpuncture ha y c hd (by rwa [← hbase])
    have h := oriented_clock_final_tangent hT hmono hparam
      (e.smooth.differentiable (by norm_num) 1) hreg.1 (e.regular 1 (by norm_num)) hreg.2
    simpa only [hT1] using h

/-- Two regular adjacent representatives of the same oriented original line
have zero actual Euclidean turn, not merely a noncuspidal join. -/
theorem pointLinePieces_regular_join_zero_turn
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {tm tp : ℝ} (ht : tm < tp)
    (e d : PointRadialC1ArcPiece ha y (lineCapSegment c tm tp))
    (hjoin : e.curve 1 = d.curve 0) (hp : d.curve 0 ∉ pointPunctures a y) :
    Complex.arg (deriv d.curve 0 / deriv e.curve 1) = 0 := by
  have hi := (pointMetricLine_isClosedEmbedding ha y c hd).injective
  have htime : tm + e.finish.1 * (tp - tm) = tm + d.start.1 * (tp - tm) := by
    apply hi
    exact e.at_one.symm.trans (hjoin.trans d.at_zero)
  have he := (e.actual_line_endpoint_tangents hd ht).2 (by rwa [hjoin])
  have hd' := (d.actual_line_endpoint_tangents hd ht).1 hp
  rw [htime] at he
  rw [← lineCap_arg_normalized_quotient, hd', ← he, Complex.arg_div_self]

end RepulsiveCoulomb
