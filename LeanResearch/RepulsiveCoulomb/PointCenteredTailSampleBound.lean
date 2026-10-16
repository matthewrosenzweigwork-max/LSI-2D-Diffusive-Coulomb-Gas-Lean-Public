import LeanResearch.RepulsiveCoulomb.PointActualTailDirectionBound
import LeanResearch.RepulsiveCoulomb.PointMetricLineEscapeBounds
import LeanResearch.RepulsiveCoulomb.MetricCenteredClippedSegments
import LeanResearch.RepulsiveCoulomb.PointGeodesicBigonExtraction
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic

/-! Records-only successor. A centered sample at sufficiently large metric
 time is actually beyond the last enclosing-circle crossing. The endpoint
 direction estimate is then applied to this constructed original-segment tail.
 No unclipping, crossing, lift, or direction certificate is supplied. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointConformal_exact_segment_continuous
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) (L : ℝ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = |t.1 - s.1| * L) :
    Continuous γ := by
  have hL : (pointSmoothConformalEDist a y (γ ⟨0, by norm_num⟩)
      (γ ⟨1, by norm_num⟩)).toReal = L := by
    simpa only [Subtype.coe_mk, sub_zero, abs_one, one_mul] using
      hd ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  apply pointConformal_geodesic_continuous ha y
    (x := γ ⟨0, by norm_num⟩) (z := γ ⟨1, by norm_num⟩) γ
  intro s t
  rw [hL]
  exact hd s t

theorem pointConformal_centered_tail_sample_direction_bound
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) (τ : Icc (0 : ℝ) 1) {L : ℝ} (hL : 0 < L)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = |t.1 - s.1| * L)
    {A R q : ℝ} (hA : 0 < A) (hR : 0 ≤ R)
    (hyA : ∀ j, 2 * ‖y j‖ ≤ A) (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ A → (pointSmoothConformalEDist a y z 0).toReal ≤ R)
    (hanchor : ‖γ τ‖ < A) (hend : A < ‖γ ⟨1, by norm_num⟩‖)
    (hq : 2 * R < q) (hwindow : q < (1 - (τ : ℝ)) * L)
    (hsmall : tailSineEnvelope A (pointExteriorHalfMass a) (pointExteriorMoment a y)
      ‖metricCenteredClippedSegment γ τ L q‖ ≤ 1 / 2) :
    ‖metricCenteredClippedSegment γ τ L q /
        (‖metricCenteredClippedSegment γ τ L q‖ : ℂ) -
      γ ⟨1, by norm_num⟩ / (‖γ ⟨1, by norm_num⟩‖ : ℂ)‖ ≤
      angularTailPotential A (pointExteriorHalfMass a) (pointExteriorMoment a y)
        ‖metricCenteredClippedSegment γ τ L q‖ := by
  let g := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  have hc : Continuous g := continuous_IccExtend_iff.mpr
    (pointConformal_exact_segment_continuous ha y γ L hd)
  have hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (g s) (g t)).toReal = |t - s| * L := by
    intro s hs t ht
    dsimp [g]
    rw [IccExtend_of_mem _ _ hs, IccExtend_of_mem _ _ ht]
    exact hd ⟨s, hs⟩ ⟨t, ht⟩
  have hgτ : g τ = γ τ := by simp [g]
  have hg1 : g 1 = γ ⟨1, by norm_num⟩ := by
    exact IccExtend_of_mem _ _ (by norm_num)
  obtain ⟨s, hs, hstart, hout, htail⟩ :=
    exists_pointConformal_actual_tail_endpoint_direction_bound ha y g hc L hL hgeo
      hA hyA hB hD τ.2 (by simpa only [hgτ] using hanchor)
      (by simpa only [hg1] using hend)
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨τ.2.1.trans hs.1.le, hs.2.le⟩
  have hgS : g s = γ ⟨s, hs01⟩ := IccExtend_of_mem _ _ hs01
  have hsA : ‖γ ⟨s, hs01⟩‖ ≤ A := by rw [← hgS, hstart]
  have hafter : s < (τ : ℝ) + q / L :=
    pointConformal_centered_parameter_after_disk_crossing ha y γ hL hd hbound
      τ ⟨s, hs01⟩ hs.1.le hanchor.le hsA hq
  let t : ℝ := (τ : ℝ) + q / L
  have hqpos : 0 < q := lt_of_le_of_lt (by positivity) hq
  have ht0 : 0 < t := add_pos_of_nonneg_of_pos τ.2.1 (div_pos hqpos hL)
  have ht1 : t < 1 := by
    have h := (div_lt_iff₀ hL).mpr hwindow
    dsimp [t]
    linarith
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hsample : metricCenteredClippedSegment γ τ L q = g t := by
    rw [metricCenteredClippedSegment, projIcc_of_mem _ ht]
    exact (IccExtend_of_mem _ _ ht).symm
  have hb := htail t ⟨hafter, ht1⟩ (by simpa only [hsample] using hsmall)
  simpa only [← hsample, hg1] using hb

end RepulsiveCoulomb
