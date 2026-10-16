module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicBigonExtraction
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! The source-time clock of an actual regular equal-image geodesic subarc
is constructed from the literal metric distance. It is continuous and
strictly increasing. No constant-speed law is transferred to the new curve. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointConformal_real_distance_continuous {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ) :
    Continuous (fun z => (pointSmoothConformalEDist a y z x).toReal) := by
  have hc : @Continuous ℂ ℝ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace inferInstance
      (fun z => (pointSmoothConformalEDist a y z x).toReal) := by
    exact @Continuous.dist ℂ ℂ
      (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (fun z => z) (fun _ => x)
      (@continuous_id ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace)
      (@continuous_const ℂ ℂ
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace x)
  rwa [pointSmoothConformalMetricSpace_topology ha y] at hc

def pointGeodesicMetricClock {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (x z : ℂ) (η : ℝ → ℂ) (u : ℝ) : ℝ :=
  (pointSmoothConformalEDist a y (η u) x).toReal /
    (pointSmoothConformalEDist a y x z).toReal

/-- A concrete monotone source-time relation for the new representative is
proved from the actual metric distance, closed trace, injectivity, and
oriented endpoints. The relation need not have constant derivative. -/
theorem pointConformal_equal_image_oriented_clock {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z)
    (γ : Icc (0 : ℝ) 1 → ℂ) (h0 : γ ⟨0, by norm_num⟩ = x)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y x z).toReal)
    (s t : Icc (0 : ℝ) 1) (hst : s < t) {η : ℝ → ℂ}
    (hc : ContinuousOn η (Icc (0 : ℝ) 1)) (hi : InjOn η (Icc (0 : ℝ) 1))
    (hη0 : η 0 = γ s) (hη1 : η 1 = γ t)
    (himage : η '' Icc (0 : ℝ) 1 = γ '' Icc s t) :
    let τ := pointGeodesicMetricClock a y x z η
    ContinuousOn τ (Icc (0 : ℝ) 1) ∧ StrictMonoOn τ (Icc (0 : ℝ) 1) ∧
      τ 0 = s.1 ∧ τ 1 = t.1 ∧ MapsTo τ (Icc (0 : ℝ) 1) (Icc s.1 t.1) ∧
      ∀ u ∈ Icc (0 : ℝ) 1,
        η u = IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ (τ u) := by
  let D := (pointSmoothConformalEDist a y x z).toReal
  have hD : 0 < D := by
    apply ENNReal.toReal_pos
    · exact (pointSmoothConformalEDist_eq_zero_iff ha y x z).not.mpr hxz
    · exact (pointSmoothConformalEDist_lt_top ha y x z).ne
  let τ := pointGeodesicMetricClock a y x z η
  have hγclock (v : Icc (0 : ℝ) 1) : (pointSmoothConformalEDist a y (γ v) x).toReal / D = v.1 := by
    have h := hd v ⟨0, by norm_num⟩
    rw [h0, zero_sub, abs_neg, abs_of_nonneg v.2.1] at h
    rw [h, mul_div_cancel_right₀ _ hD.ne']
  have hτc : ContinuousOn τ (Icc (0 : ℝ) 1) :=
    ((pointConformal_real_distance_continuous ha y x).comp_continuousOn hc).div_const D
  have hτ0 : τ 0 = s.1 := by
    change (pointSmoothConformalEDist a y (η 0) x).toReal / D = s.1
    rw [hη0]
    exact hγclock s
  have hτ1 : τ 1 = t.1 := by
    change (pointSmoothConformalEDist a y (η 1) x).toReal / D = t.1
    rw [hη1]
    exact hγclock t
  have hsource (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ∃ v ∈ Icc s t, τ u = v.1 ∧ η u = γ v := by
    have hmem : η u ∈ η '' Icc (0 : ℝ) 1 := ⟨u, hu, rfl⟩
    rw [himage] at hmem
    obtain ⟨v, hv, hvu⟩ := hmem
    refine ⟨v, hv, ?_, hvu.symm⟩
    change (pointSmoothConformalEDist a y (η u) x).toReal / D = v.1
    rw [← hvu]
    exact hγclock v
  have hparam (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      η u = IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ (τ u) := by
    obtain ⟨v, hv, hτv, huv⟩ := hsource u hu
    rw [hτv, IccExtend_of_mem _ _ v.2]
    exact huv
  have hτi : InjOn τ (Icc (0 : ℝ) 1) := by
    intro u hu v hv heq
    apply hi hu hv
    rw [hparam u hu, hparam v hv, heq]
  have hτmono : StrictMonoOn τ (Icc (0 : ℝ) 1) :=
    hτc.strictMonoOn_of_injOn_Icc (by norm_num) (by rw [hτ0, hτ1]; exact hst.le) hτi
  refine ⟨hτc, hτmono, hτ0, hτ1, ?_, hparam⟩
  intro u hu
  obtain ⟨v, hv, hτv, _⟩ := hsource u hu
  change τ u ∈ Icc s.1 t.1
  rw [hτv]
  exact hv

end RepulsiveCoulomb
