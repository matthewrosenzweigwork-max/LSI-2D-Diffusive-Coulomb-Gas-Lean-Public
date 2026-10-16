module

public import LeanResearch.RepulsiveCoulomb.PointIncidentChartMetricBounds
public import LeanResearch.RepulsiveCoulomb.PointConformalGeodesic
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Shrink actual open charts in the old metric.
A minimizing path between points of a sufficiently small old ball stays in
a larger old ball by the triangle inequality. Centered local upper estimates
then globalize exactly along that path, with no source-convexity assertion. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- An actual source restriction, preserving the original chart function and
germ while upgrading centered local estimates to all source-pair bounds. -/
theorem exists_pointConformal_chart_metric_shrink
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ) (p : ℂ) (hp : p ∈ e.source) {c : ℝ}
    (hlower : ∀ x ∈ e.source, ∀ z ∈ e.source,
      c * (pointSmoothConformalEDist a y x z).toReal ≤ dist (e x) (e z))
    (hlocal : ∀ x ∈ e.source, ∀ᶠ z in 𝓝 x,
      dist (e x) (e z) ≤ (pointSmoothConformalEDist a y x z).toReal) :
    ∃ f : OpenPartialHomeomorph ℂ ℂ,
      p ∈ f.source ∧ f.source ⊆ e.source ∧ (f : ℂ → ℂ) = e ∧
      ∀ x ∈ f.source, ∀ z ∈ f.source,
        c * (pointSmoothConformalEDist a y x z).toReal ≤ dist (f x) (f z) ∧
          dist (f x) (f z) ≤ (pointSmoothConformalEDist a y x z).toReal := by
  obtain ⟨δ, hδ, hδe⟩ := exists_pointConformal_closedBall_subset_open ha y e.open_source hp
  obtain ⟨C⟩ := exists_pointFlatLinkConeDisk ha y p
  let R := min δ C.radius / 4
  have hR : 0 < R := div_pos (lt_min hδ C.radius_pos) (by norm_num)
  have hRC : R ≤ C.radius := by
    have h := min_le_right δ C.radius
    dsimp [R]
    linarith [C.radius_pos]
  have hRδ : 3 * R < δ := by
    have h := min_le_left δ C.radius
    dsimp [R]
    linarith
  let U := pointConeOpenBall C R
  have hUe : U ⊆ e.source := by
    intro z hz
    apply hδe z
    have h := (mem_pointConeOpenBall_iff C hRC z).mp hz
    linarith
  let f := e.restrOpen U (pointConeOpenBall_isOpen C R)
  refine ⟨f, ⟨hp, pointConeOpenBall_center C hR⟩, inter_subset_left, rfl, ?_⟩
  intro x hx z hz
  refine ⟨hlower x hx.1 z hz.1, ?_⟩
  change dist (e x) (e z) ≤ (pointSmoothConformalEDist a y x z).toReal
  obtain ⟨γ, h0, h1, hγ, hd⟩ := exists_pointConformal_geodesic ha y x z
  have hxR := (mem_pointConeOpenBall_iff C hRC x).mp hx.2
  have hzR := (mem_pointConeOpenBall_iff C hRC z).mp hz.2
  have hxz : (pointSmoothConformalEDist a y x z).toReal ≤
      (pointSmoothConformalEDist a y x p).toReal + (pointSmoothConformalEDist a y z p).toReal := by
    have h := @dist_triangle ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace x p z
    change (pointSmoothConformalEDist a y x z).toReal ≤
      (pointSmoothConformalEDist a y x p).toReal + (pointSmoothConformalEDist a y p z).toReal at h
    simpa only [pointSmoothConformalEDist_comm a y p z] using h
  have hγx (t : Icc (0 : ℝ) 1) :
      (pointSmoothConformalEDist a y (γ t) x).toReal ≤ (pointSmoothConformalEDist a y x z).toReal := by
    have heq := hd ⟨0, by norm_num⟩ t
    rw [h0] at heq
    have heq' : (pointSmoothConformalEDist a y (γ t) x).toReal =
        t.1 * (pointSmoothConformalEDist a y x z).toReal := by
      simpa only [pointSmoothConformalEDist_comm a y x (γ t), sub_zero,
        abs_of_nonneg t.2.1] using heq
    rw [heq']
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg t.2.2
  have hγmem (t : Icc (0 : ℝ) 1) : γ t ∈ e.source := by
    apply hδe (γ t)
    have h := @dist_triangle ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace (γ t) x p
    change (pointSmoothConformalEDist a y (γ t) p).toReal ≤
      (pointSmoothConformalEDist a y (γ t) x).toReal + (pointSmoothConformalEDist a y x p).toReal at h
    linarith [hγx t]
  have hcont : Continuous (fun t ↦ e (γ t)) := e.continuousOn.comp_continuous hγ hγmem
  have hbound : ∀ t, ∀ᶠ s in 𝓝 t,
      dist (e (γ t)) (e (γ s)) ≤ (pointSmoothConformalEDist a y x z).toReal * |s.1 - t.1| := by
    intro t
    filter_upwards [hγ.continuousAt.tendsto.eventually (hlocal (γ t) (hγmem t))] with s hs
    rw [hd] at hs
    simpa only [mul_comm] using hs
  have h := unitInterval_dist_le_of_centered_local_bound hcont hbound
  simpa only [h0, h1] using h

end RepulsiveCoulomb
