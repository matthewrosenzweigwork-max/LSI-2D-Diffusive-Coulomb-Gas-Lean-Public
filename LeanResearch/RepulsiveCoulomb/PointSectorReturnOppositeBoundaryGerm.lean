module

public import LeanResearch.RepulsiveCoulomb.PointRetainedFrontierEndpoint

@[expose] public section

/-! Isolated, uncompiled frontend. The old compact arc's actual radial germ
is forced to the endpoint opposite the clean ray. Source containment and small
radius are obtained from continuity; radial endpoint membership follows from
the genuine retained chart and frontier topology. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- A continuous based compact arc has an actual positive initial interval
inside any specified small chart disk. No radiality is assumed here. -/
theorem exists_arc_initial_small_chart_interval
    (α : unitInterval → ℂ) (hα : Continuous α)
    (E : OpenPartialHomeomorph ℂ ℂ) {p : ℂ}
    (hp : p ∈ E.source) (hE0 : E p = 0) (hα0 : α 0 = p)
    {R : ℝ} (hR : 0 < R) :
    ∃ τ : unitInterval, 0 < τ.1 ∧
      ∀ t : unitInterval, t ≤ τ → α t ∈ E.source ∧ ‖E (α t)‖ < R := by
  let W := E.source ∩ E ⁻¹' ball (0 : ℂ) R
  have hW : IsOpen W := E.isOpen_inter_preimage isOpen_ball
  have hpW : p ∈ W := ⟨hp, by rw [mem_preimage, hE0]; exact mem_ball_self hR⟩
  have hzero : (0 : unitInterval) ∈ α ⁻¹' W := by
    change α 0 ∈ W
    rwa [hα0]
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp ((hW.preimage hα).mem_nhds hzero)
  have hτpos : 0 < min (ε / 2) (1 / 2 : ℝ) := lt_min (half_pos hε) (by norm_num)
  let τ : unitInterval := ⟨min (ε / 2) (1 / 2), hτpos.le,
    (min_le_right _ _).trans (by norm_num)⟩
  have hτε : τ.1 < ε := by
    change min (ε / 2) (1 / 2 : ℝ) < ε
    linarith [min_le_left (ε / 2) (1 / 2 : ℝ)]
  refine ⟨τ, hτpos, ?_⟩
  intro t ht
  have htball : t ∈ ball (0 : unitInterval) ε := by
    change |(t : ℝ) - 0| < ε
    rw [sub_zero, abs_of_nonneg t.2.1]
    exact (show t.1 ≤ τ.1 from ht).trans_lt hτε
  have htW := hεsub htball
  refine ⟨htW.1, ?_⟩
  simpa only [mem_preimage, mem_ball, dist_zero_right] using htW.2

/-- A genuine old frontier point in the chart disk lies on one of the two
full retained endpoint rays. The angular witness is constructed from retained
membership, rather than assumed or chosen through a principal argument. -/
theorem PointRetainedConeNeighborhood.frontier_chart_endpoint_alternative
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hP : IsClosed P)
    (hz : z ∈ frontier P) (hzsource : z ∈ C.chart.source)
    (hznorm : ‖C.chart z‖ < C.radius) (hzp : z ≠ p) :
    0 < ‖C.chart z‖ ∧
      (C.chart z = pointRadialSectorPoint ‖C.chart z‖ C.lo ∨
        C.chart z = pointRadialSectorPoint ‖C.chart z‖ C.hi) := by
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hp := C.source hpp
  obtain ⟨_, _, hd⟩ := C.retainedWidth_inverse hznorm.le
  rw [C.chart.left_inv hzsource] at hd
  have hzR := hd.trans_lt hznorm
  have hzne : C.chart z ≠ 0 := by
    intro he
    exact hzp (C.chart.injOn hzsource hp (he.trans C.center.symm))
  have hr : 0 < ‖C.chart z‖ := norm_pos_iff.mpr hzne
  obtain ⟨r, hrange, θ, hθ, he⟩ := (C.retained z hzR.le).mp (hP.frontier_subset hz)
  have hrad : r = ‖C.chart z‖ := by
    have hn := congrArg norm he
    rw [pointRadialSectorPoint_norm hrange.1] at hn
    exact hn.symm
  have he' : C.chart z = pointRadialSectorPoint ‖C.chart z‖ θ := by rwa [hrad] at he
  have hends := C.frontier_radial_coordinate_endpoint hz hzR hr hθ he'
  refine ⟨hr, ?_⟩
  rcases hends with rfl | rfl
  · exact Or.inl he'
  · exact Or.inr he'

/-- The endpoint used by the actual compact old arc is the endpoint OTHER
than the clean ray's. The two endpoint orientations are both retained explicitly.
The ray-valued old-arc germ and its positive source interval are outputs. -/
theorem exists_sectorReturn_opposite_old_boundary_germ
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hP : IsClosed P)
    (β : unitInterval → ℂ) (hβ : Continuous β) (hiβ : Function.Injective β)
    (hβ0 : β 0 = p) (hβfront : ∀ t, β t ∈ frontier P)
    (ρ : ℝ → ℂ) {ε ξ : ℝ} (hε : 0 < ε) (hξ : ξ = C.lo ∨ ξ = C.hi)
    (hρgerm : ∀ r ∈ Ioo (0 : ℝ) ε,
      ρ r = C.chart.symm (pointRadialSectorPoint r ξ))
    (havoid : ∀ r : ℝ, 0 < r → ρ r ∉ range β) :
    ∃ τ : unitInterval, 0 < τ.1 ∧
      (∀ t : unitInterval, t ≤ τ → β t ∈ C.chart.source) ∧
      ((ξ = C.lo ∧ ∀ t : unitInterval, t ≤ τ →
        C.chart (β t) = pointRadialSectorPoint ‖C.chart (β t)‖ C.hi) ∨
       (ξ = C.hi ∧ ∀ t : unitInterval, t ≤ τ →
        C.chart (β t) = pointRadialSectorPoint ‖C.chart (β t)‖ C.lo)) := by
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  obtain ⟨τ, hτ, hsmall⟩ := exists_arc_initial_small_chart_interval β hβ C.chart
    (C.source hpp) C.center hβ0 (lt_min C.radius_pos hε)
  have hpoint (t : unitInterval) (ht : t ≤ τ) (ht0 : t ≠ 0) :
      (C.chart (β t) = pointRadialSectorPoint ‖C.chart (β t)‖ C.lo ∨
        C.chart (β t) = pointRadialSectorPoint ‖C.chart (β t)‖ C.hi) ∧
      C.chart (β t) ≠ pointRadialSectorPoint ‖C.chart (β t)‖ ξ := by
    have htp : β t ≠ p := fun he => ht0 (hiβ (he.trans hβ0.symm))
    have hsrc := (hsmall t ht).1
    have hnR := (hsmall t ht).2.trans_le (min_le_left C.radius ε)
    have hnε := (hsmall t ht).2.trans_le (min_le_right C.radius ε)
    obtain ⟨hnpos, hends⟩ := C.frontier_chart_endpoint_alternative hP (hβfront t) hsrc hnR htp
    refine ⟨hends, ?_⟩
    intro he
    have hρeq : ρ ‖C.chart (β t)‖ = β t := by
      rw [hρgerm _ ⟨hnpos, hnε⟩, ← he, C.chart.left_inv hsrc]
    exact havoid _ hnpos ⟨t, hρeq.symm⟩
  refine ⟨τ, hτ, fun t ht => (hsmall t ht).1, ?_⟩
  rcases hξ with rfl | rfl
  · refine Or.inl ⟨rfl, ?_⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hβ0, C.center, norm_zero, pointRadialSectorPoint_zero]
    · exact (hpoint t ht ht0).1.resolve_left (hpoint t ht ht0).2
  · refine Or.inr ⟨rfl, ?_⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hβ0, C.center, norm_zero, pointRadialSectorPoint_zero]
    · exact (hpoint t ht ht0).1.resolve_right (hpoint t ht ht0).2

end RepulsiveCoulomb
