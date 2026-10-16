import LeanResearch.RepulsiveCoulomb.PointActualMarkedDirection

/-! Isolated, uncompiled frontend adapter. The radial-germ inputs needed by
cap topology are extracted from the constructed actual raw direction of the
same metric edge. Neither a radial clock nor a sampled germ is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

 theorem PointRetainedConeNeighborhood.actual_initial_raw_angle_germ
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E : PointGeodesicTreeEdge a y)
    (hstart : E.start = p) (hP : ∀ t, E.curve t ∈ P) :
    ∃ τ : unitInterval, 0 < τ.1 ∧
      (∀ t : unitInterval, t ≤ τ → E.curve t ∈ C.chart.source) ∧
      ∀ t : unitInterval, t ≤ τ →
        C.chart (E.curve t) = pointRadialSectorPoint ‖C.chart (E.curve t)‖
          (C.actualInitialRawAngle ha y hadm E hstart hP) := by
  obtain ⟨r, τ, hr, hrR, hτ, _, hdr, hrad⟩ :=
    C.actualInitialRawAngle_sample ha y hadm E hstart hP
  let L := (pointSmoothConformalEDist a y E.start E.finish).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have h0 : E.curve 0 = p := E.curve_start.trans hstart
  have hdist (t : unitInterval) :
      (pointSmoothConformalEDist a y (E.curve t) p).toReal = t.1 * L := by
    have h := E.geodesic t 0
    simpa only [h0, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg t.2.1, L] using h
  have hrclock : τ.1 * L = r := (hdist τ).symm.trans hdr
  have hsource (t : unitInterval) (ht : t ≤ τ) : E.curve t ∈ C.chart.source := by
    apply C.source
    change (pointSmoothConformalEDist a y (E.curve t) p).toReal ≤ C.radius
    rw [hdist t]
    exact (mul_le_mul_of_nonneg_right (show t.1 ≤ τ.1 from ht) hL).trans
      (hrclock.trans_le hrR.le)
  refine ⟨τ, hτ, hsource, ?_⟩
  intro t ht
  let u : unitInterval := ⟨t.1 / τ.1, div_nonneg t.2.1 hτ.le,
    (div_le_one hτ).mpr (show t.1 ≤ τ.1 from ht)⟩
  have hparam : pointEdgeSubparam 0 τ u = t := by
    apply Subtype.ext
    simp only [pointEdgeSubparam, AffineMap.lineMap_apply_module',
      Set.Icc.coe_zero, sub_zero, smul_eq_mul, add_zero]
    exact div_mul_cancel₀ t.1 hτ.ne'
  have hchart := hrad u
  rw [hparam] at hchart
  have hn : ‖C.chart (E.curve t)‖ = u.1 * r := by
    rw [hchart, pointRadialSectorPoint_norm (mul_nonneg u.2.1 hr.le)]
  simpa only [hn] using hchart

/-- Positive full direction strictly below the full retained width means the
actual raw direction is strictly between the two old endpoints, whichever
endpoint the clean reference ray occupies. -/
theorem sectorReturn_raw_direction_interior_of_physical_bounds
    {k lo hi φ ξ : ℝ} (hk : 0 < k) (hφ : φ ∈ Icc lo hi)
    (hξ : ξ = lo ∨ ξ = hi)
    (hpos : 0 < k * |φ - ξ|) (hlt : k * |φ - ξ| < k * (hi - lo)) :
    φ ∈ Ioo lo hi := by
  rcases hξ with rfl | rfl
  · rw [abs_of_nonneg (sub_nonneg.mpr hφ.1)] at hpos hlt
    constructor <;> nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hφ.2), neg_sub] at hpos hlt
    constructor <;> nlinarith

end RepulsiveCoulomb
