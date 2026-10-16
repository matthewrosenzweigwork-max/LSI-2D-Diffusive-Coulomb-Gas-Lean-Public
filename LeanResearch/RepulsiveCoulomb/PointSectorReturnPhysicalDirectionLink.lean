import LeanResearch.RepulsiveCoulomb.PointSectorReturnActualEdgeGerm

/-! Isolated, uncompiled comparison with the first-marked-direction API.
The same actual clean-ray germ determines the raw reference-edge angle. Thus
the full direction in the cap formula agrees with actualPhysicalDirection,
rather than merely with an unrelated endpoint-labelled scalar. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

 theorem PointRetainedConeNeighborhood.reference_angle_eq_actual_clean_germ
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (F : PointGeodesicTreeEdge a y)
    (hF0 : F.start = p) (hFP : ∀ t, F.curve t ∈ P)
    (ρ : ℝ → ℂ)
    (hFcurve : ∀ t : unitInterval, F.curve t = ρ (pointActualEdgeLength F * t.1))
    {ε ξ : ℝ} (hε : 0 < ε) (hξ : ξ ∈ Icc C.lo C.hi)
    (hclean : ∀ u ∈ Ioo (0 : ℝ) ε,
      C.chart (ρ u) = pointRadialSectorPoint u ξ) :
    C.actualInitialRawAngle ha y hadm F hF0 hFP = ξ := by
  obtain ⟨r, σ, hr, _, hσ, _, hdr, hrad⟩ := C.actualInitialRawAngle_sample ha y hadm F hF0 hFP
  have hbase : F.curve 0 = p := F.curve_start.trans hF0
  have hrclock : r = σ.1 * pointActualEdgeLength F := by
    have h := F.geodesic σ 0
    rw [hbase, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg σ.2.1, hdr] at h
    exact h
  let u := min ε r / 2
  have hu : 0 < u := half_pos (lt_min hε hr)
  have huε : u < ε := by dsimp [u]; linarith [min_le_left ε r]
  have hur : u < r := by dsimp [u]; linarith [min_le_right ε r]
  let v : unitInterval := ⟨u / r, div_nonneg hu.le hr.le, (div_le_one hr).mpr hur.le⟩
  have hvr : v.1 * r = u := div_mul_cancel₀ u hr.ne'
  have hparam : (pointEdgeSubparam 0 σ v).1 = v.1 * σ.1 := by
    simp only [pointEdgeSubparam, AffineMap.lineMap_apply_module',
      Set.Icc.coe_zero, sub_zero, smul_eq_mul, add_zero]
  have hpoint : F.curve (pointEdgeSubparam 0 σ v) = ρ u := by
    rw [hFcurve, hparam]
    apply congrArg ρ
    calc
      pointActualEdgeLength F * (v.1 * σ.1) = v.1 * (σ.1 * pointActualEdgeLength F) := by ring
      _ = v.1 * r := by rw [← hrclock]
      _ = u := hvr
  have hrad' := hrad v
  rw [hpoint, hvr] at hrad'
  have hpolar : pointRadialSectorPoint u
      (C.actualInitialRawAngle ha y hadm F hF0 hFP) = pointRadialSectorPoint u ξ :=
    hrad'.symm.trans (hclean u ⟨hu, huε⟩)
  exact (C.retained_polar_angle_unique hadm hu hu.le
    (C.actualInitialRawAngle_spec ha y hadm F hF0 hFP).1 hξ hpolar).2

 theorem PointRetainedConeNeighborhood.actualPhysicalDirection_eq_clean_germ_offset
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E F : PointGeodesicTreeEdge a y)
    (hE0 : E.start = p) (hF0 : F.start = p)
    (hEP : ∀ t, E.curve t ∈ P) (hFP : ∀ t, F.curve t ∈ P)
    (ρ : ℝ → ℂ)
    (hFcurve : ∀ t : unitInterval, F.curve t = ρ (pointActualEdgeLength F * t.1))
    {ε ξ : ℝ} (hε : 0 < ε) (hξ : ξ ∈ Icc C.lo C.hi)
    (hclean : ∀ u ∈ Ioo (0 : ℝ) ε,
      C.chart (ρ u) = pointRadialSectorPoint u ξ) :
    C.actualPhysicalDirection ha y hadm E F hE0 hF0 hEP hFP =
      (1 + coalescedPointExponent a y p / 2) *
        |C.actualInitialRawAngle ha y hadm E hE0 hEP - ξ| := by
  have href := C.reference_angle_eq_actual_clean_germ ha y hadm F hF0 hFP ρ hFcurve hε hξ hclean
  unfold PointRetainedConeNeighborhood.actualPhysicalDirection
  rw [href]
  ring

end RepulsiveCoulomb
