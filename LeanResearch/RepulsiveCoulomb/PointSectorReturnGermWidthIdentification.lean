import LeanResearch.RepulsiveCoulomb.PointSectorReturnPhysicalDirectionLink

/-! Isolated, uncompiled exact supplied-sector width link. Genuine radial
formulas for the same actual rays identify the constructed raw angles. The
lower/upper cut formulas are the geometric outputs of old-interval occupancy. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

 theorem PointRetainedConeNeighborhood.actual_ray_germ_angle_unique
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hadm : C.Admissible)
    (ρ : ℝ → ℂ) {ε δ ξ η : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hξ : ξ ∈ Icc C.lo C.hi) (hη : η ∈ Icc C.lo C.hi)
    (hξgerm : ∀ u ∈ Ioo (0 : ℝ) ε,
      C.chart (ρ u) = pointRadialSectorPoint u ξ)
    (hηgerm : ∀ u ∈ Ioo (0 : ℝ) δ,
      C.chart (ρ u) = pointRadialSectorPoint u η) : ξ = η := by
  let r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := by dsimp [r]; linarith [min_le_left ε δ]
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_right ε δ]
  exact (C.retained_polar_angle_unique hadm hr hr.le hξ hη
    ((hξgerm r ⟨hr, hrε⟩).symm.trans (hηgerm r ⟨hr, hrδ⟩))).2

/-- Identify both the actual new-edge raw angle and the SAME clean reference
angle from the source-sector pointwise germs. The cut width is therefore the
actual full initial direction, for either old endpoint orientation. -/
theorem PointRetainedConeNeighborhood.sector_width_eq_actual_germ_direction
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E : PointGeodesicTreeEdge a y)
    (hE0 : E.start = p) (hEP : ∀ t, E.curve t ∈ P)
    (upper lower : ℝ → ℂ)
    (hEcurve : ∀ t : unitInterval, E.curve t = upper (pointActualEdgeLength E * t.1))
    {δ ε cut endpoint ξ β : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hβ : 0 ≤ β)
    (hcut : cut ∈ Icc C.lo C.hi) (hend : endpoint ∈ Icc C.lo C.hi)
    (hξ : ξ ∈ Icc C.lo C.hi)
    (hupper : ∀ u ∈ Ioo (0 : ℝ) δ,
      C.chart (upper u) = pointRadialSectorPoint u cut)
    (hlower : ∀ u ∈ Ioo (0 : ℝ) δ,
      C.chart (lower u) = pointRadialSectorPoint u endpoint)
    (hclean : ∀ u ∈ Ioo (0 : ℝ) ε,
      C.chart (lower u) = pointRadialSectorPoint u ξ)
    (hcutFormula :
      (endpoint = C.lo ∧ cut = C.lo + β / (1 + coalescedPointExponent a y p / 2)) ∨
      (endpoint = C.hi ∧ cut = C.hi - β / (1 + coalescedPointExponent a y p / 2))) :
    C.actualInitialRawAngle ha y hadm E hE0 hEP = cut ∧ ξ = endpoint ∧
      (1 + coalescedPointExponent a y p / 2) *
        |C.actualInitialRawAngle ha y hadm E hE0 hEP - ξ| = β := by
  have hnew := C.reference_angle_eq_actual_clean_germ ha y hadm E hE0 hEP upper hEcurve hδ hcut hupper
  have hold := C.actual_ray_germ_angle_unique hadm lower hε hδ hξ hend hclean hlower
  have hk : 0 < 1 + coalescedPointExponent a y p / 2 := by
    linarith [coalescedPointExponent_nonneg a y p]
  refine ⟨hnew, hold, ?_⟩
  rw [hnew, hold]
  rcases hcutFormula with ⟨rfl, hcut⟩ | ⟨rfl, hcut⟩
  · rw [hcut, add_sub_cancel_left, abs_of_nonneg (div_nonneg hβ hk.le)]
    exact mul_div_cancel₀ β hk.ne'
  · have he : C.hi - β / (1 + coalescedPointExponent a y p / 2) - C.hi =
        -(β / (1 + coalescedPointExponent a y p / 2)) := by ring
    rw [hcut, he, abs_neg, abs_of_nonneg (div_nonneg hβ hk.le)]
    exact mul_div_cancel₀ β hk.ne'

end RepulsiveCoulomb
