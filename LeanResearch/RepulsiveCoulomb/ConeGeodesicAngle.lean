module

public import LeanResearch.RepulsiveCoulomb.PointClassicalConeDisk

@[expose] public section

/-! A minimizing path through a positive-curvature-excess cone vertex must leave
at angular separation at least pi. Derived from the actual metric cosine formula. -/
noncomputable section
namespace RepulsiveCoulomb

theorem classicalCone_apex_triangle_eq_iff {α : ℝ} (hα : 0 < α)
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    @dist ℂ (classicalConeMetricSpace α hα.le).toDist u v = ‖u‖ + ‖v‖ ↔
      Real.pi ≤ (α + 1) * |Complex.arg (v / u)| := by
  have hru := norm_pos_iff.mpr hu
  have hrv := norm_pos_iff.mpr hv
  constructor
  · intro he
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hcos : -1 < Real.cos ((α + 1) * |Complex.arg (v / u)|) := by
      simpa only [Real.cos_pi] using Real.cos_lt_cos_of_nonneg_of_le_pi
        (show 0 ≤ (α + 1) * |Complex.arg (v / u)| by positivity) le_rfl hlt
    have hd := classicalCone_distance_formula hα u v
    rw [min_eq_right hlt.le] at hd
    have hrad : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * ‖u‖ * ‖v‖ *
        Real.cos ((α + 1) * |Complex.arg (v / u)|) := by
      apply Real.sqrt_pos.mp
      rw [← hd, he]
      positivity
    have hs := congrArg (fun t : ℝ => t ^ 2) hd
    rw [Real.sq_sqrt hrad.le, he] at hs
    have hcpos : 0 < Real.cos ((α + 1) * |Complex.arg (v / u)|) + 1 := by linarith
    have hp : 0 < 2 * ‖u‖ * ‖v‖ *
        (Real.cos ((α + 1) * |Complex.arg (v / u)|) + 1) := by positivity
    nlinarith
  · intro hang
    rw [classicalCone_distance_formula hα, min_eq_left hang, Real.cos_pi]
    have he : ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * ‖u‖ * ‖v‖ * (-1) = (‖u‖ + ‖v‖) ^ 2 := by ring
    rw [he, Real.sqrt_sq (by positivity)]

/-- In any proved point-cone chart, a distance-minimizing passage through a
positive-exponent puncture obeys the cone angle restriction. -/
theorem pointConformal_angle_at_positive_puncture {m : ℕ} {a : Fin m → ℝ}
    (y : Fin m → ℂ) {p u v : ℂ} (hp : 0 < coalescedPointExponent a y p)
    (e : OpenPartialHomeomorph ℂ ℂ) (hep : e p = 0)
    (hsource : p ∈ e.source) (hu : u ∈ e.source) (hv : v ∈ e.source)
    (hup : u ≠ p) (hvp : v ≠ p)
    (hd : ∀ x ∈ e.source, ∀ z ∈ e.source,
      (pointSmoothConformalEDist a y x z).toReal = pointClassicalConeDist a y p (e x) (e z))
    (hmin : (pointSmoothConformalEDist a y u v).toReal =
      (pointSmoothConformalEDist a y u p).toReal + (pointSmoothConformalEDist a y v p).toReal) :
    Real.pi ≤ (coalescedPointExponent a y p / 2 + 1) * |Complex.arg (e v / e u)| := by
  have heu : e u ≠ 0 := by
    intro hz
    exact hup (e.injOn hu hsource (hz.trans hep.symm))
  have hev : e v ≠ 0 := by
    intro hz
    exact hvp (e.injOn hv hsource (hz.trans hep.symm))
  have heq : pointClassicalConeDist a y p (e u) (e v) = ‖e u‖ + ‖e v‖ := by
    rw [← hd u hu v hv, hmin, hd u hu p hsource, hd v hv p hsource, hep,
      pointClassicalConeDist_apex, pointClassicalConeDist_apex]
  exact (classicalCone_apex_triangle_eq_iff (by positivity : 0 < coalescedPointExponent a y p / 2)
    heu hev).mp heq

/-- The local chart required by the preceding lemma exists for every admissible
configuration and positive-exponent location. -/
theorem exists_pointConformal_minimizing_angle_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ)
    (hp : 0 < coalescedPointExponent a y p) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e p = 0 ∧
      ∀ u ∈ e.source, ∀ v ∈ e.source, u ≠ p → v ≠ p →
        (pointSmoothConformalEDist a y u v).toReal =
          (pointSmoothConformalEDist a y u p).toReal +
            (pointSmoothConformalEDist a y v p).toReal →
        Real.pi ≤ (coalescedPointExponent a y p / 2 + 1) *
          |Complex.arg (e v / e u)| := by
  obtain ⟨e, he, hep, hd⟩ := exists_pointConformal_classical_chart ha y p
  exact ⟨e, he, hep, fun u hu v hv hup hvp hmin =>
    pointConformal_angle_at_positive_puncture y hp e hep he hu hv hup hvp hd hmin⟩

end RepulsiveCoulomb
