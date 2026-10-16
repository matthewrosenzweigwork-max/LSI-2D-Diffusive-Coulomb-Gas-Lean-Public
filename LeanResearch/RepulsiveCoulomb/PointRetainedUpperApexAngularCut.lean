import LeanResearch.RepulsiveCoulomb.PointRetainedApexAngularCut

/-! SOURCE-ONLY, NOT COMPILED. The second genuine old-endpoint case. This avoids
postulating that the clean bottom ray chooses the lower endpoint, and avoids
any reflection or orientation convention for the ambient cone chart. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem retainedUpperApex_radial_interval_subtract
    {R lo cut hi : ℝ} (hR : 0 ≤ R) (hlc : lo ≤ cut) (hch : cut ≤ hi)
    (hwidth : hi - lo < 2 * Real.pi) :
    pointClosedRadialInterval R lo hi \
      (pointClosedRadialInterval R cut hi \ pointClosedRadialInterval R cut cut) =
      pointClosedRadialInterval R lo cut := by
  have hinter := retainedApex_radial_interval_inter hR hlc hch hwidth
  ext z
  constructor
  · rintro ⟨⟨r,hr,θ,hθ,he⟩,hnot⟩
    by_cases hθc : θ ≤ cut
    · exact ⟨r,hr,θ,⟨hθ.1,hθc⟩,he⟩
    · have hzhi : z ∈ pointClosedRadialInterval R cut hi :=
        ⟨r,hr,θ,⟨le_of_not_ge hθc,hθ.2⟩,he⟩
      have hzcut : z ∈ pointClosedRadialInterval R cut cut := by
        by_contra hzcut
        exact hnot ⟨hzhi,hzcut⟩
      obtain ⟨s,hs,φ,hφ,heφ⟩ := hzcut
      exact ⟨s,hs,φ,⟨hlc.trans hφ.1,hφ.2⟩,heφ⟩
  · intro hz
    refine ⟨?_,?_⟩
    · obtain ⟨r,hr,θ,hθ,he⟩ := hz
      exact ⟨r,hr,θ,⟨hθ.1,hθ.2.trans hch⟩,he⟩
    · intro hw
      exact hw.2 (hinter ▸ And.intro hz hw.1)

namespace PointRetainedConeNeighborhood
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q S T : Set ℂ} {p : ℂ}

def retainedUpperApexCut (C : PointRetainedConeNeighborhood a y P p)
    {cut : ℝ} (hlc : C.lo < cut) (hch : cut ≤ C.hi)
    (hproper : C.hi - C.lo < 2 * Real.pi)
    (hQ : Q = P \ (S \ T))
    (hS : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval C.radius cut C.hi))
    (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval C.radius cut cut)) :
    PointRetainedConeNeighborhood a y Q p where
  chart := C.chart
  radius := C.radius
  radius_pos := C.radius_pos
  center := C.center
  source := C.source
  onto := C.onto
  metric := C.metric
  lo := C.lo
  hi := cut
  width_pos := hlc
  width_le_full := by linarith [C.width_le_full]
  retained := by
    intro z hz
    rw [hQ]
    change (z ∈ P ∧ ¬ (z ∈ S ∧ z ∉ T)) ↔ _
    rw [C.retained z hz,hS z hz,hT z hz]
    exact Iff.of_eq (congrArg (fun V : Set ℂ ↦ C.chart z ∈ V)
      (retainedUpperApex_radial_interval_subtract C.radius_pos.le hlc.le hch hproper))

theorem retainedUpperApexCut_width (C : PointRetainedConeNeighborhood a y P p)
    {cut : ℝ} (hlc : C.lo < cut) (hch : cut ≤ C.hi)
    (hproper : C.hi - C.lo < 2 * Real.pi)
    (hQ : Q = P \ (S \ T))
    (hS : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval C.radius cut C.hi))
    (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval C.radius cut cut)) :
    (C.retainedUpperApexCut hlc hch hproper hQ hS hT).flatPhysicalWidth =
      C.flatPhysicalWidth - (coalescedPointExponent a y p / 2 + 1) * (C.hi-cut) := by
  change (coalescedPointExponent a y p / 2 + 1) * (cut-C.lo) =
    (coalescedPointExponent a y p / 2 + 1) * (C.hi-C.lo) -
      (coalescedPointExponent a y p / 2 + 1) * (C.hi-cut)
  ring

theorem retainedUpperApexCut_admissible (C : PointRetainedConeNeighborhood a y P p)
    (hC : C.Admissible) {cut : ℝ} (hlc : C.lo < cut) (hch : cut ≤ C.hi)
    (hproper : C.hi - C.lo < 2 * Real.pi)
    (hQ : Q = P \ (S \ T))
    (hS : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval C.radius cut C.hi))
    (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval C.radius cut cut)) :
    (C.retainedUpperApexCut hlc hch hproper hQ hS hT).Admissible := by
  have hk : 0 ≤ coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  have hg := mul_nonneg hk (sub_nonneg.mpr hch)
  unfold Admissible at hC ⊢
  change Real.pi ≤ (coalescedPointExponent a y p / 2 + 1) * (2 * Real.pi - (cut-C.lo))
  nlinarith

end PointRetainedConeNeighborhood
end RepulsiveCoulomb
