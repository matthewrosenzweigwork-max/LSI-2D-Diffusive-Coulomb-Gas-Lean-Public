import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart

/-!
SOURCE-ONLY DRAFT, NOT COMPILED. Actual angular subtraction inside an OLD
retained metric chart. The new chart is constructed, including its complete
closed-disk membership field. No new chart, new angle, curvature update, or
halfplane certificate is assumed. The remaining geometric inputs are an actual
set subtraction formula and the aligned occupied-sector and free-ray germs.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Polar coordinates are unique on an arbitrary proper closed angular interval.
The interval may be reflex; no principal-argument bound is imposed. -/
theorem retainedApex_radial_coordinates_unique
    {r s lo hi θ φ : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hwidth : hi - lo < 2 * Real.pi)
    (hθ : θ ∈ Icc lo hi) (hφ : φ ∈ Icc lo hi)
    (he : pointRadialSectorPoint r θ = pointRadialSectorPoint s φ) :
    r = s ∧ θ = φ := by
  have hrs : r = s := by
    have hn := congrArg norm he
    simpa only [pointRadialSectorPoint_norm hr.le,
      pointRadialSectorPoint_norm hs] using hn
  subst s
  have hphase : Circle.exp θ = Circle.exp φ := by
    apply Subtype.ext
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') he
  refine ⟨rfl, ?_⟩
  exact (Circle.exp_injOn_Ico (a := lo) (b := lo + 2 * Real.pi) (by linarith))
    ⟨hθ.1, by linarith [hθ.2]⟩ ⟨hφ.1, by linarith [hφ.2]⟩ hphase

/-- Literal radial intersection at the shared ray. The center is handled
explicitly rather than incorrectly treated as having a unique angle. -/
theorem retainedApex_radial_interval_inter
    {R lo cut hi : ℝ} (hR : 0 ≤ R) (hlc : lo ≤ cut) (hch : cut ≤ hi)
    (hwidth : hi - lo < 2 * Real.pi) :
    pointClosedRadialInterval R lo cut ∩ pointClosedRadialInterval R cut hi =
      pointClosedRadialInterval R cut cut := by
  ext z
  constructor
  · rintro ⟨⟨r,hr,θ,hθ,heθ⟩,⟨s,hs,φ,hφ,heφ⟩⟩
    by_cases hr0 : r = 0
    · refine ⟨0,⟨le_rfl,hR⟩,cut,⟨le_rfl,le_rfl⟩,?_⟩
      simpa only [hr0,pointRadialSectorPoint_zero] using heθ
    · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
      have he := retainedApex_radial_coordinates_unique hrpos hs.1 hwidth
        ⟨hθ.1,hθ.2.trans hch⟩ ⟨hlc.trans hφ.1,hφ.2⟩ (heθ.symm.trans heφ)
      have hθcut : θ = cut := by linarith [he.2,hθ.2,hφ.1]
      exact ⟨r,hr,cut,⟨le_rfl,le_rfl⟩,by simpa only [hθcut] using heθ⟩
  · rintro ⟨r,hr,θ,hθ,he⟩
    have hθcut : θ = cut := le_antisymm hθ.2 hθ.1
    subst θ
    exact ⟨⟨r,hr,cut,⟨hlc,le_rfl⟩,he⟩,⟨r,hr,cut,⟨le_rfl,hch⟩,he⟩⟩

/-- Full radial set subtraction with the free ray retained. This is the
local set operation of a retained-apex cut, not just an angle calculation. -/
theorem retainedApex_radial_interval_subtract
    {R lo cut hi : ℝ} (hR : 0 ≤ R) (hlc : lo ≤ cut) (hch : cut ≤ hi)
    (hwidth : hi - lo < 2 * Real.pi) :
    pointClosedRadialInterval R lo hi \
      (pointClosedRadialInterval R lo cut \ pointClosedRadialInterval R cut cut) =
      pointClosedRadialInterval R cut hi := by
  have hinter := retainedApex_radial_interval_inter hR hlc hch hwidth
  ext z
  constructor
  · rintro ⟨⟨r,hr,θ,hθ,he⟩,hnot⟩
    by_cases hθc : cut ≤ θ
    · exact ⟨r,hr,θ,⟨hθc,hθ.2⟩,he⟩
    · have hzlo : z ∈ pointClosedRadialInterval R lo cut :=
        ⟨r,hr,θ,⟨hθ.1,(le_of_not_ge hθc)⟩,he⟩
      have hzcut : z ∈ pointClosedRadialInterval R cut cut := by
        by_contra hzcut
        exact hnot ⟨hzlo,hzcut⟩
      obtain ⟨s,hs,φ,hφ,heφ⟩ := hzcut
      exact ⟨s,hs,φ,⟨hφ.1,hφ.2.trans hch⟩,heφ⟩
  · intro hz
    refine ⟨?_,?_⟩
    · obtain ⟨r,hr,θ,hθ,he⟩ := hz
      exact ⟨r,hr,θ,⟨hlc.trans hθ.1,hθ.2⟩,he⟩
    · intro hw
      exact hw.2 (hinter ▸ And.intro hw.1 hz)

namespace PointRetainedConeNeighborhood
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q S T : Set ℂ} {p : ℂ}

/-- Construct every field of the retained-apex chart in the same old ambient
cone disk. In particular it retains the FULL interval [cut,hi], even when its
physical width exceeds pi. The occupancy inputs describe S and T, not Q. -/
def retainedApexCut (C : PointRetainedConeNeighborhood a y P p)
    {cut : ℝ} (hlc : C.lo ≤ cut) (hch : cut < C.hi)
    (hproper : C.hi - C.lo < 2 * Real.pi)
    (hQ : Q = P \ (S \ T))
    (hS : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval C.radius C.lo cut))
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
  lo := cut
  hi := C.hi
  width_pos := hch
  width_le_full := by linarith [C.width_le_full]
  retained := by
    intro z hz
    rw [hQ]
    change (z ∈ P ∧ ¬ (z ∈ S ∧ z ∉ T)) ↔ _
    rw [C.retained z hz,hS z hz,hT z hz]
    exact Iff.of_eq (congrArg (fun V : Set ℂ ↦ C.chart z ∈ V)
      (retainedApex_radial_interval_subtract C.radius_pos.le hlc hch.le hproper))

/-- Exact retained width, proved from the constructed endpoints. -/
theorem retainedApexCut_width (C : PointRetainedConeNeighborhood a y P p)
    {cut : ℝ} (hlc : C.lo ≤ cut) (hch : cut < C.hi)
    (hproper : C.hi - C.lo < 2 * Real.pi)
    (hQ : Q = P \ (S \ T))
    (hS : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval C.radius C.lo cut))
    (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval C.radius cut cut)) :
    (C.retainedApexCut hlc hch hproper hQ hS hT).flatPhysicalWidth =
      C.flatPhysicalWidth - (coalescedPointExponent a y p / 2 + 1) * (cut - C.lo) := by
  change (coalescedPointExponent a y p / 2 + 1) * (C.hi - cut) =
    (coalescedPointExponent a y p / 2 + 1) * (C.hi - C.lo) -
      (coalescedPointExponent a y p / 2 + 1) * (cut - C.lo)
  ring

/-- Admissibility survives actual removal: the removed-side interval grows. -/
theorem retainedApexCut_admissible (C : PointRetainedConeNeighborhood a y P p)
    (hC : C.Admissible) {cut : ℝ} (hlc : C.lo ≤ cut) (hch : cut < C.hi)
    (hproper : C.hi - C.lo < 2 * Real.pi)
    (hQ : Q = P \ (S \ T))
    (hS : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval C.radius C.lo cut))
    (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval C.radius cut cut)) :
    (C.retainedApexCut hlc hch hproper hQ hS hT).Admissible := by
  have hk : 0 ≤ coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  have hg := mul_nonneg hk (sub_nonneg.mpr hlc)
  unfold Admissible at hC ⊢
  change Real.pi ≤ (coalescedPointExponent a y p / 2 + 1) * (2 * Real.pi - (C.hi-cut))
  nlinarith

/-- The initial signed atom increments by exactly the occupied physical angle.
This formula works at ambient exponent zero and at arbitrary reflex old links. -/
theorem retainedApexCut_turn (C : PointRetainedConeNeighborhood a y P p)
    {cut β νp : ℝ} (hlc : C.lo ≤ cut) (hch : cut < C.hi)
    (hproper : C.hi - C.lo < 2 * Real.pi)
    (hQ : Q = P \ (S \ T))
    (hS : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval C.radius C.lo cut))
    (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval C.radius cut cut))
    (hβ : (coalescedPointExponent a y p / 2 + 1) * (cut-C.lo) = β)
    (hν : νp = Real.pi - C.flatPhysicalWidth) :
    Real.pi - (C.retainedApexCut hlc hch hproper hQ hS hT).flatPhysicalWidth = νp + β := by
  rw [C.retainedApexCut_width hlc hch hproper hQ hS hT,hβ,hν]
  ring

end PointRetainedConeNeighborhood
end RepulsiveCoulomb
