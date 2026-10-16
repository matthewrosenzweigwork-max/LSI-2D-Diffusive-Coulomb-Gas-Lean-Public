module

public import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart

@[expose] public section

/-! SOURCE-ONLY, NOT COMPILED. Restrict an existing WHOLE retained chart to a
smaller positive closed metric disk, preserving its entire ordered interval. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem retainedApex_restrict_interval {r R lo hi : ℝ} (hrR : r ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    z ∈ pointClosedRadialInterval R lo hi ↔ z ∈ pointClosedRadialInterval r lo hi := by
  constructor
  · rintro ⟨s,hs,θ,hθ,he⟩
    refine ⟨s,⟨hs.1,?_⟩,θ,hθ,he⟩
    rw [he,pointRadialSectorPoint_norm hs.1] at hz
    exact hz
  · rintro ⟨s,hs,θ,hθ,he⟩
    exact ⟨s,⟨hs.1,hs.2.trans hrR⟩,θ,hθ,he⟩

namespace PointRetainedConeNeighborhood
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}

def retainedApexRestrict (C : PointRetainedConeNeighborhood a y P p)
    {r : ℝ} (hr : 0 < r) (hrC : r ≤ C.radius) :
    PointRetainedConeNeighborhood a y P p := by
  have hnorm (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius) :
      ‖C.chart z‖ = (pointSmoothConformalEDist a y z p).toReal := by
    have hp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
      rw [pointSmoothConformalEDist_self,ENNReal.toReal_zero]
      exact C.radius_pos.le
    rw [C.metric z hz p hp,C.center,pointClassicalConeDist_apex]
  exact
    { chart := C.chart
      radius := r
      radius_pos := hr
      center := C.center
      source := fun z hz ↦ C.source (hz.trans hrC)
      onto := by
        refine ⟨?_,?_,?_⟩
        · intro z hz
          change ‖C.chart z‖ ≤ r
          rw [hnorm z (hz.trans hrC)]
          exact hz
        · intro z hz w hw he
          exact C.onto.injOn (hz.trans hrC) (hw.trans hrC) he
        · intro w hw
          obtain ⟨z,hz,he⟩ := C.onto.surjOn (hw.trans hrC)
          refine ⟨z,?_,he⟩
          change (pointSmoothConformalEDist a y z p).toReal ≤ r
          rw [← hnorm z hz,he]
          exact hw
      metric := fun z hz w hw ↦ C.metric z (hz.trans hrC) w (hw.trans hrC)
      lo := C.lo
      hi := C.hi
      width_pos := C.width_pos
      width_le_full := C.width_le_full
      retained := by
        intro z hz
        exact (C.retained z (hz.trans hrC)).trans
          (retainedApex_restrict_interval hrC ((hnorm z (hz.trans hrC)).trans_le hz)) }

@[simp] theorem retainedApexRestrict_width (C : PointRetainedConeNeighborhood a y P p)
    {r : ℝ} (hr : 0 < r) (hrC : r ≤ C.radius) :
    (C.retainedApexRestrict hr hrC).flatPhysicalWidth = C.flatPhysicalWidth := rfl

@[simp] theorem retainedApexRestrict_admissible (C : PointRetainedConeNeighborhood a y P p)
    {r : ℝ} (hr : 0 < r) (hrC : r ≤ C.radius) :
    (C.retainedApexRestrict hr hrC).Admissible ↔ C.Admissible := Iff.rfl

end PointRetainedConeNeighborhood
end RepulsiveCoulomb
