import LeanResearch.RepulsiveCoulomb.PointFlatHalfDiskEdgeOccupancy
import LeanResearch.RepulsiveCoulomb.PointPassingEdgeComplementChart

/-! NEW SOURCE-ONLY, UNCOMPILED. Actual halfdisk occupancy and its actual
diameter image construct a FULL complementary chart. The given set germs refer
to the supplied local map, not to a new chart or an asserted angle update. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def PointFlatLinkConeDisk.translatedRestrict
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {r : ℝ} (hr : 0<r) (hrC : r≤C.radius) :
    PointFlatLinkConeDisk a y p where
  chart:=C.chart
  radius:=r
  radius_pos:=hr
  center:=C.center
  source:=fun _ hz ↦ C.source (hz.trans hrC)
  onto:=by
    refine ⟨?_,?_,?_⟩
    · intro z hz
      change ‖C.chart z‖ ≤ r
      rw [C.norm_chart (hz.trans hrC)]
      exact hz
    · intro z hz w hw he
      exact C.onto.injOn (hz.trans hrC) (hw.trans hrC) he
    · intro w hw
      obtain ⟨z,hz,he⟩:=C.onto.surjOn (hw.trans hrC)
      refine ⟨z,?_,he⟩
      change (pointSmoothConformalEDist a y z p).toReal ≤ r
      rw [← C.norm_chart hz,he]
      exact hw
  metric:=fun z hz w hw ↦ C.metric z (hz.trans hrC) w (hw.trans hrC)

/-- Every exposed interior atom keeps its exact old coefficient -pi*a,
including marked points of arbitrary nonnegative exponent. -/
theorem pointActualHalfDisk_construct_complementary_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {L : ℝ} (hL : 0<L) (f : flatLinkSectorDisk Real.pi L → ℂ)
    (hd : ∀ x z,(pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z)
    {P Q S T : Set ℂ}
    (hP : ∀ z,(pointSmoothConformalEDist a y z
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal≤L → z∈P)
    (hS : ∀ z,(pointSmoothConformalEDist a y z
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal≤L →
      (z∈S ↔ z∈range f))
    (hT : ∀ z,(pointSmoothConformalEDist a y z
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal≤L →
      (z∈T ↔ z∈f '' {w | w.1.im=0}))
    (hQ : Q=P \ (S \ T)) :
    ∃ E : PointRetainedConeNeighborhood a y Q
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)),
      E.flatPhysicalWidth=
        (coalescedPointExponent a y (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))/2+1)*
          (2*Real.pi)-Real.pi ∧
      Real.pi-E.flatPhysicalWidth=
        -Real.pi*coalescedPointExponent a y (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)) ∧
      E.Admissible := by
  obtain ⟨C,ρ,hρ,hρL,hρC,hocc,hedge,hhalf⟩:=
    exists_pointFlatHalfDisk_occupied_and_edge_germs ha y hL f hd
  let p:=f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)
  let k:=coalescedPointExponent a y p/2+1
  let cut:=Real.pi/k
  have hk : 0<k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hk1 : 1≤k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hc : 0<cut := div_pos Real.pi_pos hk
  have hcpi : cut≤Real.pi := (div_le_iff₀ hk).mpr (by nlinarith [Real.pi_pos])
  have hc2 : cut<2*Real.pi := by linarith [Real.pi_pos]
  let D:=C.translatedRestrict hρ hρC
  have hDP (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal≤ρ) : z∈P :=
    hP z (hz.trans hρL)
  have hDS (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal≤ρ) :
      z∈S ↔ C.chart z∈pointClosedRadialInterval ρ 0 cut :=
    (hS z (hz.trans hρL)).trans (hocc z hz)
  have hDT (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal≤ρ) :
      z∈T ↔ C.chart z∈pointClosedRadialInterval ρ 0 0 ∪ pointClosedRadialInterval ρ cut cut :=
    (hT z (hz.trans hρL)).trans (hedge z hz)
  let E:=D.passingEdgeComplement hc hc2 hQ hDP hDS hDT
  exact ⟨E,D.passingEdgeComplement_width_atom_admissible hc hc2 hQ hDP hDS hDT hhalf⟩

end RepulsiveCoulomb
