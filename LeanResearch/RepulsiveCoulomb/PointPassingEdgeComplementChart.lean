import LeanResearch.RepulsiveCoulomb.PointRetainedApexAngularCut
import LeanResearch.RepulsiveCoulomb.PointFlatLinkConeDisk

/-!
SOURCE-ONLY DRAFT, NOT COMPILED. Complementary FULL interval at a newly exposed
old interior point. The removed set has an actual normalized occupied interval;
the new chart, complementary width, signed atom and admissibility are outputs.
No restriction of the retained physical width to pi is made.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem passingEdge_polar_two_pi (r : ℝ) :
    pointRadialSectorPoint r (2*Real.pi) = pointRadialSectorPoint r 0 := by
  unfold pointRadialSectorPoint
  rw [show 2*Real.pi = 0 + 2*Real.pi by ring,Circle.exp_add_two_pi]

private theorem passingEdge_full_disk (R : ℝ) :
    pointClosedRadialInterval R 0 (2*Real.pi) = {z : ℂ | ‖z‖ ≤ R} := by
  ext z
  constructor
  · rintro ⟨r,hr,θ,hθ,he⟩
    change ‖z‖ ≤ R
    rw [he,pointRadialSectorPoint_norm hr.1]
    exact hr.2
  · intro hz
    change ‖z‖ ≤ R at hz
    by_cases hz0 : z = 0
    · refine ⟨0,⟨le_rfl,?_⟩,0,⟨le_rfl,by positivity⟩,?_⟩
      · simpa only [hz0,norm_zero] using hz
      · simp only [hz0,pointRadialSectorPoint_zero]
    · obtain ⟨θ,hθ,he⟩ := exists_pointRadialSectorPoint_angle z hz0
      exact ⟨‖z‖,⟨norm_nonneg z,hz⟩,θ,⟨hθ.1,hθ.2.le⟩,he.symm⟩

/-- Correct intersection of two complementary closed angular intervals.
The wraparound ray at 0=2*pi is indispensable. -/
theorem passingEdge_complementary_intervals_inter {R cut : ℝ}
    (hR : 0 ≤ R) (hc : 0 < cut) (hc2 : cut < 2*Real.pi) :
    pointClosedRadialInterval R 0 cut ∩ pointClosedRadialInterval R cut (2*Real.pi) =
      pointClosedRadialInterval R 0 0 ∪ pointClosedRadialInterval R cut cut := by
  ext z
  constructor
  · rintro ⟨⟨r,hr,θ,hθ,heθ⟩,⟨s,hs,φ,hφ,heφ⟩⟩
    by_cases hr0 : r = 0
    · left
      exact ⟨0,⟨le_rfl,hR⟩,0,⟨le_rfl,le_rfl⟩,by
        simpa only [hr0,pointRadialSectorPoint_zero] using heθ⟩
    · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
      by_cases hφ2 : φ = 2*Real.pi
      · left
        refine ⟨s,hs,0,⟨le_rfl,le_rfl⟩,?_⟩
        simpa only [hφ2,passingEdge_polar_two_pi] using heφ
      · have hφlt : φ < 2*Real.pi := lt_of_le_of_ne hφ.2 hφ2
        have hrs : r = s := by
          have hn := congrArg norm (heθ.symm.trans heφ)
          simpa only [pointRadialSectorPoint_norm hr.1,
            pointRadialSectorPoint_norm hs.1] using hn
        have hphase : Circle.exp θ = Circle.exp φ := by
          apply Subtype.ext
          subst s
          exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hrpos.ne') (heθ.symm.trans heφ)
        have hθφ := (Circle.exp_injOn_Ico (a := 0) (b := 2*Real.pi) (by linarith))
          ⟨hθ.1,hθ.2.trans_lt hc2⟩ ⟨hc.le.trans hφ.1,hφlt⟩ hphase
        have hθcut : θ = cut := by linarith [hθ.2,hφ.1]
        right
        exact ⟨r,hr,cut,⟨le_rfl,le_rfl⟩,by simpa only [hθcut] using heθ⟩
  · rintro (⟨r,hr,θ,hθ,he⟩ | ⟨r,hr,θ,hθ,he⟩)
    · have hθ0 : θ = 0 := le_antisymm hθ.2 hθ.1
      subst θ
      exact ⟨⟨r,hr,0,⟨le_rfl,hc.le⟩,he⟩,
        ⟨r,hr,2*Real.pi,⟨hc2.le,le_rfl⟩,he.trans (passingEdge_polar_two_pi r).symm⟩⟩
    · have hθc : θ = cut := le_antisymm hθ.2 hθ.1
      subst θ
      exact ⟨⟨r,hr,cut,⟨hc.le,le_rfl⟩,he⟩,⟨r,hr,cut,⟨le_rfl,hc2.le⟩,he⟩⟩

/-- Literal closed-disk subtraction leaves the complementary whole interval,
including both edge germs and the center. -/
theorem passingEdge_radial_disk_subtract {R cut : ℝ}
    (hR : 0 ≤ R) (hc : 0 < cut) (hc2 : cut < 2*Real.pi) :
    {z : ℂ | ‖z‖ ≤ R} \
      (pointClosedRadialInterval R 0 cut \
        (pointClosedRadialInterval R 0 0 ∪ pointClosedRadialInterval R cut cut)) =
      pointClosedRadialInterval R cut (2*Real.pi) := by
  rw [← passingEdge_full_disk]
  have hinter := passingEdge_complementary_intervals_inter hR hc hc2
  ext z
  constructor
  · rintro ⟨⟨r,hr,θ,hθ,he⟩,hnot⟩
    by_cases hcθ : cut ≤ θ
    · exact ⟨r,hr,θ,⟨hcθ,hθ.2⟩,he⟩
    · have hlo : z ∈ pointClosedRadialInterval R 0 cut :=
        ⟨r,hr,θ,⟨hθ.1,le_of_not_ge hcθ⟩,he⟩
      have hedge : z ∈ pointClosedRadialInterval R 0 0 ∪
          pointClosedRadialInterval R cut cut := by
        by_contra he
        exact hnot ⟨hlo,he⟩
      exact (hinter.symm ▸ hedge).2
  · intro hz
    refine ⟨?_,?_⟩
    · obtain ⟨r,hr,θ,hθ,he⟩ := hz
      exact ⟨r,hr,θ,⟨hc.le.trans hθ.1,hθ.2⟩,he⟩
    · intro hw
      exact hw.2 (hinter ▸ And.intro hw.1 hz)

namespace PointFlatLinkConeDisk
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q S T : Set ℂ} {p : ℂ}

/-- Construct the actual complementary retained chart. P fills this small
ambient disk; S is its occupied halfdisk; T is the two boundary radial germs.
The source-localization step proving hS and hT must precede this constructor. -/
def passingEdgeComplement (C : PointFlatLinkConeDisk a y p)
    {cut : ℝ} (hc : 0 < cut) (hc2 : cut < 2*Real.pi)
    (hQ : Q = P \ (S \ T))
    (hP : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius → z ∈ P)
    (hS : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval C.radius 0 cut))
    (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval C.radius 0 0 ∪
        pointClosedRadialInterval C.radius cut cut)) :
    PointRetainedConeNeighborhood a y Q p where
  chart := C.chart
  radius := C.radius
  radius_pos := C.radius_pos
  center := C.center
  source := C.source
  onto := C.onto
  metric := C.metric
  lo := cut
  hi := 2*Real.pi
  width_pos := hc2
  width_le_full := by linarith
  retained := by
    intro z hz
    have hn : C.chart z ∈ {w : ℂ | ‖w‖ ≤ C.radius} :=
      (C.norm_chart hz).trans_le hz
    have hid := Iff.of_eq (congrArg (fun V : Set ℂ ↦ C.chart z ∈ V)
      (passingEdge_radial_disk_subtract C.radius_pos.le hc hc2))
    rw [hQ]
    change (z ∈ P ∧ ¬ (z ∈ S ∧ z ∉ T)) ↔ _
    rw [hS z hz,hT z hz]
    simpa only [Set.mem_diff,hP z hz,hn,true_and] using hid

/-- Physical width, all-point coefficient, and admissibility are consequences
of the actual occupied halfdisk angle pi. -/
theorem passingEdgeComplement_width_atom_admissible (C : PointFlatLinkConeDisk a y p)
    {cut : ℝ} (hc : 0 < cut) (hc2 : cut < 2*Real.pi)
    (hQ : Q = P \ (S \ T))
    (hP : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius → z ∈ P)
    (hS : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval C.radius 0 cut))
    (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius →
      (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval C.radius 0 0 ∪
        pointClosedRadialInterval C.radius cut cut))
    (hhalf : (coalescedPointExponent a y p/2+1)*cut = Real.pi) :
    let E := C.passingEdgeComplement hc hc2 hQ hP hS hT
    E.flatPhysicalWidth = (coalescedPointExponent a y p/2+1)*(2*Real.pi)-Real.pi ∧
      Real.pi-E.flatPhysicalWidth = -Real.pi*coalescedPointExponent a y p ∧
      E.Admissible := by
  dsimp only
  have hw : (C.passingEdgeComplement hc hc2 hQ hP hS hT).flatPhysicalWidth =
      (coalescedPointExponent a y p/2+1)*(2*Real.pi)-Real.pi := by
    change (coalescedPointExponent a y p/2+1)*(2*Real.pi-cut) = _
    nlinarith [hhalf]
  refine ⟨hw,?_,?_⟩
  · rw [hw]
    ring
  · change Real.pi ≤ (coalescedPointExponent a y p/2+1)*(2*Real.pi-(2*Real.pi-cut))
    nlinarith [hhalf]

end PointFlatLinkConeDisk
end RepulsiveCoulomb
