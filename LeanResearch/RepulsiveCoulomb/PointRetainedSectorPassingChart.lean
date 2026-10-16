module

public import LeanResearch.RepulsiveCoulomb.RetainedSectorPassingHalfDisk
public import LeanResearch.RepulsiveCoulomb.PointFlatHalfDiskEdgeOccupancy
public import LeanResearch.RepulsiveCoulomb.PointPassingEdgeComplementChart

@[expose] public section

/-!
SOURCE-ONLY, NOT COMPILED. Construct the new retained chart at EVERY nonapex
free-sector-edge point which is in the old interior. The literal source
halfdisk, exact local sector image, exact free-edge germ and occupied angle pi
are all derived from the actual supplied sector isometry.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

private def retainedPassingRestrict
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {ρ : ℝ} (hρ : 0 < ρ) (hρC : ρ ≤ C.radius) :
    PointFlatLinkConeDisk a y p where
  chart := C.chart
  radius := ρ
  radius_pos := hρ
  center := C.center
  source := fun z hz ↦ C.source (hz.trans hρC)
  onto := by
    refine ⟨?_,?_,?_⟩
    · intro z hz
      change ‖C.chart z‖ ≤ ρ
      rw [C.norm_chart (hz.trans hρC)]
      exact hz
    · intro z hz w hw he
      exact C.onto.injOn (hz.trans hρC) (hw.trans hρC) he
    · intro w hw
      obtain ⟨z,hz,he⟩ := C.onto.surjOn (hw.trans hρC)
      refine ⟨z,?_,he⟩
      change (pointSmoothConformalEDist a y z p).toReal ≤ ρ
      rw [← C.norm_chart hz,he]
      exact hw
  metric := fun z hz w hw ↦ C.metric z (hz.trans hρC) w (hw.trans hρC)

/-- Exact equality of the actual global free-ray germ and the embedded
halfdisk's straight source edge. Distance preservation excludes distant points. -/
theorem pointRetainedSectorPassingHalfDisk_edge_germ
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ)
    {β r L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) (hLr : L < r) (hr : 0 ≤ r)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {z : ℂ}
    (hz : (pointSmoothConformalEDist a y z
      (σ (retainedApexUpperSource hβ.le hβπ ⟨r,hr⟩))).toReal ≤ L) :
    z ∈ range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)) ↔
      z ∈ (σ ∘ retainedSectorPassingHalfDisk hβ hβπ hLsin) '' {w | w.1.im = 0} := by
  constructor
  · rintro ⟨u,rfl⟩
    rw [hσ] at hz
    obtain ⟨w,hw⟩ := retainedSectorPassingHalfDisk_local_coverage hβ hβπ hLsin hr
      (retainedApexUpperSource hβ.le hβπ u) hz
    have hwe : w.1.im = 0 :=
      (retainedSectorPassingHalfDisk_mem_upper_iff hβ hβπ hLsin hLr w).mp ⟨u,hw.symm⟩
    exact ⟨w,hwe,congrArg σ hw⟩
  · rintro ⟨w,hwe,rfl⟩
    obtain ⟨u,hu⟩ :=
      (retainedSectorPassingHalfDisk_mem_upper_iff hβ hβπ hLsin hLr w).mpr hwe
    exact ⟨u,congrArg σ hu⟩

/-- All full retained-chart fields, the complementary physical width, exact
old interior signed atom and admissibility are constructed from actual sector
geometry. The only global topological input is the separately proved literal
set identity Q=P\(S\T); no local occupancy or new angle is assumed. -/
theorem pointRetainedSector_construct_passing_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P Q : Set ℂ}
    (hQ : Q = P \ (range σ \
      range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u))))
    (r : NNReal) (hr : 0 < (r:ℝ))
    (hp : σ (retainedApexUpperSource hβ.le hβπ r) ∈ interior P) :
    ∃ E : PointRetainedConeNeighborhood a y Q (σ (retainedApexUpperSource hβ.le hβπ r)),
      E.flatPhysicalWidth =
        (coalescedPointExponent a y (σ (retainedApexUpperSource hβ.le hβπ r))/2+1)*
          (2*Real.pi)-Real.pi ∧
      Real.pi-E.flatPhysicalWidth =
        -Real.pi*coalescedPointExponent a y (σ (retainedApexUpperSource hβ.le hβπ r)) ∧
      E.Admissible := by
  let p := σ (retainedApexUpperSource hβ.le hβπ r)
  have hn : P ∈ @nhds ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace p := by
    rw [pointSmoothConformalMetricSpace_topology ha y]
    exact mem_interior_iff_mem_nhds.mp hp
  obtain ⟨ε,hε,hball⟩ :=
    (@Metric.nhds_basis_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p).mem_iff.mp hn
  obtain ⟨L₀,hL₀,hL₀r,hL₀sin⟩ := retainedSectorPassingHalfDisk_exists_radius hβ hβπ hr
  let L := min L₀ (ε/2)
  have hL : 0 < L := lt_min hL₀ (half_pos hε)
  have hLL₀ : L ≤ L₀ := min_le_left _ _
  have hLε : L ≤ ε/2 := min_le_right _ _
  have hLr : L < (r:ℝ) := hLL₀.trans_lt hL₀r
  have hLsin : β < Real.pi → L ≤ (r:ℝ)*Real.sin β := fun h ↦ hLL₀.trans (hL₀sin h)
  let f : flatLinkSectorDisk Real.pi L → ℂ := σ ∘ retainedSectorPassingHalfDisk hβ hβπ hLsin
  have hf (x z : flatLinkSectorDisk Real.pi L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z := by
    dsimp only [f, Function.comp_apply]
    rw [hσ]
    exact (retainedSectorPassingHalfDisk_isometry hβ hβπ hLsin).dist_eq x z
  have hapex : f (flatLinkSectorDiskApex Real.pi_pos.le hL.le) = p := by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskApex Real.pi_pos.le hL.le)) = _
    rw [retainedSectorPassingHalfDisk_apex hβ hβπ hLsin hL.le (NNReal.coe_nonneg r)]
    change σ (retainedApexUpperSource hβ.le hβπ r) = p
    rfl
  have hout := exists_pointFlatHalfDisk_occupied_and_edge_germs ha y hL f hf
  rw [hapex] at hout
  obtain ⟨C,ρ,hρ,hρL,hρC,hocc,hedge,hwidth⟩ := hout
  let k := coalescedPointExponent a y p/2+1
  let cut := Real.pi/k
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hk1 : 1 ≤ k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hc : 0 < cut := div_pos Real.pi_pos hk
  have hcπ : cut ≤ Real.pi := (div_le_iff₀ hk).mpr (by nlinarith [Real.pi_pos])
  have hc2 : cut < 2*Real.pi := by linarith [Real.pi_pos]
  let K := retainedPassingRestrict C hρ hρC
  have hPfull (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ K.radius) : z ∈ P := by
    apply hball
    change (pointSmoothConformalEDist a y z p).toReal < ε
    exact (hz.trans (hρL.trans hLε)).trans_lt (half_lt_self hε)
  have hS (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ K.radius) :
      z ∈ range σ ↔ K.chart z ∈ pointClosedRadialInterval K.radius 0 cut :=
    (pointRetainedSectorPassingHalfDisk_germ y hβ hβπ hLsin r.2 σ hσ (hz.trans hρL)).trans
      (hocc z hz)
  have hT (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ K.radius) :
      z ∈ range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)) ↔
        K.chart z ∈ pointClosedRadialInterval K.radius 0 0 ∪ pointClosedRadialInterval K.radius cut cut :=
    (pointRetainedSectorPassingHalfDisk_edge_germ y hβ hβπ hLsin hLr r.2 σ hσ
      (hz.trans hρL)).trans (hedge z hz)
  let E := K.passingEdgeComplement hc hc2 hQ hPfull hS hT
  exact ⟨E,K.passingEdgeComplement_width_atom_admissible hc hc2 hQ hPfull hS hT hwidth⟩

end RepulsiveCoulomb
