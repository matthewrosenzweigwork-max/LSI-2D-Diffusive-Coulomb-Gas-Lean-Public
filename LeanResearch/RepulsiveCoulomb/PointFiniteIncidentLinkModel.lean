module

public import LeanResearch.RepulsiveCoulomb.PointActualSectorIncidentOccupancy
public import LeanResearch.RepulsiveCoulomb.FiniteLinkEndpointSubdivision

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. A common-radius model for every actual incident
sector in a finite family. Nonincident closed sectors are excluded on the
same disk. The complement is retained literally. This constructs the local
range geometry needed before cyclic subdivision; it is not a flat atlas or
an assumed new metric. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem flatLinkOccupiedDisk_radius_cutoff {w : ℂ} {ρ R lo hi : ℝ}
    (hρR : ρ ≤ R) (hw : ‖w‖ ≤ ρ) :
    w ∈ flatLinkOccupiedDisk R lo hi ↔ w ∈ flatLinkOccupiedDisk ρ lo hi := by
  constructor
  · rintro ⟨r, hr, θ, hθ, he⟩
    have hn : ‖w‖ = r := by rw [he, sectorPolar_norm hr.1]
    exact ⟨r, ⟨hr.1, hn ▸ hw⟩, θ, hθ, he⟩
  · rintro ⟨r, hr, θ, hθ, he⟩
    exact ⟨r, ⟨hr.1, hr.2.trans hρR⟩, θ, hθ, he⟩

theorem exists_pointConformal_closedBall_subset_open
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {U : Set ℂ} (hU : IsOpen U) {p : ℂ} (hp : p ∈ U) :
    ∃ R : ℝ, 0 < R ∧ ∀ z,
      (pointSmoothConformalEDist a y z p).toReal ≤ R → z ∈ U := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  letI : PseudoMetricSpace ℂ := (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
  letI : PseudoEMetricSpace ℂ := (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace
  letI : UniformSpace ℂ := (pointSmoothConformalMetricSpace ha y).toUniformSpace
  letI : TopologicalSpace ℂ := (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
  have hU' : IsOpen U := by
    change @IsOpen ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace U
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU' p hp
  refine ⟨ε / 2, half_pos hε, fun z hz ↦ ?_⟩
  exact hball (hz.trans_lt (half_lt_self hε))

/-- One positive radius works for the whole finite family, including the
empty family. Every boundary interval is read in the same given cone chart,
so subsequent order comparisons concern actual shared angular coordinates. -/
theorem exists_pointFiniteSector_common_incident_link
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {ι : Type*} [Fintype ι] (S : ι → PointActualAllocatedSector a y) (p : ℂ)
    (hseam : ∀ i, p ∉ (S i).openImage) (C : PointFlatLinkConeDisk a y p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ C.radius ∧ ∃ lo : ι → ℝ,
      ∀ i z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
        (z ∈ range (S i).map ↔ p ∈ range (S i).map ∧
          C.chart z ∈ flatLinkOccupiedDisk ρ (lo i)
            (lo i + (if p = (S i).apex then (S i).beta else Real.pi) /
              (coalescedPointExponent a y p / 2 + 1))) := by
  classical
  have hmodel : ∀ i, ∃ R : ℝ, 0 < R ∧ ∃ lo : ℝ,
      ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ R →
        (z ∈ range (S i).map ↔ p ∈ range (S i).map ∧
          C.chart z ∈ flatLinkOccupiedDisk R lo
            (lo + (if p = (S i).apex then (S i).beta else Real.pi) /
              (coalescedPointExponent a y p / 2 + 1))) := by
    intro i
    by_cases hp : p ∈ range (S i).map
    · obtain ⟨R, hR, _, lo, hlo⟩ :=
        (S i).exists_incident_fixed_chart_occupancy ha y hp (hseam i) C
      exact ⟨R, hR, lo, fun z hz ↦ by simpa only [hp, true_and] using hlo z hz⟩
    · obtain ⟨R, hR, hclear⟩ := exists_pointConformal_closedBall_subset_open ha y
        ((S i).isClosedEmbedding ha).isClosed_range.isOpen_compl hp
      refine ⟨R, hR, 0, fun z hz ↦ ?_⟩
      have hznot : z ∉ range (S i).map := hclear z hz
      simp only [hp, hznot, false_and]
  choose R hR lo hlo using hmodel
  let radii : Finset ℝ := insert C.radius (Finset.univ.image R)
  have hradii : radii.Nonempty := ⟨C.radius, Finset.mem_insert_self _ _⟩
  let ρ := radii.min' hradii
  have hρ : 0 < ρ := by
    apply (radii.lt_min'_iff hradii).mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact C.radius_pos
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact hR i
  have hρC : ρ ≤ C.radius := radii.min'_le _ (Finset.mem_insert_self _ _)
  have hρR (i : ι) : ρ ≤ R i := radii.min'_le _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  refine ⟨ρ, hρ, hρC, lo, fun i z hz ↦ ?_⟩
  have hnorm : ‖C.chart z‖ ≤ ρ := by
    rw [C.norm_chart (hz.trans hρC)]
    exact hz
  exact (hlo i z (hz.trans (hρR i))).trans
    (and_congr_right fun _ ↦ flatLinkOccupiedDisk_radius_cutoff (hρR i) hnorm)

end RepulsiveCoulomb
