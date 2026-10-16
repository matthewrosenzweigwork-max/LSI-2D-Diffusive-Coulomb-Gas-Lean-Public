module

public import LeanResearch.RepulsiveCoulomb.PointRetainedSectorBottomFullness
public import LeanResearch.RepulsiveCoulomb.RetainedSectorSourceTopology
public import LeanResearch.RepulsiveCoulomb.PointInteriorZeroExponentFlatChart
public import LeanResearch.RepulsiveCoulomb.MetricFullStripLocalFullness

@[expose] public section

/-!
SOURCE-ONLY, NOT COMPILED. Actual relative openness of the removed sector S\T.
At positive bottom points, fullness is derived from the source halfdisk and the
actual old boundary. At open-sector points, the original unmarked-interior
condition gives a genuine Euclidean target disk and local isometric fullness.
There is no assumed relative-openness or residual-side certificate.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem retainedApexUpperSource_isometry {β : ℝ} (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    Isometry (retainedApexUpperSource hβ hβπ) := by
  apply Isometry.of_dist_eq
  intro r s
  change dist (sectorPolar r β) (sectorPolar s β) = dist (r:ℝ) (s:ℝ)
  rw [dist_eq_norm,Real.dist_eq]
  have he : sectorPolar r β-sectorPolar s β = (((r:ℝ)-(s:ℝ):ℝ):ℂ)*conePhase β := by
    simp only [sectorPolar,Complex.ofReal_sub]
    ring
  rw [he,norm_mul,conePhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]

/-- Off the free ray, the source radius is positive and its angle is strictly
below beta. This includes positive bottom points at angle zero. -/
theorem retainedSector_source_off_upper {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (x : closedEuclideanSector β) (hx : x ∉ range (retainedApexUpperSource hβ.le hβπ)) :
    0 < ‖x.1‖ ∧ Complex.arg x.1 < β := by
  have hx0 : x.1 ≠ 0 := by
    intro hx0
    apply hx
    refine ⟨0,Subtype.ext ?_⟩
    change sectorPolar 0 β = x.1
    rw [sectorPolar_zero,hx0]
  refine ⟨norm_pos_iff.mpr hx0,lt_of_le_of_ne x.2.2 ?_⟩
  intro he
  apply hx
  refine ⟨⟨‖x.1‖,norm_nonneg _⟩,Subtype.ext ?_⟩
  change sectorPolar ‖x.1‖ β = x.1
  exact (congrArg (sectorPolar ‖x.1‖) he).symm.trans (sectorPolar_norm_arg x.1)

/-- Strict positive source angles are actual interior points of the literal
source sector; the argument uses only a small local polar neighborhood. -/
theorem retainedSector_strict_source_interior {β : ℝ} (hβπ : β ≤ Real.pi)
    (x : closedEuclideanSector β) (hx0 : 0 < ‖x.1‖)
    (ha0 : 0 < Complex.arg x.1) (haβ : Complex.arg x.1 < β) :
    x.1 ∈ interior (closedEuclideanSector β) := by
  let R := ‖x.1‖+1
  have hsub : pointClosedRadialInterval R 0 β ⊆ closedEuclideanSector β := by
    rintro z ⟨r,hr,θ,hθ,rfl⟩
    rw [← sectorPolar_eq_pointRadialSectorPoint]
    by_cases hr0 : r = 0
    · subst r
      simp [sectorPolar_zero,closedEuclideanSector,show 0 ≤ β from x.2.1.trans x.2.2]
    · change 0 ≤ Complex.arg _ ∧ Complex.arg _ ≤ β
      rw [sectorPolar_arg (lt_of_le_of_ne hr.1 (Ne.symm hr0))
        ⟨by linarith [hθ.1,Real.pi_pos],hθ.2.trans hβπ⟩]
      exact hθ
  have hi := interior_mono hsub (sectorReturn_radial_point_mem_interior_interval hx0
    (show ‖x.1‖ < R by dsimp [R]; linarith) ⟨ha0,haβ⟩)
  rw [← sectorPolar_eq_pointRadialSectorPoint,sectorPolar_norm_arg] at hi
  exact hi

/-- The removed piece is relatively OPEN in the actual old P. The regular
open-sector hypothesis is the original supplied-sector condition (interior and
unmarked), not any property of the future residual. -/
theorem pointRetainedSector_without_free_ray_relative_open
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (hσP : ∀ x, σ x ∈ P)
    (hbottom : ∀ u : NNReal, σ (retainedApexBottomSource hβ.le hβπ u) ∈ frontier P)
    (hOld : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Admissible)
    (hregular : ∀ x : closedEuclideanSector β,
      0 < ‖x.1‖ → 0 < Complex.arg x.1 → Complex.arg x.1 < β →
        σ x ∈ interior P ∧ coalescedPointExponent a y (σ x) = 0) :
    IsOpen {z : P | z.1 ∈ range σ \
      range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u))} := by
  let F : closedEuclideanSector β → P := fun x ↦ ⟨σ x,hσP x⟩
  have hopen : @IsOpen P (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
      (range F \ range (F ∘ retainedApexUpperSource hβ.le hβπ)) := by
    letI : MetricSpace P := pointRegionMetricSpace ha y P
    letI : PseudoMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoMetricSpace
    letI : PseudoEMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoEMetricSpace
    letI : TopologicalSpace P := (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
    have hF : Isometry F := Isometry.of_dist_eq (fun x z ↦ hσ x z)
    have htopclosed : IsClosed (range (F ∘ retainedApexUpperSource hβ.le hβπ)) :=
      (@Isometry.isClosedEmbedding NNReal P (inferInstance : EMetricSpace NNReal)
        (inferInstance : CompleteSpace NNReal) (pointRegionMetricSpace ha y P).toEMetricSpace
        (F ∘ retainedApexUpperSource hβ.le hβπ)
        (hF.comp (retainedApexUpperSource_isometry hβ.le hβπ))).isClosed_range
    apply isOpen_iff_mem_nhds.mpr
    rintro p ⟨⟨x,rfl⟩,hxT⟩
    have hxupper : x ∉ range (retainedApexUpperSource hβ.le hβπ) := by
      rintro ⟨u,hu⟩
      exact hxT ⟨u,congrArg F hu⟩
    obtain ⟨hx0,hxβ⟩ := retainedSector_source_off_upper hβ hβπ x hxupper
    have hfill : ∃ ε : ℝ, 0 < ε ∧ ball (F x) ε ⊆ range F := by
      by_cases hxarg : Complex.arg x.1 = 0
      · let r : NNReal := ⟨‖x.1‖,norm_nonneg _⟩
        have hxr : retainedApexBottomSource hβ.le hβπ r = x := by
          apply Subtype.ext
          change sectorPolar ‖x.1‖ 0 = x.1
          rw [← hxarg,sectorPolar_norm_arg]
        obtain ⟨C,hC⟩ := hOld (σ (retainedApexBottomSource hβ.le hβπ r)) (hbottom r)
        obtain ⟨ε,hε,hfull⟩ := pointRetainedSector_bottom_locally_full ha y hβ hβπ σ hσ hσP hbottom
          r hx0 C hC
        refine ⟨ε,hε,?_⟩
        intro z hz
        have hz' : (pointSmoothConformalEDist a y z.1
            (σ (retainedApexBottomSource hβ.le hβπ r))).toReal ≤ ε := by
          rw [hxr]
          exact hz.le
        obtain ⟨w,hw⟩ := (hfull z.1 hz').mpr z.2
        exact ⟨w,Subtype.ext hw⟩
      · have hxarg0 : 0 < Complex.arg x.1 := lt_of_le_of_ne x.2.1 (Ne.symm hxarg)
        obtain ⟨hxP,hxκ⟩ := hregular x hx0 hxarg0 hxβ
        obtain ⟨C⟩ := exists_pointInterior_zeroExponent_flatDiskChart ha y hxP hxκ
        have hxi := retainedSector_strict_source_interior hβπ x hx0 hxarg0 hxβ
        obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxi)
        let ε := min δ C.radius/2
        have hε : 0 < ε := half_pos (lt_min hδ C.radius_pos)
        have hεδ : ε ≤ δ := by dsimp [ε]; linarith [min_le_left δ C.radius,lt_min hδ C.radius_pos]
        have hεC : ε ≤ C.radius := by dsimp [ε]; linarith [min_le_right δ C.radius,lt_min hδ C.radius_pos]
        exact ⟨ε,hε,metricFlatDisk_isometry_locally_full F hF x C hε hεC
          (fun z hz ↦ hδball (hz.trans_le hεδ))⟩
    obtain ⟨ε,hε,hfill⟩ := hfill
    exact Filter.mem_of_superset
      (Filter.inter_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) (htopclosed.isOpen_compl.mem_nhds hxT))
      (fun z hz ↦ ⟨hfill hz.1,hz.2⟩)
  rw [pointRegionMetricSpace_topology ha y P] at hopen
  have he : (range F \ range (F ∘ retainedApexUpperSource hβ.le hβπ)) =
      {z : P | z.1 ∈ range σ \
        range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u))} := by
    ext z
    constructor
    · rintro ⟨⟨x,hx⟩,hzT⟩
      refine ⟨⟨x,congrArg Subtype.val hx⟩,?_⟩
      rintro ⟨u,hu⟩
      exact hzT ⟨u,Subtype.ext hu⟩
    · rintro ⟨⟨x,hx⟩,hzT⟩
      refine ⟨⟨x,Subtype.ext hx⟩,?_⟩
      rintro ⟨u,hu⟩
      exact hzT ⟨u,congrArg Subtype.val hu⟩
  rwa [he] at hopen

end RepulsiveCoulomb
