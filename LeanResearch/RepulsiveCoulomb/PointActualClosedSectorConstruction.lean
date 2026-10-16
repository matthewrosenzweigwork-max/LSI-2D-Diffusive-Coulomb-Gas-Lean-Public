module

public import LeanResearch.RepulsiveCoulomb.PointActualUnboundedWindow
public import LeanResearch.RepulsiveCoulomb.EuclideanSectorWindowExhaustion
public import LeanResearch.RepulsiveCoulomb.PointRetainedConvexFlatEmbedding

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Construct the actual entire closed sector by
nested angular exhaustion and complete-target metric extension. Neither an
open map, global isometry, compatible family, nor continuation certificate is
input. The marked beta-edge is selected by this Cauchy extension, not by an
arbitrary ambient ray continuation through a cone point.
-/
noncomputable section
open Set Metric Filter Topology
namespace RepulsiveCoulomb
namespace PointActualSectorData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointActualSectorData a y ha P)

/-- The actual ambient and intrinsic distance-preserving closed sector,
with exact initial chart agreement, interior clearance, properness, and every
metric curve length preserved. Exact full bottom-ray matching and top marked
contact are separate identifications of the map constructed here. -/
theorem exists_actual_closed_sector_map :
    ∃ F : closedEuclideanSector D.beta → P,
      (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
      (∀ x z, (pointRegionIntrinsicEDist ha y P (F x).1 (F z).1).toReal = dist x z) ∧
      (∀ z, ‖z.1‖ ≤ D.chart.radius → (F z).1 = D.chart.flatInverse z.1) ∧
      (∀ z, Complex.arg z.1 ∈ Ioo (0 : ℝ) D.beta →
        (F z).1 ∈ interior P ∧ (F z).1 ∉ pointSignedMarked D.nu D.alpha) ∧
      IsClosedEmbedding (fun z ↦ (F z).1) ∧ IsProperMap (fun z ↦ (F z).1) ∧
      ∀ γ : ℝ → closedEuclideanSector D.beta, ∀ s t,
        pointConformalMetricLength ha y (fun r ↦ (F (γ r)).1) s t = eVariationOn γ (Icc s t) := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : EMetricSpace P := M.toEMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  letI : UniformSpace P := M.toUniformSpace
  letI : TopologicalSpace P := M.toUniformSpace.toTopologicalSpace
  letI : CompleteSpace P := pointRegionMetricSpace_complete ha y D.region_closed
  let S := sectorWindow D.beta
  have hb (n : ℕ) := sectorWindow_bounds D.beta_pos n
  have hex (n : ℕ) : ∃ f : S n → P, Isometry f ∧
      (∀ z, ‖z.1‖ ≤ D.chart.radius → (f z).1 = D.chart.flatInverse z.1) ∧
      ∀ z, z.1 ≠ 0 → (f z).1 ∈ interior P ∧ (f z).1 ∉ pointSignedMarked D.nu D.alpha := by
    obtain ⟨f, hf, hseed, hreg⟩ := D.exists_unbounded_closed_window
      (hb n).1 (hb n).2.1 (hb n).2.2
    exact ⟨f, Isometry.of_dist_eq hf, hseed, hreg⟩
  choose f hf hseed hreg using hex
  have hmono {i j : ℕ} (hij : i ≤ j) : S i ⊆ S j := sectorWindow_mono D.beta_pos D.beta_pi hij
  have hSconv (n : ℕ) : Convex ℝ (S n) :=
    flatInteriorAngularWindow_convex (hb n).1 (hb n).2.1 ((hb n).2.2.le.trans D.beta_pi)
  have hSne (n : ℕ) : (interior (S n)).Nonempty :=
    (flatInteriorAngularWindow_truncation_interior_nonempty (hb n).1 (hb n).2.1
      ((hb n).2.2.le.trans D.beta_pi) (by norm_num : (0 : ℝ) < 1)).mono
      (interior_mono inter_subset_left)
  have hS0 (n : ℕ) : (0 : ℂ) ∈ S n :=
    zero_mem_flatInteriorAngularWindow ((hb n).1.trans (hb n).2.1).le
  have hSarg (n : ℕ) (q : S n) (hq : q.1 ≠ 0) :
      Complex.arg q.1 ∈ Ioo (0 : ℝ) D.beta := by
    have h := flatInteriorAngularWindow_arg (hb n).1 (hb n).2.1
      ((hb n).2.2.le.trans D.beta_pi) q.2 hq
    exact ⟨(hb n).1.trans_le h.1, h.2.trans_lt (hb n).2.2⟩
  have hcompat : ∀ i j : ℕ, ∀ z (hi : z ∈ S i) (hj : z ∈ S j),
      f i ⟨z, hi⟩ = f j ⟨z, hj⟩ := by
    intro i j z hi hj
    rcases le_total i j with hij | hji
    · exact D.stages_agree (hSconv i) (hSne i) (hS0 i) (hmono hij)
        (sectorWindow_subset D.beta_pos i) (hSarg i) (f i) (f j) (hf i) (hf j)
        (hseed i) (hseed j) ⟨z, hi⟩
    · exact (D.stages_agree (hSconv j) (hSne j) (hS0 j) (hmono hji)
        (sectorWindow_subset D.beta_pos j) (hSarg j) (f j) (f i) (hf j) (hf i)
        (hseed j) (hseed i) ⟨z, hj⟩).symm
  have hdir : Directed (· ⊆ ·) S :=
    fun i j ↦ ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  have hclosure := closure_iUnion_sectorWindow D.beta_pos D.beta_pi
  let incl : closedEuclideanSector D.beta → closure (⋃ n, S n) :=
    fun z ↦ ⟨z.1, hclosure.symm ▸ z.2⟩
  have hinc : Isometry incl := fun _ _ ↦ rfl
  let F := directedFlatClosure S f hcompat ∘ incl
  have hF : Isometry F := (directedFlatClosure_isometry S f hdir hcompat hf).comp hinc
  have hFold (n : ℕ) (z : S n) :
      F ⟨z.1, sectorWindow_subset D.beta_pos n z.2⟩ = f n z :=
    directedFlatClosure_apply S f hdir hcompat hf n z
  have hFseed (z : closedEuclideanSector D.beta) (hz : ‖z.1‖ ≤ D.chart.radius) :
      (F z).1 = D.chart.flatInverse z.1 := by
    let q : ℕ → closedEuclideanSector D.beta := fun n ↦
      ⟨sectorWindowApprox D.beta z.1 n, sectorWindow_subset D.beta_pos n
        (sectorWindowApprox_mem D.beta_pos D.beta_pi z.2 n)⟩
    have hq : Tendsto q atTop (𝓝 z) := tendsto_subtype_rng.mpr (sectorWindowApprox_tendsto D.beta z.1)
    let q0 : ℕ → retainedFlatSectorDisk D.beta D.chart.radius := fun n ↦
      ⟨(q n).1, (q n).2, by
        change ‖sectorWindowApprox D.beta z.1 n‖ ≤ D.chart.radius
        rw [sectorWindowApprox_norm]
        exact hz⟩
    let z0 : retainedFlatSectorDisk D.beta D.chart.radius := ⟨z.1, z.2, hz⟩
    have hq0 : Tendsto q0 atTop (𝓝 z0) := tendsto_subtype_rng.mpr (sectorWindowApprox_tendsto D.beta z.1)
    let G := D.chart.cappedFlatSectorChart D.beta_width
    have hGi : Isometry G := D.chart.cappedFlatSectorChart_isometry ha D.beta_width D.beta_pi
    have heq : F ∘ q = G ∘ q0 := by
      funext n
      apply Subtype.ext
      have h := hFold n ⟨(q n).1, sectorWindowApprox_mem D.beta_pos D.beta_pi z.2 n⟩
      exact (congrArg Subtype.val h).trans (hseed n _ (by
          change ‖sectorWindowApprox D.beta z.1 n‖ ≤ D.chart.radius
          rw [sectorWindowApprox_norm]
          exact hz))
    have hlimF := hF.continuous.tendsto z |>.comp hq
    have hlimG := hGi.continuous.tendsto z0 |>.comp hq0
    rw [heq] at hlimF
    exact congrArg Subtype.val (tendsto_nhds_unique hlimF hlimG)
  have hFreg (z : closedEuclideanSector D.beta) (hz : Complex.arg z.1 ∈ Ioo (0 : ℝ) D.beta) :
      (F z).1 ∈ interior P ∧ (F z).1 ∉ pointSignedMarked D.nu D.alpha := by
    obtain ⟨n, hn⟩ := mem_iUnion.mp (mem_iUnion_sectorWindow_of_strict_arg D.beta_pos D.beta_pi hz)
    have hz0 : z.1 ≠ 0 := by intro he; rw [he, Complex.arg_zero] at hz; exact lt_irrefl _ hz.1
    have he := hFold n ⟨z.1, hn⟩
    exact he.symm ▸ hreg n ⟨z.1, hn⟩ hz0
  letI : CompleteSpace (closedEuclideanSector D.beta) :=
    (closedEuclideanSector_isClosed D.beta_pos D.beta_pi).isComplete.completeSpace_coe
  have hclosedP : @IsClosedEmbedding (closedEuclideanSector D.beta) P _
      M.toUniformSpace.toTopologicalSpace F := hF.isClosedEmbedding
  rw [pointRegionMetricSpace_topology ha y P] at hclosedP
  have hclosed : IsClosedEmbedding (fun z : closedEuclideanSector D.beta ↦ (F z).1) := by
    letI : TopologicalSpace P := TopologicalSpace.induced (Subtype.val : P → ℂ) inferInstance
    exact D.region_closed.isClosedEmbedding_subtypeVal.comp hclosedP
  have hFcont : Continuous (fun z ↦ (F z).1) := hclosed.continuous
  have hintrinsic (x z : closedEuclideanSector D.beta) :
      (pointRegionIntrinsicEDist ha y P (F x).1 (F z).1).toReal = dist x z := by
    let hconv := closedEuclideanSector_convex D.beta_pos D.beta_pi
    let γ : unitInterval → ℂ := fun t ↦ (F (convexDomainSegment hconv x z t)).1
    have hdγ : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal := by
      intro s t
      change @dist P M.toDist (F (convexDomainSegment hconv x z s))
        (F (convexDomainSegment hconv x z t)) =
          |t.1 - s.1| * @dist P M.toDist (F x) (F z)
      rw [hF.dist_eq, hF.dist_eq, convexDomainSegment_dist, mul_comm]
    have heq := pointRegionIntrinsicEDist_eq_of_contained_geodesic ha y γ
      (congrArg (fun q ↦ (F q).1) (convexDomainSegment_zero hconv x z))
      (congrArg (fun q ↦ (F q).1) (convexDomainSegment_one hconv x z))
      (hFcont.comp (continuous_convexDomainSegment hconv x z))
      (fun t ↦ (F (convexDomainSegment hconv x z t)).2) hdγ
    rw [heq]
    exact hF.dist_eq x z
  exact ⟨F, fun x z ↦ hF.dist_eq x z, hintrinsic, hFseed, hFreg,
    hclosed, hclosed.isProperMap, pointFlat_isometry_metricLength ha y F hF⟩

end PointActualSectorData
end RepulsiveCoulomb
