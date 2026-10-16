import LeanResearch.RepulsiveCoulomb.FullStripResidualTopology
import LeanResearch.RepulsiveCoulomb.MetricFullStripLocalFullness
import LeanResearch.RepulsiveCoulomb.PointInteriorZeroExponentFlatChart

/-! The concrete endpoint instantiates the topology from the given actual map,
retained old-boundary charts, and the ordinary marked-support hypotheses. The
actual lower metric instances are explicit; ordinary complex topology is only
identified through the proved pointRegionMetricSpace_topology equality. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- Removing a supplied positive-width full strip gives the literal closed
opposite side of its ACTUAL top line. There is no maximal-height assertion here.
Top marks are allowed; only the old bottom and the strict open strip are clean. -/
theorem pointFullStrip_construct_residual_halfplane
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    (hP : IsClosed P) {h : ℝ} (hh : 0 < h)
    (F : flatFullNormalStrip h → P)
    (hF : ∀ z w, (pointSmoothConformalEDist a y (F z).1 (F w).1).toReal = dist z w)
    (hclosed : IsClosedEmbedding (fun z ↦ (F z).1))
    (hboundary : frontier P = range (fun r ↦ (F (fullStripBottom hh.le r)).1))
    (hpositive : ∀ z, 0 < z.1.im → (F z).1 ∈ interior P)
    (nu : ℂ → ℝ)
    (hnu : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      nu p = Real.pi - C.flatPhysicalWidth)
    (marks : Set ℂ)
    (hmarkedInterior : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ marks)
    (hmarkedBoundary : ∀ p ∈ frontier P, nu p ≠ 0 → p ∈ marks)
    (hcleanBottom : ∀ r, (F (fullStripBottom hh.le r)).1 ∉ marks)
    (hcleanOpen : ∀ z, 0 < z.1.im → z.1.im < h → (F z).1 ∉ marks) :
    let S : Set ℂ := range (fun z ↦ (F z).1)
    let top : ℝ → ℂ := fun r ↦ (F (fullStripTop hh.le r)).1
    ∃ D : PlanarLineHalfplaneHomeomorphs top,
      Pᶜ ∪ (S \ range top) = D.positive ∧
      P \ S = D.negative ∧
      closure (P \ S) = closure D.negative ∧
      closure (P \ S) ⊆ P ∧
      frontier (closure (P \ S)) = range top ∧
      Nonempty (closure (P \ S) ≃ₜ planarClosedUpperHalfplane) ∧
      range top ⊆ interior P := by
  let S : Set ℂ := range (fun z ↦ (F z).1)
  let top : ℝ → ℂ := fun r ↦ (F (fullStripTop hh.le r)).1
  obtain ⟨htopmetric, D, hbottomplus⟩ := pointFullStrip_top_metric_and_sides ha y hh F hF
  have hSP : S ⊆ P := by rintro p ⟨z, rfl⟩; exact (F z).2
  have htS : range top ⊆ S := by rintro p ⟨r, rfl⟩; exact mem_range_self _
  have hboundS : frontier P ⊆ S := by
    rw [hboundary]
    rintro p ⟨r, rfl⟩; exact mem_range_self _
  have hrelative : IsOpen {z : P | z.1 ∈ S \ range top} := by
    let M := pointRegionMetricSpace ha y P
    letI : MetricSpace P := M
    letI : PseudoMetricSpace P := M.toPseudoMetricSpace
    letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
    letI : UniformSpace P := M.toUniformSpace
    have hFi : @Isometry _ P inferInstance M.toPseudoEMetricSpace F := Isometry.of_dist_eq hF
    have hbottom : ∀ r, Nonempty (@MetricFlatHalfDiskChart P M (F (fullStripBottom hh.le r))) := by
      intro r
      have hp : (F (fullStripBottom hh.le r)).1 ∈ frontier P := hboundary.symm ▸ mem_range_self r
      obtain ⟨C, hC⟩ := hnu _ hp
      have hn : nu (F (fullStripBottom hh.le r)).1 = 0 := by
        by_contra hn
        exact hcleanBottom r (hmarkedBoundary _ hp hn)
      have hw : C.flatPhysicalWidth = Real.pi := by rw [hn] at hC; linarith
      exact ⟨C.flatHalfDiskChart ha y (F (fullStripBottom hh.le r)).2 hw⟩
    have hinterior : ∀ z, 0 < z.1.im → z.1.im < h →
        Nonempty (@MetricFlatDiskChart P M (F z)) := by
      intro z hz ht
      have hi := hpositive z hz
      have ha0 : coalescedPointExponent a y (F z).1 = 0 := by
        by_contra ha0
        exact hcleanOpen z hz ht (hmarkedInterior _ hi ha0)
      exact exists_pointInterior_zeroExponent_flatDiskChart ha y hi ha0
    have ho := @metricFullStrip_without_top_open P M h hh F hFi hbottom hinterior
    have he : range F \ range (F ∘ fullStripTop hh.le) = {z : P | z.1 ∈ S \ range top} := by
      ext z
      constructor
      · rintro ⟨⟨w, rfl⟩, hw⟩
        refine ⟨mem_range_self w, ?_⟩
        rintro ⟨r, hr⟩
        exact hw ⟨r, Subtype.ext hr⟩
      · rintro ⟨⟨w, hw⟩, ht⟩
        refine ⟨⟨w, Subtype.ext hw⟩, ?_⟩
        rintro ⟨r, hr⟩
        exact ht ⟨r, congrArg Subtype.val hr⟩
    rw [he] at ho
    change @IsOpen P M.toUniformSpace.toTopologicalSpace _ at ho
    rw [pointRegionMetricSpace_topology ha y P] at ho
    exact ho
  have hbelow : IsConnected (S \ range top) :=
    fullStrip_without_top_connected hh (fun z ↦ (F z).1) hclosed.continuous hclosed.injective
  have hpbelow : (F (fullStripBottom hh.le 0)).1 ∈ S \ range top := by
    refine ⟨mem_range_self _, ?_⟩
    intro hp
    have him := (fullStrip_image_mem_top_iff hh.le hclosed.injective (fullStripBottom hh.le 0)).mp hp
    exact hh.ne him
  have hpfront : (F (fullStripBottom hh.le 0)).1 ∈ frontier P := hboundary.symm ▸ mem_range_self 0
  obtain ⟨hremove, hremain, hclosure, hsubset, hfront⟩ :=
    fullStrip_residual_is_negative_side D hP hclosed.isClosed_range hSP htS hboundS hrelative
      (fullStrip_old_halfplane_exterior_connected H hHP) hbelow hpbelow hpfront hbottomplus
  refine ⟨D, hremove, hremain, hclosure, hsubset, hfront, ?_, ?_⟩
  · exact ⟨(Homeomorph.setCongr hclosure).trans D.negative_homeomorph⟩
  · rintro p ⟨r, rfl⟩
    exact hpositive (fullStripTop hh.le r) hh

end RepulsiveCoulomb
