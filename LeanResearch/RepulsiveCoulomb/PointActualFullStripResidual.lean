module

public import LeanResearch.RepulsiveCoulomb.PointFullStripCurvatureTransport

@[expose] public section

/-! Final concrete supplied-strip endpoint. Closed/proper image and interior
membership of every positive source height are DERIVED from the actual isometry,
complete closed source, whole-bottom identity, and ordinary point-metric topology.
Neither a residual certificate nor local occupancy/update conclusions are inputs.
This bounded theorem makes no maximal-height or first-marked-contact assertion. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem pointFullStrip_closed_proper_and_positive_interior
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) {h : ℝ} (hh : 0 < h)
    (F : flatFullNormalStrip h → P)
    (hF : ∀ z w, (pointSmoothConformalEDist a y (F z).1 (F w).1).toReal = dist z w)
    (hboundary : frontier P = range (fun r ↦ (F (fullStripBottom hh.le r)).1)) :
    IsClosedEmbedding (fun z ↦ (F z).1) ∧ IsProperMap (fun z ↦ (F z).1) ∧
      ∀ z, 0 < z.1.im → (F z).1 ∈ interior P := by
  have hi : @Isometry (flatFullNormalStrip h) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace (fun z ↦ (F z).1) :=
    @Isometry.of_dist_eq _ ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace _ hF
  have hc := @flatFullNormalStrip_isometry_closed_proper ℂ (pointSmoothConformalMetricSpace ha y)
    h (fun z ↦ (F z).1) hi
  have hclosed : @IsClosedEmbedding (flatFullNormalStrip h) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace (fun z ↦ (F z).1) := hc.1
  have hproper : @IsProperMap (flatFullNormalStrip h) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace (fun z ↦ (F z).1) := hc.2
  rw [pointSmoothConformalMetricSpace_topology ha y] at hclosed hproper
  refine ⟨hclosed,hproper,?_⟩
  intro z hz
  by_contra hnot
  have hp : (F z).1 ∈ frontier P := ⟨subset_closure (F z).2,hnot⟩
  rw [hboundary] at hp
  obtain ⟨r,hr⟩ := hp
  have he := hclosed.injective hr
  have him := congrArg (fun u : flatFullNormalStrip h ↦ u.1.im) he
  exact (ne_of_gt hz) him.symm

/-- COMPLETE BOUNDED ENDPOINT: literal residual halfplane; actual complementary
retained intervals; removed width pi and retained width lambda_X-pi; unchanged
signed curvature at every ambient point; and all ordinary budget support kept
on the closed new side. F and h are supplied, not asserted to be maximal. -/
theorem pointFullStrip_actual_residual_and_all_point_update
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    {h : ℝ} (hh : 0 < h) (F : flatFullNormalStrip h → P)
    (hF : ∀ z w, (pointSmoothConformalEDist a y (F z).1 (F w).1).toReal = dist z w)
    (hboundary : frontier P = range (fun r ↦ (F (fullStripBottom hh.le r)).1))
    (nu : ℂ → ℝ)
    (hnu : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      nu p = Real.pi - C.flatPhysicalWidth)
    (marks budget : Set ℂ)
    (hmarkedInterior : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ marks)
    (hmarkedBoundary : ∀ p ∈ frontier P, nu p ≠ 0 → p ∈ marks)
    (hcleanBottom : ∀ r, (F (fullStripBottom hh.le r)).1 ∉ marks)
    (hcleanOpen : ∀ z, 0 < z.1.im → z.1.im < h → (F z).1 ∉ marks)
    (hbudgetP : budget ⊆ P) (hbudgetMarks : budget ⊆ marks) :
    let S : Set ℂ := range (fun z ↦ (F z).1)
    let top : ℝ → ℂ := fun r ↦ (F (fullStripTop hh.le r)).1
    let Q : Set ℂ := closure (P \ S)
    ∃ D : PlanarLineHalfplaneHomeomorphs top,
      (∀ s t, (pointSmoothConformalEDist a y (top s) (top t)).toReal = dist s t) ∧
      Pᶜ ∪ (S \ range top) = D.positive ∧
      P \ S = D.negative ∧ Q = closure D.negative ∧
      Q ⊆ P ∧ interior Q = P \ S ∧ frontier Q = range top ∧
      Nonempty (Q ≃ₜ planarClosedUpperHalfplane) ∧
      (∀ p ∈ Q, Nonempty (PointRetainedConeNeighborhood a y Q p)) ∧
      (∀ s, ∃ C : PointRetainedConeNeighborhood a y (closure D.positive) (top s),
        ∃ E : PointRetainedConeNeighborhood a y Q (top s),
          C.chart = E.chart ∧
          ((C.lo = 0 ∧ C.hi = E.lo ∧ E.hi = 2*Real.pi) ∨
            (E.lo = 0 ∧ E.hi = C.lo ∧ C.hi = 2*Real.pi)) ∧
          C.flatPhysicalWidth = Real.pi ∧
          E.flatPhysicalWidth = (1+coalescedPointExponent a y (top s)/2)*(2*Real.pi)-Real.pi ∧
          Real.pi-E.flatPhysicalWidth = -Real.pi*coalescedPointExponent a y (top s) ∧ E.Admissible) ∧
      (∀ p, pointFullStripSignedCoefficient a y Q
        (fun z ↦ -Real.pi*coalescedPointExponent a y z) p = pointFullStripSignedCoefficient a y P nu p) ∧
      budget ⊆ Q := by
  let S : Set ℂ := range (fun z ↦ (F z).1)
  let top : ℝ → ℂ := fun r ↦ (F (fullStripTop hh.le r)).1
  let Q : Set ℂ := closure (P \ S)
  have hP : IsClosed P := by
    rw [hHP]
    exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  obtain ⟨hclosed,hproper,hpositive⟩ :=
    pointFullStrip_closed_proper_and_positive_interior ha y hP hh F hF hboundary
  obtain ⟨D,hremoved,hremainder,hclosure,hQP,hfrontier,hhomeo,hTint⟩ :=
    pointFullStrip_construct_residual_halfplane ha y H hHP hP hh F hF hclosed hboundary
      hpositive nu hnu marks hmarkedInterior hmarkedBoundary hcleanBottom hcleanOpen
  have hinterior : interior Q = P \ S := by
    change interior (closure (P \ S)) = P \ S
    rw [hclosure,D.negative_interior,hremainder]
  have htopmetric : ∀ s t, (pointSmoothConformalEDist a y (top s) (top t)).toReal = dist s t := by
    intro s t
    rw [hF]
    exact (fullStripTop_isometry hh.le).dist_eq s t
  refine ⟨D,htopmetric,hremoved,hremainder,hclosure,hQP,hinterior,hfrontier,hhomeo,?_,?_,?_,?_⟩
  · intro p hp
    by_cases hi : p ∈ interior Q
    · obtain ⟨C,_,_,_⟩ := pointInterior_construct_full_retained_chart ha y hi
      exact ⟨C⟩
    · have hf : p ∈ frontier Q := ⟨subset_closure hp,hi⟩
      obtain ⟨s,hs⟩ := (hfrontier ▸ hf : p ∈ range top)
      change Nonempty (PointRetainedConeNeighborhood a y (closure (P \ S)) p)
      rw [← hs,hclosure]
      obtain ⟨C,E,_,_,_,_,_,_⟩ :=
        pointFullStrip_construct_residual_top_widths ha y hh F hF hpositive D hremoved s
      exact ⟨E⟩
  · intro s
    change ∃ C : PointRetainedConeNeighborhood a y (closure D.positive) (top s),
      ∃ E : PointRetainedConeNeighborhood a y (closure (P \ S)) (top s), _
    rw [hclosure]
    exact pointFullStrip_construct_residual_top_widths ha y hh F hF hpositive D hremoved s
  · exact pointFullStrip_all_point_coefficient_eq a y hP isClosed_closure hQP hinterior hfrontier hTint nu
      (pointFullStrip_removed_coefficient_zero y hh F hclosed.injective hboundary hpositive nu marks
        hmarkedInterior hmarkedBoundary hcleanBottom hcleanOpen)
  · exact pointFullStrip_budget_support_retained hh F rfl hfrontier hbudgetP hbudgetMarks hcleanBottom hcleanOpen

end RepulsiveCoulomb
