import LeanResearch.RepulsiveCoulomb.MetricFlatHalfDiskChart
import LeanResearch.RepulsiveCoulomb.PointSignedCurvatureFinite

/-! ISOLATED SOURCE-ONLY DRAFT. Construct the relative endpoint chart needed
by longitudinal continuation directly from original signed boundary geometry
and a clean minimizing ray. Ambient exponent zero is nowhere required. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem pointCleanRay_exists_actual_retained_halfDisk
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (hν : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo))
    (ρ : NNReal → P)
    (hρ : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (hfront : ∀ t, (ρ t).1 ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {(ρ 0).1})
      (range (fun t ↦ (ρ t).1)))
    (t : NNReal) (ht : 0 < t) :
    Nonempty (@MetricFlatHalfDiskChart P (pointRegionMetricSpace ha y P) (ρ t)) := by
  letI : MetricSpace P := pointRegionMetricSpace ha y P
  letI : PseudoEMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoEMetricSpace
  have hne : (ρ t).1 ≠ (ρ 0).1 := by
    intro he
    have hsub : ρ t = ρ 0 := Subtype.ext he
    exact ht.ne' (hρ.injective hsub)
  have hoff : (ρ t).1 ∉ pointSignedMarked ν α := by
    intro hm
    exact (Set.disjoint_left.mp hclean) ⟨hm, hne⟩ ⟨t, rfl⟩
  have hνzero : ν (ρ t).1 = 0 := (pointSigned_eq_zero_off_marked hoff).1
  obtain ⟨C, hC⟩ := hν (ρ t).1 (hfront t)
  have hwidth : C.flatPhysicalWidth = Real.pi := by
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    nlinarith [hνzero, hC]
  exact ⟨C.flatHalfDiskChart ha y (ρ t).2 hwidth⟩

end RepulsiveCoulomb
