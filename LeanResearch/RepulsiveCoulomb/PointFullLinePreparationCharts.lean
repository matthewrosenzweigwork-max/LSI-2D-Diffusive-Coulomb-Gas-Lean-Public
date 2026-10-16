import LeanResearch.RepulsiveCoulomb.PointFullStripMarkedFirstContact
import LeanResearch.RepulsiveCoulomb.PointActualFullStripResidual
import LeanResearch.RepulsiveCoulomb.PointFullLinePreparationAlgebra

/-! SOURCE-ONLY, UNCOMPILED. Full interior charts and genuine boundary turns
supply the old full/admissible retained geometry needed for contained minimizers.
The old whole-boundary metric line remains an explicit independent input. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- The previously constructed full unwrapped circle covers its whole disk. -/
theorem pointFullLine_full_of_full_interval
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    (hlo : C.lo = 0) (hhi : C.hi = 2 * Real.pi) : C.Full := by
  intro z hz
  apply (C.retained z hz).mpr
  rw [hlo, hhi, pointClosedRadialInterval_full_disk]
  exact C.onto.mapsTo hz

theorem pointFullLine_interior_full_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (hp : p ∈ interior P) :
    ∃ C : PointRetainedConeNeighborhood a y P p, C.Full := by
  obtain ⟨C, hlo, hhi, _⟩ := pointInterior_construct_full_retained_chart ha y hp
  exact ⟨C, pointFullLine_full_of_full_interval C hlo hhi⟩

/-- The old all-point Full/Admissible input is derived from actual interior
charts and clean genuine boundary turns. No old convexity certificate is added. -/
theorem pointFullLine_old_full_or_admissible_charts
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {turn : ℂ → ℝ} {ν α : ℂ →₀ ℝ}
    (hν : PointFullStripCurvatureRepresentation a y P turn ν)
    (hturn : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      turn p = Real.pi - C.flatPhysicalWidth)
    (hclean : Disjoint (↑(pointSignedMarked ν α) : Set ℂ) (frontier P)) :
    ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Full ∨ C.Admissible := by
  intro p hp
  by_cases hi : p ∈ interior P
  · obtain ⟨C, hC⟩ := pointFullLine_interior_full_chart ha y hi
    exact ⟨C, Or.inl hC⟩
  · have hf : p ∈ frontier P := ⟨subset_closure hp, hi⟩
    obtain ⟨C, hC⟩ := hturn p hf
    have ht : turn p = 0 := by
      by_contra ht
      exact disjoint_left.mp hclean (hν.boundary_marked α p hf ht) hf
    have hw : C.flatPhysicalWidth = Real.pi := by rw [ht] at hC; linarith
    refine ⟨C, Or.inr ?_⟩
    unfold PointRetainedConeNeighborhood.Admissible
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth at hw
    have he := coalescedPointExponent_nonneg a y p
    have hπe : 0 ≤ Real.pi * coalescedPointExponent a y p := mul_nonneg Real.pi_pos.le he
    nlinarith

/-- Source coordinate normalization joining the two recovered packages. -/
theorem pointFullLine_top_point_eq {h : ℝ} (hh : 0 ≤ h) (r : ℝ) :
    fullStripPoint r ⟨h, hh, le_rfl⟩ = fullStripTop hh r := by
  apply Subtype.ext
  apply Complex.ext <;> simp [fullStripPoint, fullStripTop, flatShearedPoint]

end RepulsiveCoulomb
