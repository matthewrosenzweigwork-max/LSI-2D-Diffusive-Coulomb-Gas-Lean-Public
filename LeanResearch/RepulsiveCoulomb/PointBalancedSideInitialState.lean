import LeanResearch.RepulsiveCoulomb.PointBalancedSideRetainedCharts
import LeanResearch.RepulsiveCoulomb.PointBalancedLineIntrinsicSides
import LeanResearch.RepulsiveCoulomb.PointOriginalFiniteActualAllocation

/-! SOURCE-ONLY, UNCOMPILED. Initial signed halfplanes from the original
nonnegative exponents and locations. The line, fixed sides, ambient halfplane
maps, retained charts, finite boundary cover, and signed invariant are derived. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The literal negative scaling prescribed by the balanced construction. -/
def pointBalancedSideBudget (B : ℝ) (ν : ℂ →₀ ℝ) : ℂ →₀ ℝ :=
  (-((1 + B) / B)) • ν

@[simp] theorem pointBalancedSideBudget_apply (B : ℝ) (ν : ℂ →₀ ℝ) (p : ℂ) :
    pointBalancedSideBudget B ν p = -((1+B)/B) * ν p := by
  simp [pointBalancedSideBudget]

/-- All finite sums are reconciled on their actual supports before using the
balanced side mass. In particular A+V=pi is proved rather than postulated. -/
theorem pointBalancedSideBudget_invariant
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) {B : ℝ} (hB : 0 < B)
    (ν : ℂ →₀ ℝ) (hs : ν.support ⊆ positivePointLocations a y)
    (hn : ∀ p, ν p ≤ 0) (hm : pointLineSignedSideMass a y ν = -(Real.pi * B)) :
    PointSignedBudgetInvariant ν (pointBalancedSideBudget B ν) := by
  classical
  let α := pointBalancedSideBudget B ν
  have hmark : pointSignedMarked ν α ⊆ positivePointLocations a y := by
    intro p hp
    apply hs
    rw [Finsupp.mem_support_iff]
    rcases (mem_pointSignedMarked ν α p).mp hp with hp | hp
    · exact hp
    · intro hz
      exact hp (by simp [α, hz])
  have hV : pointSignedCurvatureMass ν α = -(Real.pi * B) := by
    calc
      pointSignedCurvatureMass ν α = pointLineSignedSideMass a y ν := by
        unfold pointSignedCurvatureMass pointLineSignedSideMass
        apply Finset.sum_subset hmark
        intro p _ hp
        exact (pointSigned_eq_zero_off_marked hp).1
      _ = _ := hm
  have hA : pointSignedBudgetMass ν α = Real.pi * (1+B) := by
    calc
      pointSignedBudgetMass ν α = -((1+B)/B) * pointSignedCurvatureMass ν α := by
        simp only [pointSignedBudgetMass, pointSignedCurvatureMass, α,
          pointBalancedSideBudget_apply, Finset.mul_sum]
      _ = Real.pi * (1+B) := by rw [hV]; field_simp [hB.ne']
  have hk : 1 ≤ (1+B)/B := (le_div_iff₀ hB).mpr (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro p
    change max (-(ν p)) 0 ≤ -((1+B)/B) * ν p
    rw [max_eq_left (neg_nonneg.mpr (hn p))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (neg_nonneg.mpr (hn p))]
  · change 0 < pointSignedBudgetMass ν α
    rw [hA]
    exact mul_pos Real.pi_pos (by linarith)
  · change pointSignedBudgetMass ν α + pointSignedCurvatureMass ν α ≤ Real.pi
    rw [hA, hV]
    linarith

/-- The actual ambient homeomorphisms, closed frontiers and interiors for the
same fixed balanced sides. The lower side is explicitly conjugated. -/
theorem pointMetricLine_fixed_halfplanes
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (line : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (line s) (line t)).toReal = dist s t)
    {A B : Set ℂ} (hA : IsOpen A) (hB : IsOpen B)
    (hAc : IsConnected A) (hBc : IsConnected B) (hAB : Disjoint A B)
    (hcover : A ∪ B = (range line)ᶜ) :
    ∃ H J : ℂ ≃ₜ ℂ,
      closure A = H ⁻¹' planarClosedUpperHalfplane ∧
      closure B = J ⁻¹' planarClosedUpperHalfplane ∧
      frontier (closure A) = range line ∧ frontier (closure B) = range line ∧
      interior (closure A) = A ∧ interior (closure B) = B := by
  obtain ⟨D⟩ := nonempty_pointMetricLine_halfplaneHomeomorphs ha y line hd
  let H := D.straightening
  let J := H.trans Complex.conjCLE.toHomeomorph
  have hpos : closure D.positive = H ⁻¹' planarClosedUpperHalfplane := by
    rw [D.positive_eq, ← H.preimage_closure]
    exact congrArg (fun S ↦ H ⁻¹' S) (Complex.closure_setOfPred_lt_im 0)
  have hneg : closure D.negative = J ⁻¹' planarClosedUpperHalfplane := by
    rw [D.negative_eq, ← H.preimage_closure]
    rw [show closure planarOpenLowerHalfplane = planarClosedLowerHalfplane from
      Complex.closure_setOfPred_im_lt 0]
    ext z
    change (H z).im ≤ 0 ↔ 0 ≤ (starRingEnd ℂ (H z)).im
    simp
  have hip : interior (closure D.positive) = D.positive := by
    rw [← closure_sdiff_frontier, closure_closure, D.positive_closed_frontier,
      ← D.positive_frontier, closure_sdiff_frontier, D.positive_open.interior_eq]
  have hin : interior (closure D.negative) = D.negative := by
    rw [← closure_sdiff_frontier, closure_closure, D.negative_closed_frontier,
      ← D.negative_frontier, closure_sdiff_frontier, D.negative_open.interior_eq]
  rcases D.align_actual_sides hA hB hAc hBc hAB hcover with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨H, J, hpos, hneg, D.positive_closed_frontier, D.negative_closed_frontier, hip, hin⟩
  · exact ⟨J, H, hneg, hpos, D.negative_closed_frontier, D.positive_closed_frontier, hin, hip⟩

/-- Actual all-point boundary coefficient charts on the fixed side pair. At
unmarked line points both physical widths are pi by the complementary bounds. -/
theorem pointBalancedLine_retained_boundary_coefficients
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (line : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (line s) (line t)).toReal = dist s t)
    {A B : Set ℂ} (hA : IsOpen A) (hB : IsOpen B)
    (hAc : IsConnected A) (hBc : IsConnected B) (hAB : Disjoint A B)
    (hcover : A ∪ B = (range line)ᶜ) (Λ : ℂ → ℝ)
    (hw : ∀ p ∈ pointLinePositiveAtomLocations a y line,
      PointLinePhysicalSideWidths a y A B p (Λ p)
        (2*Real.pi + Real.pi*coalescedPointExponent a y p - Λ p) ∧
      Real.pi ≤ Λ p ∧ Real.pi ≤ 2*Real.pi + Real.pi*coalescedPointExponent a y p - Λ p) :
    ∀ p ∈ range line,
      (∃ C : PointRetainedConeNeighborhood a y (closure A) p,
        pointLineSignedSideCurvature a y line A Λ p = Real.pi-C.flatPhysicalWidth ∧ C.Admissible) ∧
      (∃ E : PointRetainedConeNeighborhood a y (closure B) p,
        pointLineSignedSideCurvature a y line B
          (fun q ↦ 2*Real.pi + Real.pi*coalescedPointExponent a y q - Λ q) p =
          Real.pi-E.flatPhysicalWidth ∧ E.Admissible) := by
  classical
  intro p hp
  by_cases hpLoc : p ∈ positivePointLocations a y
  · have hpAtom : p ∈ pointLinePositiveAtomLocations a y line :=
      Finset.mem_filter.mpr ⟨hpLoc, hp⟩
    obtain ⟨hwidth, hwA, hwB⟩ := hw p hpAtom
    obtain ⟨C, E, hC, hE, hc, he⟩ := hwidth.retained_charts ha y hwA hwB
    exact ⟨⟨C, by simp [hpLoc, hp, hC], hc⟩,
      ⟨E, by simp [hpLoc, hp, hE], he⟩⟩
  · have hκ := coalescedPointExponent_eq_zero_of_not_mem a y hpLoc
    obtain ⟨s, rfl⟩ := hp
    obtain ⟨D⟩ := nonempty_pointMetricLine_halfplaneHomeomorphs ha y line hd
    obtain ⟨C, E, hC, hE, hc, he, hsum⟩ :=
      pointMetricLine_construct_admissible_retained_charts ha y line hd D s
    rw [hκ] at hsum
    have hCpi : C.flatPhysicalWidth = Real.pi := by nlinarith
    have hEpi : E.flatPhysicalWidth = Real.pi := by nlinarith
    rcases D.align_actual_sides hA hB hAc hBc hAB hcover with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨C, by simp [hpLoc, hCpi], hc⟩, ⟨E, by simp [hpLoc, hEpi], he⟩⟩
    · exact ⟨⟨E, by simp [hpLoc, hEpi], he⟩, ⟨C, by simp [hpLoc, hCpi], hc⟩⟩

/-- A single genuine complete minimizing line is a finite closed boundary cover. -/
def pointMetricLine_boundary_piece
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} (line : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (line s) (line t)).toReal = dist s t) :
    PointClosedBoundaryGeodesicPiece a y where
  interval := univ
  interval_closed := isClosed_univ
  interval_convex := convex_univ
  curve := fun t ↦ line t.1
  metric := fun s t ↦ hd s.1 t.1

theorem pointMetricLine_boundary_piece_range
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} (line : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (line s) (line t)).toReal = dist s t) :
    range (pointMetricLine_boundary_piece line hd).curve = range line := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩; exact mem_range_self s.1
  · rintro ⟨s, rfl⟩; exact ⟨⟨s, mem_univ s⟩, rfl⟩

/-- All nonboundary coefficients have their original curvature meaning. -/
theorem pointLineSignedSideCurvature_region_coefficients
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (line : ℝ → ℂ)
    {A : Set ℂ} (hfA : frontier A = range line)
    (hint : interior (closure A) = A) (Λ : ℂ → ℝ)
    (hline : Disjoint A (range line)) :
    (∀ p, p ∉ closure A → pointLineSignedSideCurvature a y line A Λ p = 0) ∧
    (∀ p ∈ interior (closure A), pointLineSignedSideCurvature a y line A Λ p =
      -Real.pi * coalescedPointExponent a y p) := by
  classical
  constructor
  · intro p hp
    have hpA : p ∉ A := fun h ↦ hp (subset_closure h)
    have hpL : p ∉ range line := fun h ↦ hp (frontier_subset_closure (hfA.symm ▸ h))
    simp [hpL, hpA]
  · intro p hp
    have hpA : p ∈ A := hint ▸ hp
    have hpL : p ∉ range line := fun h ↦ disjoint_left.mp hline hpA h
    by_cases hpLoc : p ∈ positivePointLocations a y
    · simp [hpLoc, hpL, hpA, neg_mul]
    · simp [hpLoc, coalescedPointExponent_eq_zero_of_not_mem a y hpLoc]

/-- Output data only. Neither halfplane states nor their final coefficient
cancellation are premises to the original-input construction. -/
structure PointBalancedInitialStates {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) where
  left : Set ℂ
  right : Set ℂ
  curvatureLeft : ℂ →₀ ℝ
  curvatureRight : ℂ →₀ ℝ
  allocationLeft : ℂ →₀ ℝ
  allocationRight : ℂ →₀ ℝ
  leftState : PointGeometricCutState a y left curvatureLeft allocationLeft
  rightState : PointGeometricCutState a y right curvatureRight allocationRight
  disjoint_interiors : Disjoint (interior left) (interior right)
  cancellation : ∀ p, (1 - 1/(1+pointExteriorHalfMass a)) *
    (allocationLeft p + allocationRight p) = Real.pi * coalescedPointExponent a y p

/-- Both actual states are constructed solely from the original ha,y and the
positive-mass case test. Collisions and zero original weights are unrestricted. -/
theorem exists_pointBalancedInitialStates
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) : Nonempty (PointBalancedInitialStates a y) := by
  classical
  obtain ⟨line, _, hd, A, B, hA, hBo, hAc, hBc, hAB, hcover, hfA, hfB, Λ,
    hw, hsA, hsB, hn, hmA, hmB, hsplit⟩ :=
    exists_pointConformal_actual_curvature_balanced_line ha y
  let ΛB := fun p ↦ 2*Real.pi + Real.pi*coalescedPointExponent a y p - Λ p
  let νA := pointLineSignedSideCurvature a y line A Λ
  let νB := pointLineSignedSideCurvature a y line B ΛB
  let αA := pointBalancedSideBudget (pointExteriorHalfMass a) νA
  let αB := pointBalancedSideBudget (pointExteriorHalfMass a) νB
  obtain ⟨H, J, hH, hJ, hfAc, hfBc, hiA, hiB⟩ :=
    pointMetricLine_fixed_halfplanes ha y line hd hA hBo hAc hBc hAB hcover
  have hbd := pointBalancedLine_retained_boundary_coefficients ha y line hd
    hA hBo hAc hBc hAB hcover Λ hw
  have hAL : Disjoint A (range line) := disjoint_left.mpr (by
    intro p hp hl
    have h := (show p ∈ A ∪ B from Or.inl hp)
    rw [hcover] at h
    exact h hl)
  have hBL : Disjoint B (range line) := disjoint_left.mpr (by
    intro p hp hl
    have h := (show p ∈ A ∪ B from Or.inr hp)
    rw [hcover] at h
    exact h hl)
  obtain ⟨hAoff, hAint⟩ := pointLineSignedSideCurvature_region_coefficients a y line hfA hiA Λ hAL
  obtain ⟨hBoff, hBint⟩ := pointLineSignedSideCurvature_region_coefficients a y line hfB hiB ΛB hBL
  have hαA : ∀ p, αA p ≠ 0 → p ∈ closure A := by
    intro p hp
    by_contra hn
    exact hp (by simp [αA, νA, hAoff p hn])
  have hαB : ∀ p, αB p ≠ 0 → p ∈ closure B := by
    intro p hp
    by_contra hn
    exact hp (by simp [αB, νB, hBoff p hn])
  have hbA : PointSignedBudgetInvariant νA αA :=
    pointBalancedSideBudget_invariant a y hB νA hsA (fun p ↦ (hn p).1) hmA
  have hbB : PointSignedBudgetInvariant νB αB :=
    pointBalancedSideBudget_invariant a y hB νB hsB (fun p ↦ (hn p).2) hmB
  let pieces : Fin 1 → PointClosedBoundaryGeodesicPiece a y :=
    fun _ ↦ pointMetricLine_boundary_piece line hd
  have hcA : frontier (closure A) = ⋃ i, range (pieces i).curve := by
    simpa only [pieces, iUnion_const, pointMetricLine_boundary_piece_range] using hfAc
  have hcB : frontier (closure B) = ⋃ i, range (pieces i).curve := by
    simpa only [pieces, iUnion_const, pointMetricLine_boundary_piece_range] using hfBc
  let KA := PointGeometricCutState.ofOriginal ha H hH hAoff hAint
    (fun p hp ↦ (hbd p (hfAc ▸ hp)).1) hαA hbA pieces hcA
  let KB := PointGeometricCutState.ofOriginal ha J hJ hBoff hBint
    (fun p hp ↦ (hbd p (hfBc ▸ hp)).2) hαB hbB pieces hcB
  refine ⟨⟨closure A, closure B, νA, νB, αA, αB, KA, KB, ?_, ?_⟩⟩
  · simpa only [hiA, hiB] using hAB
  · intro p
    change (1 - 1/(1+pointExteriorHalfMass a)) *
      (-((1+pointExteriorHalfMass a)/pointExteriorHalfMass a) * νA p +
        -((1+pointExteriorHalfMass a)/pointExteriorHalfMass a) * νB p) = _
    rw [← mul_add, show νA p + νB p = -(Real.pi * coalescedPointExponent a y p) from hsplit p]
    have h1 : 1 + pointExteriorHalfMass a ≠ 0 := ne_of_gt (by linarith)
    field_simp [hB.ne', h1]
    ring

end RepulsiveCoulomb
