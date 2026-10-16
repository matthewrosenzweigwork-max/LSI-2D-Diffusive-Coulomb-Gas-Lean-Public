import LeanResearch.RepulsiveCoulomb.PointRetainedSectorFiniteBoundaryCoverClassical

/-!
NEW SOURCE-ONLY, UNCOMPILED. An iteration-facing companion with exactly the
original supplied-sector hypotheses. It retains the actually constructed
Schoenflies sides and their conjugated ambient straightening, full charts,
all-point signed geometry, exact budget changes, and an actual finite boundary
cover. No desired post-cut property is supplied as an input certificate.

The earlier 24 retained-apex bodies are immutable. The repaired finite-cover
successor has distinct declarations and does not import the earlier cover.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Conjugating the constructed negative side gives the ambient preimage
required by the original halfplane premise at the next step. -/
theorem PlanarLineHalfplaneHomeomorphs.retainedApex_closure_negative_eq_upper
    {line : ℝ → ℂ} (D : PlanarLineHalfplaneHomeomorphs line) :
    closure D.negative =
      (D.straightening.trans Complex.conjCLE.toHomeomorph) ⁻¹'
        planarClosedUpperHalfplane := by
  rw [D.negative_eq, ← D.straightening.preimage_closure]
  change D.straightening ⁻¹' closure {z : ℂ | z.im < 0} = _
  rw [Complex.closure_setOfPred_im_lt]
  ext x
  change (D.straightening x).im ≤ 0 ↔
    0 ≤ (starRingEnd ℂ (D.straightening x)).im
  simp only [Complex.conj_im, neg_nonneg]

/-- Concrete output data. The theorem constructs every field from its original
sector and old-region inputs. This structure is never an additional premise. -/
structure PointRetainedApexIterationOutput {m N : ℕ}
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (P S Q : Set ℂ) (top bottom : NNReal → ℂ) (p : ℂ)
    (ν α νQ αQ : ℂ →₀ ℝ) (β : ℝ)
    (C : PointRetainedConeNeighborhood a y P p) where
  old_forward : NNReal → ℂ
  old_forward_closed : IsClosedEmbedding old_forward
  old_forward_zero : old_forward 0 = p
  sides : PlanarLineHalfplaneHomeomorphs (planarTwoRayJoin top old_forward)
  removed_side : Pᶜ ∪ (S \ range top) = sides.positive
  kept_side : interior P \ S = sides.negative
  ambient : ℂ ≃ₜ ℂ
  ambient_eq : ambient = sides.straightening.trans Complex.conjCLE.toHomeomorph
  region_eq : Q = ambient ⁻¹' planarClosedUpperHalfplane
  residual_closure : Q = closure (P \ S)
  residual_side : Q = closure sides.negative
  literal_union : Q = (P \ S) ∪ range top
  literal_difference : Q = P \ (S \ range top)
  subset_old : Q ⊆ P
  isClosed : IsClosed Q
  connected : IsConnected Q
  interior_eq : interior Q = interior P \ S
  frontier_eq : frontier Q = range top ∪ (frontier P \ S)
  halfplane_homeomorph : Nonempty (Q ≃ₜ planarClosedUpperHalfplane)
  exact_contact : S ∩ frontier P = range bottom
  apex_old_frontier : p ∈ frontier P
  apex_retained : p ∈ frontier Q
  top_zero : top 0 = p
  top_closed : IsClosedEmbedding top
  top_metric : ∀ r s, (pointSmoothConformalEDist a y (top r) (top s)).toReal = dist r s
  top_frontier : range top ⊆ frontier Q
  open_top_old_interior : ∀ r : NNReal, 0 < (r:ℝ) → top r ∈ interior P
  apex_chart : ∃ E : PointRetainedConeNeighborhood a y Q p,
    E.flatPhysicalWidth = C.flatPhysicalWidth-β ∧ E.Admissible
  charts : ∀ x ∈ Q, ∃ E : PointRetainedConeNeighborhood a y Q x,
    E.Full ∨ E.Admissible
  exterior_coeff : ∀ x, x ∉ Q → νQ x = 0
  interior_coeff : ∀ x ∈ interior Q, νQ x = -Real.pi*coalescedPointExponent a y x
  boundary_coeff : ∀ x ∈ frontier Q, ∃ E : PointRetainedConeNeighborhood a y Q x,
    νQ x = Real.pi-E.flatPhysicalWidth ∧ E.Admissible
  interior_unchanged : ∀ x ∈ interior Q, x ∈ interior P ∧ νQ x = ν x
  curvature_exact : νQ = ν + Finsupp.single p β
  allocation_exact : αQ = α - Finsupp.single p β
  negative_nonincrease : ∀ x, signedBudgetNeg (νQ x) ≤ signedBudgetNeg (ν x)
  allocation_support : ∀ x, αQ x ≠ 0 → x ∈ Q
  budget_invariant : PointSignedBudgetInvariant νQ αQ
  curvature_mass : pointSignedCurvatureMass νQ αQ = pointSignedCurvatureMass ν α+β
  allocation_mass : pointSignedBudgetMass νQ αQ = pointSignedBudgetMass ν α-β
  boundary_pieces : Fin (N+1) → PointClosedBoundaryGeodesicPiece a y
  boundary_cover : frontier Q = ⋃ i, range (boundary_pieces i).curve
  geodesicallyConvex : PointGeodesicallyConvex a y Q
  intrinsic_metric : ∀ x ∈ Q, ∀ z ∈ Q,
    pointRegionIntrinsicEDist ha y Q x z = pointSmoothConformalEDist a y x z

/-- The same original premises as the frozen retained-apex endpoint, now with
all data needed to use the new halfplane as the original region of another
step. A next clean ray or supplied sector is not claimed by this interface. -/
theorem point_actual_retained_apex_iteration_output
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    (hσP : ∀ x, σ x ∈ P)
    (hbottom : ∀ u : NNReal, σ (retainedApexBottomSource hβ.le hβπ u) ∈ frontier P)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth)
    (ν α : ℂ →₀ ℝ) (hbudget : PointSignedBudgetInvariant ν α)
    (hβbudget : β ≤ α (σ (flatLinkSectorApex hβ.le)))
    (hAremaining : 0 < pointSignedBudgetMass ν α-β)
    (hνoff : ∀ x, x ∉ P → ν x = 0)
    (hνint : ∀ x ∈ interior P, ν x = -Real.pi*coalescedPointExponent a y x)
    (hνboundary : ∀ x ∈ frontier P, ∃ K : PointRetainedConeNeighborhood a y P x,
      ν x = Real.pi-K.flatPhysicalWidth ∧ K.Admissible)
    (hαP : ∀ x, α x ≠ 0 → x ∈ P)
    (hcleanBottom : ∀ u : NNReal, 0 < (u:ℝ) →
      ν (σ (retainedApexBottomSource hβ.le hβπ u)) = 0 ∧
      α (σ (retainedApexBottomSource hβ.le hβπ u)) = 0)
    (hcleanOpen : ∀ x : closedEuclideanSector β,
      0 < ‖x.1‖ → 0 < Complex.arg x.1 → Complex.arg x.1 < β →
        σ x ∈ interior P ∧ ν (σ x) = 0 ∧ α (σ x) = 0) :
    let p := σ (flatLinkSectorApex hβ.le)
    let S := range σ
    let top := fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)
    let bottom := fun u : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ u)
    let Q := closure (P \ S)
    let νQ := retainedApexCurvature ν p β
    let αQ := retainedApexBudget α p β
    Nonempty (PointRetainedApexIterationOutput (N:=N) a ha y P S Q top bottom p ν α νQ αQ β C) := by
  classical
  let p := σ (flatLinkSectorApex hβ.le)
  let S := range σ
  let top := fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)
  let bottom := fun u : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ u)
  let Q := closure (P \ S)
  let νQ := retainedApexCurvature ν p β
  let αQ := retainedApexBudget α p β
  obtain ⟨hcontact,hQclosed,hQpreconn,hQP,hhomeo,hQeq,hQfront,hpQfront,
      hapexChart,hcharts,hOff,hInt,hBoundary,hsameInterior,hnegative,hsupport,
      hinvariant,hV,hA,hconvex,hmetric⟩ :=
    point_actual_retained_apex_sector_removal ha y hβ hβπ σ hσ H hHP hσP hbottom
      pieces hpieces C hC hremain ν α hbudget hβbudget hAremaining
      hνoff hνint hνboundary hαP hcleanBottom hcleanOpen
  have hOld (x : ℂ) (hx : x ∈ frontier P) :
      ∃ K : PointRetainedConeNeighborhood a y P x, K.Admissible := by
    obtain ⟨K,_,hK⟩ := hνboundary x hx
    exact ⟨K,hK⟩
  have hregular (x : closedEuclideanSector β) (hx0 : 0 < ‖x.1‖)
      (hxarg : 0 < Complex.arg x.1) (hxβ : Complex.arg x.1 < β) :
      σ x ∈ interior P ∧ coalescedPointExponent a y (σ x) = 0 := by
    obtain ⟨hxP,hxν,_⟩ := hcleanOpen x hx0 hxarg hxβ
    have he : -Real.pi*coalescedPointExponent a y (σ x) = 0 := (hνint _ hxP).symm.trans hxν
    exact ⟨hxP,(mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr Real.pi_pos.ne')⟩
  obtain ⟨g,hg,hg0,D,hremoved,hkeep,hQside,_,_,_,_,hTopInterior⟩ :=
    pointRetainedSector_construct_residual_of_contact ha y hβ hβπ σ hσ H hHP hσP
      hbottom hOld hregular hcontact
  change Q = closure D.negative at hQside
  change interior P \ S = D.negative at hkeep
  change Q = P \ (S \ range top) at hQeq
  let H' : ℂ ≃ₜ ℂ := D.straightening.trans Complex.conjCLE.toHomeomorph
  have hQambient : Q = H' ⁻¹' planarClosedUpperHalfplane :=
    hQside.trans D.retainedApex_closure_negative_eq_upper
  have hQconnected : IsConnected Q := hQside.symm ▸ D.negative_connected.closure
  have hQinterior : interior Q = interior P \ S := by
    rw [hQside,translatedCut_negative_interior D,hkeep]
  have hP : IsClosed P := by
    rw [hHP]
    exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  have htop0 : top 0 = p := congrArg σ (Subtype.ext (sectorPolar_zero β))
  have hbottom0 : bottom 0 = p := congrArg σ (Subtype.ext (sectorPolar_zero 0))
  have hpfront : p ∈ frontier P := hbottom0 ▸ hbottom 0
  have htopmetric : ∀ r s : NNReal,
      (pointSmoothConformalEDist a y (top r) (top s)).toReal = dist r s := by
    intro r s
    exact (hσ _ _).trans ((retainedApexUpperSource_isometry hβ.le hβπ).dist_eq r s)
  have htopclosed : IsClosedEmbedding top :=
    pointMetricRay_isClosedEmbedding ha y top htopmetric
  have htopfront : range top ⊆ frontier Q := by
    rw [hQfront]
    exact subset_union_left
  have hfront_old_top : frontier Q ⊆ range top ∪ frontier P := by
    rw [hQfront]
    exact union_subset_union_right _ diff_subset
  obtain ⟨fresh,hfresh⟩ := pointRetainedSector_construct_finite_boundary_cover_classical
    ha y hP hQclosed hQP hconvex pieces hpieces top htopmetric htopfront hfront_old_top
  have hQunion : Q = (P \ S) ∪ range top := by
    rw [hQeq]
    ext x
    constructor
    · rintro ⟨hxP,hx⟩
      by_cases hxT : x ∈ range top
      · exact Or.inr hxT
      · exact Or.inl ⟨hxP,fun hxS ↦ hx ⟨hxS,hxT⟩⟩
    · rintro (hx | hx)
      · exact ⟨hx.1,fun hw ↦ hx.2 hw.1⟩
      · obtain ⟨u,rfl⟩ := hx
        exact ⟨hσP _,fun hw ↦ hw.2 (mem_range_self u)⟩
  exact ⟨{
    old_forward := g
    old_forward_closed := hg
    old_forward_zero := hg0
    sides := D
    removed_side := hremoved
    kept_side := hkeep
    ambient := H'
    ambient_eq := rfl
    region_eq := hQambient
    residual_closure := rfl
    residual_side := hQside
    literal_union := hQunion
    literal_difference := hQeq
    subset_old := hQP
    isClosed := hQclosed
    connected := hQconnected
    interior_eq := hQinterior
    frontier_eq := hQfront
    halfplane_homeomorph := hhomeo
    exact_contact := hcontact
    apex_old_frontier := hpfront
    apex_retained := hpQfront
    top_zero := htop0
    top_closed := htopclosed
    top_metric := htopmetric
    top_frontier := htopfront
    open_top_old_interior := hTopInterior
    apex_chart := hapexChart
    charts := hcharts
    exterior_coeff := hOff
    interior_coeff := hInt
    boundary_coeff := hBoundary
    interior_unchanged := hsameInterior
    curvature_exact := rfl
    allocation_exact := rfl
    negative_nonincrease := hnegative
    allocation_support := hsupport
    budget_invariant := hinvariant
    curvature_mass := hV
    allocation_mass := hA
    boundary_pieces := fresh
    boundary_cover := hfresh
    geodesicallyConvex := hconvex
    intrinsic_metric := hmetric
  }⟩

end RepulsiveCoulomb
