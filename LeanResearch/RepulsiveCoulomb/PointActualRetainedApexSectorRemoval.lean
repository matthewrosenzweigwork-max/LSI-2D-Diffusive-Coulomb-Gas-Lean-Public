import LeanResearch.RepulsiveCoulomb.PointRetainedSectorExactContact
import LeanResearch.RepulsiveCoulomb.PointRetainedSectorResidualTopology
import LeanResearch.RepulsiveCoulomb.PointRetainedApexAllPointAssembly
import LeanResearch.RepulsiveCoulomb.PointRetainedSectorFullInteriorChart

/-!
SOURCE-ONLY, NOT COMPILED. The actual supplied-sector retained-apex case.
Exact contact, literal residual halfplane, full retained charts, all-point
geometric signed coefficients, residual allocation support and signed budget
are constructed from the original sector, original region, and original true
signed invariant. No desired contact/residual/chart/update certificate is input.

The finite old boundary cover and original full retained-chart coefficient
formulas are actual geometric assumptions on P. Original open-sector and clean
bottom conditions refer to nu/alpha, not merely to ambient puncture labels.
A clean old boundary point may remain an ambient singular cone of retained
width pi; its ambient exponent is NEVER inferred zero from nu=alpha=0.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The removed sector below its free ray has zero ORIGINAL coefficients.
The apex is on the free ray and is therefore never incorrectly deleted here. -/
theorem retainedSector_removed_coefficients_zero
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ) (ν α : ℂ →₀ ℝ)
    (hbottom : ∀ u : NNReal, 0 < (u:ℝ) →
      ν (σ (retainedApexBottomSource hβ.le hβπ u)) = 0 ∧
      α (σ (retainedApexBottomSource hβ.le hβπ u)) = 0)
    (hopen : ∀ x : closedEuclideanSector β,
      0 < ‖x.1‖ → 0 < Complex.arg x.1 → Complex.arg x.1 < β →
        ν (σ x) = 0 ∧ α (σ x) = 0) :
    ∀ z ∈ range σ \ range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)),
      ν z = 0 ∧ α z = 0 := by
  rintro z ⟨⟨x,rfl⟩,hxT⟩
  have hxupper : x ∉ range (retainedApexUpperSource hβ.le hβπ) := by
    rintro ⟨u,hu⟩
    exact hxT ⟨u,congrArg σ hu⟩
  obtain ⟨hx0,hxβ⟩ := retainedSector_source_off_upper hβ hβπ x hxupper
  by_cases hxarg : Complex.arg x.1 = 0
  · have he : retainedApexBottomSource hβ.le hβπ ⟨‖x.1‖,norm_nonneg _⟩ = x := by
      apply Subtype.ext
      change sectorPolar ‖x.1‖ 0 = x.1
      rw [← hxarg,sectorPolar_norm_arg]
    simpa only [he] using hbottom ⟨‖x.1‖,norm_nonneg _⟩ hx0
  · exact hopen x hx0 (lt_of_le_of_ne x.2.1 (Ne.symm hxarg)) hxβ

/-- COMPLETE SOURCE DRAFT of Pro retained-apex removal for an ACTUAL supplied
sector. The function nuQ is independently characterized at every ambient point
by the constructed residual geometry, making nuQ=nu+beta*delta_p genuine.
No compiler acceptance is claimed for this draft or its new dependency chain. -/
theorem point_actual_retained_apex_sector_removal
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
    let Q := closure (P \ S)
    let νQ := retainedApexCurvature ν p β
    let αQ := retainedApexBudget α p β
    S ∩ frontier P = range (fun u : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ u)) ∧
    IsClosed Q ∧ IsPreconnected Q ∧ Q ⊆ P ∧
    Nonempty (Q ≃ₜ planarClosedUpperHalfplane) ∧
    Q = P \ (S \ range top) ∧ frontier Q = range top ∪ (frontier P \ S) ∧
    p ∈ frontier Q ∧
    (∃ E : PointRetainedConeNeighborhood a y Q p,
      E.flatPhysicalWidth = C.flatPhysicalWidth-β ∧ E.Admissible) ∧
    (∀ x ∈ Q, ∃ E : PointRetainedConeNeighborhood a y Q x, E.Full ∨ E.Admissible) ∧
    (∀ x, x ∉ Q → νQ x = 0) ∧
    (∀ x ∈ interior Q, νQ x = -Real.pi*coalescedPointExponent a y x) ∧
    (∀ x ∈ frontier Q, ∃ E : PointRetainedConeNeighborhood a y Q x,
      νQ x = Real.pi-E.flatPhysicalWidth ∧ E.Admissible) ∧
    (∀ x ∈ interior Q, x ∈ interior P ∧ νQ x = ν x) ∧
    (∀ x, signedBudgetNeg (νQ x) ≤ signedBudgetNeg (ν x)) ∧
    (∀ x, αQ x ≠ 0 → x ∈ Q) ∧ PointSignedBudgetInvariant νQ αQ ∧
    pointSignedCurvatureMass νQ αQ = pointSignedCurvatureMass ν α+β ∧
    pointSignedBudgetMass νQ αQ = pointSignedBudgetMass ν α-β ∧
    PointGeodesicallyConvex a y Q ∧
    (∀ x ∈ Q, ∀ z ∈ Q, pointRegionIntrinsicEDist ha y Q x z = pointSmoothConformalEDist a y x z) := by
  let p := σ (flatLinkSectorApex hβ.le)
  let S := range σ
  let top := fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)
  let Q := closure (P \ S)
  let νQ := retainedApexCurvature ν p β
  let αQ := retainedApexBudget α p β
  have hP : IsClosed P := by
    rw [hHP]
    exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  have hOld (x : ℂ) (hx : x ∈ frontier P) :
      ∃ K : PointRetainedConeNeighborhood a y P x, K.Admissible := by
    obtain ⟨K,_,hK⟩ := hνboundary x hx
    exact ⟨K,hK⟩
  have hνraw (x : ℂ) (hx : x ∈ frontier P) :
      ∃ K : PointRetainedConeNeighborhood a y P x,
        ν x = Real.pi-(1+coalescedPointExponent a y x/2)*(K.hi-K.lo) := by
    obtain ⟨K,hK,_⟩ := hνboundary x hx
    refine ⟨K,?_⟩
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
      add_comm (coalescedPointExponent a y x/2) 1] using hK
  have hregular (x : closedEuclideanSector β) (hx0 : 0 < ‖x.1‖)
      (hxarg : 0 < Complex.arg x.1) (hxβ : Complex.arg x.1 < β) :
      σ x ∈ interior P ∧ coalescedPointExponent a y (σ x) = 0 := by
    obtain ⟨hxP,hxν,_⟩ := hcleanOpen x hx0 hxarg hxβ
    have he : -Real.pi*coalescedPointExponent a y (σ x) = 0 := (hνint _ hxP).symm.trans hxν
    exact ⟨hxP,(mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr Real.pi_pos.ne')⟩
  have hcontact := pointRetainedSector_exact_old_boundary_contact ha y hβ hβπ σ hσ H hHP hσP
    hbottom (fun x hx0 hxarg hxβ ↦ (hcleanOpen x hx0 hxarg hxβ).1)
    pieces hpieces C hC hremain hbudget hβbudget hνraw
  obtain ⟨g,hg,hg0,D,hA,hR,hQclosedSide,hQeq,hQP,hQfront,hhomeo,hTopInterior⟩ :=
    pointRetainedSector_construct_residual_of_contact ha y hβ hβπ σ hσ H hHP hσP
      hbottom hOld hregular hcontact
  have hQclosed : IsClosed Q := isClosed_closure
  have hQconn : IsPreconnected Q := by
    change IsPreconnected (closure (P \ range σ))
    rw [hQclosedSide]
    exact D.negative_connected.isPreconnected.closure
  have htop0 : top 0 = p := congrArg σ (Subtype.ext (sectorPolar_zero β))
  have hbottom0 : σ (retainedApexBottomSource hβ.le hβπ 0) = p :=
    congrArg σ (Subtype.ext (sectorPolar_zero 0))
  have hpfront : p ∈ frontier P := hbottom0 ▸ hbottom 0
  have hpT : p ∈ range top := ⟨0,htop0⟩
  have hpQfront : p ∈ frontier Q := hQfront.symm ▸ Or.inl hpT
  have hclean := retainedSector_removed_coefficients_zero hβ hβπ σ ν α hcleanBottom
    (fun x hx0 hxarg hxβ ↦ (hcleanOpen x hx0 hxarg hxβ).2)
  obtain ⟨hσclosed,_⟩ := pointRetainedSector_closed_proper ha y hβ hβπ σ hσ
  have hSclosed : IsClosed S := hσclosed.isClosed_range
  let δ := C.radius/2
  have hδ : 0 < δ := half_pos C.radius_pos
  have hδC : δ < C.radius := half_lt_self C.radius_pos
  have hfrontδ : σ (flatLinkSectorDiskInclusion
      (flatLinkSectorDiskPoint hβ.le hβπ δ ⟨hδ.le,le_rfl⟩ 0)) ∈ frontier P := by
    have he : flatLinkSectorDiskInclusion (flatLinkSectorDiskPoint hβ.le hβπ δ ⟨hδ.le,le_rfl⟩ 0) =
        retainedApexBottomSource hβ.le hβπ ⟨δ,hδ.le⟩ := by
      apply Subtype.ext
      change sectorPolar δ (β * (0 : unitInterval).1) = sectorPolar δ 0
      simp only [Set.Icc.coe_zero, mul_zero]
    rw [he]
    exact hbottom _
  obtain ⟨hapexChart,_,_,hapexWidth,_,hapexAdm⟩ :=
    pointRetainedApex_construct_apex_chart_from_frontier ha y hβ hβπ hδ σ hσ hσP C hC hremain
      hδ le_rfl hδC hfrontδ hQeq
  obtain ⟨hOff,hInt,hBoundary⟩ := pointRetainedApex_all_point_geometric_coefficients
    ha y hβ hβπ hδ σ hσ hP hSclosed hσP C hC hremain hpfront hδ le_rfl hδC hfrontδ
    ν hνoff hνint hνboundary (fun x hx ↦ (hclean x hx).1) hQeq rfl hQfront hTopInterior
  have hcharts (x : ℂ) (hx : x ∈ Q) :
      ∃ E : PointRetainedConeNeighborhood a y Q x, E.Full ∨ E.Admissible := by
    by_cases hi : x ∈ interior Q
    · obtain ⟨E,hE⟩ := pointRetainedSector_construct_full_interior_chart ha y hi
      exact ⟨E,Or.inl hE⟩
    · obtain ⟨E,_,hE⟩ := hBoundary x ⟨subset_closure hx,hi⟩
      exact ⟨E,Or.inr hE⟩
  have hsameInterior (x : ℂ) (hx : x ∈ interior Q) : x ∈ interior P ∧ νQ x = ν x := by
    have hxP := interior_mono hQP hx
    exact ⟨hxP,(hInt x hx).trans (hνint x hxP).symm⟩
  have hnegative (x : ℂ) : signedBudgetNeg (νQ x) ≤ signedBudgetNeg (ν x) := by
    by_cases hxp : x = p
    · subst x
      rw [retainedApexCurvature_at]
      change max (-(ν p+β)) 0 ≤ max (-(ν p)) 0
      exact max_le_max (by linarith) le_rfl
    · change signedBudgetNeg (retainedApexCurvature ν p β x) ≤ signedBudgetNeg (ν x)
      rw [retainedApexCurvature_off ν β hxp]
  have hsupport := retainedApex_budget_support_retained (β := β) hQeq (hσP _) hpT hαP
    (fun x hx ↦ (hclean x hx).2)
  have hinvariant := hbudget.retainedApex p hβbudget hAremaining
  obtain ⟨hV,hA'⟩ := retainedApex_mass_changes ν α p β
  obtain ⟨hconvex,hmetric⟩ := pointRetainedRegion_intrinsic_eq_and_geodesicallyConvex ha y
    hQclosed hQconn hcharts
  exact ⟨hcontact,hQclosed,hQconn,hQP,hhomeo,hQeq,hQfront,hpQfront,
    ⟨hapexChart,hapexWidth,hapexAdm⟩,hcharts,hOff,hInt,hBoundary,hsameInterior,hnegative,
    hsupport,hinvariant,hV,hA',hconvex,hmetric⟩

end RepulsiveCoulomb
