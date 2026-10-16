module

public import LeanResearch.RepulsiveCoulomb.PointDisappearingSectorExactContact
public import LeanResearch.RepulsiveCoulomb.PointDisappearingSectorResidualTopology
public import LeanResearch.RepulsiveCoulomb.PointDisappearingSectorCurvatureMeaning
public import LeanResearch.RepulsiveCoulomb.DisappearingSectorRemovedCoefficients
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripStateAdapters
public import LeanResearch.RepulsiveCoulomb.PointRetainedSectorFiniteBoundaryCoverClassical

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. End-to-end actual supplied-sector Case II source
construction, including exact finite departure/contact, actual ambient H',
Full-or-Admissible charts, all-point general ambient finite coefficients,
residual support, true budget invariant and finite-boundary-cover preservation.
No desired z/contact/residual/chart/update/finite-cover certificate is input.
All frozen prerequisite bodies remain unchanged. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Output-only reusable iteration state, produced after the actual cut.
The new ambient straightening is retained, so no geometric information is lost
by returning only an abstract homeomorphism of the closed residual subtype. -/
structure PointDisappearingSectorIterationOutput {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (N : ℕ) (P S Q : Set ℂ)
    (τ : NNReal → ℂ) (p : ℂ) (ν μ α αQ : ℂ →₀ ℝ) (β : ℝ) where
  old_forward : NNReal → ℂ
  old_forward_closed : IsClosedEmbedding old_forward
  old_forward_zero : old_forward 0=τ 0
  old_forward_range : range old_forward=insert (τ 0) (frontier P\S)
  old_forward_meet : range old_forward∩S={τ 0}
  sides : PlanarLineHalfplaneHomeomorphs (planarTwoRayJoin τ old_forward)
  removed_side : Pᶜ∪(S\range τ)=sides.positive
  kept_side : interior P\S=sides.negative
  residual_closure : Q=closure (P\S)
  residual_side : Q=closure sides.negative
  state : PointRetainedSignedHalfplaneState a y Q μ αQ
  state_ambient : state.ambient=sides.negativeAmbientStraightening
  literal_union : Q=(P\S)∪range τ
  literal_difference : Q=P\(S\range τ)
  subset_old : Q⊆P
  interior_eq : interior Q=interior P\S
  frontier_eq : frontier Q=range τ∪range old_forward
  apex_removed : p∉Q
  departure_retained : τ 0∈frontier Q
  departure_negative : ν (τ 0)<0
  departure_ne_apex : τ 0≠p
  top_metric : ∀ t u,(pointSmoothConformalEDist a y (τ t) (τ u)).toReal=dist t u
  open_top_old_interior : ∀ t : NNReal,0<(t:ℝ) → τ t∈interior P
  open_top_coeff : ∀ t : NNReal,0<(t:ℝ) → μ (τ t)=ν (τ t)
  departure_chart : ∃ C : PointRetainedConeNeighborhood a y P (τ 0),
    ∃ E : PointRetainedConeNeighborhood a y Q (τ 0),
      C.Admissible ∧ E.Admissible ∧ ν (τ 0)=Real.pi-C.flatPhysicalWidth ∧
      μ (τ 0)=Real.pi-E.flatPhysicalWidth ∧ E.flatPhysicalWidth=C.flatPhysicalWidth-Real.pi
  open_top_chart : ∀ t : NNReal,0<(t:ℝ) →
    ∃ E : PointRetainedConeNeighborhood a y Q (τ t),E.Admissible ∧
      E.flatPhysicalWidth=(coalescedPointExponent a y (τ t)/2+1)*(2*Real.pi)-Real.pi ∧
      μ (τ t)=Real.pi-E.flatPhysicalWidth
  apex_budget_spent : α p=β
  apex_old_coeff : ν p=Real.pi-β
  apex_old_nonnegative : 0≤ν p
  old_positive_mass_away_zero : pointSignedPositiveMassAway ν α p=0
  old_off_apex_nonpositive : ∀ x,x≠p → ν x≤0
  old_off_apex_budget : ∀ x,x≠p → α x=signedBudgetNeg (ν x)
  curvature_exact : μ=ν-Finsupp.single p (ν p)+Finsupp.single (τ 0) Real.pi
  allocation_exact : αQ=α-Finsupp.single p β
  allocation_is_old_negative : αQ=pointSignedNegativePart ν
  negative_nonincrease : ∀ x,signedBudgetNeg (μ x) ≤ signedBudgetNeg (ν x)
  budget_invariant : PointSignedBudgetInvariant μ αQ
  curvature_mass : pointSignedCurvatureMass μ αQ=pointSignedCurvatureMass ν α+β
  allocation_mass : pointSignedBudgetMass μ αQ=pointSignedBudgetMass ν α-β
  intrinsic_eq : ∀ ha : (∀ j,0≤a j), ∀ x∈Q,∀ z∈Q,
    pointRegionIntrinsicEDist ha y Q x z=pointSmoothConformalEDist a y x z
  finite_boundary_cover : ∃ fresh : Fin (N+1) → PointClosedBoundaryGeodesicPiece a y,
    frontier Q=⋃ i,range (fresh i).curve

/-- COMPLETE SOURCE DRAFT of Pro disappearing-apex removal. The actual
first departure and its exact contact are outputs. All-point coefficient
meaning, ambient straightening and a new finite geodesic boundary cover are
constructed before returning the reusable iteration state. -/
theorem point_actual_disappearing_apex_sector_iteration
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (H : ℂ≃ₜℂ) (hHP : P=H ⁻¹' planarClosedUpperHalfplane)
    (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ t : NNReal,σ (retainedApexBottomSource hβ.le hβπ t)∈frontier P)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P=⋃ i,range (pieces i).curve)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β)
    (ν α : ℂ →₀ ℝ) (hbudget : PointSignedBudgetInvariant ν α)
    (hβα : β≤α (σ (flatLinkSectorApex hβ.le)))
    (hremaining : 0<pointSignedBudgetMass ν α-β)
    (hνO : ∀ x,x∉P → ν x=0)
    (hνI : ∀ x∈interior P,ν x= -Real.pi*coalescedPointExponent a y x)
    (hνB : ∀ x∈frontier P,∃ K : PointRetainedConeNeighborhood a y P x,
      ν x=Real.pi-K.flatPhysicalWidth ∧ K.Admissible)
    (hαP : ∀ x,α x≠0 → x∈P)
    (hcleanBottom : ∀ t : NNReal,0<(t:ℝ) →
      ν (σ (retainedApexBottomSource hβ.le hβπ t))=0 ∧ α (σ (retainedApexBottomSource hβ.le hβπ t))=0)
    (hcleanOpen : ∀ x : closedEuclideanSector β,0<‖x.1‖ → 0<Complex.arg x.1 → Complex.arg x.1<β →
      σ x∈interior P ∧ ν (σ x)=0 ∧ α (σ x)=0) :
    ∃ r : NNReal,0<(r:ℝ) ∧
      (range σ∩frontier P=
        range (fun t : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ t)) ∪
        (fun t : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ t)) '' Icc 0 r) ∧
      (∀ t : NNReal,0<(t:ℝ) → t<r →
        ν (σ (retainedApexUpperSource hβ.le hβπ t))=0 ∧ α (σ (retainedApexUpperSource hβ.le hβπ t))=0) ∧
      let p:=σ (flatLinkSectorApex hβ.le)
      let S:=range σ
      let τ : NNReal → ℂ:=fun t ↦ σ (disappearingSectorTail hβ.le hβπ r t)
      let Q:=closure (P\S)
      let μ:=disappearingApexCurvature ν p (τ 0)
      let αQ:=retainedApexBudget α p β
      Nonempty (PointDisappearingSectorIterationOutput a y N P S Q τ p ν μ α αQ β) := by
  let p:=σ (flatLinkSectorApex hβ.le)
  let S:=range σ
  have hP : IsClosed P:=by rw [hHP]; exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  have hPconn : IsPreconnected P:=by
    obtain ⟨_,_,hc,_,_,_,hcl,_,_,_⟩:=planar_halfplane_partition
    have hclosedconn : IsConnected planarClosedUpperHalfplane:=hcl ▸ hc.closure
    rw [hHP]
    exact (H.isConnected_preimage.mpr hclosedconn).isPreconnected
  have hpfront : p∈frontier P:=by
    have he : retainedApexBottomSource hβ.le hβπ 0=flatLinkSectorApex hβ.le:=Subtype.ext (sectorPolar_zero 0)
    simpa only [he] using hbottom 0
  obtain ⟨Kp,hνKp,_⟩:=hνB p hpfront
  have hwidthCp : C.flatPhysicalWidth=Kp.flatPhysicalWidth:=by
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,p,add_comm]
      using C.physical_width_eq Kp
  have hνC : ν p=Real.pi-C.flatPhysicalWidth:=by rw [hwidthCp]; exact hνKp
  have hboundary : ν p=Real.pi-β:=by rwa [hfull] at hνC
  have hregular (x : closedEuclideanSector β) (hx0 : 0<‖x.1‖)
      (hxarg : 0<Complex.arg x.1) (hxβ : Complex.arg x.1<β) :
      σ x∈interior P ∧ coalescedPointExponent a y (σ x)=0:=by
    obtain ⟨hxP,hxν,_⟩:=hcleanOpen x hx0 hxarg hxβ
    have he : -Real.pi*coalescedPointExponent a y (σ x)=0:=(hνI _ hxP).symm.trans hxν
    exact ⟨hxP,(mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr Real.pi_ne_zero)⟩
  have hOld : ∀ x∈frontier P,∃ K : PointRetainedConeNeighborhood a y P x,K.Admissible:=by
    intro x hx
    obtain ⟨K,_,hK⟩:=hνB x hx
    exact ⟨K,hK⟩
  obtain ⟨r,hr,hzne,hzneg,hprefix,hprefixzero,hterminal⟩:=pointDisappearingApex_construct_actual_first_departure
    ha y hβ hβπ σ hσ hPconn hσP hbottom hregular C hC hfull hbudget hνC hβα hremaining
    hνO hνI hνB (fun t ht ↦ (hcleanBottom t ht).1)
  obtain ⟨hcontact,hopenTop⟩:=pointDisappearingSector_exact_contact_of_departure ha y hβ hβπ σ hσ
    H hHP hσP hbottom pieces hpieces r hr hprefix hterminal hbudget hboundary hβα hzneg hνB
    (fun x hx0 hxarg hxβ ↦ (hcleanOpen x hx0 hxarg hxβ).1)
  let τ : NNReal → ℂ:=fun t ↦ σ (disappearingSectorTail hβ.le hβπ r t)
  let Q:=closure (P\S)
  let z:=τ 0
  let μ:=disappearingApexCurvature ν p z
  let αQ:=retainedApexBudget α p β
  have hτ0 : z=σ (retainedApexUpperSource hβ.le hβπ r):=by simp only [z,τ,disappearingSectorTail,add_zero]
  have hzneq : z≠p:=by simpa only [hτ0] using hzne
  have hznegative : ν z<0:=by simpa only [hτ0] using hzneg
  obtain ⟨g,hg,hg0,hgrange,hgmeet,D,hremoved,hkept,hQside,hQunion,hQdiff,hQP,hQI,hQfront,hpQ,hzQ⟩:=
    pointDisappearingSector_construct_actual_residual_topology ha y hβ hβπ σ hσ H hHP hσP hbottom
      hOld hregular C hC hfull r hr hprefix hcontact
  have hclean:=disappearingSector_removed_coefficients_zero hβ hβπ σ ν α r hcleanBottom
    (fun x hx0 hxarg hxβ ↦ (hcleanOpen x hx0 hxarg hxβ).2) hprefixzero
  obtain ⟨hμO,hμI,hμB⟩:=pointDisappearingSector_all_point_curvature ha y hβ hβπ σ hσ hP hσP
    r hr hprefix hopenTop hpfront hzne ν hνI hνB hνO hzneg
    (fun x hx hxp ↦ (hclean x hx hxp).1) (Q:=Q) rfl hQdiff hQfront
  have hμrewrite : disappearingApexCurvature ν p (σ (retainedApexUpperSource hβ.le hβπ r))=μ:=by rw [← hτ0]
  rw [hμrewrite] at hμO hμI hμB
  obtain ⟨hαp,hνp,hposAway,hoffNonpos,hoffBudget,hαpart⟩:=hbudget.disappearingApex_equalities p hboundary hβπ hβα
  have hsupport : ∀ x,αQ x≠0 → x∈Q:=disappearingApex_budget_support_retained hαp hQdiff hαP
    (fun x hx hxp ↦ (hclean x hx hxp).2)
  have hnewcharts : ∀ x∈Q,∃ E : PointRetainedConeNeighborhood a y Q x,E.Full ∨ E.Admissible:=by
    intro x hx
    by_cases hi : x∈interior Q
    · obtain ⟨E,hE⟩:=pointRetainedSector_construct_full_interior_chart ha y hi
      exact ⟨E,Or.inl hE⟩
    · obtain ⟨E,_,hE⟩:=hμB x ⟨subset_closure hx,hi⟩
      exact ⟨E,Or.inr hE⟩
  have hQambient : Q=D.negativeAmbientStraightening ⁻¹' planarClosedUpperHalfplane:=
    hQside.trans D.closure_negative_eq_ambient_upper
  have hQconnected : IsConnected Q:=by
    have hside : Q=closure D.negative := hQside
    exact hside.symm ▸ D.negative_connected.closure
  let state : PointRetainedSignedHalfplaneState a y Q μ αQ:=
    { ambient:=D.negativeAmbientStraightening
      region_eq:=hQambient
      connected:=hQconnected
      charts:=hnewcharts
      interior_coeff:=hμI
      boundary_coeff:=fun x hx ↦ by obtain ⟨E,hcoeff,hE⟩:=hμB x hx; exact ⟨E,hE,hcoeff⟩
      exterior_coeff:=hμO
      allocation_support:=hsupport }
  obtain ⟨hconv,hIntrinsic⟩:=state.intrinsic_eq_and_geodesicallyConvex ha
  have hτmetric (t u : NNReal) : (pointSmoothConformalEDist a y (τ t) (τ u)).toReal=dist t u:=
    (hσ _ _).trans ((disappearingSectorTail_isometry hβ.le hβπ r).dist_eq t u)
  have hτfront : range τ⊆frontier Q:=by rw [hQfront]; exact subset_union_left
  have hfrontSub : frontier Q⊆range τ∪frontier P:=by
    rw [hQfront]
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr hx.1
  obtain ⟨fresh,hfresh⟩:=pointRetainedSector_construct_finite_boundary_cover_classical ha y hP isClosed_closure
    hQP hconv pieces hpieces τ hτmetric hτfront hfrontSub
  have hfrontFinal : frontier Q=range τ∪range g:=by
    rw [hQfront,hgrange]
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (mem_insert_of_mem _ hx)
    · rintro (hx | hx)
      · exact Or.inl hx
      · rcases mem_insert_iff.mp hx with he | hx
        · exact Or.inl (he.symm ▸ mem_range_self 0)
        · exact Or.inr hx
  have hτinterior : ∀ t : NNReal,0<(t:ℝ) → τ t∈interior P:=by
    intro t ht
    exact hopenTop (r+t) (lt_add_of_pos_right _ ht)
  have hτcoeff : ∀ t : NNReal,0<(t:ℝ) → μ (τ t)=ν (τ t):=by
    intro t ht
    have hi:=hτinterior t ht
    have hzfront : z∈frontier P:=hτ0.symm ▸ hprefix r le_rfl
    exact disappearingApexCurvature_off ν (fun he ↦ hpfront.2 (he ▸ hi))
      (fun he ↦ hzfront.2 (he ▸ hi))
  have hcorner : ∃ Cz : PointRetainedConeNeighborhood a y P z,
      ∃ E : PointRetainedConeNeighborhood a y Q z,
        Cz.Admissible ∧ E.Admissible ∧ ν z=Real.pi-Cz.flatPhysicalWidth ∧
        μ z=Real.pi-E.flatPhysicalWidth ∧ E.flatPhysicalWidth=Cz.flatPhysicalWidth-Real.pi:=by
    have hc : ∃ Cz : PointRetainedConeNeighborhood a y P (σ (retainedApexUpperSource hβ.le hβπ r)),
        ∃ E : PointRetainedConeNeighborhood a y Q (σ (retainedApexUpperSource hβ.le hβπ r)),
          Cz.Admissible ∧ E.Admissible ∧
          ν (σ (retainedApexUpperSource hβ.le hβπ r))=Real.pi-Cz.flatPhysicalWidth ∧
          μ (σ (retainedApexUpperSource hβ.le hβπ r))=Real.pi-E.flatPhysicalWidth ∧
          E.flatPhysicalWidth=Cz.flatPhysicalWidth-Real.pi:=by
      obtain ⟨Cz,hνz,hCz⟩:=hνB _ (hprefix r le_rfl)
      obtain ⟨E,hwidth,hturn,hE⟩:=pointDisappearingApex_construct_departure_chart ha y hβ hβπ σ hσ
        hσP r hr hprefix Cz hCz hνz hzneg hQdiff
      refine ⟨Cz,E,hCz,hE,hνz,?_,hwidth⟩
      have hm : μ (σ (retainedApexUpperSource hβ.le hβπ r))=
          ν (σ (retainedApexUpperSource hβ.le hβπ r))+Real.pi:=by
        rw [← hτ0,disappearingApexCurvature_at_departure ν hzneq]
      exact hm.trans hturn.symm
    rwa [← hτ0] at hc
  have htopcharts : ∀ t : NNReal,0<(t:ℝ) →
      ∃ E : PointRetainedConeNeighborhood a y Q (τ t),E.Admissible ∧
        E.flatPhysicalWidth=(coalescedPointExponent a y (τ t)/2+1)*(2*Real.pi)-Real.pi ∧
        μ (τ t)=Real.pi-E.flatPhysicalWidth:=by
    intro t ht
    obtain ⟨E,hwidth,hturn,hE⟩:=pointDisappearingSector_construct_passing_chart ha y hβ hβπ σ hσ r
      hQdiff t ht (hτinterior t ht)
    refine ⟨E,hE,hwidth,?_⟩
    rw [hτcoeff t ht,hνI _ (hτinterior t ht)]
    exact hturn.symm
  have hnegative : ∀ x,signedBudgetNeg (μ x) ≤ signedBudgetNeg (ν x):=by
    intro x
    by_cases hxp : x=p
    · subst x
      rw [disappearingApexCurvature_at_apex ν hzneq,signedBudgetNeg_zero]
      exact signedBudgetNeg_nonneg _
    by_cases hxz : x=z
    · subst x
      rw [disappearingApexCurvature_at_departure ν hzneq]
      exact disappearingApex_negative_part_add_pi _
    · rw [disappearingApexCurvature_off ν hxp hxz]
  obtain ⟨hV,hA⟩:=disappearingApex_mass_changes ν α p z hboundary
  have hnewbudget:=hbudget.disappearingApex p hzneq hboundary hβπ hβα hremaining
  refine ⟨r,hr,hcontact,hprefixzero,⟨{
    old_forward:=g
    old_forward_closed:=hg
    old_forward_zero:=hg0
    old_forward_range:=hgrange
    old_forward_meet:=hgmeet
    sides:=D
    removed_side:=hremoved
    kept_side:=hkept
    residual_closure:=rfl
    residual_side:=hQside
    state:=state
    state_ambient:=rfl
    literal_union:=hQunion
    literal_difference:=hQdiff
    subset_old:=hQP
    interior_eq:=hQI
    frontier_eq:=hfrontFinal
    apex_removed:=hpQ
    departure_retained:=hzQ
    departure_negative:=hznegative
    departure_ne_apex:=hzneq
    top_metric:=hτmetric
    open_top_old_interior:=hτinterior
    open_top_coeff:=hτcoeff
    departure_chart:=hcorner
    open_top_chart:=htopcharts
    apex_budget_spent:=hαp
    apex_old_coeff:=hboundary
    apex_old_nonnegative:=hνp
    old_positive_mass_away_zero:=hposAway
    old_off_apex_nonpositive:=hoffNonpos
    old_off_apex_budget:=hoffBudget
    curvature_exact:=rfl
    allocation_exact:=rfl
    allocation_is_old_negative:=hαpart
    negative_nonincrease:=hnegative
    budget_invariant:=hnewbudget
    curvature_mass:=hV
    allocation_mass:=hA
    intrinsic_eq:=fun _ ↦ hIntrinsic
    finite_boundary_cover:=⟨fresh,hfresh⟩ }⟩⟩

end RepulsiveCoulomb
