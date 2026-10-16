module

public import LeanResearch.RepulsiveCoulomb.DisappearingApexFirstDeparture
public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexPrefixFullness

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Actual finite first departure from the original
closed isometric sector and original finite all-point curvature/budget data.
The endpoint is constructed by a closed initial-contact supremum. Initial
agreement, existence of a noncontact, zero-turn continuation and negative sign
are all DERIVED, not fields of a departure/contact certificate. This theorem
does not yet exclude disconnected later contact. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem pointDisappearingApex_construct_actual_first_departure
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hconn : IsPreconnected P) (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ t : NNReal,σ (retainedApexBottomSource hβ.le hβπ t)∈frontier P)
    (hregular : ∀ x : closedEuclideanSector β,0<‖x.1‖ → 0<Complex.arg x.1 → Complex.arg x.1<β →
      σ x∈interior P ∧ coalescedPointExponent a y (σ x)=0)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hνC : ν (σ (flatLinkSectorApex hβ.le))=Real.pi-C.flatPhysicalWidth)
    (hβα : β≤α (σ (flatLinkSectorApex hβ.le)))
    (hremaining : 0<pointSignedBudgetMass ν α-β)
    (hνoff : ∀ x,x∉P → ν x=0)
    (hνint : ∀ x∈interior P,ν x= -Real.pi*coalescedPointExponent a y x)
    (hνboundary : ∀ x∈frontier P,∃ D : PointRetainedConeNeighborhood a y P x,
      ν x=Real.pi-D.flatPhysicalWidth ∧ D.Admissible)
    (hbottomclean : ∀ t : NNReal,0<(t:ℝ) → ν (σ (retainedApexBottomSource hβ.le hβπ t))=0) :
    ∃ r : NNReal,0<(r:ℝ) ∧
      σ (retainedApexUpperSource hβ.le hβπ r)≠σ (flatLinkSectorApex hβ.le) ∧
      ν (σ (retainedApexUpperSource hβ.le hβπ r))<0 ∧
      (∀ t : NNReal,t≤r → σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P) ∧
      (∀ t : NNReal,0<(t:ℝ) → t<r →
        ν (σ (retainedApexUpperSource hβ.le hβπ t))=0 ∧
        α (σ (retainedApexUpperSource hβ.le hβπ t))=0) ∧
      (∀ t : ℝ,(r:ℝ)<t → ¬ Icc (r:ℝ) t ⊆
        (fun u : ℝ ↦ σ (retainedApexUpperSource hβ.le hβπ u.toNNReal)) ⁻¹' frontier P) := by
  let p:=σ (flatLinkSectorApex hβ.le)
  let top : NNReal → ℂ:=fun t ↦ σ (retainedApexUpperSource hβ.le hβπ t)
  let upper : ℝ → ℂ:=fun t ↦ top t.toNNReal
  have hboundary : ν p=Real.pi-β:=by simpa only [hfull] using hνC
  have hne (t : NNReal) (ht : 0<(t:ℝ)) : top t≠p:=by
    intro he
    have hd:=hσ (retainedApexUpperSource hβ.le hβπ t) (flatLinkSectorApex hβ.le)
    change (pointSmoothConformalEDist a y (top t) p).toReal=dist (sectorPolar t β) (0:ℂ) at hd
    rw [he,pointSmoothConformalEDist_self,ENNReal.toReal_zero,dist_zero_right,sectorPolar_norm (NNReal.coe_nonneg t)] at hd
    exact ht.ne' hd.symm
  have htopc : Continuous top:=(pointRetainedSector_closed_proper ha y hβ hβπ σ hσ).1.continuous.comp
    (retainedApexUpperSource_isometry hβ.le hβπ).continuous
  have hupperc : Continuous upper:=htopc.comp continuous_real_toNNReal
  have hcontactClosed : IsClosed (upper ⁻¹' frontier P):=isClosed_frontier.preimage hupperc
  obtain ⟨δ,hδ,hδcontact⟩:=pointDisappearingApex_initial_boundary_contact ha y hβ hβπ σ hσ
    hσP hbottom C hC hfull
  have hinit : Icc (0:ℝ) δ⊆upper ⁻¹' frontier P:=by
    intro t ht
    apply hδcontact t.toNNReal
    rw [Real.coe_toNNReal _ ht.1]
    exact ht.2
  obtain ⟨t,ht⟩:=pointDisappearingApex_exists_upper_noncontact ha y hβ hβπ σ hσ hconn hσP
    hbottom hregular C hC hfull hbudget hνC hβα hremaining hνoff hνint hνboundary hbottomclean
  have hexit : ∃ t : ℝ,0≤t ∧ t∉upper ⁻¹' frontier P:=by
    refine ⟨t,t.2,?_⟩
    simpa only [Set.mem_preimage, upper, top, Real.toNNReal_coe] using ht
  have hnonpos : ∀ t : ℝ,0<t → t∈upper ⁻¹' frontier P → ν (upper t)≤0:=by
    intro t ht _
    apply hbudget.full_angle_off_apex_nonpositive p hboundary hβπ hβα
    apply hne t.toNNReal
    rwa [Real.coe_toNNReal _ ht.le]
  have hcontinue : ∀ t : ℝ,0<t → Icc (0:ℝ) t⊆upper ⁻¹' frontier P → ν (upper t)=0 →
      ∃ ε : ℝ,0<ε ∧ Icc t (t+ε)⊆upper ⁻¹' frontier P:=by
    intro t ht hprefix hturn
    have htC : upper t∈frontier P:=hprefix ⟨ht.le,le_rfl⟩
    obtain ⟨D,hνD,hD⟩:=hνboundary _ htC
    have hzero : D.flatPhysicalWidth=Real.pi:=by linarith
    have htn : (t.toNNReal:ℝ)=t:=Real.coe_toNNReal _ ht.le
    have hprefixN : ∀ u : NNReal,u≤t.toNNReal → top u∈frontier P:=by
      intro u hu
      have hum : (u:ℝ)≤t:=by
        change (u : ℝ) ≤ (t.toNNReal : ℝ) at hu
        rwa [htn] at hu
      have hc : (u : ℝ) ∈ upper ⁻¹' frontier P :=
        hprefix ⟨NNReal.coe_nonneg u, hum⟩
      simpa only [Set.mem_preimage, upper, Real.toNNReal_coe] using hc
    obtain ⟨ε,hε,hout⟩:=pointDisappearingApex_zero_turn_continues ha y hβ hβπ σ hσ hσP
      t.toNNReal (htn.symm ▸ ht) hprefixN D hD hzero
    refine ⟨ε,hε,?_⟩
    intro u hu
    let d : NNReal:=⟨u-t,sub_nonneg.mpr hu.1⟩
    have hdε : (d:ℝ)≤ε:=by
      change u - t ≤ ε
      linarith [hu.2]
    have he : t.toNNReal+d=u.toNNReal:=by
      apply Subtype.ext
      change (t.toNNReal:ℝ)+(u-t)=(u.toNNReal:ℝ)
      rw [htn,Real.coe_toNNReal _ (ht.le.trans hu.1)]
      ring
    have hc:=hout d hdε
    change top (t.toNNReal+d)∈frontier P at hc
    rwa [he] at hc
  obtain ⟨r,hr,hrC,hprefix,hnegative,hterminal⟩:=exists_negative_initial_contact_endpoint
    hcontactClosed hδ hinit hexit (fun t ↦ ν (upper t)) hnonpos hcontinue
  let R : NNReal:=⟨r,hr.le⟩
  have hRN : upper r=top R:=by simp only [upper,show r.toNNReal=R from Subtype.ext (Real.coe_toNNReal _ hr.le)]
  have hprefixN : ∀ t : NNReal,t≤R → top t∈frontier P:=by
    intro t ht
    have hm : (t : ℝ) ∈ upper ⁻¹' frontier P :=
      hprefix ⟨NNReal.coe_nonneg t, ht⟩
    simpa only [Set.mem_preimage, upper, Real.toNNReal_coe] using hm
  refine ⟨R,hr,hne R hr,?_,hprefixN,?_,hterminal⟩
  · rwa [hRN] at hnegative
  · intro t ht htR
    obtain ⟨D,hνD,hD⟩:=hνboundary _ (hprefixN t htR.le)
    have hw:=(pointDisappearingApex_upper_prefix_full ha y hβ hβπ σ hσ hσP r
      hprefixN t ht htR D hD).1
    have hνzero : ν (top t)=0:=by rw [hνD,hw,sub_self]
    obtain ⟨_,_,_,_,hoff,_⟩:=hbudget.disappearingApex_equalities p hboundary hβπ hβα
    exact ⟨hνzero,by rw [hoff _ (hne t ht),hνzero,signedBudgetNeg_zero]⟩

end RepulsiveCoulomb
