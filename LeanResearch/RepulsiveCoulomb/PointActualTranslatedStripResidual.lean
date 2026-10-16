module

public import LeanResearch.RepulsiveCoulomb.PointActualTranslatedStripTopology
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripCurvatureMeaning
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripTransferBounds
public import LeanResearch.RepulsiveCoulomb.PointFullStripResidualWidths

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Complete CONDITIONAL supplied-strip endpoint:
actual literal residual, constructed new halfplane and complete retained charts,
exact ambient signed curvature transfer, negative-part nonincrease, unchanged
mass and closed-side budget retention. All cuts/contacts/source geometry are
actual data. No maximal-width, first-contact or contact-existence claim is made.
No residual homeomorphism, residual chart, update witness or total-mass equality
is accepted as a premise. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem pointTranslatedStrip_actual_residual_and_all_point_update
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ≃ₜℂ) (hHP : P=H ⁻¹' planarClosedUpperHalfplane)
    {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P=
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (ν α : ℂ→₀ℝ)
    (hνI : ∀ x∈interior P,ν x= -Real.pi*coalescedPointExponent a y x)
    (hνB : ∀ x∈frontier P,∃ C : PointRetainedConeNeighborhood a y P x,
      C.Admissible ∧ ν x=Real.pi-C.flatPhysicalWidth)
    (hνO : ∀ x,x∉P → ν x=0)
    (Cz : PointRetainedConeNeighborhood a y P (F (translatedStripTop hb.le 0)).1)
    (hCz : Cz.Admissible) (hνz : ν (F (translatedStripTop hb.le 0)).1=Real.pi-Cz.flatPhysicalWidth)
    (hremain : Real.pi-stripAngle<Cz.flatPhysicalWidth)
    (hαP : ∀ x,α x≠0 → x∈P)
    (hαp : α (F (translatedStripBottom hb.le 0)).1=0)
    (hclean : ∀ x∈range (fun q ↦ (F q).1) \ range (fun r ↦ (F (translatedStripTop hb.le r)).1),
      x≠(F (translatedStripBottom hb.le 0)).1 → ν x=0 ∧ α x=0) :
    let S:=range (fun x ↦ (F x).1)
    let τ : NNReal→ℂ:=fun r ↦ (F (translatedStripTop hb.le r)).1
    let T:=range τ
    let Q:=closure (P\S)
    let p:=(F (translatedStripBottom hb.le 0)).1
    let z:=τ 0
    let μ:=BoundaryPreparation.transfer ν p z
    ∃ g : NNReal→ℂ,IsClosedEmbedding g ∧ g 0=z ∧
      range g=insert z (frontier P\S) ∧
      Q=P\(S\T) ∧ Q⊆P ∧ interior Q=interior P\S ∧
      frontier Q=T∪range g ∧ Nonempty (Q≃ₜplanarClosedUpperHalfplane) ∧
      p∉Q ∧ z∈frontier Q ∧
      (∀ u : Icc (0:ℝ) b,u.1<b → (F (translatedStripEdge u)).1∉Q) ∧
      (∀ x∈Q,Nonempty (PointRetainedConeNeighborhood a y Q x)) ∧
      ν p=Real.pi-stripAngle ∧
      μ=ν+Finsupp.single z (Real.pi-stripAngle)-Finsupp.single p (Real.pi-stripAngle) ∧
      (∀ x∈interior Q,μ x= -Real.pi*coalescedPointExponent a y x) ∧
      (∀ x∈frontier Q,∃ E : PointRetainedConeNeighborhood a y Q x,
        E.Admissible ∧ μ x=Real.pi-E.flatPhysicalWidth) ∧
      (∀ x,x∉Q → μ x=0) ∧
      (∀ x,pointSignedNegativePart μ x≤pointSignedNegativePart ν x) ∧
      pointSignedCurvatureMass μ α=pointSignedCurvatureMass ν α ∧
      (∀ x,α x≠0 → x∈Q) := by
  let S:=range (fun x ↦ (F x).1)
  let τ : NNReal→ℂ:=fun r ↦ (F (translatedStripTop hb.le r)).1
  let T:=range τ
  let Q:=closure (P\S)
  let p:=(F (translatedStripBottom hb.le 0)).1
  let z:=τ 0
  let μ:=BoundaryPreparation.transfer ν p z
  have hP : IsClosed P:=by
    rw [hHP]
    exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  have hpfront : p∈frontier P:=by
    have hm : p∈S∩frontier P:=hcontact.symm ▸ Or.inl ⟨0,rfl⟩
    exact hm.2
  have hcharts : ∀ x∈frontier P,∃ C : PointRetainedConeNeighborhood a y P x,C.Admissible:=by
    intro x hx
    obtain ⟨C,hC,_⟩:=hνB x hx
    exact ⟨C,hC⟩
  have hcleanInterior : ∀ x∈interior P,x∈S\T → coalescedPointExponent a y x=0:=by
    intro x hxI hxW
    have hxp : x≠p:=by intro he; exact hpfront.2 (he ▸ hxI)
    have hn:=(hclean x hxW hxp).1
    have he:=hνI x hxI
    rw [hn] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (neg_ne_zero.mpr Real.pi_ne_zero)
  obtain ⟨g,hg,hg0,hgrange,hgmeet,D,hremoved,hkeep,hclosure,hunion,hQdiff,hQP,hQI,hQfront,hhomeo⟩:=
    pointTranslatedStrip_actual_cut_topology ha y H hHP stripAngle_pos stripAngle_lt_pi hb F hF hcontact hcharts hcleanInterior
  obtain ⟨hpturn,hpQ,hzfront,htransfer,hμI,hμB,hμO⟩:=
    pointTranslatedStrip_transfer_geometric_meaning ha y hP stripAngle_pos stripAngle_lt_pi hb F hF hcontact ν
      hνI hνB hνO Cz hCz hνz hremain (fun x hx hxp ↦ (hclean x hx hxp).1)
      rfl hQdiff hQfront
  have hvi : (conePhase stripAngle).im≠0:=by rw [conePhase_im]; exact (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).ne'
  have hFinj:=(pointTranslatedStrip_closed_proper ha y hvi F hF).1.injective
  have hpz : p≠z:=translatedStrip_apex_ne_top_origin hvi hb hFinj
  have hνp_nonneg : 0≤ν p:=by rw [hpturn]; exact (sub_pos.mpr stripAngle_lt_pi).le
  have hfrontFinal : frontier Q=T∪range g:=by
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
  have hedgeRemoved (u : Icc (0:ℝ) b) (hu : u.1<b) : (F (translatedStripEdge u)).1∉Q:=by
    dsimp only [Q, S]
    rw [hQdiff]
    intro hx
    exact hx.2 ⟨mem_range_self _,translatedStrip_edge_not_top hvi hb hFinj u hu⟩
  have hallcharts : ∀ x∈Q,Nonempty (PointRetainedConeNeighborhood a y Q x):=by
    intro x hx
    by_cases hi : x∈interior Q
    · obtain ⟨C,_,_,_⟩:=pointInterior_construct_full_retained_chart ha y hi
      exact ⟨C⟩
    · obtain ⟨E,_,_⟩:=hμB x ⟨subset_closure hx,hi⟩
      exact ⟨E⟩
  have hbudget : ∀ x,α x≠0 → x∈Q:=translatedCut_budget_support_retained hQdiff α hαP hαp
    (fun x hx hxp ↦ (hclean x hx hxp).2)
  exact ⟨g,hg,hg0,hgrange,hQdiff,hQP,hQI,hfrontFinal,hhomeo,hpQ,hzfront,hedgeRemoved,
    hallcharts,hpturn,htransfer,hμI,hμB,hμO,
    pointTranslatedTransfer_negative_nonincrease ν hpz hνp_nonneg,
    pointTranslatedTransfer_curvature_mass ν α p z,hbudget⟩

end RepulsiveCoulomb
