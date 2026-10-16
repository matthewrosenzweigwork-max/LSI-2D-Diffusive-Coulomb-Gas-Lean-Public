module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripTopChart
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripRetainedGerms
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripApexFullness
public import LeanResearch.RepulsiveCoulomb.BoundaryPreparationRankDraft

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Geometric meaning of the general AMBIENT
Finsupp transfer, proved using the constructed actual retained charts. The
initial-line constructor supported only on original atoms is not reused.
The topology equalities are outputs of the separate actual cut construction;
there is no new-measure or angle-update certificate among the inputs. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Once literal cut topology has been constructed, the actual local charts
identify the transferred Finsupp with the geometric curvature everywhere. -/
theorem pointTranslatedStrip_transfer_geometric_meaning
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} (hP : IsClosed P) {stripAngle b : ℝ}
    (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P =
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (ν : ℂ→₀ℝ)
    (hνI : ∀ x∈interior P,ν x= -Real.pi*coalescedPointExponent a y x)
    (hνB : ∀ x∈frontier P,∃ C : PointRetainedConeNeighborhood a y P x,
      C.Admissible ∧ ν x=Real.pi-C.flatPhysicalWidth)
    (hνO : ∀ x,x∉P → ν x=0)
    (Cz : PointRetainedConeNeighborhood a y P (F (translatedStripTop hb.le 0)).1)
    (hCz : Cz.Admissible) (hνz : ν (F (translatedStripTop hb.le 0)).1=Real.pi-Cz.flatPhysicalWidth)
    (hremain : Real.pi-stripAngle<Cz.flatPhysicalWidth)
    (hclean : ∀ x∈range (fun q ↦ (F q).1) \
        range (fun r ↦ (F (translatedStripTop hb.le r)).1),
      x≠(F (translatedStripBottom hb.le 0)).1 → ν x=0)
    (hQclosure : Q=closure (P \ range (fun q ↦ (F q).1)))
    (hQdiff : Q=P \ (range (fun q ↦ (F q).1) \
      range (fun r ↦ (F (translatedStripTop hb.le r)).1)))
    (hQfront : frontier Q=range (fun r ↦ (F (translatedStripTop hb.le r)).1) ∪
      (frontier P \ range (fun q ↦ (F q).1))) :
    let p:=(F (translatedStripBottom hb.le 0)).1
    let z:=(F (translatedStripTop hb.le 0)).1
    let μ:=BoundaryPreparation.transfer ν p z
    ν p=Real.pi-stripAngle ∧ p∉Q ∧ z∈frontier Q ∧
      μ=ν+Finsupp.single z (Real.pi-stripAngle)-Finsupp.single p (Real.pi-stripAngle) ∧
      (∀ x∈interior Q,μ x= -Real.pi*coalescedPointExponent a y x) ∧
      (∀ x∈frontier Q,∃ E : PointRetainedConeNeighborhood a y Q x,
        E.Admissible ∧ μ x=Real.pi-E.flatPhysicalWidth) ∧
      (∀ x,x∉Q → μ x=0) := by
  let p:=(F (translatedStripBottom hb.le 0)).1
  let z:=(F (translatedStripTop hb.le 0)).1
  let μ:=BoundaryPreparation.transfer ν p z
  have hs:=Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  have hvi : (conePhase stripAngle).im≠0:=by rw [conePhase_im]; exact hs.ne'
  obtain ⟨hclosed,hproper⟩:=pointTranslatedStrip_closed_proper ha y hvi F hF
  have hSclosed:=hclosed.isClosed_range
  have hpz : p≠z:=translatedStrip_apex_ne_top_origin hvi hb hclosed.injective
  have hpfront : p∈frontier P:=by
    have hm : p∈range (fun q ↦ (F q).1) ∩ frontier P:=hcontact.symm ▸ Or.inl ⟨0,rfl⟩
    exact hm.2
  have hzfront : z∈frontier P:=by
    let u : Icc (0:ℝ) b:=⟨b,hb.le,le_rfl⟩
    have he : translatedStripEdge (v := conePhase stripAngle) u=translatedStripTop hb.le 0:=Subtype.ext rfl
    have hm : (F (translatedStripEdge u)).1∈range (fun q ↦ (F q).1) ∩ frontier P:=
      hcontact.symm ▸ Or.inr ⟨u,rfl⟩
    simpa only [he] using hm.2
  obtain ⟨Cp,hCp,hνp⟩:=hνB p hpfront
  have hpwidth:=(pointTranslatedStrip_apex_width_and_local_fullness ha y stripAngle_pos stripAngle_lt_pi hb F hF hcontact Cp hCp).1
  have hpturn : ν p=Real.pi-stripAngle:=hνp.trans (by rw [hpwidth])
  have hpW : p∈range (fun q ↦ (F q).1) \ range (fun r ↦ (F (translatedStripTop hb.le r)).1):=
    ⟨mem_range_self _,translatedStrip_bottom_not_top hvi hb hclosed.injective 0⟩
  have hpQ : p∉Q:=by
    rw [hQdiff]
    exact fun h ↦ h.2 hpW
  have hzQfront : z∈frontier Q:=by rw [hQfront]; exact Or.inl ⟨0,rfl⟩
  have hQclosed : IsClosed Q:=hQclosure.symm ▸ isClosed_closure
  have hzQ : z∈Q:=hQclosed.frontier_subset hzQfront
  have hQP : Q⊆P:=by rw [hQdiff]; exact sdiff_subset
  have htransfer : μ=ν+Finsupp.single z (Real.pi-stripAngle)-Finsupp.single p (Real.pi-stripAngle):=by
    unfold μ BoundaryPreparation.transfer
    rw [hpturn]
  refine ⟨hpturn,hpQ,hzQfront,htransfer,?_,?_,?_⟩
  · intro x hx
    have hxP:=interior_mono hQP hx
    have hxp : x≠p:=by intro he; exact hpfront.2 (he ▸ hxP)
    have hxz : x≠z:=by intro he; exact hzfront.2 (he ▸ hxP)
    rw [BoundaryPreparation.transfer_away ν hxp hxz]
    exact hνI x hxP
  · intro x hx
    rw [hQfront] at hx
    rcases hx with ⟨r,rfl⟩ | hxold
    · by_cases hr0 : r=0
      · subst r
        obtain ⟨E,hchart,hwidth,hturn,hadm⟩:=pointTranslatedStrip_construct_corner_chart
          ha y stripAngle_pos stripAngle_lt_pi hb F hF hcontact Cz hCz hremain hQdiff
        refine ⟨E,hadm,?_⟩
        rw [BoundaryPreparation.transfer_target ν hpz,hpturn,hνz]
        exact hturn.symm
      · have hrpos : 0<r:=lt_of_le_of_ne (show (0 : NNReal) ≤ r from r.2) (Ne.symm hr0)
        obtain ⟨hpI,E,hwidth,hatom,hadm⟩:=pointTranslatedStrip_construct_open_top_chart
          ha y stripAngle_pos stripAngle_lt_pi hb F hF hcontact hQdiff r hrpos
        have hrp : (F (translatedStripTop hb.le r)).1≠p:=by
          intro he
          exact hpW.2 ⟨r,he⟩
        have hrz : (F (translatedStripTop hb.le r)).1≠z:=by
          intro he
          have hsrc:=hclosed.injective he
          exact hr0 ((translatedStripTop_isometry hb.le).injective hsrc)
        refine ⟨E,hadm,?_⟩
        rw [BoundaryPreparation.transfer_away ν hrp hrz,hνI _ hpI]
        exact hatom.symm
    · have hxp : x≠p:=by intro he; exact hxold.2 (he.symm ▸ hpW.1)
      have hxz : x≠z:=by intro he; exact hxold.2 (he.symm ▸ mem_range_self (translatedStripTop hb.le 0))
      obtain ⟨C,hC,hν⟩:=hνB x hxold.1
      obtain ⟨E,hchart,hlo,hhi,hwidth⟩:=pointTranslatedStrip_retained_chart_away_from_image
        ha y hP hSclosed hxold.2 C
      have hE : E.Admissible:=by
        unfold PointRetainedConeNeighborhood.Admissible at hC ⊢
        rw [hlo,hhi]
        exact hC
      have hturn : μ x=Real.pi-E.flatPhysicalWidth:=by
        rw [BoundaryPreparation.transfer_away ν hxp hxz,hν,hwidth]
      change ∃ E : PointRetainedConeNeighborhood a y Q x,
        E.Admissible ∧ μ x = Real.pi - E.flatPhysicalWidth
      rw [hQclosure]
      exact ⟨E, hE, hturn⟩
  · intro x hxQ
    by_cases hxp : x=p
    · subst x
      exact BoundaryPreparation.transfer_source ν hpz
    have hxz : x≠z:=fun he ↦ hxQ (he.symm ▸ hzQ)
    rw [BoundaryPreparation.transfer_away ν hxp hxz]
    by_cases hxP : x∈P
    · apply hclean x _ hxp
      by_contra hxW
      exact hxQ (hQdiff.symm ▸ And.intro hxP hxW)
    · exact hνO x hxP

end RepulsiveCoulomb
