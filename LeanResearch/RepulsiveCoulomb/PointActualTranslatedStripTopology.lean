import LeanResearch.RepulsiveCoulomb.PointTranslatedStripRelativeFullness
import LeanResearch.RepulsiveCoulomb.TranslatedStripRemovedContactRay
import LeanResearch.RepulsiveCoulomb.TranslatedStripResidualTopology
import LeanResearch.RepulsiveCoulomb.PlanarOldBoundaryComplementRay

/-! NEW SOURCE-ONLY, UNCOMPILED. END-TO-END conditional cut topology from the
ACTUAL supplied translated strip, old ambient H, exact contact, admissible old
charts and clean removed interior. The new line, its Schoenflies homeomorphism,
correct component, literal residual and surviving old forward end are outputs.
No residual topology/halfplane/chart certificate is an assumption. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem pointTranslatedStrip_actual_cut_topology
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ≃ₜℂ) (hHP : P=H ⁻¹' planarClosedUpperHalfplane)
    {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P=
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (hcharts : ∀ p∈frontier P,∃ C : PointRetainedConeNeighborhood a y P p,C.Admissible)
    (hcleanInterior : ∀ p∈interior P,
      p∈range (fun x ↦ (F x).1) \ range (fun r ↦ (F (translatedStripTop hb.le r)).1) →
        coalescedPointExponent a y p=0) :
    let S:=range (fun x ↦ (F x).1)
    let τ : NNReal→ℂ:=fun r ↦ (F (translatedStripTop hb.le r)).1
    let T:=range τ
    let Q:=closure (P \ S)
    ∃ g : NNReal→ℂ,IsClosedEmbedding g ∧ g 0=τ 0 ∧
      range g=insert (τ 0) (frontier P \ S) ∧ range g∩S={τ 0} ∧
      ∃ D : PlanarLineHalfplaneHomeomorphs (planarTwoRayJoin τ g),
        Pᶜ∪(S\T)=D.positive ∧ interior P\S=D.negative ∧
        Q=closure D.negative ∧ Q=(P\S)∪T ∧ Q=P\(S\T) ∧ Q⊆P ∧
        interior Q=interior P\S ∧ frontier Q=T∪(frontier P\S) ∧
        Nonempty (Q≃ₜplanarClosedUpperHalfplane) := by
  let S:=range (fun x ↦ (F x).1)
  let τ : NNReal→ℂ:=fun r ↦ (F (translatedStripTop hb.le r)).1
  let T:=range τ
  let Q:=closure (P\S)
  let p:=(F (translatedStripBottom hb.le 0)).1
  have hP : IsClosed P:=by
    rw [hHP]
    exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  have hvi : (conePhase stripAngle).im≠0:=by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).ne'
  obtain ⟨hclosed,hproper⟩:=pointTranslatedStrip_closed_proper ha y hvi F hF
  have hSP : S⊆P:=by rintro x ⟨q,rfl⟩; exact (F q).2
  have hTS : T⊆S:=by rintro x ⟨r,rfl⟩; exact mem_range_self _
  obtain ⟨δ,hδ,hδ0,hδrange⟩:=pointTranslatedStrip_removed_contact_ray
    ha y stripAngle_pos stripAngle_lt_pi hb F hF hcontact
  obtain ⟨g,hg,hg0,hgrange,hgmeet⟩:=exists_straightened_oldBoundary_complement_ray
    H hHP hδ hδ0 hδrange
  have hτmetric : ∀ r s : NNReal,
      (pointSmoothConformalEDist a y (τ r) (τ s)).toReal=dist r s:=by
    intro r s
    rw [hF]
    exact (translatedStripTop_isometry hb.le).dist_eq r s
  have hτclosed : IsClosedEmbedding τ:=pointMetricRay_isClosedEmbedding ha y τ hτmetric
  have hzero : τ 0=g 0:=hg0.symm
  have hmeet : range τ∩range g={τ 0}:=by
    ext x
    constructor
    · rintro ⟨hxT,hxg⟩
      exact hgmeet ▸ And.intro hxg (hTS hxT)
    · intro hx
      have he : x=τ 0:=mem_singleton_iff.mp hx
      subst x
      exact ⟨mem_range_self 0,⟨0,hg0⟩⟩
  have hline : range (planarTwoRayJoin τ g)=T∪(frontier P\S):=by
    rw [planarTwoRayJoin_range hzero,hgrange]
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · rcases mem_insert_iff.mp hx with he | hx
        · exact Or.inl (he.symm ▸ mem_range_self 0)
        · exact Or.inr hx
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (mem_insert_of_mem _ hx)
  have hpW : p∈S\T:=⟨mem_range_self _,translatedStrip_bottom_not_top hvi hb hclosed.injective 0⟩
  have hpfront : p∈frontier P:=by
    have hm : p∈S∩frontier P:=hcontact.symm ▸ Or.inl ⟨0,rfl⟩
    exact hm.2
  have hpnot : p∉range (planarTwoRayJoin τ g):=by
    rw [hline]
    rintro (hp | hp)
    · exact hpW.2 hp
    · exact hp.2 hpW.1
  obtain ⟨D,hpplus⟩:=exists_planarTwoRayJoin_halfplaneHomeomorphs_positive_at
    hτclosed hg hzero hmeet hpnot
  have hrelative : IsOpen {x : P | x.1∈S\T}:=
    pointTranslatedStrip_without_top_relatively_open ha y stripAngle_pos stripAngle_lt_pi hb F hF hcontact hcharts hcleanInterior
  have hbelow : IsConnected (S\T):=
    translatedStrip_without_top_connected hvi hb (fun x ↦ (F x).1) hclosed.continuous hclosed.injective
  obtain ⟨hremove,hkeep,hclosure,hunion,hdifference,hQP,hfront,hhomeo⟩:=
    translatedCut_identify_actual_sides D hP hclosed.isClosed_range hSP hTS hline hrelative
      (translatedCut_old_exterior_connected H hHP) hbelow hpW hpfront hpplus
  have hQI : interior Q=interior P\S:=by
    dsimp only [Q, S]
    rw [hclosure,translatedCut_negative_interior D,hkeep]
  refine ⟨g,hg,hg0,hgrange,hgmeet,D,hremove,hkeep,hclosure,hunion,hdifference,hQP,hQI,?_,hhomeo⟩
  exact hfront.trans hline

end RepulsiveCoulomb
