module

public import LeanResearch.RepulsiveCoulomb.DisappearingSectorRemovedTopology
public import LeanResearch.RepulsiveCoulomb.DisappearingSectorRemovedEnd
public import LeanResearch.RepulsiveCoulomb.TranslatedStripResidualTopology
public import LeanResearch.RepulsiveCoulomb.PlanarOldBoundaryComplementRay

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Construct the actual replacement line, its
Schoenflies sides and the LITERAL disappearing-apex residual after the separate
actual-sector theorem has proved exact contact. The free boundary is only the
tail from z; the old apex and compact prefix are actually removed. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem pointDisappearingSector_construct_actual_residual_topology
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (H : ℂ≃ₜℂ) (hHP : P=H ⁻¹' planarClosedUpperHalfplane)
    (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ t : NNReal,σ (retainedApexBottomSource hβ.le hβπ t)∈frontier P)
    (hOld : ∀ p∈frontier P,∃ C : PointRetainedConeNeighborhood a y P p,C.Admissible)
    (hregular : ∀ x : closedEuclideanSector β,0<‖x.1‖ → 0<Complex.arg x.1 → Complex.arg x.1<β →
      σ x∈interior P ∧ coalescedPointExponent a y (σ x)=0)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β)
    (r : NNReal) (hr : 0<(r:ℝ))
    (hprefix : ∀ t : NNReal,t≤r → σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P)
    (hcontact : range σ∩frontier P=
      range (fun t : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ t)) ∪
      (fun t : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ t)) '' Icc 0 r) :
    let S:=range σ
    let τ : NNReal → ℂ:=fun t ↦ σ (disappearingSectorTail hβ.le hβπ r t)
    let Q:=closure (P\S)
    ∃ g : NNReal → ℂ,IsClosedEmbedding g ∧ g 0=τ 0 ∧
      range g=insert (τ 0) (frontier P\S) ∧ range g∩S={τ 0} ∧
      ∃ D : PlanarLineHalfplaneHomeomorphs (planarTwoRayJoin τ g),
        Pᶜ∪(S\range τ)=D.positive ∧ interior P\S=D.negative ∧
        Q=closure D.negative ∧ Q=(P\S)∪range τ ∧ Q=P\(S\range τ) ∧ Q⊆P ∧
        interior Q=interior P\S ∧ frontier Q=range τ∪(frontier P\S) ∧
        σ (flatLinkSectorApex hβ.le)∉Q ∧ τ 0∈frontier Q := by
  let S:=range σ
  let τ : NNReal → ℂ:=fun t ↦ σ (disappearingSectorTail hβ.le hβπ r t)
  let Q:=closure (P\S)
  let p:=σ (flatLinkSectorApex hβ.le)
  have hP : IsClosed P:=by rw [hHP]; exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  have hσclosed:=(pointRetainedSector_closed_proper ha y hβ hβπ σ hσ).1
  have hSP : S⊆P:=by rintro x ⟨q,rfl⟩; exact hσP q
  have hTS : range τ⊆S:=by rintro x ⟨t,rfl⟩; exact mem_range_self _
  have hτ0 : τ 0=σ (retainedApexUpperSource hβ.le hβπ r):=by simp only [τ,disappearingSectorTail,add_zero]
  obtain ⟨δ,hδ,hδ0,hδrange,_,_⟩:=pointDisappearingSector_actual_removed_end ha y hβ hβπ r.2 σ hσ hbottom hprefix
  have hδcontact : range δ=S∩frontier P:=hδrange.trans hcontact.symm
  obtain ⟨g,hg,hg0,hgrange,hgmeet⟩:=exists_straightened_oldBoundary_complement_ray H hHP hδ
    (hδ0.trans hτ0.symm) hδcontact
  have hτmetric (u v : NNReal) : (pointSmoothConformalEDist a y (τ u) (τ v)).toReal=dist u v:=
    (hσ _ _).trans ((disappearingSectorTail_isometry hβ.le hβπ r).dist_eq u v)
  have hτclosed:=pointMetricRay_isClosedEmbedding ha y τ hτmetric
  have hzero : τ 0=g 0:=hg0.symm
  have hmeet : range τ∩range g={τ 0}:=by
    ext x
    constructor
    · rintro ⟨hxT,hxg⟩
      exact hgmeet ▸ And.intro hxg (hTS hxT)
    · intro he
      have hx : x=τ 0:=he
      subst x
      exact ⟨mem_range_self 0,⟨0,hg0⟩⟩
  have hline : range (planarTwoRayJoin τ g)=range τ∪(frontier P\S):=by
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
  have hpS : p∈S:=mem_range_self _
  have hpT : p∉range τ:=by
    rintro ⟨t,ht⟩
    have he:=congrArg (fun q : closedEuclideanSector β ↦ ‖q.1‖) (hσclosed.injective ht)
    change ‖sectorPolar ((r:ℝ)+(t:ℝ)) β‖=‖(0:ℂ)‖ at he
    have hn : (r:ℝ)+(t:ℝ)=‖(0:ℂ)‖ :=
      (sectorPolar_norm (show (0:ℝ)≤(r:ℝ)+(t:ℝ) from add_nonneg r.2 t.2) β).symm.trans he
    rw [norm_zero] at hn
    linarith [t.2]
  have hpfront : p∈frontier P:=by
    have he : retainedApexBottomSource hβ.le hβπ 0=flatLinkSectorApex hβ.le:=Subtype.ext (sectorPolar_zero 0)
    simpa only [he] using hbottom 0
  have hpnot : p∉range (planarTwoRayJoin τ g):=by
    rw [hline]
    rintro (ht | hf)
    · exact hpT ht
    · exact hf.2 hpS
  obtain ⟨D,hpplus⟩:=exists_planarTwoRayJoin_halfplaneHomeomorphs_positive_at hτclosed hg hzero hmeet hpnot
  have hrelative:=pointDisappearingSector_without_tail_relative_open ha y hβ hβπ σ hσ hσP hbottom hOld
    hregular C hC hfull r hr hprefix
  have hconn:=disappearingSector_without_tail_connected hβ hβπ r hr σ hσclosed.continuous hσclosed.injective
  obtain ⟨hremove,hkeep,hclosure,hunion,hQdiff,hQP,hQfront,hhomeo⟩:=translatedCut_identify_actual_sides
    D hP hσclosed.isClosed_range hSP hTS hline hrelative (translatedCut_old_exterior_connected H hHP)
    hconn ⟨hpS,hpT⟩ hpfront hpplus
  have hQI : interior Q=interior P\S:=by
    dsimp only [Q,S]
    rw [hclosure,translatedCut_negative_interior D,hkeep]
  have hpQ : p∉Q:=by
    dsimp only [Q,S]
    rw [hQdiff]
    exact fun hp ↦ hp.2 ⟨hpS,hpT⟩
  have hfront : frontier Q=range τ∪(frontier P\S):=hQfront.trans hline
  refine ⟨g,hg,hg0,hgrange,hgmeet,D,hremove,hkeep,hclosure,hunion,hQdiff,hQP,hQI,hfront,hpQ,?_⟩
  rw [hfront]
  exact Or.inl (mem_range_self 0)

end RepulsiveCoulomb
