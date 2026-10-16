module

public import LeanResearch.RepulsiveCoulomb.PointFiniteBoundaryRayContacts
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Order/topology layer of the first departure.
This constructs the endpoint, rather than accepting a first-departure point.
The actual-sector caller must derive the initial collar, failure of whole-ray
contact, and zero-turn local continuation from genuine charts. Those geometric
bridges are NOT asserted proved in this lower-layer theorem. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- A closed contact set with a positive initial interval but a genuine later
noncontact has a finite largest initial interval. No finite crossing assertion
or preselected terminal point is required. -/
theorem exists_finite_initial_contact_endpoint {C : Set ℝ} (hC : IsClosed C)
    {δ : ℝ} (hδ : 0<δ) (hinit : Icc (0:ℝ) δ ⊆ C)
    (hexit : ∃ t : ℝ,0≤t ∧ t∉C) :
    ∃ r : ℝ,0<r ∧ r∈C ∧ Icc (0:ℝ) r⊆C ∧
      (∀ t : ℝ,r<t → ¬ Icc (0:ℝ) t⊆C) ∧
      (∀ t : ℝ,r<t → ¬ Icc r t⊆C) := by
  let E : Set ℝ:=Ici 0 ∩ ⋂ u : unitInterval, (fun t : ℝ ↦ u.1*t) ⁻¹' C
  have hEclosed : IsClosed E:=isClosed_Ici.inter
    (isClosed_iInter (fun u ↦ hC.preimage (continuous_const.mul continuous_id)))
  have hEiff (t : ℝ) : t∈E ↔ 0≤t ∧ Icc (0:ℝ) t⊆C:=by
    constructor
    · rintro ⟨ht,hall⟩
      refine ⟨ht,?_⟩
      intro s hs
      by_cases ht0 : t=0
      · have hs0 : s=0:=le_antisymm (ht0 ▸ hs.2) hs.1
        have hzero:=mem_iInter.mp hall (0:unitInterval)
        simpa only [mem_preimage,Set.Icc.coe_zero,zero_mul,hs0] using hzero
      · have htp : 0<t:=lt_of_le_of_ne ht (Ne.symm ht0)
        let u : unitInterval:=⟨s/t,div_nonneg hs.1 ht,(div_le_one htp).mpr hs.2⟩
        have hu:=mem_iInter.mp hall u
        change (s/t)*t∈C at hu
        rwa [div_mul_cancel₀ _ ht0] at hu
    · rintro ⟨ht,hall⟩
      refine ⟨ht,mem_iInter.mpr (fun u ↦ ?_)⟩
      apply hall
      exact ⟨mul_nonneg u.2.1 ht,mul_le_of_le_one_left ht u.2.2⟩
  have hδE : δ∈E:=(hEiff δ).mpr ⟨hδ.le,hinit⟩
  obtain ⟨t,ht,htC⟩:=hexit
  have hEbdd : BddAbove E:=by
    refine ⟨t,?_⟩
    intro s hs
    have hs':=(hEiff s).mp hs
    by_contra hnot
    exact htC (hs'.2 ⟨ht,(lt_of_not_ge hnot).le⟩)
  let r:=sSup E
  have hrE : r∈E:=hEclosed.csSup_mem ⟨δ,hδE⟩ hEbdd
  have hrpos : 0<r:=hδ.trans_le (le_csSup hEbdd hδE)
  have hprefix : Icc (0:ℝ) r⊆C:=((hEiff r).mp hrE).2
  have hmax : ∀ t : ℝ,r<t → ¬ Icc (0:ℝ) t⊆C:=by
    intro s hrs hs
    have hsE : s∈E:=(hEiff s).mpr ⟨hrpos.le.trans hrs.le,hs⟩
    exact (not_le_of_gt hrs) (le_csSup hEbdd hsE)
  refine ⟨r,hrpos,hprefix ⟨hrpos.le,le_rfl⟩,hprefix,hmax,?_⟩
  intro s hrs hcont
  apply hmax s hrs
  intro u hu
  rcases le_total u r with hur | hru
  · exact hprefix ⟨hu.1,hur⟩
  · exact hcont ⟨hru,hu.2⟩

/-- If zero-turn points admit actual forward boundary continuation, the
constructed finite endpoint has strictly negative turn. Off-apex
nonpositivity is supplied by the already-derived equality-case budget lemma. -/
theorem exists_negative_initial_contact_endpoint
    {C : Set ℝ} (hC : IsClosed C) {δ : ℝ} (hδ : 0<δ)
    (hinit : Icc (0:ℝ) δ⊆C) (hexit : ∃ t : ℝ,0≤t ∧ t∉C)
    (turn : ℝ → ℝ) (hnonpos : ∀ t : ℝ,0<t → t∈C → turn t≤0)
    (hcontinue : ∀ t : ℝ,0<t → Icc (0:ℝ) t⊆C → turn t=0 →
      ∃ ε : ℝ,0<ε ∧ Icc t (t+ε)⊆C) :
    ∃ r : ℝ,0<r ∧ r∈C ∧ Icc (0:ℝ) r⊆C ∧ turn r<0 ∧
      ∀ t : ℝ,r<t → ¬ Icc r t⊆C := by
  obtain ⟨r,hr,hrC,hprefix,_,hterminal⟩:=exists_finite_initial_contact_endpoint hC hδ hinit hexit
  have hneg : turn r<0:=by
    have hn:=hnonpos r hr hrC
    apply lt_of_le_of_ne hn
    intro he
    obtain ⟨ε,hε,hcont⟩:=hcontinue r hr hprefix he
    exact hterminal (r+ε) (lt_add_of_pos_right _ hε) hcont
  exact ⟨r,hr,hrC,hprefix,hneg,hterminal⟩

end RepulsiveCoulomb
