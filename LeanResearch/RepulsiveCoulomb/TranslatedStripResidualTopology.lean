module

public import LeanResearch.RepulsiveCoulomb.PlanarTwoRayStraightening

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED DRAFT. Unlike a full-strip cut, P \ S is
usually not open: it contains the retained old forward boundary. The correct
open kept side is interior P \ S. The theorem below constructs the literal
closed residual from ordinary local fullness and concrete boundary carriers.
Those intermediate hypotheses still have to be proved from the actual strip.
No residual halfplane homeomorphism or curvature update is a premise. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem translatedCut_exterior_union_open {P W : Set ℂ} (hP : IsClosed P)
    (hrelative : IsOpen {z : P | z.1 ∈ W}) : IsOpen (Pᶜ ∪ W) := by
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hrelative
  have he : Pᶜ ∪ W = Pᶜ ∪ U := by
    ext z
    by_cases hz : z ∈ P
    · have h := congrArg (fun V : Set P ↦ (⟨z, hz⟩ : P) ∈ V) hUeq
      simpa only [mem_union, mem_compl_iff, hz, not_true_eq_false, false_or,
        mem_preimage, mem_setOf_eq] using (Iff.of_eq h).symm
    · simp [hz]
  rw [he]
  exact hP.isOpen_compl.union hU

theorem translatedCut_exterior_union_connected {P W : Set ℂ}
    (houtside : IsConnected Pᶜ) (hW : IsConnected W)
    {p : ℂ} (hpW : p ∈ W) (hpfront : p ∈ frontier P) :
    IsConnected (Pᶜ ∪ W) := by
  have hpcl : p ∈ closure Pᶜ := frontier_subset_closure (by
    simpa only [frontier_compl] using hpfront)
  have hc : IsConnected (insert p Pᶜ) := houtside.subset_closure
    (subset_insert p _) (insert_subset hpcl subset_closure)
  have hu := hc.union ⟨p, mem_insert p _, hpW⟩ hW
  rw [insert_union, Set.insert_eq_of_mem (a := p) (s := Pᶜ ∪ W) (Or.inr hpW)] at hu
  exact hu

/-- Local fullness of S below its top identifies the two complementary open
components. The forward old boundary is handled literally, rather than being
silently put into the open kept component. -/
theorem translatedCut_identify_actual_sides
    {P S T : Set ℂ} {line : ℝ → ℂ} (D : PlanarLineHalfplaneHomeomorphs line)
    (hP : IsClosed P) (hS : IsClosed S) (hSP : S ⊆ P) (hTS : T ⊆ S)
    (hline : range line = T ∪ (frontier P \ S))
    (hrelative : IsOpen {z : P | z.1 ∈ S \ T})
    (houtside : IsConnected Pᶜ) (hbelow : IsConnected (S \ T))
    {p : ℂ} (hpbelow : p ∈ S \ T) (hpfront : p ∈ frontier P)
    (hpplus : p ∈ D.positive) :
    Pᶜ ∪ (S \ T) = D.positive ∧
    interior P \ S = D.negative ∧
    closure (P \ S) = closure D.negative ∧
    closure (P \ S) = (P \ S) ∪ T ∧
    closure (P \ S) = P \ (S \ T) ∧
    closure (P \ S) ⊆ P ∧
    frontier (closure (P \ S)) = range line ∧
    Nonempty (closure (P \ S) ≃ₜ planarClosedUpperHalfplane) := by
  let A := Pᶜ ∪ (S \ T)
  let R := interior P \ S
  have hAo : IsOpen A := translatedCut_exterior_union_open hP hrelative
  have hAc : IsConnected A := translatedCut_exterior_union_connected
    houtside hbelow hpbelow hpfront
  have hRo : IsOpen R := isOpen_interior.inter hS.isOpen_compl
  have hAR : Disjoint A R := by
    apply disjoint_left.mpr
    rintro z (hz | hz) hzR
    · exact hz (interior_subset hzR.1)
    · exact hzR.2 hz.1
  have hcover : A ∪ R = (range line)ᶜ := by
    rw [hline]
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · rintro (ht | hf)
        · exact hz (hSP (hTS ht))
        · exact hz (hP.closure_eq ▸ hf.1.1)
      · rintro (ht | hf)
        · exact hz.2 ht
        · exact hf.2 hz.1
      · rintro (ht | hf)
        · exact hz.2 (hTS ht)
        · exact hf.1.2 hz.1
    · intro hz
      by_cases hzP : z ∈ P
      · by_cases hzS : z ∈ S
        · exact Or.inl (Or.inr ⟨hzS, fun ht ↦ hz (Or.inl ht)⟩)
        · refine Or.inr ⟨?_, hzS⟩
          by_contra hzi
          exact hz (Or.inr ⟨⟨subset_closure hzP, hzi⟩, hzS⟩)
      · exact Or.inl (Or.inl hzP)
  have hAplus : A ⊆ D.positive :=
    hAc.isPreconnected.subset_left_of_subset_union D.positive_open D.negative_open
      D.disjoint (by rw [D.cover]; exact subset_union_left.trans hcover.le)
      ⟨p, Or.inr hpbelow, hpplus⟩
  have hplusA : D.positive ⊆ A :=
    D.positive_connected.isPreconnected.subset_left_of_subset_union hAo hRo hAR
      (by rw [hcover]; exact subset_union_left.trans D.cover.le)
      ⟨p, hpplus, Or.inr hpbelow⟩
  have hAe : A = D.positive := Subset.antisymm hAplus hplusA
  have hRe : R = D.negative := by
    ext z
    constructor
    · intro hz
      have hm : z ∈ D.positive ∪ D.negative := D.cover.symm ▸ (hcover ▸ Or.inr hz)
      exact hm.resolve_left (fun hp ↦ disjoint_left.mp hAR (hAe.symm ▸ hp) hz)
    · intro hz
      have hm : z ∈ A ∪ R := hcover.symm ▸ (D.cover ▸ Or.inr hz)
      exact hm.resolve_left (fun ha ↦ disjoint_left.mp D.disjoint (hAe ▸ ha) hz)
  have hRsub : R ⊆ P \ S := fun z hz ↦ ⟨interior_subset hz.1, hz.2⟩
  have holdforward : frontier P \ S ⊆ closure R := by
    intro z hz
    rw [hRe]
    apply frontier_subset_closure
    rw [D.negative_frontier, hline]
    exact Or.inr hz
  have hPScl : P \ S ⊆ closure R := by
    intro z hz
    by_cases hi : z ∈ interior P
    · exact subset_closure ⟨hi, hz.2⟩
    · exact holdforward ⟨⟨subset_closure hz.1, hi⟩, hz.2⟩
  have hclosure : closure (P \ S) = closure D.negative := by
    apply le_antisymm
    · rw [← hRe]
      exact closure_minimal hPScl isClosed_closure
    · rw [← hRe]
      exact closure_mono hRsub
  have hQP : closure (P \ S) ⊆ P := closure_minimal sdiff_subset hP
  have hTQ : T ⊆ closure (P \ S) := by
    intro z hz
    rw [hclosure]
    apply frontier_subset_closure
    rw [D.negative_frontier, hline]
    exact Or.inl hz
  have hQeq : closure (P \ S) = (P \ S) ∪ T := by
    apply Subset.antisymm
    · intro z hz
      by_cases hzS : z ∈ S
      · right
        by_contra hzT
        have hpA : z ∈ A := Or.inr ⟨hzS, hzT⟩
        have hpD : z ∈ D.positive := hAe ▸ hpA
        have hclneg : closure D.negative ⊆ D.positiveᶜ :=
          closure_minimal
            (fun w hw hpw ↦ disjoint_left.mp D.disjoint hpw hw)
            D.positive_open.isClosed_compl
        exact (hclneg (hclosure ▸ hz)) hpD
      · exact Or.inl ⟨hQP hz, hzS⟩
    · rintro z (hz | hz)
      · exact subset_closure hz
      · exact hTQ hz
  have hQdiff : closure (P \ S) = P \ (S \ T) := by
    rw [hQeq]
    ext z
    constructor
    · rintro (hz | hz)
      · exact ⟨hz.1, fun hw ↦ hz.2 hw.1⟩
      · exact ⟨hSP (hTS hz), fun hw ↦ hw.2 hz⟩
    · rintro ⟨hzP, hzW⟩
      by_cases hzS : z ∈ S
      · exact Or.inr (by by_contra hzT; exact hzW ⟨hzS, hzT⟩)
      · exact Or.inl ⟨hzP, hzS⟩
  refine ⟨hAe, hRe, hclosure, hQeq, hQdiff, hQP, ?_, ?_⟩
  · rw [hclosure]
    exact D.negative_closed_frontier
  · exact ⟨(Homeomorph.setCongr hclosure).trans D.negative_homeomorph⟩

/-- The OLD ambient homeomorphism is sufficient for exterior connectedness. -/
theorem translatedCut_old_exterior_connected {P : Set ℂ}
    (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane) : IsConnected Pᶜ := by
  have he : Pᶜ = H ⁻¹' planarOpenLowerHalfplane := by
    rw [hP]
    ext z
    simp only [mem_compl_iff, mem_preimage, planarClosedUpperHalfplane,
      planarOpenLowerHalfplane, mem_setOf_eq, not_le]
  rw [he]
  exact H.isConnected_preimage.mpr planar_halfplane_partition.2.2.2.1


/-- Interior of the constructed closed side is the open component itself. -/
theorem translatedCut_negative_interior {line : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs line) :
    interior (closure D.negative) = D.negative := by
  apply Subset.antisymm
  · intro z hz
    have hm : z ∈ D.negative ∪ range line := by
      rw [← D.negative_frontier,← closure_eq_self_union_frontier]
      exact interior_subset hz
    exact hm.resolve_right (fun ht ↦ (D.negative_closed_frontier.symm ▸ ht).2 hz)
  · exact interior_maximal subset_closure D.negative_open

/-- Budget support is kept on the CLOSED new side. The source point p is
allowed to carry a positive old turn but has zero budget. Top marks are free. -/
theorem translatedCut_budget_support_retained {P S T Q : Set ℂ}
    (hQ : Q = P \ (S \ T)) (alpha : ℂ → ℝ) {p : ℂ}
    (hbudgetP : ∀ x, alpha x ≠ 0 → x ∈ P) (hp : alpha p = 0)
    (hclean : ∀ x ∈ S \ T, x ≠ p → alpha x = 0) :
    ∀ x, alpha x ≠ 0 → x ∈ Q := by
  intro x hx
  rw [hQ]
  refine ⟨hbudgetP x hx,?_⟩
  intro hxW
  by_cases hxp : x = p
  · exact hx (by simpa only [hxp] using hp)
  · exact hx (hclean x hxW hxp)

end RepulsiveCoulomb
