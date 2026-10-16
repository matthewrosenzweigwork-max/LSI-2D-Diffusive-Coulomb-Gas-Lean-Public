module

public import LeanResearch.RepulsiveCoulomb.FullStripResidualSource

@[expose] public section

/-! Literal cut topology. The hypotheses in the intermediate theorem concern
ordinary local openness and connectedness; the point-metric endpoint constructs
them from the actual strip and genuine whole metric charts. No residual region,
residual homeomorphism, or curvature update is an input. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem fullStrip_difference_open {P S : Set ℂ} (hP : IsClosed P) (hS : IsClosed S)
    (hboundary : frontier P ⊆ S) : IsOpen (P \ S) := by
  have he : P \ S = interior P \ S := by
    ext z
    constructor
    · rintro ⟨hzP, hzS⟩
      refine ⟨?_, hzS⟩
      by_contra hzi
      exact hzS (hboundary ⟨hP.closure_eq.symm ▸ hzP, hzi⟩)
    · exact fun hz ↦ ⟨interior_subset hz.1, hz.2⟩
  rw [he, sdiff_eq]
  exact isOpen_interior.inter hS.isOpen_compl

/-- Relative openness along the old boundary becomes ambient openness after
adjoining the exterior. This is where a merely injective map would not suffice. -/
theorem fullStrip_exterior_union_open {P B : Set ℂ} (hP : IsClosed P)
    (hrelative : IsOpen {z : P | z.1 ∈ B}) : IsOpen (Pᶜ ∪ B) := by
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hrelative
  have he : Pᶜ ∪ B = Pᶜ ∪ U := by
    ext z
    by_cases hz : z ∈ P
    · have h := congrArg (fun W : Set P ↦ (⟨z, hz⟩ : P) ∈ W) hUeq
      simpa only [mem_union, mem_compl_iff, hz, not_true_eq_false, false_or,
        mem_preimage, mem_setOf_eq] using (Iff.of_eq h).symm
    · simp [hz]
  rw [he]
  exact hP.isOpen_compl.union hU

theorem fullStrip_exterior_union_connected {P B : Set ℂ}
    (houtside : IsConnected Pᶜ) (hB : IsConnected B)
    {p : ℂ} (hpB : p ∈ B) (hpfront : p ∈ frontier P) :
    IsConnected (Pᶜ ∪ B) := by
  have hpcl : p ∈ closure Pᶜ := frontier_subset_closure (by
    simpa only [frontier_compl] using hpfront)
  have hc : IsConnected (insert p Pᶜ) := houtside.subset_closure
    (subset_insert p _) (insert_subset hpcl subset_closure)
  have hu := hc.union ⟨p, mem_insert p _, hpB⟩ hB
  rw [insert_union] at hu
  rw [insert_eq_of_mem (show p ∈ Pᶜ ∪ B from Or.inr hpB)] at hu
  exact hu

/-- The actual open/closed separation argument. It yields equality of the
OPEN remainder with the correct component, hence literal equality after closure.
The side containing the old bottom is shown to contain both the strip below its
top and the old exterior. -/
theorem fullStrip_residual_is_negative_side
    {P S : Set ℂ} {top : ℝ → ℂ} (D : PlanarLineHalfplaneHomeomorphs top)
    (hP : IsClosed P) (hS : IsClosed S) (hSP : S ⊆ P)
    (htop : range top ⊆ S) (hboundary : frontier P ⊆ S)
    (hrelative : IsOpen {z : P | z.1 ∈ S \ range top})
    (houtside : IsConnected Pᶜ) (hbelow : IsConnected (S \ range top))
    {p : ℂ} (hpbelow : p ∈ S \ range top) (hpfront : p ∈ frontier P)
    (hpplus : p ∈ D.positive) :
    Pᶜ ∪ (S \ range top) = D.positive ∧
    P \ S = D.negative ∧
    closure (P \ S) = closure D.negative ∧
    closure (P \ S) ⊆ P ∧
    frontier (closure (P \ S)) = range top := by
  let A := Pᶜ ∪ (S \ range top)
  let R := P \ S
  have hAo : IsOpen A := fullStrip_exterior_union_open hP hrelative
  have hAc : IsConnected A := fullStrip_exterior_union_connected houtside hbelow hpbelow hpfront
  have hRo : IsOpen R := fullStrip_difference_open hP hS hboundary
  have hAR : Disjoint A R := by
    apply disjoint_left.mpr
    rintro z (hz | hz) hzR
    · exact hz hzR.1
    · exact hzR.2 hz.1
  have hcover : A ∪ R = (range top)ᶜ := by
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact fun ht ↦ hz (hSP (htop ht))
      · exact hz.2
      · exact fun ht ↦ hz.2 (htop ht)
    · intro hz
      by_cases hzP : z ∈ P
      · by_cases hzS : z ∈ S
        · exact Or.inl (Or.inr ⟨hzS, hz⟩)
        · exact Or.inr ⟨hzP, hzS⟩
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
  refine ⟨hAe, hRe, congrArg closure hRe, ?_, ?_⟩
  · exact closure_minimal sdiff_subset hP
  · change frontier (closure R) = range top
    rw [hRe]
    exact D.negative_closed_frontier

/-- The ordinary homeomorphism supplied for the OLD halfplane proves the
needed exterior connectedness. No property of the residual is assumed here. -/
theorem fullStrip_old_halfplane_exterior_connected {P : Set ℂ}
    (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane) : IsConnected Pᶜ := by
  have he : Pᶜ = H ⁻¹' planarOpenLowerHalfplane := by
    rw [hP]
    ext z
    simp only [mem_compl_iff, mem_preimage, planarClosedUpperHalfplane,
      planarOpenLowerHalfplane, mem_setOf_eq, not_le]
  rw [he]
  exact H.isConnected_preimage.mpr planar_halfplane_partition.2.2.2.1

end RepulsiveCoulomb
