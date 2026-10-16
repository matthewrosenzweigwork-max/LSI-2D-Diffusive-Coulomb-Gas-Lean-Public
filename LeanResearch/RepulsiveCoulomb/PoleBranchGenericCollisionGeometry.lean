import LeanResearch.RepulsiveCoulomb.PoleBranchCoulombHartogs
import LeanResearch.RepulsiveCoulomb.CoulombCollisionNull

/-! The intermediate domain is open and contains the original full-measure
collision complement. Every newly added point has exactly one possible
collision pair, so the selected residual factors are genuinely nonzero. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb

def poleBranchPairOtherRegular {N : ℕ} (p : Fin N × Fin N) : Set (CoulombConfig N) :=
  {z | ∀ q ∈ (coulombPairs N).erase p, z q.1 ≠ z q.2}

theorem poleBranchPairOtherRegular_isOpen {N : ℕ} (p : Fin N × Fin N) :
    IsOpen (poleBranchPairOtherRegular p) := by
  simp only [poleBranchPairOtherRegular, setOf_forall]
  apply isOpen_biInter_finset
  intro q hq
  exact isOpen_ne_fun (coulombCoordinate q.1).continuous (coulombCoordinate q.2).continuous

theorem poleBranch_domain_iff_selected_pair {N : ℕ} (p : Fin N × Fin N)
    (hp : p ∈ coulombPairs N) {z : CoulombConfig N} (hz : z ∈ poleBranchPairOtherRegular p) :
    z ∈ coulombDomain N ↔ z p.1 ≠ z p.2 := by
  classical
  change (∏ q ∈ coulombPairs N, (z q.1 - z q.2)) ≠ 0 ↔ _
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h
    exact sub_ne_zero.mp (h p hp)
  · intro h q hq
    by_cases he : q = p
    · subst q
      exact sub_ne_zero.mpr h
    · exact sub_ne_zero.mpr (hz q (Finset.mem_erase.mpr ⟨he, hq⟩))

theorem poleBranchCoulombRegular_isOpen (N : ℕ) : IsOpen (poleBranchCoulombRegular N) := by
  simp only [poleBranchCoulombRegular, poleBranchHyperplaneRegular, setOf_forall]
  apply isOpen_iInter_of_finite
  intro p
  apply isOpen_iInter_of_finite
  intro q
  apply isOpen_iInter_of_finite
  intro hpq
  exact (isOpen_ne.preimage (poleBranchCoulombNormal p).continuous).union
    (isOpen_ne.preimage (poleBranchCoulombNormal q).continuous)

theorem poleBranch_coulombDomain_subset_regular (N : ℕ) :
    (coulombDomain N : Set (CoulombConfig N)) ⊆ poleBranchCoulombRegular N := by
  intro z hz
  rw [poleBranchCoulombRegular_iff]
  intro p q hpq
  exact Or.inl ((coulombVandermonde_ne_zero_iff z).mp hz p.1.1 p.1.2 (ne_of_lt p.2))

theorem poleBranch_coulombDomain_dense (N : ℕ) : Dense (coulombDomain N : Set (CoulombConfig N)) :=
  Measure.dense_of_ae (coulombDomain_ae N)

theorem poleBranch_generic_collision_pair {N : ℕ} {z : CoulombConfig N}
    (hreg : z ∈ poleBranchCoulombRegular N) (hz : z ∉ coulombDomain N) :
    ∃ p : Fin N × Fin N, p ∈ coulombPairs N ∧ z p.1 = z p.2 ∧
      z ∈ poleBranchPairOtherRegular p := by
  classical
  have he : ∃ p ∈ coulombPairs N, z p.1 = z p.2 := by
    by_contra h
    push_neg at h
    apply hz
    change (∏ p ∈ coulombPairs N, (z p.1 - z p.2)) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => sub_ne_zero.mpr (h p hp))
  obtain ⟨p, hp, hpc⟩ := he
  refine ⟨p, hp, hpc, ?_⟩
  intro q hq
  have hqmem := (Finset.mem_erase.mp hq).2
  let p' : PoleBranchCoulombPair N := ⟨p, (mem_coulombPairs p).mp hp⟩
  let q' : PoleBranchCoulombPair N := ⟨q, (mem_coulombPairs q).mp hqmem⟩
  have hne : q' ≠ p' := fun h => (Finset.mem_erase.mp hq).1 (congrArg Subtype.val h)
  have H := (poleBranchCoulombRegular_iff z).mp hreg q' p' hne
  exact H.resolve_right (not_not.mpr hpc)

end RepulsiveCoulomb
