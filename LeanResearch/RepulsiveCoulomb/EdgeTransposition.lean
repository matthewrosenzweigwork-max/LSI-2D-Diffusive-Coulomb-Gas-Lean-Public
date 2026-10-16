import LeanResearch.RepulsiveCoulomb.TripleEmbedding
import LeanResearch.RepulsiveCoulomb.TripleCounting

/-! Transpositions indexed by genuine unordered two-element subsets. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb
variable {α : Type*} [DecidableEq α]

def edgeTransposition (s : Finset α) : Equiv.Perm α :=
  if h : s.card = 2 then
    Equiv.swap (Classical.choose (Finset.card_eq_two.mp h))
      (Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp h)))
  else 1

theorem edgeTransposition_endpoints (s : Finset α) (hs : s.card = 2) :
    ∃ i j, i ≠ j ∧ s = {i,j} ∧ edgeTransposition s = Equiv.swap i j := by
  let h := Finset.card_eq_two.mp hs
  refine ⟨Classical.choose h, Classical.choose (Classical.choose_spec h), ?_⟩
  have hh := Classical.choose_spec (Classical.choose_spec h)
  exact ⟨hh.1, hh.2, by simp only [edgeTransposition, dif_pos hs]⟩

theorem swap_eq_of_pair_eq (i j k l : α) (h : ({i,j} : Finset α) = {k,l}) :
    Equiv.swap i j = Equiv.swap k l := by
  have hh : ({i,j} : Set α) = {k,l} := by
    simpa only [Finset.coe_pair] using congrArg (fun s : Finset α => (s : Set α)) h
  rcases Set.pair_eq_pair_iff.mp hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact Equiv.swap_comm _ _

theorem edgeTransposition_pair (i j : α) (hij : i ≠ j) :
    edgeTransposition {i,j} = Equiv.swap i j := by
  obtain ⟨a,b,hab,hpair,he⟩ := edgeTransposition_endpoints ({i,j} : Finset α) (Finset.card_pair hij)
  exact he.trans (swap_eq_of_pair_eq a b i j hpair.symm)

theorem edgeTransposition_inv (s : Finset α) : (edgeTransposition s)⁻¹ = edgeTransposition s := by
  by_cases hs : s.card = 2
  · obtain ⟨i,j,_,_,he⟩ := edgeTransposition_endpoints s hs
    rw [he, Equiv.swap_inv]
  · simp [edgeTransposition, hs]

theorem triple_edges (i j k : α) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({i,j,k} : Finset α).powersetCard 2 = {{i,j},{i,k},{j,k}} := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hs
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hcard
    have ha := hsub (Finset.mem_insert_self a {b})
    have hb := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp_all [Finset.pair_comm]
  · intro hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> simp [Finset.mem_powersetCard, hij, hik, hjk]

theorem sum_triple_edges {E : Type*} [AddCommMonoid E] (w : Finset α → E)
    (i j k : α) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ s ∈ ({i,j,k} : Finset α).powersetCard 2, w s) = w {i,j} + w {j,k} + w {i,k} := by
  classical
  rw [triple_edges i j k hij hik hjk]
  have h1 : ({i,j} : Finset α) ≠ {i,k} := by
    intro h
    have hj := h ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self j) : j ∈ ({i,j} : Finset α))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    exact hj.elim (fun h => hij h.symm) hjk
  have h2 : ({i,j} : Finset α) ≠ {j,k} := by
    intro h
    have hi := h ▸ (Finset.mem_insert_self i {j})
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    exact hi.elim hij hik
  have h3 : ({i,k} : Finset α) ≠ {j,k} := by
    intro h
    have hi := h ▸ (Finset.mem_insert_self i {k})
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    exact hi.elim hij hik
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, h1, h2, h3,
    or_self, not_false_eq_true, Finset.sum_singleton]
  abel

end RepulsiveCoulomb
