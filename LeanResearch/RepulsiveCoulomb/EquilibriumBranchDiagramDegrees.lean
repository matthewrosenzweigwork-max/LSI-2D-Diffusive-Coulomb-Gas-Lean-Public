import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNelsonParameters
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators

/-! Multiplicity-aware finite edge-list degrees for the centered correlation
estimate. Repeated and reversed ordered edges are separate occurrences. The
active-vertex count and high-count degree bound are proved without replacing
the list by a simple graph or assuming a correlation inequality. -/
noncomputable section
open scoped BigOperators Classical
namespace RepulsiveCoulomb

/-- Both endpoint slots of every edge occurrence count toward the degree. -/
def equilibriumDiagramDegree {N p : ℕ} (e : Fin p → Fin N × Fin N) (v : Fin N) : ℕ :=
  ∑ k : Fin p, ((if (e k).1 = v then 1 else 0) + (if (e k).2 = v then 1 else 0))

def equilibriumDiagramActive {N p : ℕ} (e : Fin p → Fin N × Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun v => 0 < equilibriumDiagramDegree e v)

theorem equilibriumDiagram_mem_active {N p : ℕ} (e : Fin p → Fin N × Fin N) (v : Fin N) :
    v ∈ equilibriumDiagramActive e ↔ 0 < equilibriumDiagramDegree e v := by
  simp only [equilibriumDiagramActive, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The degree sum retains every endpoint of every repeated ordered edge. -/
theorem equilibriumDiagram_degree_sum {N p : ℕ} (e : Fin p → Fin N × Fin N) :
    (∑ v : Fin N, equilibriumDiagramDegree e v) = 2 * p := by
  unfold equilibriumDiagramDegree
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  omega

theorem equilibriumDiagram_active_degree_sum {N p : ℕ} (e : Fin p → Fin N × Fin N) :
    (∑ v ∈ equilibriumDiagramActive e, equilibriumDiagramDegree e v) = 2 * p := by
  rw [equilibriumDiagramActive, Finset.sum_filter]
  calc
    (∑ v : Fin N, if 0 < equilibriumDiagramDegree e v then equilibriumDiagramDegree e v else 0) =
        ∑ v : Fin N, equilibriumDiagramDegree e v := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs with h <;> omega
    _ = _ := equilibriumDiagram_degree_sum e

/-- Loop-free ordered edges contribute at most one endpoint at a fixed vertex. -/
theorem equilibriumDiagram_degree_le_order {N p : ℕ} (e : Fin p → Fin N × Fin N)
    (he : ∀ k, (e k).1 ≠ (e k).2) (v : Fin N) : equilibriumDiagramDegree e v ≤ p := by
  have hk (k : Fin p) :
      (if (e k).1 = v then 1 else 0) + (if (e k).2 = v then 1 else 0) ≤ (1 : ℕ) := by
    by_cases h1 : (e k).1 = v <;> by_cases h2 : (e k).2 = v
    · exact (he k (h1.trans h2.symm)).elim
    · simp only [h1, h2, if_true, if_false]
      omega
    · simp only [h1, h2, if_true, if_false]
      omega
    · simp only [h1, h2, if_true, if_false]
      omega
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hk k)
  simpa only [equilibriumDiagramDegree, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] using h

/-- Once the signed singleton diagrams have been cancelled, every active
vertex has degree at least two. This finite consequence is stated separately. -/
theorem equilibriumDiagram_min_degree_of_no_singleton {N p : ℕ}
    (e : Fin p → Fin N × Fin N) (hno : ∀ v, equilibriumDiagramDegree e v ≠ 1)
    (v : Fin N) (hv : v ∈ equilibriumDiagramActive e) : 2 ≤ equilibriumDiagramDegree e v := by
  have hp := (equilibriumDiagram_mem_active e v).mp hv
  have hn := hno v
  omega

/-- Surviving diagrams involve at most p particle labels. -/
theorem equilibriumDiagram_active_card_le {N p : ℕ} (e : Fin p → Fin N × Fin N)
    (hmin : ∀ v ∈ equilibriumDiagramActive e, 2 ≤ equilibriumDiagramDegree e v) :
    (equilibriumDiagramActive e).card ≤ p := by
  have h := Finset.sum_le_sum hmin
  rw [equilibriumDiagram_active_degree_sum] at h
  simp only [Finset.sum_const, Nat.nsmul_eq_mul] at h
  omega

/-- Removing one active vertex leaves at least two endpoints at each other
active vertex. Multiplicity, rather than simple adjacency, controls the bound. -/
theorem equilibriumDiagram_degree_complement_bound {N p : ℕ} (e : Fin p → Fin N × Fin N)
    (hmin : ∀ v ∈ equilibriumDiagramActive e, 2 ≤ equilibriumDiagramDegree e v)
    (v : Fin N) (hv : v ∈ equilibriumDiagramActive e) :
    equilibriumDiagramDegree e v + 2 * ((equilibriumDiagramActive e).card - 1) ≤ 2 * p := by
  have h := Finset.sum_le_sum (s := (equilibriumDiagramActive e).erase v)
    (fun w hw => hmin w (Finset.mem_of_mem_erase hw))
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_erase_of_mem hv] at h
  have he := Finset.add_sum_erase (equilibriumDiagramActive e) (equilibriumDiagramDegree e) hv
  rw [equilibriumDiagram_active_degree_sum] at he
  omega

/-- Exact threshold for the specialized p=2*k*m, q=4*m moment argument.
The disjoint complementary low-count range is v<=p-2m. -/
theorem equilibriumDiagram_high_count_degree_le {N p m : ℕ}
    (e : Fin p → Fin N × Fin N)
    (hmin : ∀ v ∈ equilibriumDiagramActive e, 2 ≤ equilibriumDiagramDegree e v)
    (hcount : p - 2 * m + 1 ≤ (equilibriumDiagramActive e).card) (v : Fin N) :
    equilibriumDiagramDegree e v ≤ 4 * m := by
  by_cases hv : v ∈ equilibriumDiagramActive e
  · have hd := equilibriumDiagram_degree_complement_bound e hmin v hv
    have hpos : 0 < (equilibriumDiagramActive e).card := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  · have hd : equilibriumDiagramDegree e v = 0 := by
      have hn := mt (equilibriumDiagram_mem_active e v).mpr hv
      omega
    rw [hd]
    omega

end RepulsiveCoulomb
