import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDiagramDegrees
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-! Explicit finite counting of ordered edge lists by their active particle
labels. Repetitions are retained. Lists with a fixed active set inject into
all maps Fin p -> S x S, giving choose(N,v)*v^(2p) without graph-isomorphism
or multinomial-counting assumptions. -/
noncomputable section
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem equilibriumDiagram_endpoints_active {N p : ℕ}
    (e : Fin p → Fin N × Fin N) (k : Fin p) :
    (e k).1 ∈ equilibriumDiagramActive e ∧ (e k).2 ∈ equilibriumDiagramActive e := by
  constructor
  · apply (equilibriumDiagram_mem_active e _).mpr
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin p))) =>
        Nat.zero_le ((if (e j).1 = (e k).1 then 1 else 0) +
          (if (e j).2 = (e k).1 then 1 else 0))) (Finset.mem_univ k)
    change (if (e k).1 = (e k).1 then 1 else 0) + (if (e k).2 = (e k).1 then 1 else 0) ≤
      equilibriumDiagramDegree e (e k).1 at h
    simp at h
    omega
  · apply (equilibriumDiagram_mem_active e _).mpr
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin p))) =>
        Nat.zero_le ((if (e j).1 = (e k).2 then 1 else 0) +
          (if (e j).2 = (e k).2 then 1 else 0))) (Finset.mem_univ k)
    change (if (e k).1 = (e k).2 then 1 else 0) + (if (e k).2 = (e k).2 then 1 else 0) ≤
      equilibriumDiagramDegree e (e k).2 at h
    simp at h
    omega

/-- A literal label-preserving injection supplies the fixed-support bound. -/
theorem equilibriumDiagram_count_fixed_active {N p : ℕ} (S : Finset (Fin N)) :
    (Finset.univ.filter (fun e : Fin p → Fin N × Fin N => equilibriumDiagramActive e = S)).card ≤
      S.card ^ (2 * p) := by
  let A : Finset (Fin p → Fin N × Fin N) := Finset.univ.filter (fun e => equilibriumDiagramActive e = S)
  have he (e : A) : equilibriumDiagramActive e.val = S := (Finset.mem_filter.mp e.property).2
  let encode : A → (Fin p → S × S) := fun e k =>
    (⟨(e.val k).1, by rw [← he e]; exact (equilibriumDiagram_endpoints_active e.val k).1⟩,
     ⟨(e.val k).2, by rw [← he e]; exact (equilibriumDiagram_endpoints_active e.val k).2⟩)
  have hinj : Function.Injective encode := by
    intro e f hef
    apply Subtype.ext
    funext k
    exact Prod.ext (congrArg (fun q : Fin p → S × S => (q k).1.val) hef)
      (congrArg (fun q : Fin p → S × S => (q k).2.val) hef)
  have h := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_coe, Fintype.card_pi_const, Fintype.card_prod,
    ← pow_two, ← pow_mul] using h

/-- The active-count bound includes all repeated/reversed edge occurrences.
No loop-free restriction is needed for this upper count. -/
theorem equilibriumDiagram_count_active_card (N p v : ℕ) :
    (Finset.univ.filter (fun e : Fin p → Fin N × Fin N => (equilibriumDiagramActive e).card = v)).card ≤
      N.choose v * v ^ (2 * p) := by
  let supports : Finset (Finset (Fin N)) := Finset.univ.powersetCard v
  let lists : Finset (Fin p → Fin N × Fin N) := Finset.univ.filter (fun e => (equilibriumDiagramActive e).card = v)
  let fiber (S : Finset (Fin N)) : Finset (Fin p → Fin N × Fin N) :=
    Finset.univ.filter (fun e => equilibriumDiagramActive e = S)
  have hcover : lists ⊆ supports.biUnion fiber := by
    intro e he
    apply Finset.mem_biUnion.mpr
    refine ⟨equilibriumDiagramActive e, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp he).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  calc
    lists.card ≤ (supports.biUnion fiber).card := Finset.card_le_card hcover
    _ ≤ ∑ S ∈ supports, (fiber S).card := Finset.card_biUnion_le
    _ ≤ ∑ S ∈ supports, v ^ (2 * p) := by
      apply Finset.sum_le_sum
      intro S hS
      have hSv := (Finset.mem_powersetCard.mp hS).2
      simpa only [hSv] using equilibriumDiagram_count_fixed_active (p := p) S
    _ = N.choose v * v ^ (2 * p) := by
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, supports, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]

/-- The coarser label-power count used after dividing by N^p. -/
theorem equilibriumDiagram_count_active_card_le_pow (N p v : ℕ) :
    (Finset.univ.filter (fun e : Fin p → Fin N × Fin N => (equilibriumDiagramActive e).card = v)).card ≤
      N ^ v * v ^ (2 * p) :=
  (equilibriumDiagram_count_active_card N p v).trans
    (Nat.mul_le_mul_right _ (Nat.choose_le_pow N v))

end RepulsiveCoulomb
