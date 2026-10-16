module

public import LeanResearch.RepulsiveCoulomb.PointRadialCyclicListIndex

@[expose] public section

/-! Successor draft. Retain actual first/last source identities and the initial
physical vertex when passing to natural slots. This extends the accepted list
slot construction without changing its curves, clocks, or cyclic indexing. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_point_radial_closed_list_slots_with_source_ends
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {p : ℂ} (L : List (PointRadialC1PlaneArc ha y))
    (hchain : PointRadialC1PlaneChain ha y p p L) (hlen : 2 ≤ L.length)
    (hpair : L.Pairwise (fun e f => Disjoint
      (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1))) :
    ∃ n : ℕ, ∃ arcs : ℕ → PointRadialC1PlaneArc ha y,
      n + 1 = L.length ∧ 0 < n ∧ (∀ k, arcs k ∈ L) ∧
      (∀ k < n, (arcs k).curve 1 = (arcs (k + 1)).curve 0) ∧
      (arcs n).curve 1 = (arcs 0).curve 0 ∧
      (∀ i j, i ≤ n → j ≤ n → ∀ s t,
        s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
        (arcs i).curve s = (arcs j).curve t → i = j ∧ s = t) ∧
      (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) = pointRadialC1PlaneCarrier L ∧
      (∀ hne : L ≠ [], arcs 0 = L.head hne ∧ arcs n = L.getLast hne) ∧
      (arcs 0).curve 0 = p ∧ (arcs n).curve 1 = p := by
  have hpos : 0 < L.length := by omega
  let n := L.length - 1
  let e := pointCyclicListIndex L.length hpos
  let arcs : ℕ → PointRadialC1PlaneArc ha y := fun k => L.get (e k)
  have hn : n + 1 = L.length := by dsimp [n]; omega
  have he (k : ℕ) (hk : k ≤ n) : (e k).val = k := Nat.mod_eq_of_lt (by omega)
  have he0 : e 0 = ⟨0, hpos⟩ := by apply Fin.ext; exact Nat.zero_mod _
  have hen (k : ℕ) : finRotate L.length (e k) = e (k + 1) := pointCyclicListIndex_rotate L.length hpos k
  have heclose : finRotate L.length (e n) = e 0 := by
    rw [hen]
    apply Fin.ext
    change (n + 1) % L.length = 0 % L.length
    rw [hn, Nat.mod_self, Nat.zero_mod]
  have hmem (k : ℕ) : arcs k ∈ L := List.get_mem L (e k)
  have hjoin (k : ℕ) : (arcs k).curve 1 = (L.get (finRotate L.length (e k))).curve 0 :=
    hchain.cyclic_get_endpoints hpos (e k)
  have hdisj := point_radial_list_get_pairwise hpair
  have hends (hne : L ≠ []) : arcs 0 = L.head hne ∧ arcs n = L.getLast hne := by
    constructor
    · change L.get (e 0) = L.head hne
      rw [List.get_eq_getElem, List.head_eq_getElem]
      congr 1
    · change L.get (e n) = L.getLast hne
      rw [List.get_eq_getElem, List.getLast_eq_getElem]
      congr 1
      exact (he n le_rfl).trans rfl
  have hne : L ≠ [] := List.length_pos_iff.mp hpos
  have hstart : (arcs 0).curve 0 = p := by
    rw [(hends hne).1]
    exact hchain.head_start hne
  have hend : (arcs n).curve 1 = p := by
    rw [(hends hne).2]
    exact hchain.last_finish hne
  refine ⟨n, arcs, hn, by dsimp [n]; omega, hmem, ?_, ?_, ?_, ?_, hends, hstart, hend⟩
  · intro k hk
    simpa only [hen, arcs] using hjoin k
  · simpa only [heclose, arcs] using hjoin n
  · intro i j hi hj s t hs ht heq
    by_cases hij : i = j
    · subst j
      exact ⟨rfl, (arcs i).injective (Ico_subset_Icc_self hs) (Ico_subset_Icc_self ht) heq⟩
    · have hene : e i ≠ e j := by
        intro heij
        apply hij
        simpa only [he i hi, he j hj] using congrArg Fin.val heij
      exact (disjoint_left.mp (hdisj hene) ⟨s, hs, rfl⟩ ⟨t, ht, heq.symm⟩).elim
  · ext z
    constructor
    · intro hz
      obtain ⟨k, hz⟩ := mem_iUnion.mp hz
      obtain ⟨hk, hz⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨arcs k, mem_iUnion.mpr ⟨hmem k, hz⟩⟩
    · intro hz
      obtain ⟨a, hz⟩ := mem_iUnion.mp hz
      obtain ⟨ha, hz⟩ := mem_iUnion.mp hz
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
      have hin : i.val ≤ n := by omega
      have heidx : e i.val = i := by apply Fin.ext; exact he _ hin
      refine mem_iUnion.mpr ⟨i.val, mem_iUnion.mpr ⟨hin, ?_⟩⟩
      simpa only [arcs, heidx, hi] using hz

end RepulsiveCoulomb
