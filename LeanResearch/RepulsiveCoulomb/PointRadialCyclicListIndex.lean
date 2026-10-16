module

public import LeanResearch.RepulsiveCoulomb.PointRadialC1HalfOpenCorners
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.List.Chain

@[expose] public section

/-! Concrete cyclic indices of an actual finite radial C¹ plane chain.
Endpoint matching and joint half-open simplicity come from the actual list,
not a new abstract cycle certificate. The two-edge case is retained. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointCyclicListIndex (N : ℕ) (hN : 0 < N) (k : ℕ) : Fin N :=
  ⟨k % N, Nat.mod_lt _ hN⟩

theorem pointCyclicListIndex_rotate (N : ℕ) (hN : 0 < N) (k : ℕ) :
    finRotate N (pointCyclicListIndex N hN k) = pointCyclicListIndex N hN (k + 1) := by
  letI : NeZero N := ⟨hN.ne'⟩
  rw [finRotate_apply]
  apply Fin.ext
  change (k % N + 1 % N) % N = (k + 1) % N
  exact (Nat.add_mod k 1 N).symm

theorem finRotate_ne_self_of_two_le {N : ℕ} (hN : 2 ≤ N) (i : Fin N) : finRotate N i ≠ i := by
  have hpos : 0 < N := by omega
  letI : NeZero N := ⟨hpos.ne'⟩
  intro he
  have hv := congrArg Fin.val he
  rw [finRotate_apply] at hv
  change (i.val + 1 % N) % N = i.val at hv
  rw [Nat.mod_eq_of_lt (by omega : 1 < N)] at hv
  by_cases hi : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have hiN : i.val + 1 = N := by omega
    rw [hiN, Nat.mod_self] at hv
    omega

namespace PointRadialC1PlaneChain
variable {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}

theorem head_start {p q : ℂ} {L : List (PointRadialC1PlaneArc ha y)}
    (h : PointRadialC1PlaneChain ha y p q L) (hne : L ≠ []) :
    (L.head hne).start = p := by
  cases h with
  | nil => contradiction
  | cons e ht => rfl

theorem last_finish {p q : ℂ} {L : List (PointRadialC1PlaneArc ha y)}
    (h : PointRadialC1PlaneChain ha y p q L) (hne : L ≠ []) :
    (L.getLast hne).finish = q := by
  have hnil : ∀ (p q : ℂ), PointRadialC1PlaneChain ha y p q [] → p = q := by
    intro p q hpq
    cases hpq
    rfl
  induction h with
  | nil => contradiction
  | @cons e q es h ih =>
    by_cases hes : es = []
    · subst es
      simpa using hnil e.finish q h
    · rw [List.getLast_cons hes]
      exact ih hes

theorem actual_isChain {p q : ℂ} {L : List (PointRadialC1PlaneArc ha y)}
    (h : PointRadialC1PlaneChain ha y p q L) :
    L.IsChain (fun e f => e.finish = f.start) := by
  induction h with
  | nil => exact .nil
  | @cons e q es h ih =>
    cases es with
    | nil => exact .singleton e
    | cons f fs => exact .cons_cons (h.head_start (by simp)).symm ih

/-- The actual final-to-initial join and every internal join are captured by
the literal cyclic permutation of the finite list positions. -/
theorem cyclic_get_endpoints {p : ℂ} {L : List (PointRadialC1PlaneArc ha y)}
    (h : PointRadialC1PlaneChain ha y p p L) (hlen : 0 < L.length)
    (i : Fin L.length) :
    (L.get i).finish = (L.get (finRotate L.length i)).start := by
  letI : NeZero L.length := ⟨hlen.ne'⟩
  have hne : L ≠ [] := List.length_pos_iff.mp hlen
  have hie : pointCyclicListIndex L.length hlen i.val = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  have hri : finRotate L.length i = pointCyclicListIndex L.length hlen (i.val + 1) := by
    simpa only [hie] using pointCyclicListIndex_rotate L.length hlen i.val
  by_cases hi : i.val + 1 < L.length
  · rw [hri, List.get_eq_getElem, List.get_eq_getElem]
    change (L[i.val]'i.isLt).finish =
      (L[(i.val + 1) % L.length]'(Nat.mod_lt _ hlen)).start
    simp only [Nat.mod_eq_of_lt hi]
    exact h.actual_isChain.getElem i.val hi
  · have hiN : i.val + 1 = L.length := by omega
    have hl : L.get i = L.getLast hne := by
      rw [List.get_eq_getElem, List.getLast_eq_getElem]
      congr 1
      omega
    have hr : L.get (finRotate L.length i) = L.head hne := by
      rw [hri, List.get_eq_getElem, List.head_eq_getElem]
      have hzero : (pointCyclicListIndex L.length hlen (i.val + 1)).val = 0 := by
        simp only [pointCyclicListIndex, hiN, Nat.mod_self]
      simp only [hzero]
    rw [hl, hr, h.last_finish hne, h.head_start hne]

end PointRadialC1PlaneChain

/-- The list's actual Pairwise half-open separation yields symmetric
pairwise separation at every pair of distinct finite positions. -/
theorem point_radial_list_get_pairwise
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {L : List (PointRadialC1PlaneArc ha y)}
    (h : L.Pairwise (fun e f => Disjoint
      (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1))) :
    Pairwise (fun i j : Fin L.length => Disjoint
      ((L.get i).curve '' Ico (0 : ℝ) 1) ((L.get j).curve '' Ico (0 : ℝ) 1)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact h.rel_get_of_lt hlt
  · exact (h.rel_get_of_lt hgt).symm

/-- Finite-index carrier and the original actual list carrier coincide. -/
theorem point_radial_list_index_carrier
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    (L : List (PointRadialC1PlaneArc ha y)) :
    (⋃ i : Fin L.length, (L.get i).curve '' Icc (0 : ℝ) 1) = pointRadialC1PlaneCarrier L := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨L.get i, mem_iUnion.mpr ⟨List.get_mem L i, hi⟩⟩
  · intro hz
    obtain ⟨e, he⟩ := mem_iUnion.mp hz
    obtain ⟨hemem, hze⟩ := mem_iUnion.mp he
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hemem
    exact mem_iUnion.mpr ⟨i, by rwa [hi]⟩

end RepulsiveCoulomb
