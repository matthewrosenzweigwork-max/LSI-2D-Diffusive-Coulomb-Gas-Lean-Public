module

public import LeanResearch.RepulsiveCoulomb.PointRadialCyclicTurn
public import LeanResearch.RepulsiveCoulomb.PointFiniteCyclicCornerOrder

@[expose] public section

/-! Express the checked actual radial-cycle total turn on the same finite
natural-number slots used by original point-flux accounting. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem finRotate_symm_val_predecessor (n : ℕ) (i : Fin (n + 1)) :
    ((finRotate (n + 1)).symm i).val = if i.val = 0 then n else i.val - 1 := by
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := Fin.ext hi
    have hlast : (finRotate (n + 1)).symm (0 : Fin (n + 1)) = Fin.last n := by
      apply (finRotate (n + 1)).injective
      rw [Equiv.apply_symm_apply, finRotate_last]
    rw [hi0, hlast]
    simp
  · have hi0 : i ≠ 0 := by intro he; exact hi (congrArg Fin.val he)
    rw [if_neg hi]
    exact coe_finRotate_symm_of_ne_zero hi0

/-- The actual radial-family turn formula on original slots, with their
literal cyclic predecessor, follows from the checked finite-index theorem. -/
theorem point_radial_finite_family_oriented_total_turn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (arcs : ℕ → PointRadialC1PlaneArc ha y) (n : ℕ) (hn : 0 < n)
    (hv : ∀ k < n, (arcs k).curve 1 = (arcs (k + 1)).curve 0)
    (hclose : (arcs n).curve 1 = (arcs 0).curve 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      (arcs i).curve s = (arcs j).curve t → i = j ∧ s = t)
    (w : ℂ) (hw : w ∉ ⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1)
    (τ Ξ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hτ : ∀ k ≤ n, Continuous (τ k)) (hΞ : ∀ k ≤ n, Continuous (Ξ k))
    (hτl : ∀ k ≤ n, ∀ t, Complex.exp ((τ k t : ℂ) * Complex.I) =
      deriv (arcs k).curve t / (‖deriv (arcs k).curve t‖ : ℂ))
    (hΞl : ∀ k ≤ n, ∀ t, Complex.exp ((Ξ k t : ℂ) * Complex.I) =
      ((arcs k).curve t - w) / (‖(arcs k).curve t - w‖ : ℂ))
    (hpoint : (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), (τ k 1 - τ k 0)) +
      (∑ k ∈ Finset.range (n + 1), Complex.arg (deriv (arcs k).curve 0 /
        deriv (arcs (if k = 0 then n else k - 1)).curve 1)) =
      ∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0) := by
  let e := pointCyclicListIndex (n + 1) (Nat.zero_lt_succ n)
  have he (k : ℕ) (hk : k ≤ n) : (e k).val = k := Nat.mod_eq_of_lt (by omega)
  have hei : ∀ j ≤ n, ∀ k ≤ n, e j = e k → j = k := by
    intro j hj k hk hjk
    simpa only [he j hj, he k hk] using congrArg Fin.val hjk
  have hes : ∀ i : Fin (n + 1), ∃ k ≤ n, e k = i := by
    intro i
    refine ⟨i.val, by omega, ?_⟩
    apply Fin.ext
    exact he _ (by omega)
  have hen (k : ℕ) (_ : k < n) : finRotate (n + 1) (e k) = e (k + 1) :=
    pointCyclicListIndex_rotate (n + 1) (Nat.zero_lt_succ n) k
  have hec : finRotate (n + 1) (e n) = e 0 := by
    change finRotate (n + 1) (pointCyclicListIndex (n + 1) _ n) = pointCyclicListIndex (n + 1) _ 0
    rw [pointCyclicListIndex_rotate]
    apply Fin.ext
    simp only [pointCyclicListIndex, Nat.mod_self, Nat.zero_mod]
  have hnext (i : Fin (n + 1)) : (arcs i.val).finish = (arcs (finRotate (n + 1) i).val).start := by
    by_cases hi : i.val < n
    · have hir : finRotate (n + 1) i = ⟨i.val + 1, by omega⟩ := finRotate_of_lt hi
      rw [hir]
      exact hv i.val hi
    · have hilast : i = Fin.last n := by
        apply Fin.ext
        change i.val = n
        omega
      rw [hilast, finRotate_last]
      exact hclose
  have hdisj : Pairwise (fun i j : Fin (n + 1) => Disjoint
      ((arcs i.val).curve '' Ico (0 : ℝ) 1) ((arcs j.val).curve '' Ico (0 : ℝ) 1)) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
    exact hij (Fin.ext (hinj i.val j.val (by omega) (by omega) s t hs ht (hsz.trans htz.symm)).1)
  have hsum (q : ℕ → ℝ) : (∑ k ∈ Finset.range (n + 1), q k) = ∑ i : Fin (n + 1), q i.val := by
    have hs := finite_cycle_enumeration_sum n e hei hes (fun i => q i.val)
    have hl : (∑ k ∈ Finset.range (n + 1), q (e k).val) = ∑ k ∈ Finset.range (n + 1), q k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [he k (by have := Finset.mem_range.mp hk; omega)]
    exact hl.symm.trans hs
  have ht := point_radial_C1_cycle_oriented_total_turn ha y (finRotate (n + 1))
    (finRotate_ne_self_of_two_le (by omega)) n e hei hes hen hec
    (fun i => arcs i.val) hnext hdisj w
    (by
      intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hw (mem_iUnion.mpr ⟨i.val, mem_iUnion.mpr ⟨by omega, hi⟩⟩))
    (fun i => τ i.val) (fun i => Ξ i.val)
    (fun i => hτ i.val (by omega)) (fun i => hΞ i.val (by omega))
    (fun i => hτl i.val (by omega)) (fun i => hΞl i.val (by omega))
    (by rwa [← hsum (fun k => Ξ k 1 - Ξ k 0)])
  simp only [finRotate_symm_val_predecessor] at ht
  rw [hsum (fun k => τ k 1 - τ k 0), hsum (fun k =>
    Complex.arg (deriv (arcs k).curve 0 / deriv (arcs (if k = 0 then n else k - 1)).curve 1)),
    hsum (fun k => Ξ k 1 - Ξ k 0)]
  exact ht

end RepulsiveCoulomb
