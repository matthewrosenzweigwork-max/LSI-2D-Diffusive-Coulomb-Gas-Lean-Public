module

public import LeanResearch.RepulsiveCoulomb.JordanRegularCornerOrientedTurn
public import LeanResearch.RepulsiveCoulomb.PointRadialFiniteTurn

@[expose] public section

/-! The genuine regular C1 corner-turn theorem in the original finite Nat
slots used by actual weighted point-flux accounting. Only the finite cyclic
index helpers are reused from the radial-family adapter. The arcs in this
statement have no radial or holomorphic collar requirement. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- Total oriented turn for the original regular noncuspidal finite family,
including arbitrary regular circle/line cap corners. -/
theorem finite_regular_original_family_oriented_total_turn
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hn : 0 < n)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    (hc : ∀ k ≤ n, deriv (f k) 0 / deriv (f (if k = 0 then n else k - 1)) 1 ∈ Complex.slitPlane)
    (w : ℂ) (hw : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)
    (τ Ξ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hτ : ∀ k ≤ n, Continuous (τ k)) (hΞ : ∀ k ≤ n, Continuous (Ξ k))
    (hτl : ∀ k ≤ n, ∀ t, Complex.exp ((τ k t : ℂ) * Complex.I) =
      deriv (f k) t / (‖deriv (f k) t‖ : ℂ))
    (hΞl : ∀ k ≤ n, ∀ t, Complex.exp ((Ξ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ))
    (hpoint : (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), (τ k 1 - τ k 0)) +
      (∑ k ∈ Finset.range (n + 1), Complex.arg (deriv (f k) 0 /
        deriv (f (if k = 0 then n else k - 1)) 1)) =
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
  have hnext (i : Fin (n + 1)) : f i.val 1 = f (finRotate (n + 1) i).val 0 := by
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
  have hsum (q : ℕ → ℝ) : (∑ k ∈ Finset.range (n + 1), q k) = ∑ i : Fin (n + 1), q i.val := by
    have hs := finite_cycle_enumeration_sum n e hei hes (fun i => q i.val)
    have hl : (∑ k ∈ Finset.range (n + 1), q (e k).val) = ∑ k ∈ Finset.range (n + 1), q k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [he k (by have := Finset.mem_range.mp hk; omega)]
    exact hl.symm.trans hs
  have ht := finite_regular_noncuspidal_jordan_oriented_total_turn
    (finRotate (n + 1)) (finRotate_ne_self_of_two_le (by omega)) n e hei hes hen hec
    (fun i => f i.val) (fun i => hf i.val (by omega)) hnext
    (fun i t ht => hreg i.val (by omega) t ht)
    (by
      intro i j s t hs ht hij
      have h := hinj i.val j.val (by omega) (by omega) s t hs ht hij
      exact ⟨Fin.ext h.1, h.2⟩)
    (by
      intro i
      simpa only [finRotate_symm_val_predecessor] using hc i.val (by omega)) w
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
    Complex.arg (deriv (f k) 0 / deriv (f (if k = 0 then n else k - 1)) 1)),
    hsum (fun k => Ξ k 1 - Ξ k 0)]
  exact ht

end RepulsiveCoulomb
