import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerPointWinding
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Literal reversal of the original finite corner family. Joint half-open
simplicity is transported via the constructed original periodic loop; no
assumption about the reversed drawing is introduced. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

def finiteCornerReverse (f : ℕ → ℝ → ℂ) (n : ℕ) : ℕ → ℝ → ℂ :=
  fun k t => f (n - k) (1 - t)

/-- The other endpoint convention is also jointly injective. This follows
from actual periodization, rather than assuming distinct closed arc images. -/
theorem finite_corner_joint_injOn_Ioc
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t) :
    ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ioc (0 : ℝ) 1 → t ∈ Ioc (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t := by
  obtain ⟨_, hp, hi, _, _⟩ := euclideanFiniteCornerPeriodize_properties f n hf hv hclose hinj
  have hioc := periodic_simple_loop_injOn_Ioc hp hi
  have hM : 0 < (n + 1 : ℝ) := by positivity
  intro i j hin hjn s t hs ht heq
  have hiR : (i : ℝ) ≤ n := by exact_mod_cast hin
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hsi : ((i : ℝ) + s) / (n + 1 : ℝ) ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg i) hs.1) hM,
      (div_le_one hM).mpr (by linarith [hs.2])⟩
  have htj : ((j : ℝ) + t) / (n + 1 : ℝ) ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) ht.1) hM,
      (div_le_one hM).mpr (by linarith [ht.2])⟩
  have he := hioc hsi htj (by
    rw [euclideanFiniteCornerPeriodize_slot f n hf hv hclose i hin s (Ioc_subset_Icc_self hs),
      euclideanFiniteCornerPeriodize_slot f n hf hv hclose j hjn t (Ioc_subset_Icc_self ht)]
    exact heq)
  have hsum : (i : ℝ) + s = (j : ℝ) + t := (div_left_inj' hM.ne').mp he
  have hij : i = j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hstep : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.add_one_le_iff.mpr hij)
      linarith [hs.2, ht.1]
    · have hstep : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.add_one_le_iff.mpr hji)
      linarith [ht.2, hs.1]
  exact ⟨hij, by simpa only [hij, add_left_cancel_iff] using hsum⟩

/-- All the original geometric hypotheses survive the literal reversal. -/
theorem finiteCornerReverse_properties
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0) :
    let g := finiteCornerReverse f n
    (∀ k ≤ n, ContDiff ℝ 1 (g k)) ∧
      (∀ k < n, g k 1 = g (k + 1) 0) ∧ g n 1 = g 0 0 ∧
      (∀ i j, i ≤ n → j ≤ n → ∀ s t,
        s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
        g i s = g j t → i = j ∧ s = t) ∧
      (∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (g k) t ≠ 0) ∧
      (⋃ k ≤ n, g k '' Icc (0 : ℝ) 1) = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
  have hioc := finite_corner_joint_injOn_Ioc f n (fun k hk => (hf k hk).continuous) hv hclose hinj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact (hf (n - k) (Nat.sub_le _ _)).comp (contDiff_const.sub contDiff_id)
  · intro k hk
    simp only [finiteCornerReverse, sub_self, sub_zero]
    have he := hv (n - (k + 1)) (by omega)
    have hindex : n - (k + 1) + 1 = n - k := by omega
    rw [hindex] at he
    exact he.symm
  · simpa only [finiteCornerReverse, Nat.sub_self, Nat.sub_zero, sub_self, sub_zero] using hclose.symm
  · intro i j hin hjn s t hs ht heq
    obtain ⟨hij, hst⟩ := hioc (n - i) (n - j) (Nat.sub_le _ _) (Nat.sub_le _ _) (1 - s) (1 - t)
      (by constructor <;> linarith [hs.1, hs.2])
      (by constructor <;> linarith [ht.1, ht.2]) heq
    exact ⟨by omega, by linarith⟩
  · intro k hk t ht
    change deriv (fun s : ℝ => f (n - k) (1 - s)) t ≠ 0
    rw [deriv_comp_const_sub]
    exact neg_ne_zero.mpr (hreg (n - k) (Nat.sub_le _ _) (1 - t)
      (by constructor <;> linarith [ht.1, ht.2]))
  · ext z
    simp only [mem_iUnion, mem_image]
    constructor
    · rintro ⟨k, hk, t, ht, htz⟩
      exact ⟨n - k, Nat.sub_le _ _, 1 - t,
        by constructor <;> linarith [ht.1, ht.2], htz⟩
    · rintro ⟨k, hk, t, ht, htz⟩
      refine ⟨n - k, Nat.sub_le _ _, 1 - t,
        by constructor <;> linarith [ht.1, ht.2], ?_⟩
      simpa only [finiteCornerReverse, Nat.sub_sub_self hk, sub_sub_cancel] using htz

/-- Reversing slot order preserves the finite sum. -/
theorem finite_corner_reflection_sum (n : ℕ) (q : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 1), q (n - k)) = ∑ k ∈ Finset.range (n + 1), q k := by
  classical
  apply Finset.sum_bij (fun k _ => n - k) (fun k hk => Finset.mem_range.mpr (by omega))
  · intro i hi j hj he
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact ⟨n - j, Finset.mem_range.mpr (by omega), by omega⟩
  · intro _ _
    rfl

end RepulsiveCoulomb
