import LeanResearch.RepulsiveCoulomb.JordanFiniteC1Loop
import LeanResearch.RepulsiveCoulomb.JordanSmoothArcTurnAssembly
import Mathlib.Topology.Order.ProjIcc

/-! Genuine finite tangent-turn summation for an actual matched-jet cyclic
family. The global C¹ simple regular loop is constructed, its tangent lift is
constructed, and the finite sum is obtained by restricting that lift and
proved telescoping. No finite angle-sum certificate is assumed. This is the
post-rounding theorem; the corner-rounding construction remains separate.
Records-only candidate. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem finite_matched_regular_arc_turn_sum (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0)
    (hd : ∀ k < n, deriv (f k) 1 = deriv (f (k + 1)) 0)
    (hclose : f n 1 = f 0 0) (hcloseD : deriv (f n) 1 = deriv (f 0) 0)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    (hinj : ∀ k ≤ n, InjOn (f k) (Ico (0 : ℝ) 1))
    (hdisj : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
      Disjoint (f i '' Ico (0 : ℝ) 1) (f j '' Ico (0 : ℝ) 1))
    (θ : ℕ → Icc (0 : ℝ) 1 → ℝ) (hθ : ∀ k ≤ n, Continuous (θ k))
    (hθlift : ∀ k ≤ n, ∀ t, Complex.exp ((θ k t : ℂ) * Complex.I) =
      deriv (f k) t / (‖deriv (f k) t‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (θ k 1 - θ k 0)) = 2 * Real.pi ∨
      (∑ k ∈ Finset.range (n + 1), (θ k 1 - θ k 0)) = -(2 * Real.pi) := by
  obtain ⟨Γ, hΓ, hΓclose, hΓjet, hΓinj, hΓreg, _, hslots⟩ :=
    exists_finite_matched_regular_C1_loop f n hf hv hd hclose hcloseD hreg hinj hdisj
  obtain ⟨Θ, hΘ, hΘlift⟩ := exists_regular_edge_tangent_angle_lift hΓ hΓreg
  let m : ℝ := n + 1
  have hm : 0 < m := by dsimp [m]; positivity
  let Q := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) Θ
  have hincrement (k : ℕ) (hk : k ≤ n) :
      θ k 1 - θ k 0 = Q (((k : ℝ) + 1) / m) - Q ((k : ℝ) / m) := by
    have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
    let σ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
      ⟨((k : ℝ) + t) / m, div_nonneg (add_nonneg (Nat.cast_nonneg k) t.2.1) hm.le,
        (div_le_one hm).mpr (by dsimp [m]; linarith [t.2.2])⟩
    have hσ : Continuous σ :=
      ((continuous_const.add continuous_subtype_val).div_const m).subtype_mk _
    have hD (t : Icc (0 : ℝ) 1) : deriv Γ (σ t) = m • deriv (f k) t :=
      (hslots k hk t t.2).2
    have hLiftEq (t : Icc (0 : ℝ) 1) : Circle.exp (θ k t) = Circle.exp (Θ (σ t)) := by
      apply Circle.ext
      change Complex.exp ((θ k t : ℂ) * Complex.I) = Complex.exp ((Θ (σ t) : ℂ) * Complex.I)
      rw [hθlift k hk, hΘlift, hD]
      exact (congrArg (fun z : Circle => (z : ℂ))
        (euclideanDirection_smul_pos (hreg k hk t t.2) hm)).symm
    have hi := euclidean_angle_lift_increment_eq (hθ k hk) (hΘ.comp hσ) hLiftEq
      (0 : Icc (0 : ℝ) 1) 1
    have hQ0 : Q ((k : ℝ) / m) = Θ (σ 0) := by
      have hkm : (k : ℝ) / m ∈ Icc (0 : ℝ) 1 := by
        exact ⟨div_nonneg (Nat.cast_nonneg k) hm.le,
          (div_le_one hm).mpr (by dsimp [m]; linarith)⟩
      dsimp only [Q]
      rw [Set.IccExtend_of_mem (show (0 : ℝ) ≤ 1 by norm_num) Θ hkm]
      congr 1
      apply Subtype.ext
      simp [σ]
    have hQ1 : Q (((k : ℝ) + 1) / m) = Θ (σ 1) := by
      have hkm : ((k : ℝ) + 1) / m ∈ Icc (0 : ℝ) 1 := by
        exact ⟨div_nonneg (by positivity) hm.le,
          (div_le_one hm).mpr (by dsimp [m]; linarith)⟩
      dsimp only [Q]
      rw [Set.IccExtend_of_mem (show (0 : ℝ) ≤ 1 by norm_num) Θ hkm]
      congr 1
    rw [hQ0, hQ1]
    exact hi
  have hsum : (∑ k ∈ Finset.range (n + 1), (θ k 1 - θ k 0)) = Θ 1 - Θ 0 := by
    calc
      (∑ k ∈ Finset.range (n + 1), (θ k 1 - θ k 0)) =
          ∑ k ∈ Finset.range (n + 1), (Q (((k : ℝ) + 1) / m) - Q ((k : ℝ) / m)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hincrement k (by have h := Finset.mem_range.mp hk; omega)
      _ = Q (((n + 1 : ℕ) : ℝ) / m) - Q (0 / m) := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
          Finset.sum_range_sub (fun k : ℕ => Q ((k : ℝ) / m)) (n + 1)
      _ = Θ 1 - Θ 0 := by
        have hnm : ((n + 1 : ℕ) : ℝ) = m := by simp [m]
        rw [hnm, div_self hm.ne', zero_div]
        simp [Q]
  rw [hsum]
  exact regular_closed_C1_arc_total_turn hΓ hΓclose hΓjet hΓinj hΓreg hΘ hΘlift

end RepulsiveCoulomb
