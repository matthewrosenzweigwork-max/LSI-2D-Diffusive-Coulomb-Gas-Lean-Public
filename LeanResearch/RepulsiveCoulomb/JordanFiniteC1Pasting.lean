import LeanResearch.RepulsiveCoulomb.JordanC1GlueGeometry
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Actual finite equal-slot C¹ pasting. Starting with the first curve, each
successor is glued at the next integer parameter. Literal endpoint values and
velocities imply global C¹ regularity of the construction at every seam.
The theorem proves the exact function and derivative on every closed slot.
Records-only candidate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Paste curves numbered0 through n on consecutive unit parameter slots. -/
def euclideanFiniteC1Paste (f : ℕ → ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => f 0
  | n + 1 => euclideanC1Glue (n + 1 : ℕ)
      (euclideanFiniteC1Paste f n) (fun t => f (n + 1) (t - (n + 1 : ℕ)))

/-- Exact finite construction: all original closed slots, including their
actual seam derivatives, agree with the pasted curve. -/
theorem euclideanFiniteC1Paste_properties (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0)
    (hd : ∀ k < n, deriv (f k) 1 = deriv (f (k + 1)) 0) :
    ContDiff ℝ 1 (euclideanFiniteC1Paste f n) ∧
      (∀ t : ℝ, (n : ℝ) ≤ t → euclideanFiniteC1Paste f n t = f n (t - n)) ∧
      (∀ t : ℝ, (n : ℝ) ≤ t → deriv (euclideanFiniteC1Paste f n) t = deriv (f n) (t - n)) ∧
      (∀ k ≤ n, ∀ t ∈ Icc (k : ℝ) (k + 1 : ℝ), euclideanFiniteC1Paste f n t = f k (t - k)) ∧
      (∀ k ≤ n, ∀ t ∈ Icc (k : ℝ) (k + 1 : ℝ), deriv (euclideanFiniteC1Paste f n) t =
        deriv (f k) (t - k)) := by
  induction n with
  | zero =>
    refine ⟨hf 0 le_rfl, ?_, ?_, ?_, ?_⟩
    · intro t _; simp [euclideanFiniteC1Paste]
    · intro t _; simp [euclideanFiniteC1Paste]
    · intro k hk t _
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [euclideanFiniteC1Paste]
    · intro k hk t _
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [euclideanFiniteC1Paste]
  | succ n ih =>
    have hfprev : ∀ k ≤ n, ContDiff ℝ 1 (f k) := fun k hk => hf k (by omega)
    have hvprev : ∀ k < n, f k 1 = f (k + 1) 0 := fun k hk => hv k (by omega)
    have hdprev : ∀ k < n, deriv (f k) 1 = deriv (f (k + 1)) 0 := fun k hk => hd k (by omega)
    obtain ⟨hP, hPtail, hDPtail, hPslots, hDPslots⟩ := ih hfprev hvprev hdprev
    let g : ℝ → ℂ := fun t => f (n + 1) (t - (n + 1 : ℕ))
    have hg : ContDiff ℝ 1 g := by
      have hfn := hf (n + 1) le_rfl
      dsimp [g]
      fun_prop
    have hgD (t : ℝ) : deriv g t = deriv (f (n + 1)) (t - (n + 1 : ℕ)) :=
      deriv_comp_sub_const _ _ _
    have hvglue : euclideanFiniteC1Paste f n (n + 1 : ℕ) = g (n + 1 : ℕ) := by
      rw [hPtail _ (by exact_mod_cast Nat.le_succ n)]
      have hc : ((n + 1 : ℕ) : ℝ) - n = 1 := by push_cast; ring
      simpa only [hc, g, sub_self] using hv n (Nat.lt_succ_self n)
    have hdglue : deriv (euclideanFiniteC1Paste f n) (n + 1 : ℕ) = deriv g (n + 1 : ℕ) := by
      rw [hDPtail _ (by exact_mod_cast Nat.le_succ n), hgD]
      have hc : ((n + 1 : ℕ) : ℝ) - n = 1 := by push_cast; ring
      simpa only [hc, sub_self] using hd n (Nat.lt_succ_self n)
    have hQ : ContDiff ℝ 1 (euclideanFiniteC1Paste f (n + 1)) :=
      euclideanC1Glue_contDiff hP hg hvglue hdglue
    have htail (t : ℝ) (ht : ((n + 1 : ℕ) : ℝ) ≤ t) :
        euclideanFiniteC1Paste f (n + 1) t = f (n + 1) (t - (n + 1 : ℕ)) :=
      euclideanC1Glue_eq_right hvglue ht
    have hDtail (t : ℝ) (ht : ((n + 1 : ℕ) : ℝ) ≤ t) :
        deriv (euclideanFiniteC1Paste f (n + 1)) t = deriv (f (n + 1)) (t - (n + 1 : ℕ)) := by
      change deriv (euclideanC1Glue ((n + 1 : ℕ) : ℝ) (euclideanFiniteC1Paste f n) g) t = _
      rw [euclideanC1Glue_deriv_right (hP.differentiable (by norm_num))
        (hg.differentiable (by norm_num)) hvglue hdglue ht, hgD]
    refine ⟨hQ, htail, hDtail, ?_, ?_⟩
    · intro k hk t ht
      by_cases hkn : k = n + 1
      · subst k
        exact htail t (by exact_mod_cast ht.1)
      · have hkle : k ≤ n := by omega
        have htc : t ≤ ((n + 1 : ℕ) : ℝ) := by
          have hkcast : (k : ℝ) ≤ n := by exact_mod_cast hkle
          push_cast
          linarith [ht.2]
        change euclideanC1Glue ((n + 1 : ℕ) : ℝ) (euclideanFiniteC1Paste f n) g t = _
        rw [euclideanC1Glue_eq_left _ _ _ htc]
        exact hPslots k hkle t ht
    · intro k hk t ht
      by_cases hkn : k = n + 1
      · subst k
        exact hDtail t (by exact_mod_cast ht.1)
      · have hkle : k ≤ n := by omega
        have htc : t ≤ ((n + 1 : ℕ) : ℝ) := by
          have hkcast : (k : ℝ) ≤ n := by exact_mod_cast hkle
          push_cast
          linarith [ht.2]
        change deriv (euclideanC1Glue ((n + 1 : ℕ) : ℝ) (euclideanFiniteC1Paste f n) g) t = _
        rw [euclideanC1Glue_deriv (hP.differentiable (by norm_num))
          (hg.differentiable (by norm_num)) hvglue hdglue, if_pos htc]
        exact hDPslots k hkle t ht

end RepulsiveCoulomb
