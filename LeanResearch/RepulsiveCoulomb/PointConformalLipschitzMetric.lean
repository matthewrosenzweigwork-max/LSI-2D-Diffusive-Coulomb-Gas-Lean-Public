module

public import LeanResearch.RepulsiveCoulomb.PointConformalLipschitzLength
public import LeanResearch.RepulsiveCoulomb.PointConformalIntrinsicLength
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-! Equality with the infimum of literal physical lengths over all Lipschitz
curves, and the physical upper bound on their metric variation. The additional
reparametrization step from arbitrary continuous rectifiable curves is kept
separate rather than silently replacing a BV derivative integral by arc length. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointConformalMetricLength_le_lipschitz_physical {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {s t : ℝ}
    {K : NNReal} (hγ : LipschitzOnWith K γ (Icc s t)) :
    pointConformalMetricLength ha y γ s t ≤ pointConformalPathELength a y γ s t := by
  unfold pointConformalMetricLength eVariationOn
  apply iSup_le
  rintro ⟨n, u, hu, hmem⟩
  have hsum : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, pointSmoothConformalEDist a y (γ (u (i + 1))) (γ (u i))) ≤
        pointConformalPathELength a y γ (u 0) (u k) := by
    intro k
    induction k with
    | zero => simp [pointConformalPathELength]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hsub : Icc (u k) (u (k + 1)) ⊆ Icc s t :=
        Icc_subset_Icc (hmem k).1 (hmem (k + 1)).2
      have hd := pointSmoothConformalEDist_le_lipschitz_path ha y
        (hγ.mono hsub) (hu (Nat.le_succ k))
      rw [pointSmoothConformalEDist_comm] at hd
      exact (add_le_add ih hd).trans_eq
        (pointConformalPathELength_add a y γ (hu (Nat.zero_le k)) (hu (Nat.le_succ k)))
  exact (hsum n).trans (pointConformalPathELength_mono a y γ (hmem 0).1 (hmem n).2)

/-- Genuine physical path-metric equality for all Lipschitz competitors, with
constants and punctures unrestricted beyond the manuscript's nonnegative powers. -/
theorem pointSmoothConformalEDist_eq_inf_lipschitz_physical {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    pointSmoothConformalEDist a y x z =
      ⨅ γ : {γ : ℝ → ℂ // γ 0 = x ∧ γ 1 = z ∧
        ∃ K : NNReal, LipschitzOnWith K γ (Icc (0 : ℝ) 1)},
        pointConformalPathELength a y γ.1 0 1 := by
  apply le_antisymm
  · apply le_iInf
    intro γ
    obtain ⟨K, hK⟩ := γ.2.2.2
    simpa only [γ.2.1, γ.2.2.1] using
      pointSmoothConformalEDist_le_lipschitz_path ha y hK (by norm_num : (0 : ℝ) ≤ 1)
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y hr
    obtain ⟨K, hK⟩ := hγ.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_Icc (0 : ℝ) 1) isCompact_Icc
    let γL : {η : ℝ → ℂ // η 0 = x ∧ η 1 = z ∧
        ∃ K : NNReal, LipschitzOnWith K η (Icc (0 : ℝ) 1)} := ⟨γ, h0, h1, K, hK⟩
    have hle : (⨅ η : {η : ℝ → ℂ // η 0 = x ∧ η 1 = z ∧
        ∃ K : NNReal, LipschitzOnWith K η (Icc (0 : ℝ) 1)},
        pointConformalPathELength a y η.1 0 1) ≤
      pointConformalPathELength a y γL.1 0 1 := iInf_le _ γL
    exact hle.trans_lt hlen

end RepulsiveCoulomb
