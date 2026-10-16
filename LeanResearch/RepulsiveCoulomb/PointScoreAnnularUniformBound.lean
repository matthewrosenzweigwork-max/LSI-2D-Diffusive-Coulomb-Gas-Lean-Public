module

public import LeanResearch.RepulsiveCoulomb.PointScoreAnnularDecomposition

@[expose] public section

/-! Fixed absorption parameter and radius-uniform lower-order coefficients. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointScore_annular_uniform_bound {m : ℕ} {γ Q R C : ℝ}
    (hγ : 0 < γ) (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖gradient (annularCutoff R) z‖ ≤ C / R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hscore : Integrable (fun x => ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2)) :
    R ^ 2 * (∫ x in scoreRadialAnnulus R, ψ x ^ 2) ≤
      (4 / γ ^ 2) * (∫ x in enlargedScoreAnnulus R, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2) +
      (1 / 96 : ℝ) * R ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2) +
      48 * pointScoreAnnularMassConstant γ Q ^ 2 * (∫ x in enlargedScoreAnnulus R, ‖gradient ψ x‖ ^ 2) +
      48 * pointScoreAnnularMassConstant γ Q ^ 2 * C ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2) := by
  have hRp : 0 < R := by linarith
  have hb := pointScore_bad_annulus_localized hRp hC hbound hγ
    (by norm_num : (0 : ℝ) < 1 / 96) ha y hQ ψ hψ
  have hg := pointScore_annular_mass_decomposition hγ hRp a y ψ hψ.continuous hscore
  have hratio : 0 ≤ C / R := div_nonneg hC hRp.le
  have hratioupper : C / R ≤ C := (div_le_iff₀ hRp).mpr (by nlinarith)
  have hsq : (C / R) ^ 2 ≤ C ^ 2 := by nlinarith
  have hmass : 0 ≤ ∫ x in enlargedScoreAnnulus R, ψ x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_right hsq hmass
  have hk := mul_le_mul_of_nonneg_left hscaled (sq_nonneg (pointScoreAnnularMassConstant γ Q))
  norm_num at hb
  nlinarith [hg, hb, hk]

end RepulsiveCoulomb
