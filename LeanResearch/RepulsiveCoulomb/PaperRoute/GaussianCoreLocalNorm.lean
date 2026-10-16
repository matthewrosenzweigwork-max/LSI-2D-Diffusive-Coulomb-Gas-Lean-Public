import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianGlobalPoincare
import LeanResearch.RepulsiveCoulomb.PointCoreExterior
import LeanResearch.RepulsiveCoulomb.LocalSobolevUncentering

/-! Additive experimental source. Verification status is recorded separately in evidence. The explicitly supplied half-mass disk and the new Gaussian Sobolev theorem give uncentered norms. No older normalization producer is selected. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb.PaperRoute

theorem core_local_uncentered_norm {γ Q κ S Rbase : ℝ} (hγ : 0 < γ)
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall γ Q Rbase) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (_ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ (R : ℝ), R₀ ≤ R →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      tsupport (φ : ℂ → ℝ) ⊆ ball (0 : ℂ) R →
      (∫ x, ‖φ x‖ ^ (2 * κ) ∂pointMeasure γ a y) ^
        (1 / (2 * κ)) ≤
      2 * (∫ x, |φ x| ∂pointMeasure γ a y) +
        2 * (gaussianLocalConstant γ κ S *
          Real.exp (gaussianLocalConstant γ κ S * R ^ 2) * R) *
          Real.sqrt (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) := by
  refine ⟨Rbase, hRbase, ?_⟩
  intro m a ha y hQ R hR φ hs
  let _ := pointMeasure_isProbability hγ ha y
  have hR1 : 1 ≤ R := hRbase.trans hR
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hhalf : 1 / 2 ≤ (pointMeasure γ a y).real (ball (0 : ℂ) Rbase) := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (hHalf m a y ha hQ)
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
    exact h
  have hhalfR : 1 / 2 ≤ (pointMeasure γ a y).real (ball (0 : ℂ) R) :=
    hhalf.trans (measureReal_mono (ball_subset_ball hR))
  have hhalfT : 1 / 2 ≤ (pointMeasure γ a y).real (ball (0 : ℂ) (11 * R)) :=
    hhalfR.trans (measureReal_mono (ball_subset_ball (by linarith)))
  have hq : 1 ≤ 2 * κ := by linarith
  have hφ : Integrable (φ : ℂ → ℝ) (pointMeasure γ a y) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have he := testFunction_physical_energy_integrable (pointDomain a y) φ (pointMeasure γ a y)
  have hloc := gaussian_local_sobolev hγ ha hκ hS y (hraw m a ha y hQ) (φ : ℂ → ℝ)
    (φ.contDiff.of_le (by simp)) hR1
  have hH : 0 ≤ gaussianLocalConstant γ κ S *
      Real.exp (gaussianLocalConstant γ κ S * R ^ 2) * R :=
    mul_nonneg (mul_nonneg (gaussianLocalConstant_pos hγ κ S).le (Real.exp_pos _).le) hRp.le
  have h := local_sobolev_uncentered_norm (pointMeasure γ a y) measurableSet_ball
    hhalfR hhalfT hφ he (fun _ => sq_nonneg _) hq hH hloc
  have hid : (∫ x in ball (0 : ℂ) R, ‖φ x‖ ^ (2 * κ) ∂pointMeasure γ a y) =
      ∫ x, ‖φ x‖ ^ (2 * κ) ∂pointMeasure γ a y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
    simp [hz, Real.zero_rpow (show 2 * κ ≠ 0 by linarith)]
  rwa [hid] at h

end RepulsiveCoulomb.PaperRoute
