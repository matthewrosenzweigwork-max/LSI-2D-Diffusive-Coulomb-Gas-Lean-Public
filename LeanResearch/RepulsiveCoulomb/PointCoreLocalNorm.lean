module

public import LeanResearch.RepulsiveCoulomb.PointWeightUniformTails
public import LeanResearch.RepulsiveCoulomb.PointCoreExterior
public import LeanResearch.RepulsiveCoulomb.LocalSobolevUncentering

@[expose] public section

/-! Uncentered local Gaussian Sobolev control for the actual original core,
with a radius chosen uniformly before every weighted point configuration. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem pointCore_local_uncentered_norm {γ Q : ℝ} (hγ : 0 < γ) (hQ0 : 0 ≤ Q) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ (R : ℝ), R₀ ≤ R →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      tsupport (φ : ℂ → ℝ) ⊆ ball (0 : ℂ) R →
      (∫ x, ‖φ x‖ ^ (2 * pointSobolevKappa Q) ∂pointMeasure γ a y) ^
        (1 / (2 * pointSobolevKappa Q)) ≤
      2 * (∫ x, |φ x| ∂pointMeasure γ a y) +
        2 * (pointGaussianLocalConstant γ Q (pointUniformMeanTransferConstant Q) *
          Real.exp (pointGaussianLocalConstant γ Q (pointUniformMeanTransferConstant Q) * R ^ 2) * R) *
          Real.sqrt (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) := by
  obtain ⟨R₀, hR₀, hm⟩ := pointMeasure_half_mass_ball hγ hQ0
  refine ⟨R₀, hR₀, ?_⟩
  intro m a ha y hQ R hR φ hs
  let _ := pointMeasure_isProbability hγ ha y
  have hR1 : 1 ≤ R := hR₀.trans hR
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hhalf : 1 / 2 ≤ (pointMeasure γ a y).real (ball (0 : ℂ) R₀) := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (hm m a y ha hQ)
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
    exact h
  have hhalfR : 1 / 2 ≤ (pointMeasure γ a y).real (ball (0 : ℂ) R) :=
    hhalf.trans (measureReal_mono (ball_subset_ball hR))
  have hhalfT : 1 / 2 ≤ (pointMeasure γ a y).real (ball (0 : ℂ) (11 * R)) :=
    hhalfR.trans (measureReal_mono (ball_subset_ball (by linarith)))
  have hκ := pointSobolevKappa_gt_one hQ0
  have hq : 1 ≤ 2 * pointSobolevKappa Q := by linarith
  have hφ : Integrable (φ : ℂ → ℝ) (pointMeasure γ a y) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have he := testFunction_physical_energy_integrable (pointDomain a y) φ (pointMeasure γ a y)
  have hloc := (pointGaussian_uniform_local_geometry hγ ha hQ y (φ : ℂ → ℝ)
    (φ.contDiff.of_le (by simp)) hR1).1
  have hH : 0 ≤ pointGaussianLocalConstant γ Q (pointUniformMeanTransferConstant Q) *
      Real.exp (pointGaussianLocalConstant γ Q (pointUniformMeanTransferConstant Q) * R ^ 2) * R :=
    mul_nonneg (mul_nonneg (pointGaussianLocalConstant_pos hγ Q _).le (Real.exp_pos _).le) hRp.le
  have h := local_sobolev_uncentered_norm (pointMeasure γ a y) measurableSet_ball
    hhalfR hhalfT hφ he (fun _ => sq_nonneg _) hq hH hloc
  have hid : (∫ x in ball (0 : ℂ) R, ‖φ x‖ ^ (2 * pointSobolevKappa Q) ∂pointMeasure γ a y) =
      ∫ x, ‖φ x‖ ^ (2 * pointSobolevKappa Q) ∂pointMeasure γ a y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
    simp [hz, Real.zero_rpow (show 2 * pointSobolevKappa Q ≠ 0 by linarith)]
  rwa [hid] at h

end RepulsiveCoulomb
