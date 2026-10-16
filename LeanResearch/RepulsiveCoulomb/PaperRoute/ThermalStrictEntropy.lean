import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalDensityMixture
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyNegative
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Genuine mixed entropy integrability and
integrated strict entropy for the actual P² finite-entropy density domain. -/

noncomputable section
open MeasureTheory Real Filter
namespace RepulsiveCoulomb.PaperRoute

theorem thermalDensityMixture_entropy_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {ρ σ : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x) (x : ℂ) :
    thermalDensityMixture t ρ σ x * Real.log (thermalDensityMixture t ρ σ x) ≤
      t * (ρ x * Real.log (ρ x)) + (1-t) * (σ x * Real.log (σ x)) := by
  have h := Real.convexOn_mul_log.2 (hρ0 x) (hσ0 x)
    ht0 (show 0 ≤ 1-t by linarith) (show t+(1-t)=1 by ring)
  simpa only [smul_eq_mul, thermalDensityMixture] using h

/-- The mixed entropy is genuinely integrable on the P2 density domain.
The negative part comes from the generic Gaussian comparison; the positive
part is controlled by convexity and the two supplied finite entropies. -/
theorem thermalDensityMixture_entropy_integrable {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {ρ σ : ℂ → ℝ} (hρm : Measurable ρ) (hσm : Measurable σ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x)
    (hρi : Integrable ρ) (hσi : Integrable σ)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖^2 * ρ x))
    (hσ2 : Integrable (fun x : ℂ => ‖x‖^2 * σ x))
    (hρH : Integrable (fun x => ρ x * Real.log (ρ x)))
    (hσH : Integrable (fun x => σ x * Real.log (σ x))) :
    Integrable (fun x => thermalDensityMixture t ρ σ x * 
      Real.log (thermalDensityMixture t ρ σ x)) := by
  let m := thermalDensityMixture t ρ σ
  have ht' : 0 ≤ 1-t := by linarith
  have hmm : Measurable m := (hρm.const_mul t).add (hσm.const_mul (1-t))
  have hm0 (x : ℂ) : 0 ≤ m x :=
    add_nonneg (mul_nonneg ht0 (hρ0 x)) (mul_nonneg ht' (hσ0 x))
  have hmi : Integrable m := (hρi.const_mul t).add (hσi.const_mul (1-t))
  have hm2 : Integrable (fun x : ℂ => ‖x‖^2 * m x) :=
    thermalDensityMixture_secondMoment_integrable hρ2 hσ2 t
  have hneg := equilibriumEntropyNegative_integrable (by norm_num : (0 : ℝ) < 1)
    hmm hm0 hmi hm2
  have hmajor := ((hρH.abs.const_mul t).add (hσH.abs.const_mul (1-t))).add hneg
  apply hmajor.mono' (hmm.mul (Real.measurable_log.comp hmm)).aestronglyMeasurable
  filter_upwards with x
  change ‖m x * Real.log (m x)‖ ≤ _
  rw [Real.norm_eq_abs]
  change |m x * Real.log (m x)| ≤
    (t * |ρ x * Real.log (ρ x)| + (1-t) * |σ x * Real.log (σ x)|) +
      equilibriumEntropyNegative m x
  have hc := thermalDensityMixture_entropy_le ht0 ht1 hρ0 hσ0 x
  have hp := add_le_add
    (mul_le_mul_of_nonneg_left (le_abs_self (ρ x * Real.log (ρ x))) ht0)
    (mul_le_mul_of_nonneg_left (le_abs_self (σ x * Real.log (σ x))) ht')
  have hp0 : 0 ≤ t * |ρ x * Real.log (ρ x)| + (1-t) * |σ x * Real.log (σ x)| :=
    add_nonneg (mul_nonneg ht0 (abs_nonneg _)) (mul_nonneg ht' (abs_nonneg _))
  have hn : -(m x * Real.log (m x)) ≤ equilibriumEntropyNegative m x := le_max_left _ _
  have hn0 := equilibriumEntropyNegative_nonneg m x
  change m x * Real.log (m x) ≤ _ at hc
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Genuine integrated strictness; no strict integral theorem is assumed.
If equality held in the integral comparison, nonnegative-integrand uniqueness
would force equality in pointwise strict convexity almost everywhere. -/
theorem thermalDensityMixture_entropy_strict {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {ρ σ : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x)
    (hρH : Integrable (fun x => ρ x * Real.log (ρ x)))
    (hσH : Integrable (fun x => σ x * Real.log (σ x)))
    (hmH : Integrable (fun x => thermalDensityMixture t ρ σ x * 
      Real.log (thermalDensityMixture t ρ σ x)))
    (hne : ¬ ρ =ᵐ[volume] σ) :
    (∫ x : ℂ, thermalDensityMixture t ρ σ x * Real.log (thermalDensityMixture t ρ σ x)) <
      t * (∫ x : ℂ, ρ x * Real.log (ρ x)) + (1-t) * (∫ x : ℂ, σ x * Real.log (σ x)) := by
  let F : ℂ → ℝ := fun x => thermalDensityMixture t ρ σ x * Real.log (thermalDensityMixture t ρ σ x)
  let G : ℂ → ℝ := fun x => t * (ρ x * Real.log (ρ x)) + (1-t) * (σ x * Real.log (σ x))
  have hG : Integrable G := (hρH.const_mul t).add (hσH.const_mul (1-t))
  have hFG : ∀ x, F x ≤ G x := thermalDensityMixture_entropy_le ht0.le ht1.le hρ0 hσ0
  have hle : (∫ x, F x) ≤ ∫ x, G x := integral_mono hmH hG hFG
  have hs : (∫ x, F x) < ∫ x, G x := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso
      apply hne
      have hae := (integral_eq_iff_of_ae_le hmH hG (Eventually.of_forall hFG)).mp heq
      filter_upwards [hae] with x hx
      by_contra hxy
      have hstrict := Real.strictConvexOn_mul_log.2 (hρ0 x) (hσ0 x) hxy
        ht0 (show 0 < 1-t by linarith) (show t+(1-t)=1 by ring)
      have hstrict' : F x < G x := by
        simpa only [F, G, thermalDensityMixture, smul_eq_mul] using hstrict
      exact (ne_of_lt hstrict') hx
    · exact hlt
  calc
    (∫ x : ℂ, thermalDensityMixture t ρ σ x * Real.log (thermalDensityMixture t ρ σ x)) <
        ∫ x : ℂ, G x := hs
    _ = _ := by
      change (∫ x, t * (ρ x * Real.log (ρ x)) + (1-t) * (σ x * Real.log (σ x))) = _
      rw [integral_add (hρH.const_mul t) (hσH.const_mul (1-t)),
        integral_const_mul, integral_const_mul]

end RepulsiveCoulomb.PaperRoute
