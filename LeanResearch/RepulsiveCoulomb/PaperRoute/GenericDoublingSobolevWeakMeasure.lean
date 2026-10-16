module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolevWeak
public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Calculus.Gradient

@[expose] public section

/-! All-C1 physical weak Sobolev in the two-measure form for genuine smooth truncation. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

def doublingWeakSobolevBallFactor (D P : ℝ) (μ : Measure ℂ)
    (c : ℂ) (R : ℝ) : ℝ :=
  doublingWeakSobolevConstant D P * R ^ (2 * doublingSobolevKappa D) *
    (μ).real (ball c R) / ((μ).real (ball c R)) ^ doublingSobolevKappa D

theorem doublingWeakSobolevBallFactor_nonneg {D : ℝ} (hD : 1 ≤ D) {P : ℝ} (hP : 0 < P)
    (μ : Measure ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ doublingWeakSobolevBallFactor D P μ c R := by
  unfold doublingWeakSobolevBallFactor
  exact div_nonneg (mul_nonneg (mul_nonneg (doublingWeakSobolevConstant_pos hD hP).le
    (Real.rpow_nonneg hR _)) ENNReal.toReal_nonneg) (Real.rpow_nonneg ENNReal.toReal_nonneg _)

theorem doublingWeakSobolevBallFactor_mul_energy (D P : ℝ)
    (μ : Measure ℂ) (c : ℂ) (R : ℝ) {I : ℝ} (hI : 0 ≤ I) :
    doublingWeakSobolevBallFactor D P μ c R * I ^ doublingSobolevKappa D =
      doublingWeakSobolevConstant D P * R ^ (2 * doublingSobolevKappa D) *
        (μ).real (ball c R) *
        (I / (μ).real (ball c R)) ^ doublingSobolevKappa D := by
  unfold doublingWeakSobolevBallFactor
  rw [Real.div_rpow hI (show 0 ≤ (μ).real (ball c R) from ENNReal.toReal_nonneg)]
  ring

theorem weak_sobolev_measure_form {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (v : ℂ → ℝ) (hv : ContDiff ℝ 1 v)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂μ))
    (c : ℂ) {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    ENNReal.ofReal (t ^ (2 * doublingSobolevKappa D)) *
      ((μ).restrict (ball c R))
        {x | t < ‖v x - (⨍ z in ball c R, v z ∂μ)‖} ≤
      ENNReal.ofReal (doublingWeakSobolevBallFactor D P μ c R) *
        (∫⁻ x in ball c (11 * R), ENNReal.ofReal (‖gradient v x‖ ^ 2) ∂μ) ^ doublingSobolevKappa D := by
  have hκ : 0 ≤ doublingSobolevKappa D := (lt_trans zero_lt_one (doublingSobolevKappa_gt_one D)).le
  have hg : Continuous (fun z => ‖gradient v z‖ ^ 2) := by
    simp_rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact (hv.continuous_fderiv one_ne_zero).norm.pow 2
  have hi := ofReal_integral_eq_lintegral_ofReal
    (hμ.continuous_ball_integrable hg c (11 * R))
    (Eventually.of_forall (fun z => sq_nonneg ‖gradient v z‖))
  rw [← hi, ENNReal.ofReal_rpow_of_nonneg (show 0 ≤ ∫ x in ball c (11 * R), ‖gradient v x‖ ^ 2 ∂μ from integral_nonneg (fun z => sq_nonneg _)) hκ,
    ← ENNReal.ofReal_mul (doublingWeakSobolevBallFactor_nonneg hD.1 hP μ c hR.le),
    doublingWeakSobolevBallFactor_mul_energy D P μ c R (integral_nonneg (fun z => sq_nonneg _))]
  have hs : MeasurableSet {x | t < ‖v x - (⨍ z in ball c R, v z ∂μ)‖} :=
    measurableSet_lt measurable_const (hv.continuous.sub continuous_const).norm.measurable
  rw [Measure.restrict_apply hs]
  have he : {x | t < ‖v x - (⨍ z in ball c R, v z ∂μ)‖} ∩ ball c R =
      {x | x ∈ ball c R ∧ t < ‖v x - (⨍ z in ball c R, v z ∂μ)‖} := by ext x; simp [and_comm]
  rw [he]
  exact weak_sobolev_normalized hD hμ hP v _ hv.continuous hg (fun z => sq_nonneg _) hPI c hR ht

end RepulsiveCoulomb.PaperRoute
