import LeanResearch.RepulsiveCoulomb.CoulombGaussianIntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Bounded C¹ regularity of the actual Mehler integral, including the log
composition needed in the entropy derivative. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace RepulsiveCoulomb

theorem coulombGaussianAverage_contDiff_one {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D) (a b : ℝ) :
    ContDiff ℝ 1 (coulombGaussianAverage β a b f) := by
  letI := coulombCenterGaussian_isProbability hβ
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => ∫ y, a • fderiv ℝ f (a • x + b • y) ∂coulombCenterGaussian β, ?_,
    coulombGaussianAverage_hasFDerivAt hβ hf hM hD a b⟩
  have hc := hf.continuous_fderiv (by norm_num)
  apply continuous_of_dominated (bound := fun _ : ℂ => |a| * D)
    (fun x => by fun_prop)
    (fun x => Eventually.of_forall (fun y => ?_))
    (integrable_const _) (Eventually.of_forall (fun y => by fun_prop))
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg a)

theorem coulombGaussianAverage_fderiv_norm_le {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D) (a b : ℝ) (x : ℂ) :
    ‖fderiv ℝ (coulombGaussianAverage β a b f) x‖ ≤ |a| * D := by
  letI := coulombCenterGaussian_isProbability hβ
  rw [(coulombGaussianAverage_hasFDerivAt hβ hf hM hD a b x).fderiv]
  have hb : ∀ᵐ y ∂coulombCenterGaussian β,
      ‖a • fderiv ℝ f (a • x + b • y)‖ ≤ |a| * D := by
    filter_upwards [] with y
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg a)
  simpa using norm_integral_le_of_norm_le_const hb

/-- The gradient, in the physical real metric, commutes with affine Gaussian
averaging with precisely the drift coefficient. -/
theorem coulombGaussianAverage_gradient {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D) (a b : ℝ) (x : ℂ) :
    gradient (coulombGaussianAverage β a b f) x =
      a • ∫ y, gradient f (a • x + b • y) ∂coulombCenterGaussian β := by
  unfold gradient
  rw [(coulombGaussianAverage_hasFDerivAt hβ hf hM hD a b x).fderiv, integral_smul]
  rw [map_smul]
  congr 1
  exact ((InnerProductSpace.toDual ℝ ℂ).symm.toLinearIsometry.integral_comp_comm _).symm

/-- A uniform elementary log bound on a positive bounded interval. -/
theorem coulombGaussian_log_bound {u m M : ℝ} (hm : 0 < m)
    (hmu : m ≤ u) (huM : u ≤ M) : |Real.log u| ≤ |Real.log m| + |Real.log M| := by
  have hu : 0 < u := hm.trans_le hmu
  have hlo := Real.log_le_log hm hmu
  have hhi := Real.log_le_log hu huM
  apply abs_le.mpr
  constructor
  · have := neg_abs_le (Real.log m)
    have := abs_nonneg (Real.log M)
    linarith
  · have := le_abs_self (Real.log M)
    have := abs_nonneg (Real.log m)
    linarith

/-- The entropy multiplier 1+log(Pg), with a proved finite uniform bound. -/
theorem coulombGaussianAverage_log_multiplier_bound {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {m M : ℝ} (hm : 0 < m)
    (hlo : ∀ z, m ≤ f z) (hM : ∀ z, ‖f z‖ ≤ M) (a b : ℝ) (x : ℂ) :
    ‖1 + Real.log (coulombGaussianAverage β a b f x)‖ ≤
      1 + |Real.log m| + |Real.log M| := by
  have hl := coulombGaussianAverage_lower hβ hf hM hlo a b x
  have hu := coulombGaussianAverage_norm_le hβ hM a b x
  have hu' : coulombGaussianAverage β a b f x ≤ M := (le_abs_self _).trans hu
  have hb := coulombGaussian_log_bound hm hl hu'
  calc
    ‖1 + Real.log (coulombGaussianAverage β a b f x)‖ ≤
        ‖(1 : ℝ)‖ + ‖Real.log (coulombGaussianAverage β a b f x)‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_one, Real.norm_eq_abs]
      linarith [hb]

theorem coulombGaussianAverage_log_multiplier_contDiff {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {m M D : ℝ} (hm : 0 < m)
    (hlo : ∀ z, m ≤ f z) (hM : ∀ z, ‖f z‖ ≤ M)
    (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D) (a b : ℝ) :
    ContDiff ℝ 1 (fun x => 1 + Real.log (coulombGaussianAverage β a b f x)) := by
  apply contDiff_const.add
  apply (coulombGaussianAverage_contDiff_one hβ hf hM hD a b).log
  intro x
  exact (hm.trans_le (coulombGaussianAverage_lower hβ hf.continuous hM hlo a b x)).ne'

theorem coulombGaussianAverage_log_multiplier_fderiv {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {m M D : ℝ} (hm : 0 < m)
    (hlo : ∀ z, m ≤ f z) (hM : ∀ z, ‖f z‖ ≤ M)
    (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D) (a b : ℝ) (x : ℂ) :
    fderiv ℝ (fun x => 1 + Real.log (coulombGaussianAverage β a b f x)) x =
      (coulombGaussianAverage β a b f x)⁻¹ •
        fderiv ℝ (coulombGaussianAverage β a b f) x := by
  have hp : 0 < coulombGaussianAverage β a b f x :=
    hm.trans_le (coulombGaussianAverage_lower hβ hf.continuous hM hlo a b x)
  have hd := (coulombGaussianAverage_contDiff_one hβ hf hM hD a b).differentiable (by norm_num) x
  exact ((hd.hasFDerivAt.log hp.ne').const_add 1).fderiv

theorem coulombGaussianAverage_log_multiplier_fderiv_bound {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {m M D : ℝ} (hm : 0 < m)
    (hlo : ∀ z, m ≤ f z) (hM : ∀ z, ‖f z‖ ≤ M)
    (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D) (a b : ℝ) (x : ℂ) :
    ‖fderiv ℝ (fun x => 1 + Real.log (coulombGaussianAverage β a b f x)) x‖ ≤
      (|a| * D) / m := by
  have hl := coulombGaussianAverage_lower hβ hf.continuous hM hlo a b x
  have hp := hm.trans_le hl
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ f 0)).trans (hD 0)
  rw [coulombGaussianAverage_log_multiplier_fderiv hβ hf hm hlo hM hD,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (coulombGaussianAverage β a b f x)⁻¹ * (|a| * D) :=
      mul_le_mul_of_nonneg_left
        (coulombGaussianAverage_fderiv_norm_le hβ hf hM hD a b x) (inv_nonneg.mpr hp.le)
    _ = (|a| * D) / coulombGaussianAverage β a b f x := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hm hl

end RepulsiveCoulomb
