import LeanResearch.RepulsiveCoulomb.PointWeightFormApproximation
import LeanResearch.RepulsiveCoulomb.PointWeightCircularLower
import LeanResearch.RepulsiveCoulomb.PointLogForceWeakL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Identification of the physical score of the normalized point density.
Zero-exponent locations are not punctures. Derivatives are over the real
Euclidean complex plane. This connects the literal weak-field estimate to
the score used in manuscript Proposition 3.6 (prop:uncertainty).
-/
noncomputable section
open MeasureTheory Set Metric Real Filter InnerProductSpace
open scoped ENNReal BigOperators Topology
namespace RepulsiveCoulomb

/-- The gradient of the negative logarithm of the normalized density; the
identification with that actual logarithm is proved below. -/
def pointScore {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℂ :=
  γ • z - pointLogForce a y z

theorem hasFDerivAt_log_norm_sub {y z : ℂ} (hz : z ≠ y) :
    HasFDerivAt (fun x : ℂ ↦ Real.log ‖x - y‖)
      ((‖z - y‖ ^ 2)⁻¹ • innerSL ℝ (z - y)) z := by
  have hnorm : ‖z - y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz))
  have h := ((((hasFDerivAt_id z).sub_const y).norm_sq).log hnorm).const_mul (1 / 2 : ℝ)
  have heq : (fun x : ℂ ↦ (1 / 2 : ℝ) * Real.log (‖x - y‖ ^ 2)) =
      (fun x : ℂ ↦ Real.log ‖x - y‖) := by
    funext x
    rw [Real.log_pow]
    norm_num
    ring
  simp only [id_eq] at h
  rw [heq] at h
  apply h.congr_fderiv
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

theorem exp_pointLogWeight_off_punctures {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    Real.exp (pointLogWeight γ a y z) = pointWeight γ a y z := by
  unfold pointLogWeight pointWeight
  rw [Real.exp_add, Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : a j = 0
  · simp [hj]
  · have hzy : z ≠ y j := fun heq ↦ hz ⟨j, lt_of_le_of_ne (ha j) (Ne.symm hj), heq⟩
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzy))]
    congr 1
    ring

theorem hasFDerivAt_pointLogWeight {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    HasFDerivAt (pointLogWeight γ a y) (innerSL ℝ (-pointScore γ a y z)) z := by
  have hfactor (j : Fin m) : HasFDerivAt (fun x : ℂ ↦ a j * Real.log ‖x - y j‖)
      (a j • ((‖z - y j‖ ^ 2)⁻¹ • innerSL ℝ (z - y j))) z := by
    by_cases hj : a j = 0
    · simp only [hj, zero_mul, zero_smul]
      exact hasFDerivAt_const 0 z
    · have hzy : z ≠ y j := fun heq ↦ hz ⟨j, lt_of_le_of_ne (ha j) (Ne.symm hj), heq⟩
      exact (hasFDerivAt_log_norm_sub hzy).const_mul (a j)
  have hsum : HasFDerivAt (fun x : ℂ ↦ ∑ j, a j * Real.log ‖x - y j‖)
      (∑ j, a j • ((‖z - y j‖ ^ 2)⁻¹ • innerSL ℝ (z - y j))) z := by
    convert HasFDerivAt.sum (u := Finset.univ) (fun j _ ↦ hfactor j) using 1
    ext x
    simp
  have hgauss : HasFDerivAt (fun x : ℂ ↦ -γ * ‖x‖ ^ 2 / 2)
      ((-γ / 2) • (2 • innerSL ℝ z)) z := by
    convert ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (-γ / 2)) using 1
    funext x
    ring
  have h := hgauss.add hsum
  apply h.congr_fderiv
  ext v
  simp only [pointScore, pointLogForce, neg_sub, map_sub, map_smul, map_sum,
    add_apply, sub_apply, smul_apply,
    sum_apply, smul_eq_mul]
  ring

theorem log_pointDensity_off_punctures {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {z : ℂ} (hz : z ∉ pointPunctures a y) :
    Real.log (pointDensity γ a y z) =
      Real.log ((∫ x : ℂ, pointWeight γ a y x)⁻¹) + pointLogWeight γ a y z := by
  rw [pointDensity, ← exp_pointLogWeight_off_punctures γ ha y hz,
    Real.log_mul (inv_ne_zero (pointWeight_integral_pos hγ ha y).ne') (Real.exp_pos _).ne',
    Real.log_exp]

/-- Actual score identity on exactly the prescribed punctured domain. -/
theorem pointScore_eq_gradient_neg_log_density {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {z : ℂ} (hz : z ∉ pointPunctures a y) :
    gradient (fun x : ℂ ↦ -Real.log (pointDensity γ a y x)) z = pointScore γ a y z := by
  have heq : (fun x : ℂ ↦ Real.log (pointDensity γ a y x)) =ᶠ[𝓝 z]
      (fun x : ℂ ↦ Real.log ((∫ w : ℂ, pointWeight γ a y w)⁻¹) + pointLogWeight γ a y x) := by
    filter_upwards [(pointDomain a y).isOpen.mem_nhds hz] with x hx
    exact log_pointDensity_off_punctures hγ ha y hx
  have h := ((hasFDerivAt_pointLogWeight γ ha y hz).const_add
    (Real.log ((∫ w : ℂ, pointWeight γ a y w)⁻¹))).congr_of_eventuallyEq heq
  have hn := h.neg
  have hg : HasGradientAt (fun x : ℂ ↦ -Real.log (pointDensity γ a y x)) (pointScore γ a y z) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hn using 1
    ext v
    simp
  exact hg.gradient

/-- A quantitative bad-score region estimate used by the annular uncertainty
argument. It is valid for arbitrary configurations, without separation. -/
theorem pointScore_small_region_measure {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q) :
    volume {z : ℂ | R ≤ ‖z‖ ∧ ‖pointScore γ a y z‖ < γ * R / 2} ≤
      ENNReal.ofReal (32 * Real.pi * Q ^ 2 / (γ ^ 2 * R ^ 2)) := by
  have ht : 0 < γ * R / 2 := by positivity
  have hsubset : {z : ℂ | R ≤ ‖z‖ ∧ ‖pointScore γ a y z‖ < γ * R / 2} ⊆
      {z : ℂ | γ * R / 2 < ‖pointLogForce a y z‖} := by
    intro z hz
    have h := norm_add_le (pointScore γ a y z) (pointLogForce a y z)
    have hid : pointScore γ a y z + pointLogForce a y z = γ • z := sub_add_cancel _ _
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hγ] at h
    have hr := mul_le_mul_of_nonneg_left hz.1 hγ.le
    change γ * R / 2 < ‖pointLogForce a y z‖
    linarith [hz.2]
  apply (measure_mono hsubset).trans
  convert pointLogForce_weak_l2_of_total_le ha y hQ ht using 1
  congr 1
  field_simp
  ring

end RepulsiveCoulomb
