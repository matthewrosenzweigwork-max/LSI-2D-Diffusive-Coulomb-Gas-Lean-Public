module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCenteredError

@[expose] public section

/-! Actual centered-error row moments for every positive integer order. Jensen
controls the centering potentials and their mean; the four-term inequality
retains a uniform constant independent of beta, N and the fixed particle. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumCenteredErrorMomentConstant (p : ℕ) : ℝ :=
  (4 : ℝ) ^ p * ((2 : ℝ) ^ (p - 1) * 4 * (p.factorial : ℝ))

theorem equilibriumCenteredErrorMomentConstant_pos (p : ℕ) :
    0 < equilibriumCenteredErrorMomentConstant p := by
  unfold equilibriumCenteredErrorMomentConstant
  have hp : (0 : ℝ) < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  positivity

private theorem equilibrium_four_term_pow_bound {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (p : ℕ) :
    |a - b - c + d| ^ p ≤ (4 : ℝ) ^ (p - 1) * (a ^ p + b ^ p + c ^ p + d ^ p) := by
  have habs : |a - b - c + d| ≤ (a + b) + (c + d) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hp := pow_le_pow_left₀ (abs_nonneg _) habs p
  have h1 := add_pow_le (add_nonneg ha hb) (add_nonneg hc hd) p
  have h2 := add_pow_le ha hb p
  have h3 := add_pow_le hc hd p
  have h4 := mul_le_mul_of_nonneg_left (add_le_add h2 h3)
    (by positivity : 0 ≤ (2 : ℝ) ^ (p - 1))
  have hcoef : (2 : ℝ) ^ (p - 1) * (2 : ℝ) ^ (p - 1) = (4 : ℝ) ^ (p - 1) := by
    rw [← mul_pow]
    norm_num
  apply hp.trans (h1.trans (h4.trans_eq ?_))
  rw [← mul_add, ← mul_assoc, hcoef]
  ring

/-- Every pointwise centering potential inherits the genuine p-th error
moment by Jensen under the actual probability reference. -/
theorem equilibriumErrorPotential_power_bound {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) (p : ℕ) (hp : 0 < p) (x : ℂ) :
    equilibriumErrorPotential ε R x ^ p ≤ (2 : ℝ) ^ (p - 1) * 4 * (p.factorial : ℝ) * ε ^ 2 := by
  have hi : Integrable (equilibriumDoubleCircularError ε x) R.measure := by
    simpa only [pow_one] using (equilibriumReference_double_error_power R hε 1 (by norm_num) x).1
  obtain ⟨hip, hpbound⟩ := equilibriumReference_double_error_power R hε p hp x
  have hj := (convexOn_pow p).map_integral_le (continuous_pow p).continuousOn isClosed_Ici
    (Eventually.of_forall (fun y => equilibriumDoubleCircularError_nonneg ε x y)) hi hip
  exact hj.trans hpbound

theorem equilibriumErrorPotential_power_integrable_bound {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) (p : ℕ) (hp : 0 < p) :
    Integrable (fun x : ℂ => equilibriumErrorPotential ε R x ^ p) R.measure ∧
      (∫ x : ℂ, equilibriumErrorPotential ε R x ^ p ∂R.measure) ≤
        (2 : ℝ) ^ (p - 1) * 4 * (p.factorial : ℝ) * ε ^ 2 := by
  have hi : Integrable (fun x : ℂ => equilibriumErrorPotential ε R x ^ p) R.measure := by
    apply (integrable_const ((2 : ℝ) ^ (p - 1) * 4 * (p.factorial : ℝ) * ε ^ 2)).mono'
      ((equilibriumErrorPotential_measurable R hε).pow_const p).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (equilibriumErrorPotential_bounds R hε x).1 p)]
      exact equilibriumErrorPotential_power_bound R hε p hp x)
  refine ⟨hi, ?_⟩
  have h := integral_mono hi (integrable_const _) (equilibriumErrorPotential_power_bound R hε p hp)
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem equilibriumErrorMean_power_bound {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) (p : ℕ) (hp : 0 < p) :
    equilibriumErrorMean ε R ^ p ≤ (2 : ℝ) ^ (p - 1) * 4 * (p.factorial : ℝ) * ε ^ 2 := by
  obtain ⟨hip, hbound⟩ := equilibriumErrorPotential_power_integrable_bound R hε p hp
  have h := (convexOn_pow p).map_integral_le (continuous_pow p).continuousOn isClosed_Ici
    (Eventually.of_forall (fun x => (equilibriumErrorPotential_bounds R hε x).1))
    (equilibriumErrorPotential_integrable R hε) hip
  exact h.trans hbound

/-- The exact analytic input for the generic centered ordered-pair correlation
lemma. All row moments and integrability are derived from the actual reference. -/
theorem equilibriumCenteredError_row_power {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) (p : ℕ) (hp : 0 < p) (x : ℂ) :
    Integrable (fun y : ℂ => |equilibriumCenteredError ε R x y| ^ p) R.measure ∧
      (∫ y : ℂ, |equilibriumCenteredError ε R x y| ^ p ∂R.measure) ≤
        equilibriumCenteredErrorMomentConstant p * ε ^ 2 := by
  obtain ⟨hei, heB⟩ := equilibriumReference_double_error_power R hε p hp x
  obtain ⟨hai, haB⟩ := equilibriumErrorPotential_power_integrable_bound R hε p hp
  have hax := equilibriumErrorPotential_power_bound R hε p hp x
  have hb := equilibriumErrorMean_power_bound R hε p hp
  let K : ℝ := (4 : ℝ) ^ (p - 1)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hmajor := (((hei.add (integrable_const (equilibriumErrorPotential ε R x ^ p))).add hai).add
    (integrable_const (equilibriumErrorMean ε R ^ p))).const_mul K
  simp only [Pi.add_apply] at hmajor
  have hpoint (y : ℂ) : |equilibriumCenteredError ε R x y| ^ p ≤ K *
      (equilibriumDoubleCircularError ε x y ^ p + equilibriumErrorPotential ε R x ^ p +
        equilibriumErrorPotential ε R y ^ p + equilibriumErrorMean ε R ^ p) := by
    have hscalar := equilibrium_four_term_pow_bound (equilibriumDoubleCircularError_nonneg ε x y)
      (equilibriumErrorPotential_bounds R hε x).1 (equilibriumErrorPotential_bounds R hε y).1
      (equilibriumErrorMean_bounds R hε).1 p
    simpa only [equilibriumCenteredError, K] using hscalar
  have hpair : Measurable (fun y : ℂ => (x, y)) := measurable_const.prodMk measurable_id
  have hrowComp := (equilibriumCenteredError_joint_measurable R hε).comp hpair
  have hrow : Measurable (fun y : ℂ => equilibriumCenteredError ε R x y) := by
    simpa only [Function.comp_def] using hrowComp
  have hGm : Measurable (fun y : ℂ => |equilibriumCenteredError ε R x y| ^ p) := by
    simpa only [Real.norm_eq_abs] using hrow.norm.pow_const p
  have hi : Integrable (fun y : ℂ => |equilibriumCenteredError ε R x y| ^ p) R.measure := by
    apply hmajor.mono' hGm.aestronglyMeasurable
    exact Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p)]
      exact hpoint y)
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hmajor hpoint
  have hs1 := integral_add hei (integrable_const (equilibriumErrorPotential ε R x ^ p))
  have hs2 := integral_add
    (f := fun y : ℂ => equilibriumDoubleCircularError ε x y ^ p + equilibriumErrorPotential ε R x ^ p)
    (g := fun y : ℂ => equilibriumErrorPotential ε R y ^ p)
    (hei.add (integrable_const _)) hai
  have hs3 := integral_add
    (f := fun y : ℂ => equilibriumDoubleCircularError ε x y ^ p + equilibriumErrorPotential ε R x ^ p +
      equilibriumErrorPotential ε R y ^ p) (g := fun _ : ℂ => equilibriumErrorMean ε R ^ p)
    ((hei.add (integrable_const _)).add hai) (integrable_const _)
  rw [integral_const_mul, hs3, hs2, hs1] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add heB hax) haB) hb) hK
  have hpow : (4 : ℝ) ^ p = (4 : ℝ) ^ (p - 1) * 4 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne')]
  apply h.trans (hsum.trans_eq ?_)
  unfold equilibriumCenteredErrorMomentConstant
  rw [hpow]
  dsimp only [K]
  ring

end RepulsiveCoulomb
