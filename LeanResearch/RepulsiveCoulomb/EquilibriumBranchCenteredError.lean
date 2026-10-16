module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchRegularizedEnergy

@[expose] public section

/-! Genuine centering of the finite double-error kernel under the actual
reference. Joint measurability, row integrability, zero mean, symmetry, and
the canonical one-body correction bound are proved with actual integrals. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

def equilibriumErrorPotential {β : ℝ} (ε : ℝ) (R : EquilibriumConstructedReference β) (x : ℂ) : ℝ :=
  ∫ y : ℂ, equilibriumDoubleCircularError ε x y ∂R.measure

def equilibriumErrorMean {β : ℝ} (ε : ℝ) (R : EquilibriumConstructedReference β) : ℝ :=
  ∫ x : ℂ, equilibriumErrorPotential ε R x ∂R.measure

def equilibriumCenteredError {β : ℝ} (ε : ℝ) (R : EquilibriumConstructedReference β) (x y : ℂ) : ℝ :=
  equilibriumDoubleCircularError ε x y - equilibriumErrorPotential ε R x -
    equilibriumErrorPotential ε R y + equilibriumErrorMean ε R

theorem equilibriumErrorPotential_measurable {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) : Measurable (equilibriumErrorPotential ε R) :=
  ((equilibriumDoubleCircularError_joint_measurable hε).stronglyMeasurable.integral_prod_right' (ν := (R.measure : Measure ℂ))).measurable

theorem equilibriumErrorPotential_integrable {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) : Integrable (equilibriumErrorPotential ε R) R.measure :=
  (equilibriumReference_double_error_product_integrable R hε).integral_prod_left

theorem equilibriumErrorPotential_bounds {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    0 ≤ equilibriumErrorPotential ε R x ∧ equilibriumErrorPotential ε R x ≤ 4 * ε ^ 2 := by
  refine ⟨integral_nonneg (fun y => equilibriumDoubleCircularError_nonneg ε x y), ?_⟩
  simpa only [equilibriumErrorPotential, pow_one, Nat.sub_self, pow_zero, one_mul, Nat.factorial_one, Nat.cast_one, mul_one]
    using (equilibriumReference_double_error_power R hε 1 (by norm_num) x).2

theorem equilibriumErrorMean_bounds {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) : 0 ≤ equilibriumErrorMean ε R ∧ equilibriumErrorMean ε R ≤ 4 * ε ^ 2 := by
  refine ⟨integral_nonneg (fun x => (equilibriumErrorPotential_bounds R hε x).1), ?_⟩
  have h := integral_mono (equilibriumErrorPotential_integrable R hε) (integrable_const (4 * ε ^ 2))
    (fun x => (equilibriumErrorPotential_bounds R hε x).2)
  simpa only [equilibriumErrorMean, integral_const, probReal_univ, one_smul] using h

theorem equilibriumCenteredError_joint_measurable {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) : Measurable (fun p : ℂ × ℂ => equilibriumCenteredError ε R p.1 p.2) :=
  (((equilibriumDoubleCircularError_joint_measurable hε).sub
    ((equilibriumErrorPotential_measurable R hε).comp measurable_fst)).sub
      ((equilibriumErrorPotential_measurable R hε).comp measurable_snd)).add measurable_const

theorem equilibriumCenteredError_symm {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    equilibriumCenteredError ε R x y = equilibriumCenteredError ε R y x := by
  unfold equilibriumCenteredError
  rw [equilibriumDoubleCircularError_symm hε x y]
  ring

theorem equilibriumCenteredError_row_integrable {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) : Integrable (equilibriumCenteredError ε R x) R.measure := by
  have he : Integrable (equilibriumDoubleCircularError ε x) R.measure := by
    simpa only [pow_one] using (equilibriumReference_double_error_power R hε 1 (by norm_num) x).1
  exact ((he.sub (integrable_const _)).sub (equilibriumErrorPotential_integrable R hε)).add (integrable_const _)

/-- Actual row centering at every fixed x, after every integral is justified. -/
theorem integral_equilibriumCenteredError_zero {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) : (∫ y : ℂ, equilibriumCenteredError ε R x y ∂R.measure) = 0 := by
  have he : Integrable (equilibriumDoubleCircularError ε x) R.measure := by
    simpa only [pow_one] using (equilibriumReference_double_error_power R hε 1 (by norm_num) x).1
  have ha := equilibriumErrorPotential_integrable R hε
  unfold equilibriumCenteredError
  have hs1 := integral_sub (f := equilibriumDoubleCircularError ε x)
    (g := fun _ : ℂ => equilibriumErrorPotential ε R x) he (integrable_const _)
  have hs2 := integral_sub (f := fun y : ℂ => equilibriumDoubleCircularError ε x y - equilibriumErrorPotential ε R x)
    (g := equilibriumErrorPotential ε R) (he.sub (integrable_const _)) ha
  have hs3 := integral_add (f := fun y : ℂ => equilibriumDoubleCircularError ε x y - equilibriumErrorPotential ε R x -
      equilibriumErrorPotential ε R y) (g := fun _ : ℂ => equilibriumErrorMean ε R)
    ((he.sub (integrable_const _)).sub ha) (integrable_const _)
  rw [hs3, hs2, hs1]
  simp only [integral_const, probReal_univ, one_smul]
  change equilibriumErrorPotential ε R x - equilibriumErrorPotential ε R x -
    equilibriumErrorMean ε R + equilibriumErrorMean ε R = 0
  ring

/-- The canonical correction is uniformly O(epsilon^2), independently of N.
It is retained explicitly rather than absorbed into the centered U-statistic. -/
theorem equilibriumError_oneBody_correction_bound {β : ℝ} (R : EquilibriumConstructedReference β)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 0 < N) (z : Fin N → ℂ) :
    |-(∑ i : Fin N, equilibriumErrorPotential ε R (z i)) / (N : ℝ) + equilibriumErrorMean ε R / 2| ≤
      6 * ε ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 ≤ ∑ i : Fin N, equilibriumErrorPotential ε R (z i) :=
    Finset.sum_nonneg (fun i _ => (equilibriumErrorPotential_bounds R hε (z i)).1)
  have ha1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (equilibriumErrorPotential_bounds R hε (z i)).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ha1
  have hdiv0 : 0 ≤ (∑ i : Fin N, equilibriumErrorPotential ε R (z i)) / (N : ℝ) := div_nonneg ha0 hn.le
  have hdiv1 : (∑ i : Fin N, equilibriumErrorPotential ε R (z i)) / (N : ℝ) ≤ 4 * ε ^ 2 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  obtain ⟨hb0, hb1⟩ := equilibriumErrorMean_bounds R hε
  apply abs_le.mpr
  constructor <;> rw [neg_div] <;> nlinarith [sq_nonneg ε]

end RepulsiveCoulomb
