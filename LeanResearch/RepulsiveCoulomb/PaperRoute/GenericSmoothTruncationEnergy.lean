module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericSmoothTruncationGradient
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

@[expose] public section

/-
Additive paper-route copy of the generic argument in DyadicTruncationEnergy.lean.
Only the imports and namespace are rerouted; the physical-gradient statement
and the mathematical hypotheses are unchanged. The original file is untouched.
-/

/-! Disjoint dyadic value bands and the actual sum of truncated physical
energies. Endpoints have zero truncation derivative, so no level-set nullness
is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem dyadic_value_bands_disjoint {X : Type*} (f : X → ℝ) :
    Pairwise (Function.onFun Disjoint (fun j : ℤ => {x | (2 : ℝ) ^ j < f x ∧ f x < 2 * (2 : ℝ) ^ j})) := by
  have hordered (i j : ℤ) (hij : i < j) :
      Disjoint {x | (2 : ℝ) ^ i < f x ∧ f x < 2 * (2 : ℝ) ^ i}
        {x | (2 : ℝ) ^ j < f x ∧ f x < 2 * (2 : ℝ) ^ j} := by
    have hp : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_add₀ (by norm_num), zpow_one, mul_comm] at hp
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge (hx.2.le.trans hp)) hy.1
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hordered i j h
  · exact (hordered j i h).symm

theorem smoothTruncation_energy_lintegral {a K : ℝ} (ha : 0 < a) (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (μ : Measure ℂ) :
    (∫⁻ x, ENNReal.ofReal (‖gradient (fun z => smoothDyadicTruncation a (f z)) x‖ ^ 2) ∂μ) ≤
      ENNReal.ofReal (K ^ 2) *
        ∫⁻ x in {z | a < f z ∧ f z < 2 * a}, ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂μ := by
  have hs : MeasurableSet {z | a < f z ∧ f z < 2 * a} :=
    (measurableSet_lt measurable_const hf.continuous.measurable).inter
      (measurableSet_lt hf.continuous.measurable measurable_const)
  have h := lintegral_mono (μ := μ) (fun x => ENNReal.ofReal_le_ofReal
    (smoothTruncation_gradient_energy_indicator ha hK0 hK hf x))
  have he : (fun x => ENNReal.ofReal
      ({z | a < f z ∧ f z < 2 * a}.indicator (fun z => K ^ 2 * ‖gradient f z‖ ^ 2) x)) =
      {z | a < f z ∧ f z < 2 * a}.indicator
        (fun x => ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (‖gradient f x‖ ^ 2)) := by
    ext x
    by_cases hx : x ∈ {z | a < f z ∧ f z < 2 * a}
    · simp only [Set.indicator_of_mem hx, ENNReal.ofReal_mul (sq_nonneg K)]
    · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [he, lintegral_indicator hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  exact h

theorem dyadic_truncation_energy_sum {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (μ : Measure ℂ) :
    (∑' j : ℤ, ∫⁻ x, ENNReal.ofReal
      (‖gradient (fun z => smoothDyadicTruncation ((2 : ℝ) ^ j) (f z)) x‖ ^ 2) ∂μ) ≤
      ENNReal.ofReal (K ^ 2) * ∫⁻ x, ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂μ := by
  have hs (j : ℤ) : MeasurableSet {z | (2 : ℝ) ^ j < f z ∧ f z < 2 * (2 : ℝ) ^ j} :=
    (measurableSet_lt measurable_const hf.continuous.measurable).inter
      (measurableSet_lt hf.continuous.measurable measurable_const)
  calc
    _ ≤ ∑' j : ℤ, ENNReal.ofReal (K ^ 2) *
        ∫⁻ x in {z | (2 : ℝ) ^ j < f z ∧ f z < 2 * (2 : ℝ) ^ j}, ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂μ :=
      ENNReal.tsum_le_tsum (fun j => smoothTruncation_energy_lintegral (zpow_pos (by norm_num) _) hK0 hK hf μ)
    _ = ENNReal.ofReal (K ^ 2) * ∫⁻ x in ⋃ j : ℤ,
        {z | (2 : ℝ) ^ j < f z ∧ f z < 2 * (2 : ℝ) ^ j}, ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂μ := by
      rw [ENNReal.tsum_mul_left, lintegral_iUnion hs (dyadic_value_bands_disjoint f)]
    _ ≤ _ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

end RepulsiveCoulomb.PaperRoute
