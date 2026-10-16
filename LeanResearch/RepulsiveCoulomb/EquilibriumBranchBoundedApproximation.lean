module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyMeasureDual
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section

/-! Bound-preserving continuous approximation of measurable entropy tests.
The exponential Lipschitz bound is explicit, so later measure-dual convergence
will not assume uniform convergence of an L1 approximation. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology BoundedContinuousFunction
namespace RepulsiveCoulomb

def equilibriumClip (M t : ℝ) : ℝ := max (-M) (min M t)

theorem equilibriumClip_continuous (M : ℝ) : Continuous (equilibriumClip M) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem equilibriumClip_mem {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    equilibriumClip M t ∈ Icc (-M) M := by
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clipping cannot increase distance to an already bounded target. -/
theorem equilibriumClip_error_le {M h : ℝ} (hh : |h| ≤ M) (t : ℝ) :
    |h - equilibriumClip M t| ≤ |h - t| := by
  have hb := abs_le.mp hh
  have hM : 0 ≤ M := (abs_nonneg h).trans hh
  by_cases hlo : t ≤ -M
  · rw [equilibriumClip, min_eq_right (by linarith), max_eq_left hlo,
      abs_of_nonneg (by linarith : 0 ≤ h - -M),
      abs_of_nonneg (by linarith : 0 ≤ h - t)]
    linarith
  by_cases hhi : M ≤ t
  · rw [equilibriumClip, min_eq_left hhi, max_eq_right (by linarith),
      abs_of_nonpos (by linarith : h - M ≤ 0),
      abs_of_nonpos (by linarith : h - t ≤ 0)]
    linarith
  · rw [equilibriumClip, min_eq_right (le_of_not_ge hhi),
      max_eq_right (le_of_not_ge hlo)]

/-- A scalar bound needed to transfer L1 error to the nonlinear exponential
part of the entropy dual. No derivative or compactness assumption is hidden. -/
theorem equilibrium_abs_exp_sub_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  have htan (u v : ℝ) : Real.exp u + Real.exp u * (v - u) ≤ Real.exp v := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v - u)) (Real.exp_pos u).le
    rw [← Real.exp_add, show u + (v - u) = v by ring] at h
    nlinarith
  have hab : Real.exp a * (a - b) ≤ Real.exp M * |a - b| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos a).le).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (abs_nonneg _))
  have hba : Real.exp b * (b - a) ≤ Real.exp M * |a - b| := by
    have h := (mul_le_mul_of_nonneg_left (le_abs_self (b - a)) (Real.exp_pos b).le).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb) (abs_nonneg _))
    simpa only [abs_sub_comm] using h
  exact abs_le.mpr ⟨by linarith [htan b a], by linarith [htan a b]⟩

/-- Every bounded measurable test admits bounded continuous L1 approximants
with the very same bound. This is applicable on C to the finite measure mu+nu. -/
theorem equilibrium_boundedContinuous_approximation
    {α : Type*} [TopologicalSpace α] [NormalSpace α] [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {h : α → ℝ} (hhm : Measurable h) {M : ℝ} (hM : 0 ≤ M)
    (hhb : ∀ x, |h x| ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α →ᵇ ℝ, (∀ x, |g x| ≤ M) ∧ (∫ x, |h x - g x| ∂μ) ≤ ε := by
  have hh : Integrable h μ := Integrable.of_bound hhm.aestronglyMeasurable M
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hhb x))
  obtain ⟨f, hf, hfi⟩ := hh.exists_boundedContinuous_integral_sub_le hε
  let g : α →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => equilibriumClip M (f x)) ((equilibriumClip_continuous M).comp f.continuous) M
    (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr (equilibriumClip_mem hM (f x)))
  have hgb (x : α) : |g x| ≤ M := abs_le.mpr (equilibriumClip_mem hM (f x))
  have hgi : Integrable (fun x => g x) μ := Integrable.of_bound g.continuous.measurable.aestronglyMeasurable M
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hgb x))
  refine ⟨g, hgb, ?_⟩
  have hle := integral_mono (hh.sub hgi).abs (hh.sub hfi).norm (fun x => by
    change |h x - equilibriumClip M (f x)| ≤ ‖h x - f x‖
    simpa only [Real.norm_eq_abs] using equilibriumClip_error_le (hhb x) (f x))
  exact hle.trans hf

end RepulsiveCoulomb
