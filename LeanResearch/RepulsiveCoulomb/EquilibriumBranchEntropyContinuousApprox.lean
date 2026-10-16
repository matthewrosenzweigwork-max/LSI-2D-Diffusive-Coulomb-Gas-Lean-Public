import LeanResearch.RepulsiveCoulomb.EquilibriumBranchBoundedApproximation
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyMeasurableSup

/-! Actual approximation of bounded measurable entropy-dual values by bounded
continuous tests. The simultaneous L1 approximation uses mu+nu, with an
explicit exponential error bound. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology BoundedContinuousFunction
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

private theorem equilibrium_bounded_integrable {μ : Measure α} [IsFiniteMeasure μ]
    {h : α → ℝ} (hm : Measurable h) {M : ℝ} (hb : ∀ x, |h x| ≤ M) : Integrable h μ :=
  Integrable.of_bound hm.aestronglyMeasurable M
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

theorem equilibriumEntropyMeasureDual_difference_bound {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {h g : α → ℝ}
    (hhm : Measurable h) (hgm : Measurable g) {M : ℝ}
    (hhb : ∀ x, |h x| ≤ M) (hgb : ∀ x, |g x| ≤ M) :
    |equilibriumEntropyMeasureDual μ ν h - equilibriumEntropyMeasureDual μ ν g| ≤
      (1 + Real.exp M) * (∫ x, |h x - g x| ∂(μ + ν)) := by
  have hh (ξ : Measure α) [IsFiniteMeasure ξ] : Integrable h ξ :=
    equilibrium_bounded_integrable hhm hhb
  have hg (ξ : Measure α) [IsFiniteMeasure ξ] : Integrable g ξ :=
    equilibrium_bounded_integrable hgm hgb
  have heh : Integrable (fun x => Real.exp (h x)) ν :=
    PeriodicAttractiveLogGas.Rothaus.integrable_continuous_comp_bounded hhm hhb Real.continuous_exp
  have heg : Integrable (fun x => Real.exp (g x)) ν :=
    PeriodicAttractiveLogGas.Rothaus.integrable_continuous_comp_bounded hgm hgb Real.continuous_exp
  have hμerr : |(∫ x, h x ∂μ) - (∫ x, g x ∂μ)| ≤ ∫ x, |h x - g x| ∂μ := by
    rw [← integral_sub (hh μ) (hg μ)]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (fun x => h x - g x) (μ := μ))
  have hνerr : |(∫ x, Real.exp (h x) ∂ν) - (∫ x, Real.exp (g x) ∂ν)| ≤
      Real.exp M * (∫ x, |h x - g x| ∂ν) := by
    rw [← integral_sub heh heg]
    calc
      |∫ x, Real.exp (h x) - Real.exp (g x) ∂ν| ≤
          ∫ x, |Real.exp (h x) - Real.exp (g x)| ∂ν := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun x => Real.exp (h x) - Real.exp (g x)) (μ := ν))
      _ ≤ ∫ x, Real.exp M * |h x - g x| ∂ν :=
        integral_mono (heh.sub heg).abs (((hh ν).sub (hg ν)).abs.const_mul _)
          (fun x => equilibrium_abs_exp_sub_le ((le_abs_self (h x)).trans (hhb x))
            ((le_abs_self (g x)).trans (hgb x)))
      _ = _ := integral_const_mul _ _
  have hsum : (∫ x, |h x - g x| ∂(μ + ν)) =
      (∫ x, |h x - g x| ∂μ) + (∫ x, |h x - g x| ∂ν) :=
    integral_add_measure ((hh μ).sub (hg μ)).abs ((hh ν).sub (hg ν)).abs
  have hid : equilibriumEntropyMeasureDual μ ν h - equilibriumEntropyMeasureDual μ ν g =
      ((∫ x, h x ∂μ) - (∫ x, g x ∂μ)) -
        ((∫ x, Real.exp (h x) ∂ν) - (∫ x, Real.exp (g x) ∂ν)) := by
    unfold equilibriumEntropyMeasureDual
    ring
  rw [hid, hsum]
  have htri := abs_sub ((∫ x, h x ∂μ) - (∫ x, g x ∂μ))
    ((∫ x, Real.exp (h x) ∂ν) - (∫ x, Real.exp (g x) ∂ν))
  have hμ0 : (0 : ℝ) ≤ ∫ x, |h x - g x| ∂μ :=
    integral_nonneg (fun x => abs_nonneg (h x - g x))
  have hν0 : (0 : ℝ) ≤ ∫ x, |h x - g x| ∂ν :=
    integral_nonneg (fun x => abs_nonneg (h x - g x))
  have hexp := Real.exp_pos M
  have hcross := mul_nonneg hexp.le hμ0
  nlinarith

/-- The actual dual value can be approximated with arbitrary real error by a
bounded continuous test. There is no finite-entropy assumption. -/
theorem equilibriumEntropyMeasureDual_continuous_approximation
    {α : Type*} [TopologicalSpace α] [NormalSpace α] [MeasurableSpace α] [BorelSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [(μ + ν).WeaklyRegular]
    {h : α → ℝ} (hhm : Measurable h) (hhb : ∃ M : ℝ, ∀ x, |h x| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α →ᵇ ℝ,
      |equilibriumEntropyMeasureDual μ ν h - equilibriumEntropyMeasureDual μ ν g| ≤ ε := by
  obtain ⟨M₀, hM₀⟩ := hhb
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hb : ∀ x, |h x| ≤ M := fun x => (hM₀ x).trans (le_max_left _ _)
  have hc : 0 < 1 + Real.exp M := by positivity
  obtain ⟨g, hgb, hg⟩ := equilibrium_boundedContinuous_approximation
    (μ := μ + ν) hhm hM hb (div_pos hε hc)
  refine ⟨g, (equilibriumEntropyMeasureDual_difference_bound hhm g.continuous.measurable hb hgb).trans ?_⟩
  have he := mul_le_mul_of_nonneg_left hg hc.le
  have hid : (1 + Real.exp M) * (ε / (1 + Real.exp M)) = ε := by field_simp [hc.ne']
  exact hid ▸ he

end RepulsiveCoulomb
