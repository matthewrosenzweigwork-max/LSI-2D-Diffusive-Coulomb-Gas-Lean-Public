module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyDualIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Actual measure-level bounded dual tests for relative entropy. The AC case
uses clipped log RN derivatives and permits infinite entropy. The non-AC case
has explicit null-set tests with arbitrarily large dual value. Approximation
by bounded continuous tests and weak lower semicontinuity remain separate. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology Classical
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

def equilibriumEntropyMeasureDual (μ ν : Measure α) (h : α → ℝ) : ℝ :=
  (∫ x, h x ∂μ) - (∫ x, Real.exp (h x) ∂ν) + ν.real univ

/-- The RN conversion uses actual integrability, rather than formal signed
subtraction of undefined Bochner integrals. -/
theorem integral_equilibriumEntropyDual_rnDeriv {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) {h : α → ℝ}
    (hh : Integrable h μ) (he : Integrable (fun x => Real.exp (h x)) ν) :
    (∫ x, equilibriumEntropyDual (μ.rnDeriv ν x).toReal (h x) ∂ν) =
      equilibriumEntropyMeasureDual μ ν h := by
  have hm := (integrable_toReal_rnDeriv_mul_iff hμν).mpr hh
  change (∫ x, ((μ.rnDeriv ν x).toReal * h x - Real.exp (h x)) + 1 ∂ν) = _
  have hadd := integral_add (hm.sub he) (integrable_const (μ := ν) (1 : ℝ))
  dsimp only [Pi.sub_apply] at hadd
  rw [hadd, integral_sub hm he, integral_toReal_rnDeriv_mul hμν]
  simp only [integral_const, smul_eq_mul, mul_one, equilibriumEntropyMeasureDual]

/-- The scalar monotone approximation is exactly a sequence of genuine bounded
measurable measure-dual tests, including when KL is infinite. -/
theorem equilibriumEntropyMeasureDual_clipped_tendsto {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν
      (fun x => equilibriumClippedLog n (μ.rnDeriv ν x).toReal))) atTop
      (𝓝 (InformationTheory.klDiv μ ν)) := by
  have heq (n : ℕ) : ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν
      (fun x => equilibriumClippedLog n (μ.rnDeriv ν x).toReal)) =
      ∫⁻ x, ENNReal.ofReal (equilibriumEntropyDual (μ.rnDeriv ν x).toReal
        (equilibriumClippedLog n (μ.rnDeriv ν x).toReal)) ∂ν := by
    let h : α → ℝ := fun x => equilibriumClippedLog n (μ.rnDeriv ν x).toReal
    have hhm : Measurable h := (equilibriumClippedLog_measurable n).comp
      (Measure.measurable_rnDeriv μ ν).ennreal_toReal
    have hhb : ∀ x, |h x| ≤ (n : ℝ) := fun x =>
      abs_le.mpr (equilibriumClippedLog_mem n (μ.rnDeriv ν x).toReal)
    have hh : Integrable h μ := Integrable.of_bound hhm.aestronglyMeasurable (n : ℝ)
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hhb x))
    have hexp : Integrable (fun x => Real.exp (h x)) ν :=
      PeriodicAttractiveLogGas.Rothaus.integrable_continuous_comp_bounded hhm hhb Real.continuous_exp
    have hmul := (integrable_toReal_rnDeriv_mul_iff hμν).mpr hh
    have hd : Integrable (fun x => equilibriumEntropyDual (μ.rnDeriv ν x).toReal (h x)) ν :=
      (hmul.sub hexp).add (integrable_const 1)
    have hn : 0 ≤ᵐ[ν] (fun x => equilibriumEntropyDual (μ.rnDeriv ν x).toReal (h x)) :=
      Eventually.of_forall (fun x => equilibriumEntropyDual_clipped_nonneg ENNReal.toReal_nonneg n)
    rw [← integral_equilibriumEntropyDual_rnDeriv hμν hh hexp,
      ofReal_integral_eq_lintegral_ofReal hd hn]
  simp_rw [heq]
  exact equilibrium_klDiv_clipped_dual_tendsto hμν

/-- A reference-null measurable set gives an explicit linear dual value. -/
theorem equilibriumEntropyMeasureDual_null_indicator {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set α} (hA : MeasurableSet A)
    (hνA : ν A = 0) (a : ℝ) :
    equilibriumEntropyMeasureDual μ ν (A.indicator (fun _ => a)) = μ.real A * a := by
  have ha : ∀ᵐ x ∂ν, x ∉ A := compl_mem_ae_iff.mpr hνA
  have he : (fun x => Real.exp (A.indicator (fun _ => a) x)) =ᵐ[ν] (fun _ => (1 : ℝ)) := by
    filter_upwards [ha] with x hx
    simp only [Set.indicator_of_notMem hx, Real.exp_zero]
  unfold equilibriumEntropyMeasureDual
  rw [integral_indicator_const a hA, integral_congr_ae he]
  simp only [integral_const, smul_eq_mul, mul_one]
  ring

/-- Non-AC measures have arbitrarily large values on genuine bounded measurable
dual tests. No singular-case duality theorem is assumed. -/
theorem equilibriumEntropyMeasureDual_unbounded_of_not_ac {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : ¬ μ ≪ ν) (B : ℝ) :
    ∃ h : α → ℝ, Measurable h ∧ (∃ M : ℝ, ∀ x, |h x| ≤ M) ∧
      B < equilibriumEntropyMeasureDual μ ν h := by
  have hex : ∃ A : Set α, MeasurableSet A ∧ ν A = 0 ∧ μ A ≠ 0 := by
    by_contra h
    push_neg at h
    exact hμν (Measure.AbsolutelyContinuous.mk (fun A hA hνA => h A hA hνA))
  obtain ⟨A, hA, hνA, hμA⟩ := hex
  have hmass : 0 < μ.real A := ENNReal.toReal_pos hμA (measure_ne_top μ A)
  let a : ℝ := (|B| + 1) / μ.real A
  refine ⟨A.indicator (fun _ => a), measurable_const.indicator hA, ⟨|a|, ?_⟩, ?_⟩
  · intro x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, le_refl]
    · simp only [Set.indicator_of_notMem hx, abs_zero, abs_nonneg]
  · rw [equilibriumEntropyMeasureDual_null_indicator hA hνA]
    have he : μ.real A * a = |B| + 1 := by
      dsimp only [a]
      field_simp [hmass.ne']
    rw [he]
    linarith [le_abs_self B]

end RepulsiveCoulomb
