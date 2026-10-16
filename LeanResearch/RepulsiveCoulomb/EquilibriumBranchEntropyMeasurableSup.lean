module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyMeasureDual

@[expose] public section

/-! Actual variational formula over bounded measurable tests for KL of finite
measures. Infinite entropy and singular measures are included. Continuous-test
replacement and weak lsc are separate downstream theorems. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

abbrev EquilibriumEntropyTest (α : Type*) [MeasurableSpace α] :=
  {h : α → ℝ // Measurable h ∧ ∃ M : ℝ, ∀ x, |h x| ≤ M}

def equilibriumEntropyMeasurableSup (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ h : EquilibriumEntropyTest α, ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν h.1)

/-- Every actual bounded measurable test is below KL, without assuming that KL
is finite. The scalar Fenchel inequality is integrated only on its finite branch. -/
theorem equilibriumEntropyMeasureDual_le_klDiv {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {h : α → ℝ}
    (hhm : Measurable h) (hhb : ∃ M : ℝ, ∀ x, |h x| ≤ M) :
    ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν h) ≤ InformationTheory.klDiv μ ν := by
  by_cases hac : μ ≪ ν
  swap
  · rw [InformationTheory.klDiv_of_not_ac hac]
    exact le_top
  by_cases htop : InformationTheory.klDiv μ ν = ∞
  · rw [htop]
    exact le_top
  obtain ⟨M, hM⟩ := hhb
  have hh : Integrable h μ := Integrable.of_bound hhm.aestronglyMeasurable M
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hM x))
  have he : Integrable (fun x => Real.exp (h x)) ν :=
    PeriodicAttractiveLogGas.Rothaus.integrable_continuous_comp_bounded hhm hM Real.continuous_exp
  have hm := (integrable_toReal_rnDeriv_mul_iff hac).mpr hh
  have hd : Integrable (fun x => equilibriumEntropyDual (μ.rnDeriv ν x).toReal (h x)) ν :=
    (hm.sub he).add (integrable_const 1)
  have hkm : Measurable (fun x => InformationTheory.klFun (μ.rnDeriv ν x).toReal) := by fun_prop
  have hkn : 0 ≤ᵐ[ν] (fun x => InformationTheory.klFun (μ.rnDeriv ν x).toReal) :=
    Eventually.of_forall (fun _ => InformationTheory.klFun_nonneg ENNReal.toReal_nonneg)
  have hkfin : (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (μ.rnDeriv ν x).toReal) ∂ν) ≠ ∞ := by
    rw [← InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac]
    exact htop
  have hki : Integrable (fun x => InformationTheory.klFun (μ.rnDeriv ν x).toReal) ν :=
    (lintegral_ofReal_ne_top_iff_integrable hkm.aestronglyMeasurable hkn).mp hkfin
  have hle := integral_mono hd hki
    (fun x => equilibriumEntropyDual_le ENNReal.toReal_nonneg (h x))
  rw [integral_equilibriumEntropyDual_rnDeriv hac hh he] at hle
  calc
    ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν h) ≤
        ENNReal.ofReal (∫ x, InformationTheory.klFun (μ.rnDeriv ν x).toReal ∂ν) :=
      ENNReal.ofReal_le_ofReal hle
    _ = InformationTheory.klDiv μ ν := by
      rw [ofReal_integral_eq_lintegral_ofReal hki hkn,
        InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac]

/-- Genuine KL duality for all finite measures. The reverse direction is
proved by clipped RN logarithms in the AC case and reference-null indicators
in the non-AC case; no variational equality is an input. -/
theorem equilibriumEntropyMeasurableSup_eq_klDiv {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    equilibriumEntropyMeasurableSup μ ν = InformationTheory.klDiv μ ν := by
  apply le_antisymm
  · apply iSup_le
    intro h
    exact equilibriumEntropyMeasureDual_le_klDiv h.2.1 h.2.2
  · by_cases hac : μ ≪ ν
    · apply le_of_tendsto (equilibriumEntropyMeasureDual_clipped_tendsto hac)
      exact Eventually.of_forall (fun n => by
        let h : EquilibriumEntropyTest α := ⟨
          (fun x => equilibriumClippedLog n (μ.rnDeriv ν x).toReal),
          (equilibriumClippedLog_measurable n).comp
            (Measure.measurable_rnDeriv μ ν).ennreal_toReal,
          ⟨(n : ℝ), fun x => abs_le.mpr
            (equilibriumClippedLog_mem n (μ.rnDeriv ν x).toReal)⟩⟩
        exact le_iSup (fun g : EquilibriumEntropyTest α =>
          ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν g.1)) h)
    · rw [InformationTheory.klDiv_of_not_ac hac, ← ENNReal.iSup_natCast]
      apply iSup_le
      intro n
      obtain ⟨h, hhm, hhb, hb⟩ := equilibriumEntropyMeasureDual_unbounded_of_not_ac hac (n : ℝ)
      have hle : (n : ℝ≥0∞) ≤ ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν h) := by
        simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hb.le
      exact hle.trans (le_iSup (fun g : EquilibriumEntropyTest α =>
        ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν g.1)) ⟨h, hhm, hhb⟩)

end RepulsiveCoulomb
