module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCanonicalWeakLSC

@[expose] public section

/-! Liminf control of the full logarithmic
interaction, with the negative part proved finite through genuine P² control.
Finite upper bounds subsequently imply full real interaction integrability. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

def thermalExtendedLogInteraction (μ : ProbabilityMeasure ℂ) : EReal :=
  (thermalPositiveLogInteraction μ : EReal) +
    ((-(∫ p, thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ)) : ℝ) : EReal)

theorem thermalExtendedLogInteraction_eq_extendedIntegral (μ : ProbabilityMeasure ℂ)
    (hAC : (μ : Measure ℂ) ≪ volume)
    (hP2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    thermalExtendedLogInteraction μ = equilibriumExtendedIntegral ((μ : Measure ℂ).prod μ)
      (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) := by
  rw [thermalExtendedInteraction_eq_positive_sub_negative μ hAC hP2]
  simp only [thermalExtendedLogInteraction, sub_eq_add_neg, EReal.coe_neg]

theorem thermalInteraction_le_liminf_of_uniform_secondMoment
    {μs : ℕ → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ} {M : ℝ}
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hP2 : ∀ n, Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs n))
    (hM : ∀ n, (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs n)) ≤ M) :
    thermalExtendedLogInteraction μ ≤
      liminf (fun n => thermalExtendedLogInteraction (μs n)) atTop := by
  obtain ⟨_, _, _, hneg⟩ :=
    thermal_negative_log_integral_tendsto_of_uniform_secondMoment hweak hP2 hM
  have hl : LowerSemicontinuous (fun ν : ProbabilityMeasure ℂ =>
      (thermalPositiveLogInteraction ν : EReal)) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      thermalPositiveLogInteraction_lowerSemicontinuous
      (fun x y hxy => EReal.coe_ennreal_le_coe_ennreal_iff.mpr hxy)
  have hbl : (thermalPositiveLogInteraction μ : EReal) ≤
      liminf (fun n => (thermalPositiveLogInteraction (μs n) : EReal)) atTop := by
    apply (le_liminf_iff).2
    intro b hb
    exact hweak.eventually ((lowerSemicontinuousAt_iff.mp (hl μ)) b hb)
  let C : ProbabilityMeasure ℂ → ℝ := fun ν =>
    -(∫ p, thermalNegativeLogKernel p ∂((ν : Measure ℂ).prod ν))
  have hC : Tendsto (fun n => C (μs n)) atTop (𝓝 (C μ)) := hneg.neg
  have hCE : Tendsto (fun n => (C (μs n) : EReal)) atTop (𝓝 (C μ : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hC
  have hadd := EReal.le_liminf_add
    (u := fun n => (thermalPositiveLogInteraction (μs n) : EReal))
    (v := fun n => (C (μs n) : EReal)) (f := atTop)
  rw [hCE.liminf_eq] at hadd
  exact (by simpa only [Pi.add_def, C, thermalExtendedLogInteraction] using
    (add_le_add hbl (le_refl (C μ : EReal))).trans hadd)

/-- A finite upper bound on the extended interaction forces true absolute
integrability after AC and P² have been proved. -/
theorem thermalInteraction_logKernel_integrable_of_le_real
    (μ : ProbabilityMeasure ℂ) (hAC : (μ : Measure ℂ) ≪ volume)
    (hP2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) {c : ℝ}
    (hc : thermalExtendedLogInteraction μ ≤ (c : EReal)) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((μ : Measure ℂ).prod μ) := by
  have hn : Integrable (fun p : ℂ × ℂ => max (-equilibriumLogKernel (p.1 - p.2)) 0)
      ((μ : Measure ℂ).prod μ) := by
    exact (thermalNegativeLogKernel_integrable μ hP2).congr
      (Eventually.of_forall thermalNegativeLogKernel_eq_negativePart)
  by_contra hG
  have hm : Measurable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) :=
    equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)
  have ht : equilibriumExtendedIntegral ((μ : Measure ℂ).prod μ)
      (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) = ⊤ :=
    equilibriumExtendedIntegral_eq_top_of_not_integrable hm hn hG
  rw [thermalExtendedLogInteraction_eq_extendedIntegral μ hAC hP2, ht] at hc
  exact (EReal.coe_ne_top c) (top_le_iff.mp hc)

/-- Generic finite-stage passage. Only stage energies are expanded; full
interaction integrability at the weak limit is derived from the finite upper
bound, not assumed. -/
theorem thermalInteraction_real_limit_bound
    {μs : ℕ → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ} {M c : ℝ}
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hAC : (μ : Measure ℂ) ≪ volume)
    (hACs : ∀ n, (μs n : Measure ℂ) ≪ volume)
    (hP2 : ∀ n, Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs n))
    (hM : ∀ n, (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs n)) ≤ M)
    (hGs : ∀ n, Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((μs n : Measure ℂ).prod (μs n)))
    {cs : ℕ → ℝ} (hcs : Tendsto cs atTop (𝓝 c))
    (hbound : ∀ n, (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂((μs n : Measure ℂ).prod (μs n))) ≤ cs n) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) ((μ : Measure ℂ).prod μ) ∧
    (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((μ : Measure ℂ).prod μ)) ≤ c := by
  have hμP2 := (thermal_secondMoment_of_weak_convergence hweak hP2 hM).1
  have hle := thermalInteraction_le_liminf_of_uniform_secondMoment hweak hP2 hM
  have hstage (n : ℕ) : thermalExtendedLogInteraction (μs n) ≤ (cs n : EReal) := by
    rw [thermalExtendedLogInteraction_eq_extendedIntegral (μs n) (hACs n) (hP2 n),
      equilibriumExtendedIntegral_eq_integral (hGs n)]
    exact EReal.coe_le_coe (hbound n)
  have hlim := liminf_le_liminf (f := atTop) (Eventually.of_forall hstage)
  have hcsE : Tendsto (fun n => (cs n : EReal)) atTop (𝓝 (c : EReal)) := by
    simpa only [Function.comp_def] using continuous_coe_real_ereal.continuousAt.tendsto.comp hcs
  rw [hcsE.liminf_eq] at hlim
  have hcap := hle.trans hlim
  have hμG := thermalInteraction_logKernel_integrable_of_le_real μ hAC hμP2 hcap
  refine ⟨hμP2, hμG, ?_⟩
  rw [thermalExtendedLogInteraction_eq_extendedIntegral μ hAC hμP2,
    equilibriumExtendedIntegral_eq_integral hμG, EReal.coe_le_coe_iff] at hcap
  exact hcap

end RepulsiveCoulomb.PaperRoute
