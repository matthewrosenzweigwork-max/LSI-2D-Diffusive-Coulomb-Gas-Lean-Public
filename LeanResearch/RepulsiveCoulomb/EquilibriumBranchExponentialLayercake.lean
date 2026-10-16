import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPartitionBasic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A genuine exponential layer-cake upper bound for an arbitrary real random
variable. The contribution below threshold one is bounded by e, rather than
silently replaced by an equality. Nonnegative extended integrals retain all
infinite cases until the later tail estimate proves finiteness. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibrium_exponential_layercake_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {X : α → ℝ} (hX : Measurable X) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (X x)) ∂μ) ≤ ENNReal.ofReal (Real.exp 1) *
      (1 + ∫⁻ s : ℝ in Ioi 0, μ {x : α | s + 1 < X x} * ENNReal.ofReal (Real.exp s)) := by
  let f : α → ℝ := fun x => max (X x - 1) 0
  have hfm : Measurable f := (hX.sub measurable_const).max measurable_const
  have hf0 (x : α) : 0 ≤ f x := le_max_right _ _
  have he0 (x : α) : 0 ≤ Real.exp (f x) - 1 := by
    have h := Real.exp_le_exp.mpr (hf0 x)
    rw [Real.exp_zero] at h
    linarith
  have he (x : α) : ENNReal.ofReal (Real.exp (f x)) =
      1 + ENNReal.ofReal (Real.exp (f x) - 1) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (he0 x)]
    congr 1
    ring
  have hp (x : α) : ENNReal.ofReal (Real.exp (X x)) ≤
      ENNReal.ofReal (Real.exp 1) * (1 + ENNReal.ofReal (Real.exp (f x) - 1)) := by
    have hx : X x ≤ 1 + f x := by
      have h := le_max_left (X x - 1) 0
      dsimp only [f]
      linarith
    have h := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hx)
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos 1).le, he x] at h
    exact h
  have hl := lintegral_comp_eq_lintegral_meas_lt_mul μ (Eventually.of_forall hf0) hfm.aemeasurable
    (g := Real.exp) (fun t _ => Real.continuous_exp.intervalIntegrable _ _)
    (Eventually.of_forall (fun t => (Real.exp_pos t).le))
  simp only [integral_exp, Real.exp_zero] at hl
  have ht : (∫⁻ s : ℝ in Ioi 0, μ {x : α | s < f x} * ENNReal.ofReal (Real.exp s)) =
      ∫⁻ s : ℝ in Ioi 0, μ {x : α | s + 1 < X x} * ENNReal.ofReal (Real.exp s) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    change (0 : ℝ) < s at hs
    have hsets : {x : α | s < f x} = {x : α | s + 1 < X x} := by
      ext x
      simp only [mem_setOf_eq, f, lt_max_iff]
      constructor
      · intro h
        rcases h with h | h <;> linarith
      · intro h
        exact Or.inl (by linarith)
    rw [hsets]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp 1) * (1 + ENNReal.ofReal (Real.exp (f x) - 1)) ∂μ :=
      lintegral_mono hp
    _ = ENNReal.ofReal (Real.exp 1) *
        (1 + ∫⁻ x, ENNReal.ofReal (Real.exp (f x) - 1) ∂μ) := by
      rw [lintegral_const_mul _
        (f := fun x => 1 + ENNReal.ofReal (Real.exp (f x) - 1))
        (measurable_const.add ((hfm.exp.sub measurable_const).ennreal_ofReal)),
        lintegral_add_left measurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
    _ = _ := by rw [hl, ht]

end RepulsiveCoulomb
