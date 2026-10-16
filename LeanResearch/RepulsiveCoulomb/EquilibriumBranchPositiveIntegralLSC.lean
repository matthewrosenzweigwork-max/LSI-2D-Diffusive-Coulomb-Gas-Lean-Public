import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Weak lower semicontinuity of the genuine nonnegative integral of a
continuous real function. The proof uses actual bounded continuous truncations
and monotone convergence; infinite integrals are included. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace RepulsiveCoulomb

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]

def equilibriumContinuousTruncation (f : α → ℝ) (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) (n : ℕ) : α →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (n : ℝ) (f x))
    (continuous_const.min hf) (n : ℝ) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg n) (hn x))]
      exact min_le_left _ _)

theorem equilibriumContinuousTruncation_nonneg (f : α → ℝ) (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) (n : ℕ) (x : α) :
    0 ≤ equilibriumContinuousTruncation f hf hn n x := le_min (Nat.cast_nonneg n) (hn x)

theorem equilibriumContinuousTruncation_integrable (f : α → ℝ) (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) (n : ℕ) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable (equilibriumContinuousTruncation f hf hn n) μ := by
  apply Integrable.of_bound (equilibriumContinuousTruncation f hf hn n).continuous.measurable.aestronglyMeasurable (n : ℝ)
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (equilibriumContinuousTruncation_nonneg f hf hn n x)]
    exact min_le_left _ _)

theorem equilibrium_lintegral_eq_iSup_truncations (f : α → ℝ) (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) (μ : Measure α) [IsFiniteMeasure μ] :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ⨆ n : ℕ, ENNReal.ofReal (∫ x, equilibriumContinuousTruncation f hf hn n x ∂μ) := by
  have hpoint (x : α) : ENNReal.ofReal (f x) =
      ⨆ n : ℕ, ENNReal.ofReal (equilibriumContinuousTruncation f hf hn n x) := by
    apply le_antisymm
    · obtain ⟨n, hnx⟩ := exists_nat_ge (f x)
      have he : equilibriumContinuousTruncation f hf hn n x = f x := min_eq_right hnx
      rw [← he]
      exact le_iSup (fun m : ℕ => ENNReal.ofReal (equilibriumContinuousTruncation f hf hn m x)) n
    · apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hm (n : ℕ) : Measurable (fun x => ENNReal.ofReal (equilibriumContinuousTruncation f hf hn n x)) :=
    (equilibriumContinuousTruncation f hf hn n).continuous.measurable.ennreal_ofReal
  have hmono : Monotone (fun n : ℕ => fun x : α => ENNReal.ofReal (equilibriumContinuousTruncation f hf hn n x)) := by
    intro n m hnm x
    apply ENNReal.ofReal_le_ofReal
    exact min_le_min (by exact_mod_cast hnm) le_rfl
  calc
    _ = ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (equilibriumContinuousTruncation f hf hn n x) ∂μ :=
      lintegral_congr hpoint
    _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (equilibriumContinuousTruncation f hf hn n x) ∂μ :=
      lintegral_iSup hm hmono
    _ = _ := by
      congr 1
      funext n
      exact (ofReal_integral_eq_lintegral_ofReal
        (equilibriumContinuousTruncation_integrable f hf hn n μ)
        (Eventually.of_forall (equilibriumContinuousTruncation_nonneg f hf hn n))).symm

/-- Actual weak lsc, not restricted to measures having a finite integral. -/
theorem equilibrium_positiveIntegral_lowerSemicontinuous (f : α → ℝ) (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) :
    LowerSemicontinuous (fun μ : ProbabilityMeasure α => ∫⁻ x, ENNReal.ofReal (f x) ∂μ) := by
  have he : (fun μ : ProbabilityMeasure α => ∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      (fun μ : ProbabilityMeasure α => ⨆ n : ℕ,
        ENNReal.ofReal (∫ x, equilibriumContinuousTruncation f hf hn n x ∂μ)) := by
    funext μ
    exact equilibrium_lintegral_eq_iSup_truncations f hf hn μ
  rw [he]
  apply lowerSemicontinuous_iSup
  intro n
  exact (ENNReal.continuous_ofReal.comp
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (equilibriumContinuousTruncation f hf hn n))).lowerSemicontinuous

end RepulsiveCoulomb
