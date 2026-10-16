import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyContinuousApprox
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Semicontinuity.Basic

/-! Relative entropy is genuinely weakly lower semicontinuous on planar
probability measures. Its bounded-continuous variational formula is proved
from the measurable formula and the actual approximation theorem, including
infinite entropy and non-AC measures. No equilibrium existence is claimed. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace RepulsiveCoulomb

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]

def equilibriumEntropyContinuousSup (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ h : α →ᵇ ℝ, ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν h)

/-- The bounded-continuous variational representation includes every finite
measure pair, with no AC or finite-entropy restriction. -/
theorem equilibriumEntropyContinuousSup_eq_klDiv
    [NormalSpace α] [BorelSpace α] {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [(μ + ν).WeaklyRegular] :
    equilibriumEntropyContinuousSup μ ν = InformationTheory.klDiv μ ν := by
  apply le_antisymm
  · apply iSup_le
    intro g
    exact equilibriumEntropyMeasureDual_le_klDiv g.continuous.measurable
      ⟨‖g‖, fun x => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x⟩
  · rw [← equilibriumEntropyMeasurableSup_eq_klDiv]
    apply iSup_le
    intro h
    by_cases htop : equilibriumEntropyContinuousSup μ ν = ∞
    · rw [htop]
      exact le_top
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g, hg⟩ := equilibriumEntropyMeasureDual_continuous_approximation (μ := μ) (ν := ν) h.2.1 h.2.2 hε
    have hs : ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν g) ≤
        equilibriumEntropyContinuousSup μ ν :=
      le_iSup (fun f : α →ᵇ ℝ => ENNReal.ofReal (equilibriumEntropyMeasureDual μ ν f)) g
    have hgs := (ENNReal.ofReal_le_iff_le_toReal htop).mp hs
    have hd := (le_abs_self (equilibriumEntropyMeasureDual μ ν h.1 -
      equilibriumEntropyMeasureDual μ ν g)).trans hg
    linarith

/-- Actual weak lower semicontinuity, with the pinned weak topology on
ProbabilityMeasure C. The fixed reference is any finite Borel measure. -/
theorem equilibrium_klDiv_weak_lowerSemicontinuous (ν : Measure ℂ) [IsFiniteMeasure ν] :
    LowerSemicontinuous (fun μ : ProbabilityMeasure ℂ =>
      InformationTheory.klDiv (μ : Measure ℂ) ν) := by
  have he : (fun μ : ProbabilityMeasure ℂ => InformationTheory.klDiv (μ : Measure ℂ) ν) =
      (fun μ : ProbabilityMeasure ℂ => ⨆ g : ℂ →ᵇ ℝ,
        ENNReal.ofReal (equilibriumEntropyMeasureDual (μ : Measure ℂ) ν g)) := by
    funext μ
    exact (equilibriumEntropyContinuousSup_eq_klDiv (μ := (μ : Measure ℂ)) (ν := ν)).symm
  rw [he]
  apply lowerSemicontinuous_iSup
  intro g
  apply Continuous.lowerSemicontinuous
  apply ENNReal.continuous_ofReal.comp
  exact ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).sub
    continuous_const).add continuous_const

end RepulsiveCoulomb
