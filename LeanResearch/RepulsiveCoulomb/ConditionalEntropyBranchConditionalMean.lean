module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchBinaryKL
public import Mathlib.Probability.Kernel.Disintegration.Integral

@[expose] public section

/-! Signed-integrable conditional means for the genuinely constructed arbitrary
law, with absolute integrability established before the tower identity.
Records-only draft, not staged or checked. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace RepulsiveCoulomb

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [StandardBorelSpace β] [Nonempty β]

theorem conditionalEntropyBranch_conditional_integrable (Q : Measure (α × β))
    [IsFiniteMeasure Q] {F : α × β → ℝ} (hF : Integrable F Q) :
    ∀ᵐ a ∂Q.fst, Integrable (fun b => F (a, b)) (conditionalEntropyBranchKernel Q a) := by
  have hF' : Integrable F (Q.fst ⊗ₘ conditionalEntropyBranchKernel Q) := by
    rwa [conditionalEntropyBranch_disintegration]
  exact (Measure.integrable_compProd_iff hF'.aestronglyMeasurable).mp hF' |>.1

theorem conditionalEntropyBranch_conditional_mean_integrable (Q : Measure (α × β))
    [IsFiniteMeasure Q] {F : α × β → ℝ} (hF : Integrable F Q) :
    Integrable (fun a => ∫ b, F (a, b) ∂conditionalEntropyBranchKernel Q a) Q.fst := by
  have hF' : Integrable F (Q.fst ⊗ₘ conditionalEntropyBranchKernel Q) := by
    rwa [conditionalEntropyBranch_disintegration]
  have hn := (Measure.integrable_compProd_iff hF'.aestronglyMeasurable).mp hF' |>.2
  have hm : AEStronglyMeasurable
      (fun a => ∫ b, F (a, b) ∂conditionalEntropyBranchKernel Q a) Q.fst :=
    hF.aestronglyMeasurable.integral_condKernel
  apply hn.mono' hm
  exact Eventually.of_forall (fun a => norm_integral_le_integral_norm _)

theorem conditionalEntropyBranch_conditional_mean_tower (Q : Measure (α × β))
    [IsFiniteMeasure Q] {F : α × β → ℝ} (hF : Integrable F Q) :
    (∫ a, ∫ b, F (a, b) ∂conditionalEntropyBranchKernel Q a ∂Q.fst) = ∫ p, F p ∂Q := by
  exact Measure.integral_condKernel hF

end RepulsiveCoulomb
