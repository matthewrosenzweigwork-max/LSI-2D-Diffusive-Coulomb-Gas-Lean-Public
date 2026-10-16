import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchSquareDensity
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.WithDensity

/-!
Measurable family of actual normalized density laws, including zero conditional
mass. Markov normalization is proved, not assumed, from each fiber's ordinary
integrability. Bounded core slices discharge those hypotheses downstream.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

def conditionalEntropyBranchFiberMass (κ : Kernel α β) (F : α × β → ℝ) (a : α) : ℝ :=
  ∫ b, F (a, b) ∂κ a

theorem conditionalEntropyBranchFiberMass_measurable (κ : Kernel α β) [IsMarkovKernel κ]
    {F : α × β → ℝ} (hFm : Measurable F) :
    Measurable (conditionalEntropyBranchFiberMass κ F) :=
  (hFm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

def conditionalEntropyBranchNormalizedKernel (κ : Kernel α β) [IsMarkovKernel κ]
    {F : α × β → ℝ} (hFm : Measurable F) : Kernel α β :=
  Kernel.piecewise (s := {a : α | 0 < conditionalEntropyBranchFiberMass κ F a})
    (measurableSet_lt (measurable_const : Measurable (fun _ : α => (0 : ℝ)))
      (conditionalEntropyBranchFiberMass_measurable κ hFm))
    (κ.withDensity (fun a b => ENNReal.ofReal
      (F (a, b) / conditionalEntropyBranchFiberMass κ F a))) κ

theorem conditionalEntropyBranchNormalizedKernel_apply (κ : Kernel α β) [IsMarkovKernel κ]
    {F : α × β → ℝ} (hFm : Measurable F) (a : α) :
    conditionalEntropyBranchNormalizedKernel κ hFm a =
      conditionalEntropyBranchNormalizedLaw (κ a) (fun b => F (a, b)) := by
  have hq : Measurable (fun p : α × β => ENNReal.ofReal
      (F p / conditionalEntropyBranchFiberMass κ F p.1)) :=
    (hFm.div ((conditionalEntropyBranchFiberMass_measurable κ hFm).comp
      measurable_fst)).ennreal_ofReal
  unfold conditionalEntropyBranchNormalizedKernel
  rw [Kernel.piecewise_apply]
  unfold conditionalEntropyBranchNormalizedLaw
  change (if 0 < conditionalEntropyBranchFiberMass κ F a then _ else _) =
    (if 0 < conditionalEntropyBranchFiberMass κ F a then _ else _)
  split_ifs with hm
  · exact Kernel.withDensity_apply (f := fun a b => ENNReal.ofReal
      (F (a, b) / conditionalEntropyBranchFiberMass κ F a)) κ hq a
  · rfl

theorem conditionalEntropyBranchNormalizedKernel_isMarkov (κ : Kernel α β) [IsMarkovKernel κ]
    {F : α × β → ℝ} (hFm : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
    (hFi : ∀ a, Integrable (fun b => F (a, b)) (κ a)) :
    IsMarkovKernel (conditionalEntropyBranchNormalizedKernel κ hFm) := by
  refine ⟨fun a => ?_⟩
  rw [conditionalEntropyBranchNormalizedKernel_apply]
  exact conditionalEntropyBranchNormalizedLaw_probability (fun b => hF0 (a, b)) (hFi a)

/-- Multiplying the normalized law by its real mass recovers the actual
unnormalized density law, including zero mass. -/
theorem conditionalEntropyBranch_mass_smul_normalized {P : Measure β}
    [IsProbabilityMeasure P] {F : β → ℝ} (hFm : Measurable F)
    (hF0 : ∀ b, 0 ≤ F b) (hFi : Integrable F P) :
    ENNReal.ofReal (∫ b, F b ∂P) • conditionalEntropyBranchNormalizedLaw P F =
      conditionalEntropyBranchDensityLaw P F := by
  by_cases hm : 0 < ∫ b, F b ∂P
  · rw [conditionalEntropyBranchNormalizedLaw, if_pos hm]
    unfold conditionalEntropyBranchDensityLaw
    rw [← withDensity_smul _ (hFm.div_const _).ennreal_ofReal]
    congr 1
    funext b
    rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hm.le]
    congr 1
    field_simp [hm.ne'] <;> ring
  · have hz : (∫ b, F b ∂P) = 0 := le_antisymm (not_lt.mp hm) (integral_nonneg hF0)
    have hFzero := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hF0) hFi).mp hz
    rw [hz, ENNReal.ofReal_zero, zero_smul]
    symm
    apply (withDensity_eq_zero_iff hFm.ennreal_ofReal.aemeasurable).mpr
    filter_upwards [hFzero] with b hb
    simp only [hb, Pi.zero_apply, ENNReal.ofReal_zero]

theorem conditionalEntropyBranch_fiber_mass_smul (κ : Kernel α β) [IsMarkovKernel κ]
    {F : α × β → ℝ} (hFm : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
    (hFi : ∀ a, Integrable (fun b => F (a, b)) (κ a)) (a : α) :
    ENNReal.ofReal (conditionalEntropyBranchFiberMass κ F a) •
        conditionalEntropyBranchNormalizedKernel κ hFm a =
      (κ a).withDensity (fun b => ENNReal.ofReal (F (a, b))) := by
  rw [conditionalEntropyBranchNormalizedKernel_apply]
  exact conditionalEntropyBranch_mass_smul_normalized
    (hFm.comp measurable_prodMk_left) (fun b => hF0 (a, b)) (hFi a)

end RepulsiveCoulomb
