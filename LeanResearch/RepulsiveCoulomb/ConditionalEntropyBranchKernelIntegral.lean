import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchBinaryKL
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
The missing fiber-integral interface for conditional KL in countably generated
spaces. It is proved from the pinned jointly measurable kernel RN derivative,
the genuine compProd RN identity, and the measurable fiber-AC event.
Both infinite-entropy and singular-fiber cases are included; no chain-rule
integral identity or analytic tensorization theorem is assumed.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Classical
namespace RepulsiveCoulomb

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

section Kernel
variable [MeasurableSpace.CountableOrCountablyGenerated α β]
  (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]

/-- Fiber KL expressed by a jointly measurable RN derivative and its genuine
absolute-continuity event. This is an equality for every outside value. -/
theorem conditionalEntropyBranch_fiber_kl_formula (a : α) :
    klDiv (κ a) (η a) =
      if κ a ≪ η a then
        ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂η a
      else ∞ := by
  by_cases hac : κ a ≪ η a
  · rw [if_pos hac, klDiv_eq_lintegral_klFun_of_ac hac]
    apply lintegral_congr_ae
    filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)] with b hb
    rw [hb]
  · rw [if_neg hac, klDiv_of_not_ac hac]

/-- Actual measurability of fiber KL, including the singular part. -/
theorem conditionalEntropyBranch_fiber_kl_measurable :
    Measurable (fun a => klDiv (κ a) (η a)) := by
  have hf : Measurable (fun p : α × β =>
      ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal)) :=
    (measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal
  simp_rw [conditionalEntropyBranch_fiber_kl_formula κ η]
  exact (hf.lintegral_kernel_prod_right' (κ := η)).ite
    (Kernel.measurableSet_absolutelyContinuous κ η) measurable_const

/-- Conditional joint KL is exactly the integral of fiber KL. Finiteness is
not assumed. Failure of joint AC gives a positive-measure set of infinite
fiber divergences, whereas the AC case uses nonnegative RN/Fubini identities. -/
theorem conditionalEntropyBranch_compProd_kl_integral
    (μ : Measure α) [IsFiniteMeasure μ] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  by_cases hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η
  · have hf : Measurable (fun p : α × β =>
        ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal)) :=
      (measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    calc
      (∫⁻ p, ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal) ∂μ ⊗ₘ η) =
          ∫⁻ p, ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal) ∂μ ⊗ₘ η := by
        apply lintegral_congr_ae
        filter_upwards [rnDeriv_measure_compProd_right μ κ η] with p hp
        rw [hp]
      _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂η a ∂μ :=
        Measure.lintegral_compProd hf
      _ = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hac.kernel_of_compProd] with a ha
        rw [conditionalEntropyBranch_fiber_kl_formula κ η a, if_pos ha]
  · have htop : (∫⁻ a, klDiv (κ a) (η a) ∂μ) = ∞ := by
      by_contra hfin
      have hlt := ae_lt_top (conditionalEntropyBranch_fiber_kl_measurable κ η) hfin
      apply hac
      apply Measure.absolutelyContinuous_compProd_right_iff.mpr
      filter_upwards [hlt] with a ha
      exact (klDiv_ne_top_iff.mp ha.ne).1
    rw [klDiv_of_not_ac hac, htop]

/-- Finite joint divergence supplies integrability of the actual real-valued
fiber divergences, as well as a.e. finite fiber divergence. -/
theorem conditionalEntropyBranch_compProd_kl_finite
    (μ : Measure α) [IsFiniteMeasure μ]
    (h : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞) :
    (∀ᵐ a ∂μ, klDiv (κ a) (η a) < ∞) ∧
      Integrable (fun a => (klDiv (κ a) (η a)).toReal) μ := by
  rw [conditionalEntropyBranch_compProd_kl_integral κ η μ] at h
  have hm := conditionalEntropyBranch_fiber_kl_measurable κ η
  exact ⟨ae_lt_top hm h, integrable_toReal_of_lintegral_ne_top hm.aemeasurable h⟩

theorem conditionalEntropyBranch_compProd_kl_integral_real
    (μ : Measure α) [IsFiniteMeasure μ]
    (h : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞) :
    (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal =
      ∫ a, (klDiv (κ a) (η a)).toReal ∂μ := by
  rw [conditionalEntropyBranch_compProd_kl_integral κ η μ]
  exact (integral_toReal (conditionalEntropyBranch_fiber_kl_measurable κ η).aemeasurable
    (conditionalEntropyBranch_compProd_kl_finite κ η μ h).1).symm

end Kernel

/-- The conditional cost used in the binary and finite-product modules really
is the expected KL of the constructed conditional law. -/
theorem conditionalEntropyBranch_cost_eq_integral [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) [IsFiniteMeasure Q]
    (ν : Measure β) [IsProbabilityMeasure ν] :
    conditionalEntropyBranchCost Q ν =
      ∫⁻ a, klDiv (conditionalEntropyBranchKernel Q a) ν ∂Q.fst := by
  have h := conditionalEntropyBranch_compProd_kl_integral
    (conditionalEntropyBranchKernel Q) (Kernel.const α ν) Q.fst
  simpa only [conditionalEntropyBranch_disintegration, Measure.compProd_const,
    Kernel.const_apply, conditionalEntropyBranchCost] using h

end RepulsiveCoulomb
