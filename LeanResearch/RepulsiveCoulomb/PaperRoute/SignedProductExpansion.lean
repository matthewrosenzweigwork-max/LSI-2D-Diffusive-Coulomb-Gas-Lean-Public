import Mathlib.MeasureTheory.VectorMeasure.Prod
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Tactic.Ring

/-! Additive experimental source; verification is recorded separately in evidence. Genuine signed-product
algebra and variation-integrable restricted interaction; no product or
vector-integral junk default is used as a correspondence proof. -/
noncomputable section
open MeasureTheory Set
namespace RepulsiveCoulomb.PaperRoute

private instance signed_finite_variation {α : Type*} [MeasurableSpace α]
    (σ : SignedMeasure α) : IsFiniteMeasure σ.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]
  infer_instance

/-- Genuine scalar tensor square of a signed measure. -/
def paperSignedSquare {α : Type*} [MeasurableSpace α] (σ : SignedMeasure α) :
    SignedMeasure (α × α) := σ.prod σ (ContinuousLinearMap.lsmul ℝ ℝ)

theorem paper_signed_hasProd {α : Type*} [MeasurableSpace α] (σ : SignedMeasure α) :
    VectorMeasure.HasProd σ σ (ContinuousLinearMap.lsmul ℝ ℝ) := inferInstance

/-- Rectangle uniqueness proves that this is the genuine tensor product,
not merely an expression named as an interaction integral. -/
theorem paper_signed_difference_square {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    paperSignedSquare (μ.toSignedMeasure - ν.toSignedMeasure) =
      (μ.prod μ).toSignedMeasure - (μ.prod ν).toSignedMeasure -
        (ν.prod μ).toSignedMeasure + (ν.prod ν).toSignedMeasure := by
  apply VectorMeasure.prod_eq_of_forall_apply_prod
  intro s t hs ht
  simp only [_root_.add_apply, _root_.sub_apply,
    Measure.toSignedMeasure_apply_measurable (hs.prod ht),
    Measure.toSignedMeasure_apply_measurable hs,
    Measure.toSignedMeasure_apply_measurable ht, Measure.real, Measure.prod_prod,
    ENNReal.toReal_mul, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

/-- Scaling the actual tensor square, proved on measurable rectangles. -/
theorem paper_signed_square_smul {α : Type*} [MeasurableSpace α]
    (σ : SignedMeasure α) (c : ℝ) :
    paperSignedSquare (c • σ) = (c * c) • paperSignedSquare σ := by
  apply VectorMeasure.prod_eq_of_forall_apply_prod
  intro s t hs ht
  simp only [_root_.smul_apply, paperSignedSquare, VectorMeasure.prod_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

/-- Finite positive-product integrability supplies actual signed-variation
integrability before the interaction is evaluated. The set S may be the
complement of the spatial diagonal. -/
theorem paper_signed_restricted_square_integrable {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set (α × α)} (hS : MeasurableSet S) {K : α × α → ℝ}
    (hμμ : IntegrableOn K S (μ.prod μ)) (hμν : IntegrableOn K S (μ.prod ν))
    (hνμ : IntegrableOn K S (ν.prod μ)) (hνν : IntegrableOn K S (ν.prod ν)) :
    ((paperSignedSquare (μ.toSignedMeasure - ν.toSignedMeasure)).restrict S).Integrable K := by
  rw [paper_signed_difference_square, VectorMeasure.restrict_add,
    VectorMeasure.restrict_sub, VectorMeasure.restrict_sub]
  have cv {m : Measure (α × α)} [IsFiniteMeasure m] (hm : IntegrableOn K S m) :
      (m.toSignedMeasure.restrict S).Integrable K := by
    simpa only [VectorMeasure.restrict_toSignedMeasure hS, VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure, MeasureTheory.IntegrableOn] using hm
  exact ((cv hμμ).sub_vectorMeasure (cv hμν)).sub_vectorMeasure (cv hνμ) |>.add_vectorMeasure (cv hνν)

/-- Literal signed restricted integral, justified by the previous variation
integrability and genuine tensor-square identity. -/
theorem paper_signed_restricted_square_integral {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set (α × α)} (hS : MeasurableSet S) {K : α × α → ℝ}
    (hμμ : IntegrableOn K S (μ.prod μ)) (hμν : IntegrableOn K S (μ.prod ν))
    (hνμ : IntegrableOn K S (ν.prod μ)) (hνν : IntegrableOn K S (ν.prod ν)) :
    (∫ᵛ p in S, K p ∂<•paperSignedSquare (μ.toSignedMeasure - ν.toSignedMeasure)) =
      (∫ p in S, K p ∂μ.prod μ) - (∫ p in S, K p ∂μ.prod ν) -
        (∫ p in S, K p ∂ν.prod μ) + (∫ p in S, K p ∂ν.prod ν) := by
  have cv {m : Measure (α × α)} [IsFiniteMeasure m] (hm : IntegrableOn K S m) :
      (m.toSignedMeasure.restrict S).Integrable K := by
    simpa only [VectorMeasure.restrict_toSignedMeasure hS, VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure, MeasureTheory.IntegrableOn] using hm
  change (∫ᵛ p, K p ∂<•(paperSignedSquare (μ.toSignedMeasure - ν.toSignedMeasure)).restrict S) = _
  rw [paper_signed_difference_square, VectorMeasure.restrict_add,
    VectorMeasure.restrict_sub, VectorMeasure.restrict_sub,
    VectorMeasure.integral_add_vectorMeasure
      (((cv hμμ).sub_vectorMeasure (cv hμν)).sub_vectorMeasure (cv hνμ)) (cv hνν),
    VectorMeasure.integral_sub_vectorMeasure
      ((cv hμμ).sub_vectorMeasure (cv hμν)) (cv hνμ),
    VectorMeasure.integral_sub_vectorMeasure (cv hμμ) (cv hμν)]
  simp only [VectorMeasure.restrict_toSignedMeasure hS, VectorMeasure.integral_toSignedMeasure]

end RepulsiveCoulomb.PaperRoute
