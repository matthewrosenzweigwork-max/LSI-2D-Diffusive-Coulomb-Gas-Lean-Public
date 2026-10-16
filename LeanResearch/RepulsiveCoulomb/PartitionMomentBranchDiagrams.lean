import LeanResearch.RepulsiveCoulomb.PartitionMomentBranchPeeling
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDiagramDegrees
import Mathlib.MeasureTheory.Integral.Prod

/-! Absolute integrability of signed ordered-edge diagrams is derived here
from actual row moments, before any singleton cancellation. Continuous product
measures and the exact finite real kernel are used throughout. Records-only. -/

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory

namespace RepulsiveCoulomb

variable {X : Type*} [MeasurableSpace X]

/-- Signed product for one literal edge list. -/
def partitionMomentDiagram {N p : ℕ} (G : X → X → ℝ)
    (e : Fin p → Fin N × Fin N) (x : Fin N → X) : ℝ :=
  ∏ j : Fin p, G (x (e j).1) (x (e j).2)

/-- Finite nonnegative representative of the absolute real kernel. -/
def partitionMomentAbsKernel (G : X → X → ℝ) (x y : X) : ℝ≥0∞ :=
  ENNReal.ofReal |G x y|

theorem partitionMomentDiagram_measurable {N p : ℕ}
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (e : Fin p → Fin N × Fin N) : Measurable (partitionMomentDiagram G e) := by
  apply Finset.univ.measurable_fun_prod
  intro j _
  have hm : Measurable (fun x : Fin N → X => (x (e j).1, x (e j).2)) :=
    (measurable_pi_apply (e j).1).prodMk (measurable_pi_apply (e j).2)
  simpa only [Function.comp_def, Function.uncurry] using hG.comp hm

theorem partitionMomentAbsKernel_measurable
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G)) :
    Measurable (Function.uncurry (partitionMomentAbsKernel G)) := by
  change Measurable (fun xy : X × X => ENNReal.ofReal |G xy.1 xy.2|)
  simpa only [Function.uncurry, Real.norm_eq_abs] using hG.norm.ennreal_ofReal

theorem partitionMomentDiagram_abs_product {N p : ℕ}
    (G : X → X → ℝ) (e : Fin p → Fin N × Fin N) (x : Fin N → X) :
    ENNReal.ofReal |partitionMomentDiagram G e x| =
      partitionMomentProduct (partitionMomentAbsKernel G)
        (fun j => (e j).1) (fun j => (e j).2) Finset.univ x := by
  simp only [partitionMomentDiagram, Finset.abs_prod, partitionMomentProduct,
    partitionMomentAbsKernel, ENNReal.ofReal_prod_of_nonneg (fun _ _ => abs_nonneg _)]

/-- Loop-free incidence cardinality equals the full multiplicity-aware degree.
In particular a reversed edge in a different slot counts separately. -/
theorem partitionMomentIncident_card_eq_degree {N p : ℕ}
    (e : Fin p → Fin N × Fin N) (hloop : ∀ j, (e j).1 ≠ (e j).2) (v : Fin N) :
    (partitionMomentIncident (fun j => (e j).1) (fun j => (e j).2)
      Finset.univ v).card = equilibriumDiagramDegree e v := by
  rw [partitionMomentIncident, Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold equilibriumDiagramDegree
  apply Finset.sum_congr rfl
  intro j _
  by_cases h1 : (e j).1 = v <;> by_cases h2 : (e j).2 = v
  · exact (hloop j (h1.trans h2.symm)).elim
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- The actual real row moment transports to the nonnegative Tonelli kernel. -/
theorem partitionMoment_abs_row_bound {μ : Measure X}
    (G : X → X → ℝ) {q : ℕ} {B : ℝ}
    (hrowInt : ∀ z, Integrable (fun y => |G z y| ^ q) μ)
    (hrow : ∀ z, (∫ y, |G z y| ^ q ∂μ) ≤ B) (z : X) :
    (∫⁻ y, partitionMomentAbsKernel G z y ^ q ∂μ) ≤ ENNReal.ofReal B := by
  calc
    (∫⁻ y, partitionMomentAbsKernel G z y ^ q ∂μ) =
        ENNReal.ofReal (∫ y, |G z y| ^ q ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hrowInt z)
        (Filter.Eventually.of_forall (fun y => pow_nonneg (abs_nonneg _) _))]
      simp only [partitionMomentAbsKernel, ENNReal.ofReal_pow (abs_nonneg _)]
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hrow z)

/-- Degree-controlled absolute diagram bound under the genuine product law. -/
theorem partitionMomentDiagram_lintegral_le {N p q : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x)
    (e : Fin p → Fin N × Fin N) (hloop : ∀ j, (e j).1 ≠ (e j).2)
    (hq : 0 < q) (hdegree : ∀ v, equilibriumDiagramDegree e v ≤ q)
    (B : ℝ) (hrowInt : ∀ z, Integrable (fun y => |G z y| ^ q) μ)
    (hrow : ∀ z, (∫ y, |G z y| ^ q ∂μ) ≤ B) :
    (∫⁻ x, ENNReal.ofReal |partitionMomentDiagram G e x|
        ∂Measure.pi (fun _ : Fin N => μ)) ≤
      ENNReal.ofReal B ^ ((p : ℝ) / (q : ℝ)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal B ^ (1 / (q : ℝ))
  have hroot : ∀ z, (∫⁻ y, partitionMomentAbsKernel G z y ^ q ∂μ) ^
      (1 / (q : ℝ)) ≤ C := fun z =>
    partitionMoment_root_mono hq (partitionMoment_abs_row_bound G hrowInt hrow z)
  have h := partitionMoment_lintegral_product_le (partitionMomentAbsKernel G)
    (partitionMomentAbsKernel_measurable G hG)
    (fun x y => congrArg (fun t : ℝ => ENNReal.ofReal |t|) (hsymm x y))
    (fun j => (e j).1) (fun j => (e j).2) Finset.univ hq
    (fun j _ => hloop j)
    (fun v => by rw [partitionMomentIncident_card_eq_degree e hloop]; exact hdegree v)
    C hroot
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simp_rw [← partitionMomentDiagram_abs_product] at h
  convert h using 1
  dsimp only [C]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  ring

/-- Every signed loop-free diagram is absolutely integrable using the p-th
row moment. This theorem precedes, and is independent of, row centering. -/
theorem partitionMomentDiagram_integrable {N p : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x)
    (e : Fin p → Fin N × Fin N) (hloop : ∀ j, (e j).1 ≠ (e j).2)
    (hp : 0 < p) (B : ℝ)
    (hrowInt : ∀ z, Integrable (fun y => |G z y| ^ p) μ)
    (hrow : ∀ z, (∫ y, |G z y| ^ p ∂μ) ≤ B) :
    Integrable (partitionMomentDiagram G e) (Measure.pi (fun _ : Fin N => μ)) := by
  refine ⟨(partitionMomentDiagram_measurable G hG e).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs]
  have h := partitionMomentDiagram_lintegral_le G hG hsymm e hloop hp
    (equilibriumDiagram_degree_le_order e hloop) B hrowInt hrow
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  rw [div_self hp', ENNReal.rpow_one] at h
  exact h.trans_lt ENNReal.ofReal_lt_top

/-- Real-valued absolute moment bound, retaining the original row constant. -/
theorem partitionMomentDiagram_integral_abs_le {N p q : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x)
    (e : Fin p → Fin N × Fin N) (hloop : ∀ j, (e j).1 ≠ (e j).2)
    (hq : 0 < q) (hdegree : ∀ v, equilibriumDiagramDegree e v ≤ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hrowInt : ∀ z, Integrable (fun y => |G z y| ^ q) μ)
    (hrow : ∀ z, (∫ y, |G z y| ^ q ∂μ) ≤ B) :
    (∫ x, |partitionMomentDiagram G e x| ∂Measure.pi (fun _ : Fin N => μ)) ≤
      B ^ ((p : ℝ) / (q : ℝ)) := by
  have h := partitionMomentDiagram_lintegral_le G hG hsymm e hloop hq hdegree
    B hrowInt hrow
  have hm : AEStronglyMeasurable (fun x => |partitionMomentDiagram G e x|)
      (Measure.pi (fun _ : Fin N => μ)) := by
    simpa only [Real.norm_eq_abs] using
      (partitionMomentDiagram_measurable G hG e).norm.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hm]
  have hfin : ENNReal.ofReal B ^ ((p : ℝ) / (q : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have ht := ENNReal.toReal_mono hfin h
  simpa only [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB] using ht

end RepulsiveCoulomb
