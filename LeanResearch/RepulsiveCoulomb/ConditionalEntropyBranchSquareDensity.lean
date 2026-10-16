module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchDensityKL
public import LeanResearch.PeriodicAttractiveLogGas.Rothaus

@[expose] public section

/-!
Zero-safe normalized densities and the literal extended square entropy used
by the checked one-site LSI. The zero-mass fiber uses the reference probability
as a harmless conditional law; its weighted KL is proved to be zero. Positive
mass uses the actual normalized withDensity law. The finite-log version below
covers every bounded measurable core slice without changing the full-domain
closure task downstream.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory InformationTheory Filter
open PeriodicAttractiveLogGas
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

def conditionalEntropyBranchNormalizedLaw (P : Measure α) (F : α → ℝ) : Measure α :=
  if 0 < ∫ x, F x ∂P then
    conditionalEntropyBranchDensityLaw P (fun x => F x / ∫ y, F y ∂P)
  else P

theorem conditionalEntropyBranchNormalizedLaw_probability {P : Measure α}
    [IsProbabilityMeasure P] {F : α → ℝ} (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F P) :
    IsProbabilityMeasure (conditionalEntropyBranchNormalizedLaw P F) := by
  unfold conditionalEntropyBranchNormalizedLaw
  split_ifs with hm
  · apply conditionalEntropyBranchDensityLaw_probability
      (fun x => div_nonneg (hF0 x) hm.le) (hFi.div_const _)
    rw [integral_div]
    exact div_self hm.ne'
  · infer_instance

theorem conditionalEntropyBranchNormalizedLaw_zero {P : Measure α} {F : α → ℝ}
    (hm : (∫ x, F x ∂P) = 0) : conditionalEntropyBranchNormalizedLaw P F = P := by
  simp only [conditionalEntropyBranchNormalizedLaw, hm, lt_self_iff_false, if_false]

theorem conditionalEntropyBranch_mul_log_div (t : ℝ) {m : ℝ} (hm : 0 < m) :
    (t / m) * Real.log (t / m) =
      (t * Real.log t) / m - (t / m) * Real.log m := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [Real.log_div ht hm.ne']
    ring

/-- Positive-mass entropy/KL identity, with no hidden integrability premise. -/
theorem conditionalEntropyBranch_positive_density_entropy {P : Measure α}
    [IsProbabilityMeasure P] {F : α → ℝ} (hFm : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F P)
    (hlog : Integrable (fun x => F x * Real.log (F x)) P)
    (hm : 0 < ∫ x, F x ∂P) :
    klDiv (conditionalEntropyBranchNormalizedLaw P F) P ≠ ∞ ∧
      entropy P F =
        (((∫ x, F x ∂P) * (klDiv (conditionalEntropyBranchNormalizedLaw P F) P).toReal : ℝ) : EReal) := by
  let m : ℝ := ∫ x, F x ∂P
  have hq0 (x : α) : 0 ≤ F x / m := div_nonneg (hF0 x) hm.le
  have hqi : Integrable (fun x => F x / m) P := hFi.div_const m
  have hqm : Measurable (fun x => F x / m) := hFm.div_const m
  have hqmass : (∫ x, F x / m ∂P) = 1 := by
    rw [integral_div]
    exact div_self hm.ne'
  have hlogDiv (x : α) : (F x / m) * Real.log (F x / m) =
      (F x * Real.log (F x)) / m - (F x / m) * Real.log m :=
    conditionalEntropyBranch_mul_log_div (F x) (show 0 < m from hm)
  have hqlog : Integrable (fun x => (F x / m) * Real.log (F x / m)) P := by
    simp_rw [hlogDiv]
    exact (hlog.div_const m).sub ((hFi.div_const m).mul_const (Real.log m))
  have hqreal := conditionalEntropyBranch_density_kl_real hqm hq0 hqi hqmass hqlog
  have hqfinite := conditionalEntropyBranch_density_kl_finite hqm hq0 hqi hqmass hqlog
  have hlaw : conditionalEntropyBranchNormalizedLaw P F =
      conditionalEntropyBranchDensityLaw P (fun x => F x / m) := by
    rw [conditionalEntropyBranchNormalizedLaw, if_pos hm]
  rw [hlaw]
  refine ⟨hqfinite, ?_⟩
  rw [entropy_eq_integral (Eventually.of_forall hF0) hlog, hqreal]
  apply congrArg (fun r : ℝ => (r : EReal))
  simp_rw [hlogDiv]
  rw [integral_sub (hlog.div_const m) ((hFi.div_const m).mul_const (Real.log m)),
    integral_div, integral_mul_const, integral_div]
  change (∫ x, F x * Real.log (F x) ∂P) - m * Real.log m =
    m * ((∫ x, F x * Real.log (F x) ∂P) / m - (m / m) * Real.log m)
  have hm0 : m ≠ 0 := hm.ne'
  field_simp [hm0] <;> ring

/-- The zero conditional-mass case is proved explicitly, rather than hidden
inside division by zero or an infinite conditional divergence. -/
theorem conditionalEntropyBranch_density_entropy {P : Measure α}
    [IsProbabilityMeasure P] {F : α → ℝ} (hFm : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F P)
    (hlog : Integrable (fun x => F x * Real.log (F x)) P) :
    klDiv (conditionalEntropyBranchNormalizedLaw P F) P ≠ ∞ ∧
      entropy P F =
        (((∫ x, F x ∂P) * (klDiv (conditionalEntropyBranchNormalizedLaw P F) P).toReal : ℝ) : EReal) := by
  by_cases hm : 0 < ∫ x, F x ∂P
  · exact conditionalEntropyBranch_positive_density_entropy hFm hF0 hFi hlog hm
  · have hz : (∫ x, F x ∂P) = 0 := le_antisymm (not_lt.mp hm) (integral_nonneg hF0)
    have hFzero : F =ᵐ[P] (fun _ => (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hF0) hFi).mp hz
    rw [conditionalEntropyBranchNormalizedLaw_zero hz, klDiv_self]
    constructor
    · simp
    · rw [entropy_congr_ae hFzero, entropy_zero]
      simp

/-- Exact bounded-square interface for each actual one-site core slice. The
coefficient multiplying conditional KL is exactly its conditional L2 mass. -/
theorem conditionalEntropyBranch_bounded_square_entropy {P : Measure α}
    [IsProbabilityMeasure P] {f : α → ℝ} (hfm : Measurable f)
    {M : ℝ} (hfb : ∀ x, |f x| ≤ M) :
    IsProbabilityMeasure (conditionalEntropyBranchNormalizedLaw P (fun x => f x ^ 2)) ∧
    klDiv (conditionalEntropyBranchNormalizedLaw P (fun x => f x ^ 2)) P ≠ ∞ ∧
    entropy P (fun x => f x ^ 2) =
      (((∫ x, f x ^ 2 ∂P) *
        (klDiv (conditionalEntropyBranchNormalizedLaw P (fun x => f x ^ 2)) P).toReal : ℝ) : EReal) := by
  have hi : Integrable (fun x => f x ^ 2) P :=
    Rothaus.integrable_continuous_comp_bounded hfm hfb (continuous_id.pow 2)
  have hl : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) P :=
    Rothaus.integrable_continuous_comp_bounded hfm hfb
      (Real.continuous_mul_log.comp (continuous_id.pow 2))
  exact ⟨conditionalEntropyBranchNormalizedLaw_probability (fun x => sq_nonneg _) hi,
    conditionalEntropyBranch_density_entropy (hfm.pow_const 2) (fun x => sq_nonneg _) hi hl⟩

end RepulsiveCoulomb
