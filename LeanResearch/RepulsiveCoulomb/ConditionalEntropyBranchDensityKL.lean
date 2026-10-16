import LeanResearch.PeriodicAttractiveLogGas.Entropy
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic.Ring

/-!
The literal extended entropy used by the checked LSI equals KL of a normalized
withDensity law. The main equality includes infinite entropy. Finite real
forms are separate and carry actual log-integrability hypotheses.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory InformationTheory Filter
open PeriodicAttractiveLogGas
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

def conditionalEntropyBranchDensityLaw (P : Measure α) (F : α → ℝ) : Measure α :=
  P.withDensity (fun x => ENNReal.ofReal (F x))

theorem conditionalEntropyBranchDensityLaw_probability {P : Measure α} {F : α → ℝ}
    (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F P) (hmass : (∫ x, F x ∂P) = 1) :
    IsProbabilityMeasure (conditionalEntropyBranchDensityLaw P F) := by
  constructor
  rw [conditionalEntropyBranchDensityLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hFi
      (Eventually.of_forall hF0), hmass, ENNReal.ofReal_one]

/-- Exact KL integral formula, with no finite-entropy hypothesis. -/
theorem conditionalEntropyBranch_density_kl_formula {P : Measure α}
    [IsProbabilityMeasure P] {F : α → ℝ} (hFm : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F P) (hmass : (∫ x, F x ∂P) = 1) :
    klDiv (conditionalEntropyBranchDensityLaw P F) P =
      ∫⁻ x, ENNReal.ofReal (klFun (F x)) ∂P := by
  letI := conditionalEntropyBranchDensityLaw_probability hF0 hFi hmass
  have hac : conditionalEntropyBranchDensityLaw P F ≪ P :=
    withDensity_absolutelyContinuous _ _
  have hRN : (conditionalEntropyBranchDensityLaw P F).rnDeriv P =ᵐ[P]
      (fun x => ENNReal.ofReal (F x)) := Measure.rnDeriv_withDensity P hFm.ennreal_ofReal
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  apply lintegral_congr_ae
  filter_upwards [hRN] with x hx
  rw [hx, ENNReal.toReal_ofReal (hF0 x)]

/-- The actual extended entropy, not a replacement real expression, equals
KL for every normalized nonnegative integrable density, including infinity. -/
theorem conditionalEntropyBranch_normalized_entropy_kl {P : Measure α}
    [IsProbabilityMeasure P] {F : α → ℝ} (hFm : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F P) (hmass : (∫ x, F x ∂P) = 1) :
    entropy P F = (klDiv (conditionalEntropyBranchDensityLaw P F) P : EReal) := by
  have hd (x : α) : entropyDensity (F x) = klFun (F x) + F x := by
    unfold entropyDensity klFun
    ring
  have hl : (∫⁻ x, ENNReal.ofReal (entropyDensity (F x)) ∂P) =
      klDiv (conditionalEntropyBranchDensityLaw P F) P + 1 := by
    simp_rw [hd, ENNReal.ofReal_add (klFun_nonneg (hF0 _)) (hF0 _)]
    have hkm : Measurable (fun x => ENNReal.ofReal (klFun (F x))) :=
      (measurable_klFun.comp hFm).ennreal_ofReal
    rw [lintegral_add_left hkm,
      ← conditionalEntropyBranch_density_kl_formula hFm hF0 hFi hmass,
      ← ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall hF0),
      hmass, ENNReal.ofReal_one]
  unfold entropy
  rw [hl, hmass]
  simp only [probReal_univ, Real.log_one, mul_zero, add_zero, EReal.coe_ennreal_add,
    EReal.coe_ennreal_one]
  exact EReal.add_sub_cancel_right

theorem conditionalEntropyBranch_density_kl_finite {P : Measure α}
    [IsProbabilityMeasure P] {F : α → ℝ} (hFm : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F P) (hmass : (∫ x, F x ∂P) = 1)
    (hlog : Integrable (fun x => F x * Real.log (F x)) P) :
    klDiv (conditionalEntropyBranchDensityLaw P F) P ≠ ∞ := by
  rw [conditionalEntropyBranch_density_kl_formula hFm hF0 hFi hmass]
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_klFun.comp hFm).aestronglyMeasurable
      (Eventually.of_forall (fun x => klFun_nonneg (hF0 x)))).mpr
  exact (hlog.add (integrable_const 1)).sub hFi

theorem conditionalEntropyBranch_density_kl_real {P : Measure α}
    [IsProbabilityMeasure P] {F : α → ℝ} (hFm : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F P) (hmass : (∫ x, F x ∂P) = 1)
    (hlog : Integrable (fun x => F x * Real.log (F x)) P) :
    (klDiv (conditionalEntropyBranchDensityLaw P F) P).toReal =
      ∫ x, F x * Real.log (F x) ∂P := by
  have hk : Integrable (fun x => klFun (F x)) P :=
    (hlog.add (integrable_const 1)).sub hFi
  have hn : ∀ x, 0 ≤ klFun (F x) := fun x => klFun_nonneg (hF0 x)
  rw [conditionalEntropyBranch_density_kl_formula hFm hF0 hFi hmass,
    ← ofReal_integral_eq_lintegral_ofReal hk (Eventually.of_forall hn),
    ENNReal.toReal_ofReal (integral_nonneg hn)]
  change (∫ x, (F x * Real.log (F x) + 1) - F x ∂P) = _
  have hsum : Integrable (fun x => F x * Real.log (F x) + 1) P :=
    hlog.add (integrable_const 1)
  rw [integral_sub hsum hFi,
    integral_add hlog (integrable_const 1), hmass]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, add_sub_cancel_right]

end RepulsiveCoulomb
