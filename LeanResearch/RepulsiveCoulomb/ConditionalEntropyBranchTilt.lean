import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchVariational
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
Actual scalar tilted-law KL expansion and Jensen normalization estimate.
The measure is Mathlib's genuinely normalized exponential tilt. Applications
to the Coulomb law must separately identify that tilt off collisions and then
use nullity; no assertion here identifies exp(log 0) with a vanishing weight.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory InformationTheory Real Filter
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

/-- Finite KL against the normalized tilt implies finite KL against the base
when the tilt exponent is competitor-integrable. In particular, base entropy
is not silently inferred by subtracting an unproved integral. -/
theorem conditionalEntropyBranch_base_finite_of_tilt {Q P : Measure α}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] {G : α → ℝ}
    (he : Integrable (fun x => Real.exp (G x)) P) (hG : Integrable G Q)
    (hKL : klDiv Q (P.tilted G) ≠ ∞) : klDiv Q P ≠ ∞ := by
  letI : IsProbabilityMeasure (P.tilted G) := isProbabilityMeasure_tilted he
  obtain ⟨hact, hit⟩ := klDiv_ne_top_iff.mp hKL
  have hac : Q ≪ P := hact.trans (tilted_absolutelyContinuous P G)
  have heq : (fun x => llr Q (P.tilted G) x + G x -
      Real.log (∫ y, Real.exp (G y) ∂P)) =ᵐ[Q] llr Q P := by
    filter_upwards [llr_tilted_right hac he] with x hx
    rw [hx]
    ring
  have hi : Integrable (llr Q P) Q :=
    ((hit.add hG).sub (integrable_const _)).congr heq
  exact klDiv_ne_top hac hi

theorem conditionalEntropyBranch_tilt_finite_of_base {Q P : Measure α}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] {G : α → ℝ}
    (he : Integrable (fun x => Real.exp (G x)) P) (hG : Integrable G Q)
    (hKL : klDiv Q P ≠ ∞) : klDiv Q (P.tilted G) ≠ ∞ := by
  letI : IsProbabilityMeasure (P.tilted G) := isProbabilityMeasure_tilted he
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.mp hKL
  exact klDiv_ne_top (hac.trans (absolutelyContinuous_tilted he))
    (integrable_llr_tilted_right hac hG hi he)

/-- Finite real KL expansion under a true exponential tilt. -/
theorem conditionalEntropyBranch_tilt_kl_identity {Q P : Measure α}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] {G : α → ℝ}
    (he : Integrable (fun x => Real.exp (G x)) P) (hG : Integrable G Q)
    (hKL : klDiv Q P ≠ ∞) :
    (klDiv Q (P.tilted G)).toReal = (klDiv Q P).toReal -
      (∫ x, G x ∂Q) + Real.log (∫ x, Real.exp (G x) ∂P) := by
  letI : IsProbabilityMeasure (P.tilted G) := isProbabilityMeasure_tilted he
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.mp hKL
  have hact := hac.trans (absolutelyContinuous_tilted he)
  rw [toReal_klDiv_of_measure_eq hact (by simp),
    toReal_klDiv_of_measure_eq hac (by simp)]
  exact integral_llr_tilted_right hac hG he hi

theorem conditionalEntropyBranch_log_normalizer_lower {P : Measure α}
    [IsProbabilityMeasure P] {G : α → ℝ} (hG : Integrable G P)
    (he : Integrable (fun x => Real.exp (G x)) P) :
    (∫ x, G x ∂P) ≤ Real.log (∫ x, Real.exp (G x) ∂P) := by
  simpa only [klDiv_self, ENNReal.toReal_zero, zero_add] using
    conditionalEntropyBranch_variational (Q := P) (P := P) (by simp) hG he

/-- The exact one-site scalar inequality used after Han--Shearer. All three
analytic integrability premises are displayed, including the base expectation
of the potential that enters Jensen's inequality. -/
theorem conditionalEntropyBranch_tilt_potential_lower {Q P : Measure α}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] {Φ : α → ℝ} (β : ℝ)
    (hΦQ : Integrable Φ Q) (hΦP : Integrable Φ P)
    (he : Integrable (fun x => Real.exp (-β * Φ x)) P)
    (hKL : klDiv Q P ≠ ∞) :
    (klDiv Q P).toReal + β * ((∫ x, Φ x ∂Q) - (∫ x, Φ x ∂P)) ≤
      (klDiv Q (P.tilted (fun x => -β * Φ x))).toReal := by
  have hid := conditionalEntropyBranch_tilt_kl_identity he (hΦQ.const_mul (-β)) hKL
  have hJ := conditionalEntropyBranch_log_normalizer_lower (hΦP.const_mul (-β)) he
  rw [integral_const_mul] at hid hJ
  rw [hid]
  nlinarith

end RepulsiveCoulomb
