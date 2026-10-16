import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.EReal.Operations

/-! Extended signed integrals with an actually integrable negative part.
The shift identity includes infinite positive integrals and is intended for the
full P2 free-energy correspondence. It never subtracts two infinite quantities
under the theorem's hypotheses. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

def equilibriumExtendedIntegral (μ : Measure α) (f : α → ℝ) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (f x) ∂μ) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ) : EReal)

theorem equilibriumExtendedIntegral_eq_integral {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) : equilibriumExtendedIntegral μ f = (∫ x, f x ∂μ : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ :=
    ((lintegral_ofReal_le_lintegral_enorm f).trans_lt hf.2).ne
  have hn : (∫⁻ x, ENNReal.ofReal (-f x) ∂μ) ≠ ∞ :=
    ((lintegral_ofReal_le_lintegral_enorm (fun x => -f x)).trans_lt hf.neg.2).ne
  rw [equilibriumExtendedIntegral, ← EReal.coe_ennreal_toReal hp,
    ← EReal.coe_ennreal_toReal hn, ← EReal.coe_sub,
    ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]

theorem equilibriumExtendedIntegral_negative_ne_top {μ : Measure α} {f : α → ℝ}
    (hn : Integrable (fun x => max (-f x) 0) μ) :
    (∫⁻ x, ENNReal.ofReal (-f x) ∂μ) ≠ ∞ := by
  have he : (fun x => ENNReal.ofReal (max (-f x) 0)) =
      (fun x => ENNReal.ofReal (-f x)) := by
    funext x
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact max_eq_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (-f x) from bot_le)
  have h := (lintegral_ofReal_ne_top_iff_integrable hn.aestronglyMeasurable
    (Eventually.of_forall (fun x => le_max_right (-f x) 0))).mpr hn
  rwa [he] at h

/-- An infinite positive integral cannot be hidden by the Bochner integral's
default value when the negative part is integrable. -/
theorem equilibriumExtendedIntegral_eq_top_of_not_integrable {μ : Measure α} {f : α → ℝ}
    (hfm : Measurable f) (hn : Integrable (fun x => max (-f x) 0) μ)
    (hf : ¬ Integrable f μ) : equilibriumExtendedIntegral μ f = ⊤ := by
  have hp : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ∞ := by
    by_contra h
    have he : (fun x => ENNReal.ofReal (max (f x) 0)) =
        (fun x => ENNReal.ofReal (f x)) := by
      funext x
      rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
      exact max_eq_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (f x) from bot_le)
    have hi : Integrable (fun x => max (f x) 0) μ :=
      (lintegral_ofReal_ne_top_iff_integrable
        (hfm.max measurable_const).aestronglyMeasurable
        (Eventually.of_forall (fun x => le_max_right (f x) 0))).mp (by rwa [he])
    apply hf
    apply (hi.sub hn).congr
    exact Eventually.of_forall (fun x => by
      dsimp only [Pi.sub_apply]
      by_cases hx : 0 ≤ f x
      · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
        ring
      · rw [max_eq_right (le_of_not_ge hx), max_eq_left (by linarith)]
        ring)
  unfold equilibriumExtendedIntegral
  rw [hp, EReal.coe_ennreal_top]
  apply EReal.top_sub
  exact fun h => equilibriumExtendedIntegral_negative_ne_top hn
    (EReal.coe_ennreal_eq_top_iff.mp h)

/-- Adding an integrable real function to make the integrand nonnegative gives
exactly the same extended signed integral after subtracting its finite integral.
The identity covers infinite positive integrals, not just ordinary finite ones. -/
theorem equilibriumExtendedIntegral_eq_shifted {μ : Measure α} {f k : α → ℝ}
    (hfm : Measurable f) (hn : Integrable (fun x => max (-f x) 0) μ)
    (hk : Integrable k μ) (hshift : ∀ x, 0 ≤ f x + k x) :
    equilibriumExtendedIntegral μ f =
      ((∫⁻ x, ENNReal.ofReal (f x + k x) ∂μ) : EReal) - (∫ x, k x ∂μ : ℝ) := by
  by_cases hf : Integrable f μ
  · have hs := hf.add hk
    have he : ((∫⁻ x, ENNReal.ofReal (f x + k x) ∂μ) : EReal) =
        (∫ x, f x + k x ∂μ : ℝ) := by
      have hi := ofReal_integral_eq_lintegral_ofReal hs (Eventually.of_forall hshift)
      dsimp only [Pi.add_apply] at hi
      rw [← hi, EReal.coe_ennreal_ofReal]
      have hnon : (0 : ℝ) ≤ ∫ x, f x + k x ∂μ := integral_nonneg hshift
      rw [max_eq_left hnon]
    rw [equilibriumExtendedIntegral_eq_integral hf, he, ← EReal.coe_sub,
      integral_add hf hk, add_sub_cancel_right]
  · have hs : ¬ Integrable (fun x => f x + k x) μ := by
      intro h
      apply hf
      apply (h.sub hk).congr
      exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply]; ring)
    have htop : (∫⁻ x, ENNReal.ofReal (f x + k x) ∂μ) = ∞ := by
      by_contra h
      exact hs ((lintegral_ofReal_ne_top_iff_integrable
        (hfm.aestronglyMeasurable.add hk.aestronglyMeasurable)
        (Eventually.of_forall hshift)).mp h)
    rw [equilibriumExtendedIntegral_eq_top_of_not_integrable hfm hn hf,
      htop, EReal.coe_ennreal_top, EReal.top_sub_coe]

end RepulsiveCoulomb
