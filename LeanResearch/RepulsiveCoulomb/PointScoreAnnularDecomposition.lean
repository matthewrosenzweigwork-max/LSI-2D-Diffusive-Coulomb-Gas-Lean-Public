module

public import LeanResearch.RepulsiveCoulomb.DyadicScoreCover

@[expose] public section

/-! Actual good/bad score decomposition on a radial annulus. The score-energy
integrability premise is explicit and must be discharged on the original core. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointScore_annular_mass_decomposition {m : ℕ} {γ R : ℝ}
    (hγ : 0 < γ) (hR : 0 < R) (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ψ : ℂ → ℝ) (hψ : Continuous ψ)
    (hscore : Integrable (fun x => ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2)) :
    R ^ 2 * (∫ x in scoreRadialAnnulus R, ψ x ^ 2) ≤
      (4 / γ ^ 2) * (∫ x in enlargedScoreAnnulus R, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2) +
      R ^ 2 * (∫ x in pointScoreBadAnnulus γ a y R, ψ x ^ 2) := by
  let A := scoreRadialAnnulus R
  let B := pointScoreBadAnnulus γ a y R
  let G := A \ B
  have hB : MeasurableSet B := pointScoreBadAnnulus_measurable γ a y R
  have hG : MeasurableSet G := (scoreRadialAnnulus_measurable R).diff hB
  have hsub : B ⊆ A := fun x hx => ⟨hx.1, hx.2.1⟩
  have hi : IntegrableOn (fun x => ψ x ^ 2) A :=
    (continuous_integrableOn_enlargedScoreAnnulus (hψ.pow 2) R).mono_set
      (scoreRadialAnnulus_subset_enlarged hR)
  have hsplit := setIntegral_sdiff hB hi hsub
  have hgood : R ^ 2 * (∫ x in G, ψ x ^ 2) ≤
      (4 / γ ^ 2) * (∫ x in G, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_mono_on ((hi.mono_set sdiff_subset).const_mul (R ^ 2))
      ((hscore.integrableOn).const_mul (4 / γ ^ 2)) hG
    intro x hx
    have hs : γ * R / 2 ≤ ‖pointScore γ a y x‖ := by
      by_contra h
      exact hx.2 ⟨hx.1.1, hx.1.2, lt_of_not_ge h⟩
    simpa only [mul_assoc] using pointScore_good_quadratic_bound hγ hR a y x (ψ x) hs
  have hscorele : (∫ x in G, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2) ≤
      ∫ x in enlargedScoreAnnulus R, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2 := by
    apply setIntegral_mono_set hscore.integrableOn
      (Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    exact Eventually.of_forall (fun x hx => scoreRadialAnnulus_subset_enlarged hR hx.1)
  have hgood' := hgood.trans (mul_le_mul_of_nonneg_left hscorele (by positivity))
  change (∫ x in G, ψ x ^ 2) = (∫ x in A, ψ x ^ 2) - (∫ x in B, ψ x ^ 2) at hsplit
  change R ^ 2 * (∫ x in A, ψ x ^ 2) ≤ _ + R ^ 2 * (∫ x in B, ψ x ^ 2)
  rw [hsplit] at hgood'
  nlinarith

end RepulsiveCoulomb
