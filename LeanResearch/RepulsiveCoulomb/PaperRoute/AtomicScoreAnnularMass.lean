import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicScoreArea
import LeanResearch.RepulsiveCoulomb.AnnularIntegratedEnergy

/-! The new exceptional area feeds the actual Ladyzhenskaya, cutoff, Young and
physical-gradient localization argument, with its own new K constant.

Proof bodies are adapted from the corresponding frozen score/annular/moment
modules. This new application replaces every hardwired old weak-force, bad-area,
uncertainty and moment producer with the new finite-atomic maximal route.
Generic cutoff, overlap, integrability, ground-state and Fatou identities are
reused unchanged; actual proof-body dependencies are audited separately. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

def atomicScoreAnnularMassConstant (γ Q : ℝ) : ℝ :=
  Real.sqrt (atomicScoreBadAreaConstant γ Q) * (planarLadyzhenskayaConstant : ℝ)

theorem atomicScoreAnnularMassConstant_nonneg (γ Q : ℝ) : 0 ≤ atomicScoreAnnularMassConstant γ Q :=
  mul_nonneg (Real.sqrt_nonneg _) (NNReal.coe_nonneg _)

theorem atomic_pointScore_bad_annulus_mass_cutoff {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    R ^ 2 * (∫ x in pointScoreBadAnnulus γ a y R, ψ x ^ 2) ≤
      atomicScoreAnnularMassConstant γ Q * R *
        Real.sqrt (∫ x : ℂ, (annularCutoff R x * ψ x) ^ 2) *
        Real.sqrt (∫ x : ℂ, ‖gradient (fun z => annularCutoff R z * ψ z) x‖ ^ 2) := by
  let v : ℂ → ℝ := fun x => annularCutoff R x * ψ x
  let E := pointScoreBadAnnulus γ a y R
  let K := atomicScoreBadAreaConstant γ Q
  have hv : ContDiff ℝ 1 v := ((annularCutoff_contDiff R).of_le (by simp)).mul hψ
  have hc : HasCompactSupport v := (annularCutoff_hasCompactSupport hR).mul_right
  have hE : MeasurableSet E := pointScoreBadAnnulus_measurable γ a y R
  have hi : (∫ x in E, ψ x ^ 2) = ∫ x in E, v x ^ 2 := by
    apply setIntegral_congr_fun hE
    intro x hx
    have hcut := annularCutoff_one hR ⟨hx.1, hx.2.1.le⟩
    simp only [v, hcut, one_mul]
  have harea := atomic_pointScoreBadAnnulus_real_volume_le hγ hR ha y hQ
  have hK : 0 ≤ K := atomicScoreBadAreaConstant_nonneg γ Q
  have hroot : Real.sqrt (volume.real E) ≤ Real.sqrt K / R := by
    apply (Real.sqrt_le_left (div_nonneg (Real.sqrt_nonneg _) hR.le)).mpr
    rw [div_pow, Real.sq_sqrt hK]
    exact harea
  have hscale : R ^ 2 * Real.sqrt (volume.real E) ≤ R * Real.sqrt K := by
    calc
      _ ≤ R ^ 2 * (Real.sqrt K / R) := mul_le_mul_of_nonneg_left hroot (sq_nonneg R)
      _ = _ := by field_simp
  have hreg := planar_region_mass_ladyzhenskaya hv hc E (atomic_pointScoreBadAnnulus_volume_ne_top hγ hR ha y hQ)
  calc
    _ = R ^ 2 * ∫ x in E, v x ^ 2 := by rw [hi]
    _ ≤ R ^ 2 * (Real.sqrt (volume.real E) * (planarLadyzhenskayaConstant : ℝ) *
        Real.sqrt (∫ x : ℂ, v x ^ 2) * Real.sqrt (∫ x : ℂ, ‖gradient v x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hreg (sq_nonneg R)
    _ = (R ^ 2 * Real.sqrt (volume.real E)) * ((planarLadyzhenskayaConstant : ℝ) *
        Real.sqrt (∫ x : ℂ, v x ^ 2) * Real.sqrt (∫ x : ℂ, ‖gradient v x‖ ^ 2)) := by ring
    _ ≤ (R * Real.sqrt K) * ((planarLadyzhenskayaConstant : ℝ) *
        Real.sqrt (∫ x : ℂ, v x ^ 2) * Real.sqrt (∫ x : ℂ, ‖gradient v x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right hscale (mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    _ = _ := by dsimp only [atomicScoreAnnularMassConstant, K, v]; ring

theorem atomic_pointScore_bad_annulus_mass_young {m : ℕ} {γ Q R δ : ℝ}
    (hγ : 0 < γ) (hR : 0 < R) (hδ : 0 < δ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    R ^ 2 * (∫ x in pointScoreBadAnnulus γ a y R, ψ x ^ 2) ≤
      δ * R ^ 2 * (∫ x : ℂ, (annularCutoff R x * ψ x) ^ 2) +
      atomicScoreAnnularMassConstant γ Q ^ 2 / (4 * δ) *
        (∫ x : ℂ, ‖gradient (fun z => annularCutoff R z * ψ z) x‖ ^ 2) := by
  exact (atomic_pointScore_bad_annulus_mass_cutoff hγ hR ha y hQ ψ hψ).trans
    (sqrt_product_young (integral_nonneg (fun _ => sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _)) hδ)

theorem atomic_pointScore_bad_annulus_localized {R C γ Q δ : ℝ} {m : ℕ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖gradient (annularCutoff R) z‖ ≤ C / R)
    (hγ : 0 < γ) (hδ : 0 < δ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    R ^ 2 * (∫ x in pointScoreBadAnnulus γ a y R, ψ x ^ 2) ≤
      δ * R ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2) +
      atomicScoreAnnularMassConstant γ Q ^ 2 / (4 * δ) *
        (2 * (∫ x in enlargedScoreAnnulus R, ‖gradient ψ x‖ ^ 2) +
          2 * (C / R) ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2)) := by
  apply (atomic_pointScore_bad_annulus_mass_young hγ hR hδ ha y hQ ψ hψ).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (annular_product_mass_le hR hψ.continuous) (by positivity)
  · exact mul_le_mul_of_nonneg_left (annular_product_energy_le hR hC hbound hψ) (by positivity)

end RepulsiveCoulomb.PaperRoute
