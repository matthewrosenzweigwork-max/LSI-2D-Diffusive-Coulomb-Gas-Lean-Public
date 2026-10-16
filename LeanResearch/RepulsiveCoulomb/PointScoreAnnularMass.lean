module

public import LeanResearch.RepulsiveCoulomb.PointScoreAnnulus
public import LeanResearch.RepulsiveCoulomb.AnnularCutoff
public import LeanResearch.RepulsiveCoulomb.PlanarRegionMass

@[expose] public section

/-! The actual exceptional-annulus mass estimate from the score area bound,
strictly supported smooth cutoff, Holder and Ladyzhenskaya. No local Poincare
or David--Semmes input occurs in this estimate. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointScoreAnnularMassConstant (γ Q : ℝ) : ℝ :=
  Real.sqrt (pointScoreBadAreaConstant γ Q) * (planarLadyzhenskayaConstant : ℝ)

theorem pointScoreAnnularMassConstant_nonneg (γ Q : ℝ) : 0 ≤ pointScoreAnnularMassConstant γ Q :=
  mul_nonneg (Real.sqrt_nonneg _) (NNReal.coe_nonneg _)

theorem pointScore_bad_annulus_mass_cutoff {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    R ^ 2 * (∫ x in pointScoreBadAnnulus γ a y R, ψ x ^ 2) ≤
      pointScoreAnnularMassConstant γ Q * R *
        Real.sqrt (∫ x : ℂ, (annularCutoff R x * ψ x) ^ 2) *
        Real.sqrt (∫ x : ℂ, ‖gradient (fun z => annularCutoff R z * ψ z) x‖ ^ 2) := by
  let v : ℂ → ℝ := fun x => annularCutoff R x * ψ x
  let E := pointScoreBadAnnulus γ a y R
  let K := pointScoreBadAreaConstant γ Q
  have hv : ContDiff ℝ 1 v := ((annularCutoff_contDiff R).of_le (by simp)).mul hψ
  have hc : HasCompactSupport v := (annularCutoff_hasCompactSupport hR).mul_right
  have hE : MeasurableSet E := pointScoreBadAnnulus_measurable γ a y R
  have hi : (∫ x in E, ψ x ^ 2) = ∫ x in E, v x ^ 2 := by
    apply setIntegral_congr_fun hE
    intro x hx
    have hcut := annularCutoff_one hR ⟨hx.1, hx.2.1.le⟩
    simp only [v, hcut, one_mul]
  have harea := pointScoreBadAnnulus_real_volume_le hγ hR ha y hQ
  have hK : 0 ≤ K := pointScoreBadAreaConstant_nonneg γ Q
  have hroot : Real.sqrt (volume.real E) ≤ Real.sqrt K / R := by
    apply (Real.sqrt_le_left (div_nonneg (Real.sqrt_nonneg _) hR.le)).mpr
    rw [div_pow, Real.sq_sqrt hK]
    exact harea
  have hscale : R ^ 2 * Real.sqrt (volume.real E) ≤ R * Real.sqrt K := by
    calc
      _ ≤ R ^ 2 * (Real.sqrt K / R) := mul_le_mul_of_nonneg_left hroot (sq_nonneg R)
      _ = _ := by field_simp
  have hreg := planar_region_mass_ladyzhenskaya hv hc E (pointScoreBadAnnulus_volume_ne_top hγ hR ha y hQ)
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
    _ = _ := by dsimp only [pointScoreAnnularMassConstant, K, v]; ring

end RepulsiveCoulomb
