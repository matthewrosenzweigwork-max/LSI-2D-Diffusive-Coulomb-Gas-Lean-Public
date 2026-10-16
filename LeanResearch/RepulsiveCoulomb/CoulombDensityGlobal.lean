module

public import LeanResearch.RepulsiveCoulomb.CoulombDensityLocal

@[expose] public section

/-! Fixed-configuration-space global density domination. The constant may
 depend on particle number and temperature; no uniformity is asserted. -/
noncomputable section
open MeasureTheory Set
namespace RepulsiveCoulomb

def coulombDensityGlobalBound (N : ℕ) (β : ℝ) : ℝ :=
  (∫ z : CoulombConfig N, coulombWeight β z)⁻¹ *
    Real.exp ((coulombRadialExponent N β) ^ 2 / β)

theorem coulombDensityGlobalBound_pos {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    0 < coulombDensityGlobalBound N β :=
  mul_pos (inv_pos.mpr (coulombWeight_integral_pos hβ)) (Real.exp_pos _)

theorem coulombDensity_le_globalBound {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (z : CoulombConfig N) : coulombDensity N β z ≤ coulombDensityGlobalBound N β := by
  have he : Real.exp (-(β / 4) * ‖z‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖z‖])
  have hw := (coulombWeight_le_gaussian hβ z).trans
    (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
  rw [mul_one] at hw
  exact mul_le_mul_of_nonneg_left hw (inv_pos.mpr (coulombWeight_integral_pos hβ)).le

theorem coulombMeasure_le_globalVolume {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    coulombMeasure N β ≤ ENNReal.ofReal (coulombDensityGlobalBound N β) •
      (volume : Measure (CoulombConfig N)) := by
  rw [coulombMeasure_eq_withDensity hβ, ← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun z =>
    ENNReal.ofReal_le_ofReal (coulombDensity_le_globalBound hβ z))

def coulombVolumeToGibbsL2 {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Lp ℝ 2 (volume : Measure (CoulombConfig N)) →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (coulombMeasure_le_globalVolume hβ)

theorem coulombVolumeToGibbsL2_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℝ 2 (volume : Measure (CoulombConfig N))) :
    coulombVolumeToGibbsL2 hβ f =ᵐ[coulombMeasure N β] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (coulombMeasure_le_globalVolume hβ) f

end RepulsiveCoulomb
