import LeanResearch.RepulsiveCoulomb.PointMeasureParametric

/-! Actual Tonelli factorization of the unnormalized full labeled density. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coulomb_raw_one_site_lintegral {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    {F : CoulombConfig (N + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, ENNReal.ofReal (coulombWeight β z) * F z) =
      ∫⁻ y : CoulombConfig N,
        ENNReal.ofReal (coulombWeightAtExponent β (β / ((N + 1 : ℕ) : ℝ)) y) *
        ∫⁻ w : ℂ, ENNReal.ofReal (pointWeight β
          (fun _ : Fin N => β / ((N + 1 : ℕ) : ℝ)) (fun j => y j) w) * F (coulombInsertZero w y) := by
  have hw := (coulombWeight_continuous (N := N + 1) hβ).measurable.ennreal_ofReal.mul hF
  have hm := (coulombSplitZero_measurePreserving N).symm
  have he : ((coulombSplitZero N).symm : ℂ × CoulombConfig N → CoulombConfig (N + 1)) =
      fun p => coulombInsertZero p.1 p.2 := by
    funext p
    exact coulombSplitZero_symm_apply p.1 p.2
  have hpull := hm.lintegral_comp hw
  rw [he] at hpull
  dsimp only [Pi.mul_apply] at hpull
  rw [← hpull]
  have hprod : Measurable (fun p : ℂ × CoulombConfig N =>
      ENNReal.ofReal (coulombWeight β (coulombInsertZero p.1 p.2)) * F (coulombInsertZero p.1 p.2)) :=
    hw.comp (coulombInsertZero_measurable N)
  rw [Measure.volume_eq_prod ℂ (CoulombConfig N), lintegral_prod_symm (μ := volume) (ν := volume) _ hprod.aemeasurable]
  apply lintegral_congr
  intro y
  change (∫⁻ w : ℂ, ENNReal.ofReal (coulombWeight β (coulombInsertZero w y)) * F (coulombInsertZero w y)) = _
  simp_rw [coulombWeight_one_site_factorization,
    ENNReal.ofReal_mul (coulombWeightAtExponent_nonneg β (β / ((N + 1 : ℕ) : ℝ)) y), mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end RepulsiveCoulomb
