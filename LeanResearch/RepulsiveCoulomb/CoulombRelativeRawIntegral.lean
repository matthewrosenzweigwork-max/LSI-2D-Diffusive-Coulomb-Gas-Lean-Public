import LeanResearch.RepulsiveCoulomb.CoulombRelativeKernel

/-! Tonelli factorization in actual center-frozen relative coordinates. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def coulombRelativeFrozenWeight (N : ℕ) (β : ℝ) (p : ℂ × CoulombConfig N) : ℝ :=
  coulombRelativeScale N (β / ((N + 2 : ℕ) : ℝ)) *
    Real.exp (-β * ‖p.1‖ ^ 2 / 2) *
      coulombWeightAtExponent β (β / ((N + 2 : ℕ) : ℝ)) p.2

theorem coulombRelativeFrozenWeight_nonneg (N : ℕ) (β : ℝ) (p : ℂ × CoulombConfig N) :
    0 ≤ coulombRelativeFrozenWeight N β p :=
  mul_nonneg (mul_nonneg (coulombRelativeScale_pos N _).le (Real.exp_pos _).le)
    (coulombWeightAtExponent_nonneg _ _ _)

theorem coulombRelativeFrozenWeight_continuous (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    Continuous (coulombRelativeFrozenWeight N β) := by
  exact (continuous_const.mul (by fun_prop)).mul
    ((coulombWeightAtExponent_continuous β (div_nonneg hβ (Nat.cast_nonneg _))).comp continuous_snd)

theorem coulombRelativeInsert_joint_measurable (N : ℕ) :
    Measurable (fun p : (ℂ × CoulombConfig N) × ℂ => coulombRelativeInsert p.1.1 p.2 p.1.2) := by
  have he : (fun p : (ℂ × CoulombConfig N) × ℂ => coulombRelativeInsert p.1.1 p.2 p.1.2) =
      (coulombRelativeFrozenFirst N).symm := by
    funext p
    exact (coulombRelativeFrozenFirst_symm_apply p.1 p.2).symm
  rw [he]
  exact (coulombRelativeFrozenFirst N).symm.measurable

theorem coulomb_raw_relative_lintegral {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    {F : CoulombConfig (N + 2) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, ENNReal.ofReal (coulombWeight β z) * F z) =
      ∫⁻ p : ℂ × CoulombConfig N, ENNReal.ofReal (coulombRelativeFrozenWeight N β p) *
        ∫⁻ u : ℂ, ENNReal.ofReal (pointWeight β (coulombRelativeExponents N β)
          (coulombRelativeRoots p.1 p.2) u) * F (coulombRelativeInsert p.1 u p.2) := by
  have hw := (coulombWeight_continuous (N := N + 2) hβ).measurable.ennreal_ofReal.mul hF
  have hm := (coulombRelativeFrozenFirst_measurePreserving N).symm
  have he : ((coulombRelativeFrozenFirst N).symm : (ℂ × CoulombConfig N) × ℂ → CoulombConfig (N + 2)) =
      fun p => coulombRelativeInsert p.1.1 p.2 p.1.2 := by
    funext p
    exact coulombRelativeFrozenFirst_symm_apply p.1 p.2
  have hpull := hm.lintegral_comp hw
  rw [he] at hpull
  dsimp only [Pi.mul_apply] at hpull
  rw [← hpull]
  have hprod : Measurable (fun p : (ℂ × CoulombConfig N) × ℂ =>
      ENNReal.ofReal (coulombWeight β (coulombRelativeInsert p.1.1 p.2 p.1.2)) *
        F (coulombRelativeInsert p.1.1 p.2 p.1.2)) :=
    hw.comp (coulombRelativeInsert_joint_measurable N)
  rw [Measure.volume_eq_prod (ℂ × CoulombConfig N) ℂ,
    lintegral_prod (μ := volume) (ν := volume) _ hprod.aemeasurable]
  apply lintegral_congr
  intro p
  change (∫⁻ u : ℂ, ENNReal.ofReal (coulombWeight β (coulombRelativeInsert p.1 u p.2)) *
    F (coulombRelativeInsert p.1 u p.2)) = _
  have hfactor (u : ℂ) : coulombWeight β (coulombRelativeInsert p.1 u p.2) =
      coulombRelativeFrozenWeight N β p *
        pointWeight β (coulombRelativeExponents N β) (coulombRelativeRoots p.1 p.2) u :=
    coulombWeight_relative_factorization β p.1 u p.2
  simp_rw [hfactor, ENNReal.ofReal_mul (coulombRelativeFrozenWeight_nonneg N β p), mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end RepulsiveCoulomb

