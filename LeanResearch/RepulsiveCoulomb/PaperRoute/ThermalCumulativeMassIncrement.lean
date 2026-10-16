import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCumulativeMass
import Mathlib.MeasureTheory.Measure.Real

/-! Actual annular cumulative-mass control from
density domination and the physical planar ball volume. No radiality,
probability, differentiability or desired Lipschitz conclusion is assumed. -/
noncomputable section
open MeasureTheory Real Set Metric
open scoped ENNReal
namespace RepulsiveCoulomb.PaperRoute

theorem cumulativeMass_increment_le_of_density_bound
    {ρ : ℂ → ℝ} {M s r : ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hs : 0 ≤ s) (hsr : s ≤ r) :
    0 ≤ equilibriumCumulativeMass (equilibriumDensityMeasure ρ) r -
      equilibriumCumulativeMass (equilibriumDensityMeasure ρ) s ∧
    equilibriumCumulativeMass (equilibriumDensityMeasure ρ) r -
      equilibriumCumulativeMass (equilibriumDensityMeasure ρ) s ≤
        Real.pi * M * (r^2-s^2) := by
  let μ : Measure ℂ := equilibriumDensityMeasure ρ
  let ν : Measure ℂ := ENNReal.ofReal M • (volume : Measure ℂ)
  let A : Set ℂ := ball (0 : ℂ) r \ ball (0 : ℂ) s
  have hM : 0 ≤ M := (hρ0 0).trans (hρM 0)
  have hr : 0 ≤ r := hs.trans hsr
  have hdom : μ ≤ ν := equilibriumDensityMeasure_le_volume hρM
  have hsub : ball (0 : ℂ) s ⊆ ball (0 : ℂ) r := ball_subset_ball hsr
  have hνfin : ν (ball (0 : ℂ) r) ≠ ∞ := by
    dsimp only [ν]
    rw [Measure.smul_apply, smul_eq_mul, Complex.volume_ball]
    finiteness
  have hμfin : μ (ball (0 : ℂ) r) ≠ ∞ :=
    ne_top_of_le_ne_top hνfin (hdom (ball 0 r))
  have hvfin : (volume : Measure ℂ) (ball (0 : ℂ) r) ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  have hνAfin : ν A ≠ ∞ := measure_ne_top_of_subset sdiff_subset hνfin
  have hμdiff : μ.real A = μ.real (ball (0 : ℂ) r) - μ.real (ball (0 : ℂ) s) :=
    measureReal_sdiff hsub measurableSet_ball hμfin
  have hvdiff : (volume : Measure ℂ).real A =
      (volume : Measure ℂ).real (ball (0 : ℂ) r) -
        (volume : Measure ℂ).real (ball (0 : ℂ) s) :=
    measureReal_sdiff hsub measurableSet_ball hvfin
  have hbound : μ.real A ≤ M * (volume : Measure ℂ).real A := by
    have h := ENNReal.toReal_mono hνAfin (hdom A)
    simpa only [measureReal_def, ν, Measure.smul_apply, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using h
  have hvol (t : ℝ) (ht : 0 ≤ t) :
      (volume : Measure ℂ).real (ball (0 : ℂ) t) = Real.pi * t^2 := by
    simp only [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal ht, ENNReal.coe_toReal,
      NNReal.coe_real_pi]
    ring
  change 0 ≤ μ.real (ball (0 : ℂ) r) - μ.real (ball (0 : ℂ) s) ∧
    μ.real (ball (0 : ℂ) r) - μ.real (ball (0 : ℂ) s) ≤ Real.pi * M * (r^2-s^2)
  constructor
  · rw [← hμdiff]
    exact measureReal_nonneg
  · rw [← hμdiff]
    calc
      μ.real A ≤ M * (volume : Measure ℂ).real A := hbound
      _ = Real.pi * M * (r^2-s^2) := by
        rw [hvdiff, hvol r hr, hvol s hs]
        ring

end RepulsiveCoulomb.PaperRoute
