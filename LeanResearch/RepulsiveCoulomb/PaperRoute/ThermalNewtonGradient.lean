module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCumulativeMassIncrement
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNewtonC1

@[expose] public section

/-! Actual Lipschitz control of the physical
Newton gradient from bounded density and the proved annular mass increment.
No gradient-Lipschitz or Sobolev certificate is assumed. -/
noncomputable section
open MeasureTheory Real Metric Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace RepulsiveCoulomb.PaperRoute

def thermalNewtonGradient (μ : Measure ℂ) (x : ℂ) : ℂ :=
  (-(equilibriumCumulativeMass μ ‖x‖ / ‖x‖ ^ 2)) • x

theorem thermalNewtonGradient_zero (μ : Measure ℂ) : thermalNewtonGradient μ 0 = 0 := by
  simp only [thermalNewtonGradient, smul_zero]

/-- Scalar coefficient control, with each denominator strictly positive.
The assumptions are the smaller ball-mass bound and actual annular increment. -/
theorem thermal_radial_coefficient_variation {C r s a b : ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (hsr : s ≤ r)
    (hb0 : 0 ≤ b) (hb : b ≤ C * s ^ 2)
    (hab0 : 0 ≤ a - b) (hab : a - b ≤ C * (r ^ 2 - s ^ 2)) :
    |a / r ^ 2 - b / s ^ 2| * s ≤ 4 * C * (r - s) := by
  have hr : 0 < r := hs.trans_le hsr
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hdelta : 0 ≤ r ^ 2 - s ^ 2 := by nlinarith
  have hbq0 : 0 ≤ b / s ^ 2 := div_nonneg hb0 hs2.le
  have hbq : b / s ^ 2 ≤ C := (div_le_iff₀ hs2).mpr hb
  have hbs : b / s ^ 2 * s ^ 2 = b := div_mul_cancel₀ _ hs2.ne'
  have har : a / r ^ 2 * r ^ 2 = a := div_mul_cancel₀ _ hr2.ne'
  have hup : a / r ^ 2 - b / s ^ 2 ≤ C * (r ^ 2 - s ^ 2) / r ^ 2 := by
    apply (le_div_iff₀ hr2).mpr
    have h := mul_nonneg hbq0 hdelta
    nlinarith
  have hlo : b / s ^ 2 - a / r ^ 2 ≤ C * (r ^ 2 - s ^ 2) / r ^ 2 := by
    apply (le_div_iff₀ hr2).mpr
    have h := mul_le_mul_of_nonneg_right hbq hdelta
    nlinarith
  have habs : |a / r ^ 2 - b / s ^ 2| ≤ C * (r ^ 2 - s ^ 2) / r ^ 2 :=
    abs_le.mpr ⟨by linarith, hup⟩
  calc
    _ ≤ (C * (r ^ 2 - s ^ 2) / r ^ 2) * s := mul_le_mul_of_nonneg_right habs hs.le
    _ = (C * (r ^ 2 - s ^ 2) * s) / r ^ 2 := by ring
    _ ≤ 2 * C * (r - s) := by
      apply (div_le_iff₀ hr2).mpr
      have hp : 0 ≤ C * (r - s) ^ 2 * (2 * r + s) := by positivity
      nlinarith
    _ ≤ 4 * C * (r - s) := by nlinarith [mul_nonneg hC (sub_nonneg.mpr hsr)]

/-- Ordered-radius vector estimate, including the origin without an inverse-
radius singularity. -/
theorem thermalNewtonGradient_norm_sub_le_ordered {ρ : ℂ → ℝ} {M : ℝ}
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρM : ∀ z, ρ z ≤ M)
    (x y : ℂ) (hxy : ‖y‖ ≤ ‖x‖) :
    ‖thermalNewtonGradient (equilibriumDensityMeasure ρ) x -
      thermalNewtonGradient (equilibriumDensityMeasure ρ) y‖ ≤ 5 * (Real.pi * M) * ‖x - y‖ := by
  let μ := equilibriumDensityMeasure ρ
  let C : ℝ := Real.pi * M
  have hM : 0 ≤ M := (hρ0 0).trans (hρM 0)
  have hC : 0 ≤ C := mul_nonneg Real.pi_pos.le hM
  have hm (r : ℝ) (hr : 0 ≤ r) : equilibriumCumulativeMass μ r ≤ C * r ^ 2 := by
    simpa only [C, mul_comm M Real.pi] using equilibriumCumulativeMass_density_bound hρ0 hρM hr
  by_cases hy : y = 0
  · subst y
    rw [thermalNewtonGradient_zero, sub_zero, sub_zero]
    by_cases hx : x = 0
    · subst x
      simp only [thermalNewtonGradient_zero, norm_zero, mul_zero, le_refl]
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hq : equilibriumCumulativeMass μ ‖x‖ / ‖x‖ ^ 2 ≤ C :=
      (div_le_iff₀ (sq_pos_of_pos hr)).mpr (hm ‖x‖ hr.le)
    have hq0 : 0 ≤ equilibriumCumulativeMass μ ‖x‖ / ‖x‖ ^ 2 :=
      div_nonneg (equilibriumCumulativeMass_nonneg _ _) (sq_nonneg _)
    change ‖(-(equilibriumCumulativeMass μ ‖x‖ / ‖x‖ ^ 2)) • x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hq0]
    have h := mul_le_mul_of_nonneg_right hq (norm_nonneg x)
    change _ ≤ 5 * C * ‖x‖
    nlinarith [mul_nonneg hC (norm_nonneg x)]
  have hs : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hr : 0 < ‖x‖ := hs.trans_le hxy
  let a : ℝ := equilibriumCumulativeMass μ ‖x‖ / ‖x‖ ^ 2
  let b : ℝ := equilibriumCumulativeMass μ ‖y‖ / ‖y‖ ^ 2
  have ha0 : 0 ≤ a := div_nonneg (equilibriumCumulativeMass_nonneg _ _) (sq_nonneg _)
  have ha : a ≤ C := (div_le_iff₀ (sq_pos_of_pos hr)).mpr (hm ‖x‖ hr.le)
  have hincr := cumulativeMass_increment_le_of_density_bound hρ0 hρM hs.le hxy
  have hvar : |a - b| * ‖y‖ ≤ 4 * C * (‖x‖ - ‖y‖) :=
    thermal_radial_coefficient_variation hC hs hxy
      (equilibriumCumulativeMass_nonneg _ _) (hm ‖y‖ hs.le) hincr.1 hincr.2
  have hsplit : thermalNewtonGradient μ x - thermalNewtonGradient μ y =
      (-a) • (x - y) + (b - a) • y := by
    dsimp only [thermalNewtonGradient, a, b]
    module
  calc
    _ = ‖(-a) • (x - y) + (b - a) • y‖ := by rw [hsplit]
    _ ≤ ‖(-a) • (x - y)‖ + ‖(b - a) • y‖ := norm_add_le _ _
    _ = a * ‖x - y‖ + |a - b| * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_neg, abs_of_nonneg ha0, abs_sub_comm b a]
    _ ≤ C * ‖x - y‖ + 4 * C * (‖x‖ - ‖y‖) :=
      add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hvar
    _ ≤ 5 * C * ‖x - y‖ := by
      have h := mul_le_mul_of_nonneg_left (norm_sub_norm_le x y) (show 0 ≤ (4 : ℝ) * C by positivity)
      linarith

def thermalNewtonLipschitzConstant (M : ℝ) : ℝ≥0 := Real.toNNReal (5 * Real.pi * M)

theorem thermalNewtonGradient_lipschitz {ρ : ℂ → ℝ} {M : ℝ}
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρM : ∀ z, ρ z ≤ M) :
    LipschitzWith (thermalNewtonLipschitzConstant M)
      (thermalNewtonGradient (equilibriumDensityMeasure ρ)) := by
  have hM : 0 ≤ M := (hρ0 0).trans (hρM 0)
  have hC : 0 ≤ 5 * Real.pi * M := by positivity
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  have hcoef : (thermalNewtonLipschitzConstant M : ℝ) = 5 * Real.pi * M := Real.coe_toNNReal _ hC
  rw [hcoef]
  by_cases hxy : ‖y‖ ≤ ‖x‖
  · simpa only [mul_assoc] using thermalNewtonGradient_norm_sub_le_ordered hρ0 hρM x y hxy
  · have h := thermalNewtonGradient_norm_sub_le_ordered hρ0 hρM y x (le_of_not_ge hxy)
    simpa only [norm_sub_rev, mul_assoc] using h

theorem thermalNewtonGradient_riesz (μ : Measure ℂ) (x : ℂ) :
    innerSL ℝ (thermalNewtonGradient μ x) = equilibriumNewtonDerivative μ x := by
  simp only [thermalNewtonGradient, map_smul, equilibriumNewtonDerivative, neg_div]

/-- The already justified actual Newton derivative equals the Riesz transform
of the newly controlled physical gradient. -/
theorem thermalDensityPotential_fderiv_eq_newtonGradient {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y)
    (x : ℂ) : fderiv ℝ (equilibriumDensityPotential ρ) x =
      innerSL ℝ (thermalNewtonGradient (equilibriumDensityMeasure ρ) x) := by
  rw [thermalNewtonGradient_riesz]
  exact (equilibriumDensityPotential_hasFDerivAt_newton hρm hρ0 hρM hρi hρmass hρ2 hUrad x).fderiv

end RepulsiveCoulomb.PaperRoute
