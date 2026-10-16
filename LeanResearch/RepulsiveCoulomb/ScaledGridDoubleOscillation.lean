module

public import LeanResearch.RepulsiveCoulomb.RawPointDoubleOscillationScaling
public import LeanResearch.RepulsiveCoulomb.RawPointGradientScaling
public import LeanResearch.RepulsiveCoulomb.TriangularGridDoubleOscillation

@[expose] public section

/-! Actual mesh-rescaled PL double oscillation on any positive physical scale.
The only mesh condition is16h<=R, which vanishes in the fine-mesh limit. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def scaledTriangularGridInterpolant (h : ℝ) (v : (ℤ × ℤ) →₀ ℝ) (z : ℂ) : ℝ :=
  triangularGridInterpolant v (h⁻¹ • z)

theorem mass_sqrt_scaling (G M C : ℝ) (hG : 0 ≤ G) :
    ((G^2*M)*Real.sqrt ((G^2*M)*C))*G = G^4*(M*Real.sqrt (M*C)) := by
  rw [show (G^2*M)*C = G^2*(M*C) by ring, Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hG]
  ring

theorem ennreal_mass_sqrt_scaling (G M C : ℝ) (hG : 0 ≤ G) (hM : 0 ≤ M) :
    ENNReal.ofReal (G^4) * (2 * ENNReal.ofReal (M*Real.sqrt (M*C))) =
      2 * ENNReal.ofReal ((G^2*M)*Real.sqrt ((G^2*M)*C)) * ENNReal.ofReal G := by
  have hK : 0 ≤ (G^2*M)*Real.sqrt ((G^2*M)*C) :=
    mul_nonneg (mul_nonneg (sq_nonneg G) hM) (Real.sqrt_nonneg _)
  calc
    _ = 2 * ENNReal.ofReal (G^4*(M*Real.sqrt (M*C))) := by
      rw [ENNReal.ofReal_mul (pow_nonneg hG 4)]
      ring
    _ = 2 * ENNReal.ofReal (((G^2*M)*Real.sqrt ((G^2*M)*C))*G) := by rw [mass_sqrt_scaling G M C hG]
    _ = _ := by rw [ENNReal.ofReal_mul hK]; ring

theorem scaledTriangularGrid_double_oscillation {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (v : (ℤ × ℤ) →₀ ℝ) {h : ℝ} (hh : 0 < h) (x : ℂ) {R : ℝ} (hmesh : 16*h ≤ R) :
    let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R)
    let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
    (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |scaledTriangularGridInterpolant h v q.1 - scaledTriangularGridInterpolant h v q.2| ∂ν.prod ν) ≤
      2 * ENNReal.ofReal (M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q)) *
        ∫⁻ z in ball x (2*R), ENNReal.ofReal ‖gradient (scaledTriangularGridInterpolant h v) z‖ *
          ENNReal.ofReal (rawPointWeight a y z) := by
  let G := rawPointLengthScale a h
  let M' := (rawPointMeasure (fun j => 2*a j) (fun j => h⁻¹ • y j)).real (ball (h⁻¹ • x) (R/h))
  let ν' := (rawPointMeasure (fun j => 2*a j) (fun j => h⁻¹ • y j)).restrict (ball (h⁻¹ • x) (R/h))
  let D' := ∫⁻ q : ℂ × ℂ, ENNReal.ofReal |triangularGridInterpolant v q.1 - triangularGridInterpolant v q.2| ∂ν'.prod ν'
  let I' := ∫⁻ z in ball (h⁻¹ • x) (2*(R/h)), ENNReal.ofReal ‖gradient (triangularGridInterpolant v) z‖ *
    ENNReal.ofReal (rawPointWeight a (fun j => h⁻¹ • y j) z)
  have hG : 0 ≤ G := (rawPointLengthScale_pos a hh).le
  have hM' : 0 ≤ M' := ENNReal.toReal_nonneg
  have hsmall := triangularGrid_double_oscillation ha hQ (fun j => h⁻¹ • y j) v (h⁻¹ • x)
    ((le_div_iff₀ hh).mpr hmesh)
  change D' ≤ 2 * ENNReal.ofReal (M'*Real.sqrt (M'*pointGridRelativeIsoperimetricConstant Q)) * I' at hsmall
  dsimp only
  unfold scaledTriangularGridInterpolant
  rw [rawPoint_double_oscillation_scaling ha y hh (triangularGridInterpolant v)
    (triangularGridInterpolant_lipschitz v).continuous.measurable x R,
    rawPoint_gradient_ball_scaling a y (triangularGridInterpolant v) hh x (2*R),
    rawPointSquaredMeasure_ball_scaling ha y hh x R]
  rw [show (2*R)/h = 2*(R/h) by ring]
  change ENNReal.ofReal (G^4) * D' ≤
    2 * ENNReal.ofReal ((G^2*M')*Real.sqrt ((G^2*M')*pointGridRelativeIsoperimetricConstant Q)) *
      (ENNReal.ofReal G * I')
  calc
    _ ≤ ENNReal.ofReal (G^4) *
        (2 * ENNReal.ofReal (M'*Real.sqrt (M'*pointGridRelativeIsoperimetricConstant Q)) * I') := by gcongr
    _ = (ENNReal.ofReal (G^4) * (2 * ENNReal.ofReal (M'*Real.sqrt (M'*pointGridRelativeIsoperimetricConstant Q)))) * I' := by ring
    _ = _ := by rw [ennreal_mass_sqrt_scaling G M' _ hG hM']; ring

end RepulsiveCoulomb
