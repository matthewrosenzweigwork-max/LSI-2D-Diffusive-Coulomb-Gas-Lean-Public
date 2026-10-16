import LeanResearch.RepulsiveCoulomb.DbarBranchWirtingerAlgebra
import LeanResearch.RepulsiveCoulomb.CoulombDbarCore
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Actual compact-support integration by parts for complex test functions and
the literal dbar/partial operators. Every split integral has an integrability
proof; these identities do not rely on the default value of a Bochner integral. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ComplexConjugate
namespace RepulsiveCoulomb

theorem dbarComplexCore_directional_product_integrable {N : ℕ}
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) (v : CoulombConfig N) :
    Integrable (fun z => φ z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z v) volume := by
  have hd : Continuous (fun z => fderiv ℝ (ψ : CoulombConfig N → ℂ) z v) :=
    (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (φ.continuous.mul hd).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right

theorem dbarComplexCore_directional_ibp {N : ℕ}
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) (v : CoulombConfig N) :
    (∫ z, φ z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z v) =
      -(∫ z, fderiv ℝ (φ : CoulombConfig N → ℂ) z v * ψ z) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (dbarComplexCore_directional_product_integrable ψ φ v).congr
      (Eventually.of_forall fun z => mul_comm _ _)
  · exact dbarComplexCore_directional_product_integrable φ ψ v
  · exact (φ.continuous.mul ψ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  · intro z _
    exact φ.contDiff.differentiable (by simp) z
  · intro z _
    exact ψ.contDiff.differentiable (by simp) z

theorem dbarComplexCore_integral_coordinate_split {N : ℕ}
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) (i : Fin N) :
    (∫ z, φ z * coulombDbarCoordinate ψ z i) = (1 / 2 : ℂ) *
      ((∫ z, φ z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z (coulombCoordinateInjection N i 1)) +
        Complex.I * (∫ z, φ z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z (coulombCoordinateInjection N i Complex.I))) := by
  calc
    _ = ∫ z, (1 / 2 : ℂ) *
        ((φ z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z (coulombCoordinateInjection N i 1)) +
          Complex.I * (φ z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z (coulombCoordinateInjection N i Complex.I))) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by dsimp only [coulombDbarCoordinate]; ring
    _ = _ := by
      rw [integral_const_mul, integral_add
        (dbarComplexCore_directional_product_integrable φ ψ _)
        ((dbarComplexCore_directional_product_integrable φ ψ _).const_mul Complex.I), integral_const_mul]

theorem dbarComplexCore_bilinear_ibp {N : ℕ}
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) (i : Fin N) :
    (∫ z, φ z * coulombDbarCoordinate ψ z i) = -(∫ z, coulombDbarCoordinate φ z i * ψ z) := by
  have hx := dbarComplexCore_directional_ibp φ ψ (coulombCoordinateInjection N i 1)
  have hy := dbarComplexCore_directional_ibp φ ψ (coulombCoordinateInjection N i Complex.I)
  have hcomm (v : CoulombConfig N) :
      (∫ z, fderiv ℝ (φ : CoulombConfig N → ℂ) z v * ψ z) =
        ∫ z, ψ z * fderiv ℝ (φ : CoulombConfig N → ℂ) z v :=
    integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [hcomm] at hx hy
  have hbcomm : (∫ z, coulombDbarCoordinate φ z i * ψ z) =
      ∫ z, ψ z * coulombDbarCoordinate φ z i :=
    integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [hbcomm, dbarComplexCore_integral_coordinate_split, dbarComplexCore_integral_coordinate_split, hx, hy]
  ring

theorem dbarComplexCore_hermitian_ibp {N : ℕ}
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) (i : Fin N) :
    (∫ z, conj (φ z) * coulombDbarCoordinate ψ z i) =
      ∫ z, conj (-coulombDCoordinate φ z i) * ψ z := by
  let φc : TestFunction (coulombDomain N) ℂ ⊤ :=
    TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap φ
  have h := dbarComplexCore_bilinear_ibp φc ψ i
  have hφc : (φc : CoulombConfig N → ℂ) = fun z => conj (φ z) := rfl
  change (∫ z, conj (φ z) * coulombDbarCoordinate ψ z i) = _ at h
  rw [h, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [hφc, coulombDbarCoordinate_conj (φ.contDiff.differentiable (by simp) z)]
    simp only [map_neg, neg_mul]

end RepulsiveCoulomb
