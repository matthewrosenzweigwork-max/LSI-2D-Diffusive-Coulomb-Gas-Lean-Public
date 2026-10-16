module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.CylindricalDiracLabeledPoincare

@[expose] public section

/-! Additive original-paper producer. The actual many-particle pair-collision distributional row,
with the unit normal coordinate and its literal tangential Dirac measure.
All tests are compact C2 functions on the full physical Euclidean space. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb.PaperRoute

theorem paper_pair_normal_log_fundamental {N : ℕ}
    (i j : Fin (N + 2)) (hij : i ≠ j)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => planarLogKernel (paperPairNormalChart i j hij z 0) * Laplacian.laplacian φ z) ∧
    (∫ z : CoulombConfig (N + 2), planarLogKernel (paperPairNormalChart i j hij z 0) *
      Laplacian.laplacian φ z) =
        (-2 * Real.pi) * ∫ y : CoulombConfig (N + 1), φ (paperPairNormalTrace i j hij y) := by
  let e := paperPairNormalChart i j hij
  let ψ : CoulombConfig (N + 2) → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ 2 ψ := hφ.comp e.symm.toContinuousLinearEquiv.contDiff
  have hψc : HasCompactSupport ψ := hφc.comp_isClosedEmbedding e.symm.isometry.isClosedEmbedding
  have hLap := CollisionCalculus.laplacian_comp_linearIsometryEquiv e.symm hφ
  have h := cylindrical_log_fundamental_solution hψ hψc
  have he : (fun z : CoulombConfig (N + 2) => planarLogKernel (e z 0) *
      Laplacian.laplacian ψ (e z)) =
      (fun z => planarLogKernel (e z 0) * Laplacian.laplacian φ z) := by
    funext z
    rw [hLap]
    simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  have hi := e.measurePreserving.integrable_comp_of_integrable h.1
  have hchange := e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding
    (fun z : CoulombConfig (N + 2) => planarLogKernel (z 0) * Laplacian.laplacian ψ z)
  change Integrable (fun z => planarLogKernel (e z 0) * Laplacian.laplacian ψ (e z)) at hi
  rw [he] at hi
  change (∫ z, planarLogKernel (e z 0) * Laplacian.laplacian ψ (e z)) = _ at hchange
  rw [he] at hchange
  refine ⟨hi, ?_⟩
  exact hchange.trans h.2

/-- Literal `Delta log|z_i-z_j| = 2*pi*delta_0((z_i-z_j)/sqrt(2))`.
The right-hand measure includes tangential Lebesgue volume. -/
theorem paper_pair_collision_dirac {N : ℕ}
    (i j : Fin (N + 2)) (hij : i ≠ j)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : CoulombConfig (N + 2) => Real.log ‖z i - z j‖ * Laplacian.laplacian φ z) ∧
    Integrable φ (paperPairNormalDirac i j hij) ∧
    (∫ z : CoulombConfig (N + 2), Real.log ‖z i - z j‖ * Laplacian.laplacian φ z) =
      (2 * Real.pi) * ∫ z, φ z ∂paperPairNormalDirac i j hij := by
  obtain ⟨hiF, hF⟩ := paper_pair_normal_log_fundamental i j hij hφ hφc
  have hiΔ := CollisionCalculus.integrable_laplacian (μ := volume) hφ hφc
  have hiC := hiΔ.const_mul (Real.log (Real.sqrt 2))
  have he : (fun z : CoulombConfig (N + 2) => Real.log ‖z i - z j‖ * Laplacian.laplacian φ z) =ᵐ[volume]
      (fun z => Real.log (Real.sqrt 2) * Laplacian.laplacian φ z -
        planarLogKernel (paperPairNormalChart i j hij z 0) * Laplacian.laplacian φ z) := by
    filter_upwards [paper_pair_log_unit_normal_ae i j hij] with z hz
    rw [hz]
    unfold planarLogKernel
    ring
  have hi := (hiC.sub hiF).congr he.symm
  refine ⟨hi, paperPairNormalDirac_test_integrable i j hij hφ.continuous hφc, ?_⟩
  rw [integral_congr_ae he, integral_sub hiC hiF, integral_const_mul,
    CollisionCalculus.integral_laplacian_eq_zero hφ hφc, mul_zero, zero_sub, hF,
    paperPairNormalDirac_integral i j hij hφ.continuous]
  ring

end RepulsiveCoulomb.PaperRoute
