import LeanResearch.RepulsiveCoulomb.PaperRoute.CylindricalTraceLabeledPoincare
import LeanResearch.RepulsiveCoulomb.PaperRoute.CollisionLaplacianCalculus

/-! Additive original-paper producer. Full-space cylindrical logarithmic fundamental solution.
Normal planar delta production, tangential compact IBP and justified Fubini
are actual theorem applications; no distributional certificate is assumed. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb.PaperRoute

theorem cylindrical_normal_pairing {N : ℕ}
    {φ : CoulombConfig (N + 1) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z : CoulombConfig (N + 1), planarLogKernel (z 0) * collisionNormalLaplacian φ z) =
      (-2 * Real.pi) * ∫ y : CoulombConfig N, φ (coulombInsertZero 0 y) := by
  have hc := collisionNormalLaplacian_continuous hφ
  have hs := collisionNormalLaplacian_compact hφc
  have hi := cylindrical_log_test_integrable_prod hc hs
  rw [cylindrical_log_test_integral_split hc hs, integral_integral_swap hi]
  calc
    _ = ∫ y : CoulombConfig N, (-2 * Real.pi) * φ (coulombInsertZero 0 y) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        simp_rw [collision_normal_trace_slice hφ]
        exact (cylindrical_normal_slice_fundamental hφ hφc y).2)
    _ = _ := integral_const_mul _ _

theorem cylindrical_tangent_pairing_zero {N : ℕ}
    {φ : CoulombConfig (N + 1) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z : CoulombConfig (N + 1), planarLogKernel (z 0) * collisionTangentLaplacian φ z) = 0 := by
  have hc := collisionTangentLaplacian_continuous hφ
  have hs := collisionTangentLaplacian_compact hφc
  rw [cylindrical_log_test_integral_split hc hs]
  have hz (u : ℂ) :
      (∫ y : CoulombConfig N, Laplacian.laplacian (fun ξ => φ (coulombInsertZero u ξ)) y) = 0 :=
    CollisionCalculus.integral_laplacian_eq_zero
      (hφ.comp (collision_tangent_insert_contDiff u))
      (hφc.comp_isClosedEmbedding (cylindrical_tangent_insert_isometry u).isClosedEmbedding)
  simp_rw [collision_tangent_trace_slice hφ, integral_const_mul, hz, mul_zero]
  exact integral_zero _ _

/-- Genuine distributional normal-coordinate identity for every compact C2
full-space real test, including tests crossing the collision hyperplane. -/
theorem cylindrical_log_fundamental_solution {N : ℕ}
    {φ : CoulombConfig (N + 1) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : CoulombConfig (N + 1) => planarLogKernel (z 0) * Laplacian.laplacian φ z) ∧
    (∫ z : CoulombConfig (N + 1), planarLogKernel (z 0) * Laplacian.laplacian φ z) =
      (-2 * Real.pi) * ∫ y : CoulombConfig N, φ (coulombInsertZero 0 y) := by
  have hiN := cylindrical_log_test_integrable (collisionNormalLaplacian_continuous hφ)
    (collisionNormalLaplacian_compact hφc)
  have hiT := cylindrical_log_test_integrable (collisionTangentLaplacian_continuous hφ)
    (collisionTangentLaplacian_compact hφc)
  have he : (fun z : CoulombConfig (N + 1) => planarLogKernel (z 0) * Laplacian.laplacian φ z) =
      (fun z => planarLogKernel (z 0) * collisionNormalLaplacian φ z) +
      (fun z => planarLogKernel (z 0) * collisionTangentLaplacian φ z) := by
    funext z
    rw [collisionConfig_laplacian_split hφ, mul_add]
    rfl
  rw [he]
  refine ⟨hiN.add hiT, ?_⟩
  change (∫ z : CoulombConfig (N + 1), planarLogKernel (z 0) * collisionNormalLaplacian φ z +
    planarLogKernel (z 0) * collisionTangentLaplacian φ z) = _
  rw [integral_add hiN hiT, cylindrical_normal_pairing hφ hφc,
    cylindrical_tangent_pairing_zero hφ hφc, add_zero]

end RepulsiveCoulomb.PaperRoute
