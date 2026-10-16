import LeanResearch.RepulsiveCoulomb.CoulombPairGradientSum
import LeanResearch.RepulsiveCoulomb.CoulombFormSwap

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombForm_pair_gradient_integrable (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) (i j : Fin N) :
    Integrable (fun z => ‖coulombFormGradientL N hβ u z i - coulombFormGradientL N hβ u z j‖ ^ 2)
      (coulombMeasure N β) :=
  ((Lp.memLp (coulombFormGradientL N hβ u)).continuousLinearMap_comp
    (coulombCoordinate i - coulombCoordinate j)).norm.integrable_sq

theorem coulombForm_pair_gradient_sum_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) :
    (∑ p ∈ coulombPairs N, ∫ z, ‖coulombFormGradientL N hβ u z p.1 -
      coulombFormGradientL N hβ u z p.2‖ ^ 2 ∂coulombMeasure N β) ≤
        (N : ℝ) * coulombFormEnergy N hβ u := by
  have hi := integrable_finsetSum (coulombPairs N)
    (fun p _ => coulombForm_pair_gradient_integrable N hβ u p.1 p.2)
  have h := integral_mono hi ((coulombFormGradient_square_integrable N hβ u).const_mul (N : ℝ))
    (fun z => coulomb_pair_norm_sq_sum_le (coulombFormGradientL N hβ u z))
  have he : (∫ z, ∑ p ∈ coulombPairs N, ‖coulombFormGradientL N hβ u z p.1 -
      coulombFormGradientL N hβ u z p.2‖ ^ 2 ∂coulombMeasure N β) =
      ∑ p ∈ coulombPairs N, ∫ z, ‖coulombFormGradientL N hβ u z p.1 -
        coulombFormGradientL N hβ u z p.2‖ ^ 2 ∂coulombMeasure N β :=
    integral_finsetSum _ (fun p _ => coulombForm_pair_gradient_integrable N hβ u p.1 p.2)
  rw [he, integral_const_mul, ← coulombFormEnergy_eq_integral] at h
  exact h

theorem coulombForm_pair_gradient_norm_sum_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (N + 2) hβ) :
    (∑ p ∈ coulombPairs (N + 2), ‖coulombFormPairGradientL (N + 2) hβ p.1 p.2 u‖ ^ 2) ≤
      ((N + 2 : ℕ) : ℝ) * coulombFormEnergy (N + 2) hβ u := by
  simp_rw [coulombFormPairGradientL_norm_eq_integral N hβ]
  exact coulombForm_pair_gradient_sum_le (N + 2) hβ u

end RepulsiveCoulomb

