import LeanResearch.RepulsiveCoulomb.PointCoreEntropyLayer

/-! The normalized defective entropy bound from actual smooth dyadic SPI. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointCore_normalized_entropy_of_spi {m : ℕ} {γ A B K : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hA : 0 < A) (hB : 0 < B)
    (hK0 : 0 ≤ K) (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    (hSPI : ∀ s : ℝ, 0 < s → ∀ ψ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, ψ x ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖gradient (ψ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B / s) * (∫ x, |ψ x| ∂pointMeasure γ a y) ^ 2)
    (φ : TestFunction (pointDomain a y) ℝ ⊤)
    (hφ : (∫ x, φ x ^ 2 ∂pointMeasure γ a y) = 1) :
    (∫ x, φ x ^ 2 * Real.log (φ x ^ 2) ∂pointMeasure γ a y) ≤
      192 * B * K ^ 2 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        (4 + 384 * A) * Real.log 2 := by
  obtain ⟨N, hb⟩ := testFunction_dyadic_bound (pointDomain a y) φ
  have hlayer := pointCore_entropy_layer_integral hγ ha y φ N hb
  have hp := pointCore_spi_truncation_sum hγ ha y hA hB hK0 hK hSPI φ hφ N
  have hneg : (∫ x, (-φ : TestFunction (pointDomain a y) ℝ ⊤) x ^ 2 ∂pointMeasure γ a y) = 1 := by
    change (∫ x, (-φ x) ^ 2 ∂pointMeasure γ a y) = 1
    simpa only [neg_sq] using hφ
  have hn := pointCore_spi_truncation_sum hγ ha y hA hB hK0 hK hSPI (-φ) hneg N
  rw [testFunction_neg_energy] at hn
  rw [hφ] at hlayer
  simp_rw [mul_add] at hlayer
  rw [Finset.sum_add_distrib] at hlayer
  have hsum := add_le_add hp hn
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 96 * Real.log 2 by positivity)
  have hupper := hlayer.trans (add_le_add le_rfl hscaled)
  have hid : 4 * Real.log 2 * 1 + 96 * Real.log 2 *
      ((B / Real.log 2 * K ^ 2 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) + 2 * A) +
        (B / Real.log 2 * K ^ 2 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) + 2 * A)) =
      192 * B * K ^ 2 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        (4 + 384 * A) * Real.log 2 := by
    field_simp
    <;> ring
  exact hupper.trans_eq hid

end RepulsiveCoulomb
