module

public import LeanResearch.RepulsiveCoulomb.TruncationSPIWeighted
public import LeanResearch.RepulsiveCoulomb.FiniteTruncationEnergy

@[expose] public section

/-! Summed logarithmically weighted truncated masses, with finite defect. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointCore_spi_truncation_sum {m : ℕ} {γ A B K : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hA : 0 < A) (hB : 0 < B)
    (hK0 : 0 ≤ K) (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    (hSPI : ∀ s : ℝ, 0 < s → ∀ ψ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, ψ x ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖gradient (ψ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B / s) * (∫ x, |ψ x| ∂pointMeasure γ a y) ^ 2)
    (φ : TestFunction (pointDomain a y) ℝ ⊤)
    (hφ : (∫ x, φ x ^ 2 ∂pointMeasure γ a y) = 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, ((k : ℝ) + 1) *
      (∫ x, (pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) φ x) ^ 2 ∂pointMeasure γ a y)) ≤
      (B / Real.log 2) * K ^ 2 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) + 2 * A := by
  have h := Finset.sum_le_sum (s := Finset.range N)
    (fun k _ => pointCore_spi_weighted_truncation hγ ha y hA hB hSPI φ hφ k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  have he := pointCore_finite_truncation_energy hγ ha y hK0 hK φ N
  have hb := finite_dyadic_geometric_error N
  have hE := mul_le_mul_of_nonneg_left he (div_pos hB (Real.log_pos (by norm_num : (1 : ℝ) < 2))).le
  have hB' := mul_le_mul_of_nonneg_left hb hA.le
  nlinarith only [h, hE, hB']

theorem testFunction_neg_energy (Ω : TopologicalSpace.Opens ℂ)
    (φ : TestFunction Ω ℝ ⊤) (μ : Measure ℂ) :
    (∫ x, ‖gradient (-φ : TestFunction Ω ℝ ⊤) x‖ ^ 2 ∂μ) =
      ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂μ := by
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  have h := TauCeti.gradient_const_smul (𝕜 := ℝ) (f := (φ : ℂ → ℝ)) (x := x) (-1)
  have hn := congrArg (fun v : ℂ => ‖v‖ ^ 2) h
  simpa using hn

theorem testFunction_bounded (Ω : TopologicalSpace.Opens ℂ)
    (φ : TestFunction Ω ℝ ⊤) : ∃ M : ℝ, ∀ x, |φ x| ≤ M := by
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.exists_bound_of_continuousOn φ.continuous.continuousOn
  refine ⟨|M| + 1, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport (φ : ℂ → ℝ)
  · have h := hM x hx
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self M]
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    positivity

end RepulsiveCoulomb
