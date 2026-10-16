import LeanResearch.RepulsiveCoulomb.PointCoreSmoothTruncation

/-! Finite actual-core energy sums inherit the disjoint-band bound. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace RepulsiveCoulomb

theorem pointCore_finite_truncation_energy {m : ℕ} {γ K : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hK0 : 0 ≤ K) (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∫ x, ‖gradient
      (pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) ≤
      K ^ 2 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) := by
  let _ := pointMeasure_isProbability hγ ha y
  let μ := pointMeasure γ a y
  let e : ℤ → ℝ≥0∞ := fun j => ∫⁻ x, ENNReal.ofReal
    (‖gradient (fun z => smoothDyadicTruncation ((2 : ℝ) ^ j) (φ z)) x‖ ^ 2) ∂μ
  have hall := dyadic_truncation_energy_sum hK0 hK (φ.contDiff.of_le (by simp)) μ
  change (∑' j, e j) ≤ _ at hall
  have hinj : Function.Injective (fun k : ℕ => ((k + 1 : ℕ) : ℤ)) := by
    intro i j h
    exact Nat.add_right_cancel (Int.ofNat.inj h)
  have hf : (∑ k ∈ Finset.range N, e ((k + 1 : ℕ) : ℤ)) ≤
      ENNReal.ofReal (K ^ 2) * ∫⁻ x, ENNReal.ofReal (‖gradient (φ : ℂ → ℝ) x‖ ^ 2) ∂μ :=
    (ENNReal.sum_le_tsum _).trans ((ENNReal.tsum_comp_le_tsum_of_injective hinj e).trans hall)
  have heq (k : ℕ) : ENNReal.ofReal
      (∫ x, ‖gradient (pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) φ : ℂ → ℝ) x‖ ^ 2 ∂μ) =
      e ((k + 1 : ℕ) : ℤ) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (testFunction_physical_energy_integrable _ (pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) φ) μ)
      (Eventually.of_forall (fun _ => sq_nonneg _))]
    simp only [e, zpow_natCast]
    rfl
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg K) (integral_nonneg (fun _ => sq_nonneg _)))).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.ofReal_mul (sq_nonneg K), ofReal_integral_eq_lintegral_ofReal
      (testFunction_physical_energy_integrable _ φ μ) (Eventually.of_forall (fun _ => sq_nonneg _))]
  change (∑ k ∈ Finset.range N, ENNReal.ofReal (∫ x, ‖gradient (pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) φ : ℂ → ℝ) x‖ ^ 2 ∂μ)) ≤ _
  simpa only [heq] using hf

end RepulsiveCoulomb
