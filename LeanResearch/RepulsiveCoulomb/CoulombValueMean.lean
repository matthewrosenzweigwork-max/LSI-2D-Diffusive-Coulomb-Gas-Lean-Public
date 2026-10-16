import LeanResearch.RepulsiveCoulomb.CoulombValueRepresentation

/-! Actual Gibbs L2 means and variances, with no core restriction. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace ProbabilityTheory
open scoped Topology
namespace RepulsiveCoulomb

def coulombValueMeanL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp ℝ 2 (coulombMeasure (N + 2) β) →L[ℝ] ℝ :=
  innerSL ℝ (coulombFormValueL (N + 2) hβ (coulombConstantForm N hβ))

theorem coulombValueMeanL_eq_integral (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure (N + 2) β)) :
    coulombValueMeanL N hβ v = ∫ z, v z ∂coulombMeasure (N + 2) β := by
  change inner ℝ (coulombFormValueL (N + 2) hβ (coulombConstantForm N hβ)) v = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coulombConstantForm_value N hβ] with z hz
  rw [hz]
  simp

theorem coulombValue_norm_sq_eq_integral (N : ℕ) {β : ℝ}
    (v : Lp ℝ 2 (coulombMeasure (N + 2) β)) :
    ‖v‖ ^ 2 = ∫ z, (v z) ^ 2 ∂coulombMeasure (N + 2) β := by
  rw [coulomb_L2_norm_sq N]
  simp only [Real.norm_eq_abs, sq_abs]

theorem coulombValue_variance_eq_norm_mean (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure (N + 2) β)) :
    variance (v : CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) =
      ‖v‖ ^ 2 - (coulombValueMeanL N hβ v) ^ 2 := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  rw [variance_eq_sub (Lp.memLp v)]
  change (∫ z, v z ^ 2 ∂coulombMeasure (N + 2) β) -
    (∫ z, v z ∂coulombMeasure (N + 2) β) ^ 2 = _
  rw [← coulombValue_norm_sq_eq_integral, ← coulombValueMeanL_eq_integral]

theorem coulombValueMeanL_permute (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (σ : Equiv.Perm (Fin (N + 2))) (v : Lp ℝ 2 (coulombMeasure (N + 2) β)) :
    coulombValueMeanL N hβ (coulombValuePermuteL (N + 2) hβ σ v) = coulombValueMeanL N hβ v := by
  rw [coulombValueMeanL_eq_integral, coulombValueMeanL_eq_integral]
  calc
    _ = ∫ z, v (coulombPermute σ z) ∂coulombMeasure (N + 2) β :=
      integral_congr_ae (coulombValuePermuteL_coe (N + 2) hβ σ v)
    _ = _ := (coulombPermute_gibbs_preserving hβ.le σ).integral_comp
      (coulombPermute σ).toMeasurableEquiv.measurableEmbedding v

end RepulsiveCoulomb

