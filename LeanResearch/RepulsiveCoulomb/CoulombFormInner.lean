import LeanResearch.RepulsiveCoulomb.CoulombClosedForm

/-! Polarization of the actual closed physical form norm. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
namespace RepulsiveCoulomb

def coulombFormEnergyPair (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u v : CoulombFormDomain N hβ) : ℝ :=
  inner ℝ (coulombFormGradientL N hβ u) (coulombFormGradientL N hβ v)

theorem coulombForm_inner_eq (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u v : CoulombFormDomain N hβ) :
    inner ℝ u v = inner ℝ (coulombFormValueL N hβ u) (coulombFormValueL N hβ v) +
      coulombFormEnergyPair N hβ u v := by
  have hu := coulombForm_norm_sq N hβ u
  have hv := coulombForm_norm_sq N hβ v
  have hs := coulombForm_norm_sq N hβ (u + v)
  simp only [coulombFormEnergy, map_add, norm_add_sq_real] at hu hv hs
  unfold coulombFormEnergyPair
  nlinarith only [hu, hv, hs]

theorem coulombFormValueL_norm_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) : ‖coulombFormValueL N hβ u‖ ≤ ‖u‖ := by
  have hn := coulombForm_norm_sq N hβ u
  have he := coulombFormEnergy_nonneg N hβ u
  nlinarith [norm_nonneg u, norm_nonneg (coulombFormValueL N hβ u)]

end RepulsiveCoulomb
