import LeanResearch.RepulsiveCoulomb.EquilibriumBranchActualErrorMoments
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNelsonMarkov

/-! The actual Nelson tail bound for canonical A_N under the constructed
thermal product reference. Its moment input is the instantiated generic
correlation theorem, not an assumed exponential or partition estimate. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumPartitionTailConstant (T : ℝ) (k m : ℕ) : ℝ :=
  (2 * T) ^ (2 * k * m) * equilibriumCanonicalErrorMomentConstant k m

theorem equilibriumPartitionTailConstant_pos {T : ℝ} (hT : 0 < T) (k m : ℕ) :
    0 < equilibriumPartitionTailConstant T k m :=
  mul_pos (pow_pos (by positivity) _) (equilibriumCanonicalErrorMomentConstant_pos k m)

/-- Uniform actual probability tail for every N>=2, beta>0, 0<=t<=T and s>=1.
The first term uses the stronger N^(-2m) from the finite-list moment theorem. -/
theorem equilibriumReference_actual_nelson_tail {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N k m : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (hm : 1 ≤ m)
    {T t s : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) (hs : 1 ≤ s) :
    (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)))
      {z : Fin N → ℂ | s < -t * equilibriumModulatedEnergy R.density z} ≤
      ENNReal.ofReal (equilibriumPartitionTailConstant T k m *
        ((N : ℝ) ^ (-((2 * m : ℕ) : ℝ)) + Real.exp (-((k : ℝ) / T) * s))) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  let ε := equilibriumNelsonRadius T s
  have hε : 0 < ε := equilibriumNelsonRadius_pos T s
  have hε1 : ε ≤ 1 := equilibriumNelsonRadius_le_one hT hs0.le
  obtain ⟨hEi, hEb⟩ := equilibriumReference_canonical_error_moment hβ R hN hk hm hε hε1
  have h := equilibriumReference_nelson_markov hβ R (by omega : 0 < N) hT ht htT hs0
    (2 * k * m) hEi hEb
  have hfactor : ((2 * T) / s) ^ (2 * k * m) ≤ (2 * T) ^ (2 * k * m) := by
    apply pow_le_pow_left₀ (by positivity : 0 ≤ (2 * T) / s)
    apply (div_le_iff₀ hs0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * T)]
  have heps2 : ε ^ 2 ≤ 1 := by nlinarith
  have hNpow : 1 / (N : ℝ) ^ (2 * m) = (N : ℝ) ^ (-((2 * m : ℕ) : ℝ)) := by
    rw [Real.rpow_neg (by positivity : 0 ≤ (N : ℝ)), Real.rpow_natCast, one_div]
  have hepsk : ε ^ k = Real.exp (-((k : ℝ) / T) * s) := by
    dsimp only [ε, equilibriumNelsonRadius]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hterms : ε ^ 2 / (N : ℝ) ^ (2 * m) + ε ^ k ≤
      (N : ℝ) ^ (-((2 * m : ℕ) : ℝ)) + Real.exp (-((k : ℝ) / T) * s) := by
    rw [← hNpow, ← hepsk]
    exact add_le_add (div_le_div_of_nonneg_right heps2 (pow_nonneg (Nat.cast_nonneg _) _)) le_rfl
  have hE0 := (equilibriumCanonicalErrorMomentConstant_pos k m).le
  have hterms0 : 0 ≤ ε ^ 2 / (N : ℝ) ^ (2 * m) + ε ^ k :=
    add_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hε.le _)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    ((2 * T) / s) ^ (2 * k * m) *
        (equilibriumCanonicalErrorMomentConstant k m * (ε ^ 2 / (N : ℝ) ^ (2 * m) + ε ^ k)) ≤
      (2 * T) ^ (2 * k * m) *
        (equilibriumCanonicalErrorMomentConstant k m * (ε ^ 2 / (N : ℝ) ^ (2 * m) + ε ^ k)) :=
      mul_le_mul_of_nonneg_right hfactor (mul_nonneg hE0 hterms0)
    _ ≤ (2 * T) ^ (2 * k * m) * (equilibriumCanonicalErrorMomentConstant k m *
        ((N : ℝ) ^ (-((2 * m : ℕ) : ℝ)) + Real.exp (-((k : ℝ) / T) * s))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hterms hE0) (by positivity)
    _ = _ := by unfold equilibriumPartitionTailConstant; ring

end RepulsiveCoulomb
