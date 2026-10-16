import LeanResearch.RepulsiveCoulomb.EquilibriumBranchModulatedErrorIdentity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPartitionBasic

/-! Exact scale and event algebra for the Nelson partition tail. The radius
exp(-s/T) and the factor 1/2 in the regularized lower bound are retained. This
module does not assume the missing centered correlation moment estimate. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumNelsonRadius (T s : ℝ) : ℝ := Real.exp (-s / T)

theorem equilibriumNelsonRadius_pos (T s : ℝ) : 0 < equilibriumNelsonRadius T s := Real.exp_pos _

theorem equilibriumNelsonRadius_le_one {T s : ℝ} (hT : 0 < T) (hs : 0 ≤ s) :
    equilibriumNelsonRadius T s ≤ 1 :=
  Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hT.le)

/-- The actual double-smoothed lower bound at the tail-dependent radius gives
-t*A_epsilon<=s/2 uniformly over 0<=t<=T, with no particle-number term. -/
theorem equilibriumReference_regularized_nelson_scale {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) {T t s : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) (hs : 0 ≤ s) :
    -s / 2 ≤ t * equilibriumRegularizedModulatedEnergy (equilibriumNelsonRadius T s) R z := by
  have hlow := equilibriumReference_regularized_modulated_lower hβ R hN z (equilibriumNelsonRadius_pos T s)
  have hmul := mul_le_mul_of_nonneg_left hlow ht
  have hlog : Real.log (equilibriumNelsonRadius T s) = -s / T := by
    rw [equilibriumNelsonRadius, Real.log_exp]
  rw [hlog] at hmul
  have hratio : t * s / T ≤ s := by
    apply (div_le_iff₀ hT).mpr
    nlinarith [mul_le_mul_of_nonneg_right htT hs]
  have he : t * ((-s / T) / 2) = -(t * s / T) / 2 := by ring
  rw [he] at hmul
  linarith

private theorem equilibrium_nelson_event_scalar {A B T t s : ℝ}
    (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T)
    (hB : -s / 2 ≤ t * B) (hA : s < -t * A) :
    s / (2 * T) < |A - B| := by
  have hab : B - A ≤ |A - B| := by simpa only [neg_sub] using neg_le_abs (A - B)
  have h1 := mul_le_mul_of_nonneg_left hab ht
  have h2 := mul_le_mul_of_nonneg_right htT (abs_nonneg (A - B))
  apply (div_lt_iff₀ (by positivity : 0 < 2 * T)).mpr
  nlinarith

/-- The exact tail event is contained in a large regularization-error event.
No collision condition is needed until the error is replaced by its centered
proxy identity; that replacement is only almost everywhere under the product law. -/
theorem equilibriumReference_nelson_event_inclusion {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    {T t s : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) (hs : 0 ≤ s) :
    {z : Fin N → ℂ | s < -t * equilibriumModulatedEnergy R.density z} ⊆
      {z : Fin N → ℂ | s / (2 * T) <
        |equilibriumModulatedEnergy R.density z -
          equilibriumRegularizedModulatedEnergy (equilibriumNelsonRadius T s) R z|} := by
  intro z hz
  exact equilibrium_nelson_event_scalar hT ht htT
    (equilibriumReference_regularized_nelson_scale hβ R hN z hT ht htT hs) hz

/-- The singular deterministic log-N estimate supplies a genuine almost-everywhere
upper cutoff for the exponential layer-cake variable. -/
theorem equilibriumReference_nelson_tail_cutoff {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ z : Fin N → ℂ ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)),
      -t * equilibriumModulatedEnergy R.density z ≤ T * (Real.log (N : ℝ) / 4 + 1 / 2) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hn
  have hC : 0 ≤ Real.log (N : ℝ) / 4 + 1 / 2 := by linarith
  filter_upwards [equilibriumReference_product_injective_ae hβ R N] with z hz
  have h1 := mul_le_mul_of_nonneg_left (equilibriumReference_modulated_log_lower hβ R hN z hz) ht
  have h2 := mul_le_mul_of_nonneg_right htT hC
  nlinarith

end RepulsiveCoulomb
