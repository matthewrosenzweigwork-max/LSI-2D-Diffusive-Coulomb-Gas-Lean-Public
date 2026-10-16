import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue

/-! Constructive positive endpoint-speed interpolation by a polynomial.
This supplies reparameterizations needed to glue finitely many regular arcs
with matched actual tangent velocities; no reparameterization certificate is input.
Records-only phase-four candidate, not yet checked. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def euclideanEndpointSpeedCorrection (a b : ℝ) (k : ℕ) : ℝ :=
  6 * (1 - (a + b) / (k + 2 : ℝ))

def euclideanEndpointReparam (a b : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  a / (k + 2 : ℝ) * (1 - (1 - t) ^ (k + 2)) +
    b / (k + 2 : ℝ) * t ^ (k + 2) +
    euclideanEndpointSpeedCorrection a b k * (t ^ 2 / 2 - t ^ 3 / 3)

def euclideanEndpointSpeed (a b : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  a * (1 - t) ^ (k + 1) + b * t ^ (k + 1) +
    euclideanEndpointSpeedCorrection a b k * t * (1 - t)

@[simp] theorem euclideanEndpointReparam_zero (a b : ℝ) (k : ℕ) :
    euclideanEndpointReparam a b k 0 = 0 := by simp [euclideanEndpointReparam]

@[simp] theorem euclideanEndpointReparam_one (a b : ℝ) (k : ℕ) :
    euclideanEndpointReparam a b k 1 = 1 := by
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  simp only [euclideanEndpointReparam, euclideanEndpointSpeedCorrection,
    sub_self, zero_pow (by omega : k + 2 ≠ 0), one_pow, sub_zero]
  field_simp
  ring

theorem euclideanEndpointReparam_contDiff (a b : ℝ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanEndpointReparam a b k) := by
  unfold euclideanEndpointReparam
  fun_prop

theorem euclideanEndpointReparam_hasDerivAt (a b : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (euclideanEndpointReparam a b k) (euclideanEndpointSpeed a b k t) t := by
  have h₁ := (hasDerivAt_const t (1 : ℝ)).sub
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).fun_pow (k + 2))
  have h₂ := (hasDerivAt_id t).fun_pow (k + 2)
  have h₃ := (((hasDerivAt_id t).fun_pow 2).div_const 2).sub
    (((hasDerivAt_id t).fun_pow 3).div_const 3)
  have h := ((h₁.const_mul (a / (k + 2 : ℝ))).add
    (h₂.const_mul (b / (k + 2 : ℝ)))).add
    (h₃.const_mul (euclideanEndpointSpeedCorrection a b k))
  convert! h using 1
  unfold euclideanEndpointSpeed
  simp only [show k + 2 - 1 = k + 1 by omega, Nat.cast_add, Nat.cast_ofNat,
    Pi.sub_apply, id_eq]
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

@[simp] theorem euclideanEndpointReparam_deriv (a b : ℝ) (k : ℕ) (t : ℝ) :
    deriv (euclideanEndpointReparam a b k) t = euclideanEndpointSpeed a b k t :=
  (euclideanEndpointReparam_hasDerivAt a b k t).deriv

@[simp] theorem euclideanEndpointReparam_deriv_zero (a b : ℝ) (k : ℕ) :
    deriv (euclideanEndpointReparam a b k) 0 = a := by
  simp [euclideanEndpointSpeed]

@[simp] theorem euclideanEndpointReparam_deriv_one (a b : ℝ) (k : ℕ) :
    deriv (euclideanEndpointReparam a b k) 1 = b := by
  simp [euclideanEndpointSpeed]

theorem euclideanEndpointSpeed_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {k : ℕ} (hk : a + b < (k + 2 : ℝ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < euclideanEndpointSpeed a b k t := by
  have hn : 0 < (k + 2 : ℝ) := by positivity
  have hc : 0 < euclideanEndpointSpeedCorrection a b k := by
    unfold euclideanEndpointSpeedCorrection
    exact mul_pos (by norm_num) (sub_pos.mpr ((div_lt_one hn).mpr hk))
  by_cases ht1 : t = 1
  · simp [euclideanEndpointSpeed, ht1, hb]
  have ht1' : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hfirst : 0 < a * (1 - t) ^ (k + 1) := mul_pos ha (pow_pos (sub_pos.mpr ht1') _)
  have hsecond : 0 ≤ b * t ^ (k + 1) := mul_nonneg hb.le (pow_nonneg ht.1 _)
  have hthird : 0 ≤ euclideanEndpointSpeedCorrection a b k * t * (1 - t) :=
    mul_nonneg (mul_nonneg hc.le ht.1) (sub_nonneg.mpr ht.2)
  unfold euclideanEndpointSpeed
  linarith

theorem euclideanEndpointReparam_strictMonoOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {k : ℕ} (hk : a + b < (k + 2 : ℝ)) :
    StrictMonoOn (euclideanEndpointReparam a b k) (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (euclideanEndpointReparam_contDiff a b k).continuous.continuousOn
  intro t ht
  rw [euclideanEndpointReparam_deriv]
  exact euclideanEndpointSpeed_pos ha hb hk (interior_subset ht)

theorem euclideanEndpointReparam_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {k : ℕ} (hk : a + b < (k + 2 : ℝ)) :
    euclideanEndpointReparam a b k '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
  have hm := (euclideanEndpointReparam_strictMonoOn ha hb hk).monotoneOn
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    have hl := hm (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ht ht.1
    have hu := hm ht (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ht.2
    change 0 ≤ euclideanEndpointReparam a b k t ∧ euclideanEndpointReparam a b k t ≤ 1
    simpa only [euclideanEndpointReparam_zero, euclideanEndpointReparam_one] using And.intro hl hu
  · simpa only [euclideanEndpointReparam_zero, euclideanEndpointReparam_one] using
      intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
        (euclideanEndpointReparam_contDiff a b k).continuous.continuousOn

/-- Construct a smooth increasing reparameterization of the standard interval
with any prescribed strictly positive endpoint speeds. -/
theorem exists_smooth_positive_endpoint_reparameterization {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      φ 0 = 0 ∧ φ 1 = 1 ∧ deriv φ 0 = a ∧ deriv φ 1 = b ∧
      (∀ t ∈ Icc (0 : ℝ) 1, 0 < deriv φ t) ∧
      StrictMonoOn φ (Icc (0 : ℝ) 1) ∧ φ '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (a + b)
  have hk' : a + b < (k + 2 : ℝ) := by linarith
  refine ⟨euclideanEndpointReparam a b k, euclideanEndpointReparam_contDiff a b k,
    euclideanEndpointReparam_zero a b k, euclideanEndpointReparam_one a b k,
    euclideanEndpointReparam_deriv_zero a b k, euclideanEndpointReparam_deriv_one a b k,
    ?_, euclideanEndpointReparam_strictMonoOn ha hb hk', euclideanEndpointReparam_image ha hb hk'⟩
  intro t ht
  rw [euclideanEndpointReparam_deriv]
  exact euclideanEndpointSpeed_pos ha hb hk' ht

end RepulsiveCoulomb
