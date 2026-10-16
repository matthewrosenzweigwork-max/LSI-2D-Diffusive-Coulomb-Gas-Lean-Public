import LeanResearch.RepulsiveCoulomb.CoulombCenterChart
import Mathlib.Order.Interval.Finset.Fin

/-! The exact real coefficients of the manuscript Helmert transform.  All
statements are finite algebra, including the cancellation of a shorter row
against a longer one. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

/-- Unnormalized relative row: `k` initial ones, followed by `-k`. -/
def coulombHelmertRaw {N : ℕ} (k j : Fin N) : ℝ :=
  (if j < k then 1 else 0) - (if j = k then (k.val : ℝ) else 0)

theorem coulombHelmert_prefix_sum {N : ℕ} (k : Fin N) :
    (∑ j : Fin N, if j < k then (1 : ℝ) else 0) = (k.val : ℝ) := by
  have hf : Finset.univ.filter (fun j : Fin N => j < k) = Finset.Iio k := by
    ext j
    simp
  rw [← Finset.sum_filter, hf]
  simp

theorem coulombHelmertRaw_sum {N : ℕ} (k : Fin N) :
    ∑ j, coulombHelmertRaw k j = 0 := by
  unfold coulombHelmertRaw
  rw [Finset.sum_sub_distrib, coulombHelmert_prefix_sum]
  simp

theorem coulombHelmertRaw_mul_of_lt {N : ℕ} {k l : Fin N} (hkl : k < l)
    (j : Fin N) :
    coulombHelmertRaw k j * coulombHelmertRaw l j = coulombHelmertRaw k j := by
  by_cases hjk : j < k
  · have hjl := lt_trans hjk hkl
    simp [coulombHelmertRaw, hjk, hjl, ne_of_lt hjk, ne_of_lt hjl]
  · by_cases heq : j = k
    · subst j
      simp [coulombHelmertRaw, hkl, ne_of_lt hkl]
    · simp [coulombHelmertRaw, hjk, heq]

theorem coulombHelmertRaw_square {N : ℕ} (k j : Fin N) :
    coulombHelmertRaw k j * coulombHelmertRaw k j =
      (if j < k then (1 : ℝ) else 0) +
        (if j = k then (k.val : ℝ) ^ 2 else 0) := by
  by_cases hjk : j < k
  · simp [coulombHelmertRaw, hjk, ne_of_lt hjk]
  · by_cases heq : j = k
    · subst j
      simp [coulombHelmertRaw, pow_two]
    · simp [coulombHelmertRaw, hjk, heq]

theorem coulombHelmertRaw_sum_square {N : ℕ} (k : Fin N) :
    ∑ j, coulombHelmertRaw k j * coulombHelmertRaw k j =
      (k.val : ℝ) * ((k.val : ℝ) + 1) := by
  simp_rw [coulombHelmertRaw_square]
  rw [Finset.sum_add_distrib, coulombHelmert_prefix_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem coulombHelmertRaw_sum_mul {N : ℕ} {k l : Fin N} (hkl : k ≠ l) :
    ∑ j, coulombHelmertRaw k j * coulombHelmertRaw l j = 0 := by
  rcases lt_or_gt_of_ne hkl with h | h
  · simp_rw [coulombHelmertRaw_mul_of_lt h]
    exact coulombHelmertRaw_sum k
  · simp_rw [mul_comm (coulombHelmertRaw k _), coulombHelmertRaw_mul_of_lt h]
    exact coulombHelmertRaw_sum l

/-- Positive normalization factor for the row with `k` initial ones. -/
def coulombHelmertScale (k : ℕ) : ℝ :=
  (Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)))⁻¹

theorem coulombHelmertScale_sq (k : ℕ) (hk : 0 < k) :
    coulombHelmertScale k * coulombHelmertScale k *
      ((k : ℝ) * ((k : ℝ) + 1)) = 1 := by
  have hp : 0 < (k : ℝ) * ((k : ℝ) + 1) := by positivity
  have hs : Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hp)
  have hsq := Real.sq_sqrt hp.le
  unfold coulombHelmertScale
  field_simp
  nlinarith

/-- Embed a real coefficient vector into the complex Euclidean configuration. -/
def coulombHelmertRealVector {N : ℕ} (f : Fin N → ℝ) : CoulombConfig N :=
  WithLp.toLp 2 (fun j => (f j : ℂ))

theorem coulombHelmertRealVector_inner {N : ℕ} (f g : Fin N → ℝ) :
    inner ℂ (coulombHelmertRealVector f) (coulombHelmertRealVector g) =
      ((∑ j, f j * g j : ℝ) : ℂ) := by
  simp [PiLp.inner_apply, coulombHelmertRealVector, RCLike.inner_apply',
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, mul_comm]

end RepulsiveCoulomb
