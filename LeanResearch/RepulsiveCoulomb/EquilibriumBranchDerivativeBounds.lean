import LeanResearch.RepulsiveCoulomb.EquilibriumBranchRadialDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Finite-order product estimates used for the physical thermal-density
Gaussian tails. Constants are finite sums of the actual Leibniz coefficients;
no derivative bound is assumed beyond the order explicitly supplied. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators RealInnerProductSpace
open scoped ENNReal
namespace RepulsiveCoulomb

/-- A positive constant controlling every binomial row through order n. -/
def equilibriumLeibnizConstant (n : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)

theorem equilibriumLeibnizConstant_pos (n : ℕ) : 0 < equilibriumLeibnizConstant n := by
  unfold equilibriumLeibnizConstant
  positivity

theorem equilibriumLeibnizConstant_row_le {j n : ℕ} (hj : j ≤ n) :
    (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) ≤ equilibriumLeibnizConstant n := by
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ Finset.range (n + 1)) =>
      show 0 ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) by positivity)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  unfold equilibriumLeibnizConstant
  linarith

/-- The full real Fréchet derivative product bound, uniformly through a supplied
finite order. A and B can be spatial weights evaluated at the same point. -/
theorem equilibrium_iteratedFDeriv_smul_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℂ → ℝ} {g : ℂ → V} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    {n j : ℕ} (hj : j ≤ n) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℂ)
    (hfa : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hgb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun y => f y • g y) x‖ ≤
      equilibriumLeibnizConstant n * A * B := by
  have hprod := norm_iteratedFDeriv_smul_le hf hg x (n := j) (by simp)
  have hsum : (∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (j - i) g x‖) ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * A * B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ n := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj
        have hji : j - i ≤ n := (Nat.sub_le j i).trans hj
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hfa i hi') (Nat.cast_nonneg _))
          (hgb (j - i) hji) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]
  exact hprod.trans (hsum.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (equilibriumLeibnizConstant_row_le hj) hA) hB))

theorem equilibrium_iteratedFDeriv_mul_bound {f g : ℂ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    {n j : ℕ} (hj : j ≤ n) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℂ)
    (hfa : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hgb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun y => f y * g y) x‖ ≤
      equilibriumLeibnizConstant n * A * B :=
  equilibrium_iteratedFDeriv_smul_bound hf hg hj hA hB x hfa hgb

/-- Constant maps have all iterated derivatives bounded by their own norm,
including the zeroth derivative. -/
theorem equilibrium_iteratedFDeriv_const_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : V) (j : ℕ) (x : ℂ) :
    ‖iteratedFDeriv ℝ j (fun _ : ℂ => c) x‖ ≤ ‖c‖ := by
  cases j with
  | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
  | succ j =>
      rw [iteratedFDeriv_succ_const]
      simpa only [Pi.zero_apply, norm_zero] using norm_nonneg c

/-- All orders of the physical linear coordinate covector are bounded by
1+|x|. This avoids introducing normalized or rescaled physical gradients. -/
theorem equilibrium_iteratedFDeriv_innerSL_norm_le (j : ℕ) (x : ℂ) :
    ‖iteratedFDeriv ℝ j (innerSL ℝ : ℂ → ℂ →L[ℝ] ℝ) x‖ ≤ 1 + ‖x‖ := by
  cases j with
  | zero =>
      rw [norm_iteratedFDeriv_zero, innerSL_apply_norm]
      linarith
  | succ j =>
      have he : fderiv ℝ (innerSL ℝ : ℂ → ℂ →L[ℝ] ℝ) =
          (fun _ : ℂ => (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) := by
        funext y
        exact (innerSL ℝ).hasFDerivAt.fderiv
      rw [← norm_iteratedFDeriv_fderiv, he]
      exact (equilibrium_iteratedFDeriv_const_norm_le _ j x).trans
        ((norm_innerSL_le ℝ).trans (by linarith [norm_nonneg x]))

/-- A scalar affine combination preserves actual finite derivative bounds. -/
theorem equilibrium_iteratedFDeriv_affine_norm_le {f : ℂ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (c d : ℝ) (j : ℕ) (x : ℂ) {D : ℝ}
    (hD : ‖iteratedFDeriv ℝ j f x‖ ≤ D) :
    ‖iteratedFDeriv ℝ j (fun y => c + d * f y) x‖ ≤ |c| + |d| * D := by
  have hfj : ContDiffAt ℝ j f x := (hf.of_le (by simp)).contDiffAt
  have hdfj : ContDiffAt ℝ j (fun y => d * f y) x := contDiffAt_const.mul hfj
  rw [fun_iteratedFDeriv_add_apply contDiffAt_const hdfj]
  apply (norm_add_le _ _).trans
  have hd : iteratedFDeriv ℝ j (fun y => d * f y) x =
      d • iteratedFDeriv ℝ j f x := by
    simpa only [smul_eq_mul] using (iteratedFDeriv_const_smul_apply' (a := d) hfj)
  rw [hd, norm_smul, Real.norm_eq_abs]
  exact add_le_add
    (by simpa only [Real.norm_eq_abs] using equilibrium_iteratedFDeriv_const_norm_le c j x)
    (mul_le_mul_of_nonneg_left hD (abs_nonneg d))

end RepulsiveCoulomb
