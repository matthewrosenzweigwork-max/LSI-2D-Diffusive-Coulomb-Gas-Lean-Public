import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Exact index and conjugation conventions for the compact basic identity.
The Frobenius square is an explicit sum of entry norms; it is not Mathlib's
ordinary matrix norm. Alternating two-forms use one half of that full sum. -/
noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace RepulsiveCoulomb

def dbarMatrixFrobeniusSq {ι : Type*} [Fintype ι] (J : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖J i j‖ ^ 2

def dbarMatrixTransposeCross {ι : Type*} [Fintype ι] (J : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, (J i j * conj (J j i)).re

def dbarAlternatingMatrixSq {ι : Type*} [Fintype ι] (F : Matrix ι ι ℂ) : ℝ :=
  (1 / 2 : ℝ) * dbarMatrixFrobeniusSq F

theorem dbarMatrixFrobeniusSq_nonneg {ι : Type*} [Fintype ι] (J : Matrix ι ι ℂ) :
    0 ≤ dbarMatrixFrobeniusSq J :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem dbarMatrixFrobeniusSq_transpose {ι : Type*} [Fintype ι] (J : Matrix ι ι ℂ) :
    dbarMatrixFrobeniusSq J.transpose = dbarMatrixFrobeniusSq J := by
  unfold dbarMatrixFrobeniusSq
  exact Finset.sum_comm

theorem dbarComplex_norm_sub_sq (a b : ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * conj b).re := by
  have hn : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * (inner ℂ a b).re + ‖b‖ ^ 2 :=
    norm_sub_sq (𝕜 := ℂ) a b
  rw [hn, RCLike.inner_apply']
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem dbarAlternatingMatrixSq_antisymmetrize {ι : Type*} [Fintype ι] (J : Matrix ι ι ℂ) :
    dbarAlternatingMatrixSq (J - J.transpose) = dbarMatrixFrobeniusSq J - dbarMatrixTransposeCross J := by
  have he : dbarMatrixFrobeniusSq (J - J.transpose) =
      dbarMatrixFrobeniusSq J + dbarMatrixFrobeniusSq J.transpose - 2 * dbarMatrixTransposeCross J := by
    simp only [dbarMatrixFrobeniusSq, dbarMatrixTransposeCross, Matrix.sub_apply, Matrix.transpose_apply,
      dbarComplex_norm_sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [dbarAlternatingMatrixSq, he, dbarMatrixFrobeniusSq_transpose]
  ring

theorem dbarMatrixTransposeCross_trace {ι : Type*} [Fintype ι] (J : Matrix ι ι ℂ) :
    dbarMatrixTransposeCross J = (Matrix.trace (J * J.map (starRingEnd ℂ))).re := by
  simp only [dbarMatrixTransposeCross, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply, Complex.re_sum]

theorem dbarAlternatingMatrixSq_pairs {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : ∀ i j, F j i = -F i j) :
    dbarAlternatingMatrixSq F = ∑ p ∈ coulombPairs N, ‖F p.1 p.2‖ ^ 2 := by
  classical
  let h : Fin N → Fin N → ℝ := fun i j => if i < j then ‖F i j‖ ^ 2 else 0
  have hd (i : Fin N) : F i i = 0 := by
    have hh := hF i i
    linear_combination (1 / 2 : ℂ) * hh
  have he (i j : Fin N) : ‖F i j‖ ^ 2 = h i j + h j i := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [h, hij, not_lt_of_ge hij.le]
    · simp [h, hd]
    · simp [h, hji, not_lt_of_ge hji.le, hF i j]
  have hfrob : dbarMatrixFrobeniusSq F = 2 * ∑ i, ∑ j, h i j := by
    simp only [dbarMatrixFrobeniusSq, he, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => h j i)]
    ring
  have hpairs : (∑ p ∈ coulombPairs N, ‖F p.1 p.2‖ ^ 2) = ∑ i, ∑ j, h i j := by
    rw [coulombPairs, Finset.sum_filter]
    exact Fintype.sum_prod_type _
  rw [dbarAlternatingMatrixSq, hfrob, hpairs]
  ring

theorem dbarMetric_transformed_curl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S R J : Matrix ι ι ℂ) (hRS : R * S = 1) :
    R * (J * (S * S).transpose - (S * S) * J.transpose) * R.transpose =
      (R * J * S.transpose) - (R * J * S.transpose).transpose := by
  have hStRt : S.transpose * R.transpose = 1 := by
    rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  have hRH : R * (S * S) = S := by rw [← Matrix.mul_assoc, hRS, Matrix.one_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_mul]
  have hleft : R * (J * (S.transpose * S.transpose)) * R.transpose = R * J * S.transpose := by
    calc
      _ = R * J * S.transpose * (S.transpose * R.transpose) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hStRt, Matrix.mul_one]
  have hright : R * ((S * S) * J.transpose) * R.transpose = S * J.transpose * R.transpose := by
    rw [← Matrix.mul_assoc R (S * S), hRH]
  rw [hleft, hright, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

theorem dbarMetric_transpose_cross_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S R J : Matrix ι ι ℂ) (hS : S.IsHermitian) (hR : R.IsHermitian)
    (hRS : R * S = 1) (hSR : S * R = 1) :
    dbarMatrixTransposeCross (R * J * S.transpose) = dbarMatrixTransposeCross J := by
  have hRc : R.map (starRingEnd ℂ) = R.transpose := by
    ext i j
    exact hR.apply j i
  have hSc : S.transpose.map (starRingEnd ℂ) = S := hS
  have hStRt : S.transpose * R.transpose = 1 := by
    rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  have he : (R * J * S.transpose) * (R * J * S.transpose).map (starRingEnd ℂ) =
      R * (J * J.map (starRingEnd ℂ)) * S := by
    rw [Matrix.map_mul, Matrix.map_mul, hRc, hSc]
    calc
      _ = R * J * (S.transpose * R.transpose) * J.map (starRingEnd ℂ) * S := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hStRt, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [dbarMatrixTransposeCross_trace, he, dbarMatrixTransposeCross_trace]
  congr 1
  rw [Matrix.trace_mul_cycle, hSR, Matrix.one_mul]

theorem dbarMetric_compact_algebra_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S R J : Matrix ι ι ℂ) (hS : S.IsHermitian) (hR : R.IsHermitian)
    (hRS : R * S = 1) (hSR : S * R = 1) :
    dbarAlternatingMatrixSq (R * (J * (S * S).transpose - (S * S) * J.transpose) * R.transpose) +
      dbarMatrixTransposeCross J = dbarMatrixFrobeniusSq (R * J * S.transpose) := by
  rw [dbarMetric_transformed_curl S R J hRS, dbarAlternatingMatrixSq_antisymmetrize,
    dbarMetric_transpose_cross_invariant S R J hS hR hRS hSR]
  ring

theorem dbarMetric_compact_algebra_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S R J : Matrix ι ι ℂ) (hS : S.IsHermitian) (hR : R.IsHermitian)
    (hRS : R * S = 1) (hSR : S * R = 1) :
    0 ≤ dbarAlternatingMatrixSq (R * (J * (S * S).transpose - (S * S) * J.transpose) * R.transpose) +
      dbarMatrixTransposeCross J := by
  rw [dbarMetric_compact_algebra_identity S R J hS hR hRS hSR]
  exact dbarMatrixFrobeniusSq_nonneg _

end RepulsiveCoulomb
