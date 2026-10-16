import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Exact one-real-dimensional Jacobian: the norm determinant of a map from the
real line is its speed, with no normalization constant. -/
noncomputable section
namespace RepulsiveCoulomb

theorem realLine_normDet_eq_norm_apply_one {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (A : ℝ →ₗ[ℝ] V) : A.normDet = ‖A 1‖ := by
  have h := A.normDet_sq_eq_det_gram (OrthonormalBasis.singleton (Fin 1) ℝ)
  have hs : A.normDet ^ 2 = ‖A 1‖ ^ 2 := by
    simpa [Matrix.gram, Matrix.det_unique, real_inner_self_eq_norm_sq] using h
  have hn := A.normDet_nonneg
  have hm := norm_nonneg (A 1)
  nlinarith

end RepulsiveCoulomb
