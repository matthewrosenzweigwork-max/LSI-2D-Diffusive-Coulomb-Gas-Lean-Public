module

public import LeanResearch.RepulsiveCoulomb.CoulombWirtinger

@[expose] public section

/-! The converse classical Cauchy-Riemann implication on the actual Euclidean
configuration space. Real differentiability is essential here; this theorem
does not assert regularity of a weak L2 kernel element. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb

theorem coulombCoordinateInjection_sum {N : ℕ} (z : CoulombConfig N) :
    (∑ i, coulombCoordinateInjection N i (z i)) = z := by
  ext j
  simp [coulombCoordinateInjection_eq_single, EuclideanSpace.single]

theorem coulombCoordinateInjection_real_decomposition {N : ℕ} (i : Fin N) (w : ℂ) :
    coulombCoordinateInjection N i w =
      w.re • coulombCoordinateInjection N i 1 + w.im • coulombCoordinateInjection N i Complex.I := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im w).symm
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul]

theorem coulombRealLinear_coordinate_complex {N : ℕ}
    (L : CoulombConfig N →L[ℝ] ℂ) (i : Fin N)
    (hI : L (coulombCoordinateInjection N i Complex.I) = Complex.I * L (coulombCoordinateInjection N i 1))
    (w : ℂ) : L (coulombCoordinateInjection N i w) = w * L (coulombCoordinateInjection N i 1) := by
  rw [coulombCoordinateInjection_real_decomposition, map_add, map_smul, map_smul, hI]
  simp only [Complex.real_smul]
  calc
    _ = ((w.re : ℂ) + w.im * Complex.I) * L (coulombCoordinateInjection N i 1) := by ring
    _ = _ := by rw [Complex.re_add_im]

def coulombComplexLinearFromReal {N : ℕ} (L : CoulombConfig N →L[ℝ] ℂ) : CoulombConfig N →L[ℂ] ℂ :=
  ∑ i, L (coulombCoordinateInjection N i 1) • EuclideanSpace.proj (𝕜 := ℂ) i

theorem coulombComplexLinearFromReal_restrict {N : ℕ} (L : CoulombConfig N →L[ℝ] ℂ)
    (hI : ∀ i, L (coulombCoordinateInjection N i Complex.I) = Complex.I * L (coulombCoordinateInjection N i 1)) :
    (coulombComplexLinearFromReal L).restrictScalars ℝ = L := by
  ext z
  change (coulombComplexLinearFromReal L) z = L z
  conv_rhs => rw [← coulombCoordinateInjection_sum z, map_sum]
  simp only [coulombComplexLinearFromReal, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change L (coulombCoordinateInjection N i 1) * z i = L (coulombCoordinateInjection N i (z i))
  rw [coulombRealLinear_coordinate_complex L i (hI i) (z i), mul_comm]

theorem coulombDifferentiableAt_of_real_and_dbar_zero {N : ℕ}
    {f : CoulombConfig N → ℂ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (hbar : coulombDbar f z = 0) : DifferentiableAt ℂ f z := by
  have hI (i : Fin N) : fderiv ℝ f z (coulombCoordinateInjection N i Complex.I) =
      Complex.I * fderiv ℝ f z (coulombCoordinateInjection N i 1) := by
    have hi := congrArg (fun w : CoulombConfig N => w i) hbar
    change (fderiv ℝ f z (coulombCoordinateInjection N i 1) +
      Complex.I * fderiv ℝ f z (coulombCoordinateInjection N i Complex.I)) / 2 = 0 at hi
    have hs := (div_eq_zero_iff.mp hi).resolve_right (by norm_num)
    calc
      _ = (-Complex.I) * (Complex.I * fderiv ℝ f z (coulombCoordinateInjection N i Complex.I)) := by
        simp [← mul_assoc]
      _ = (-Complex.I) * (-fderiv ℝ f z (coulombCoordinateInjection N i 1)) := by
        rw [eq_neg_of_add_eq_zero_right hs]
      _ = _ := by ring
  exact (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt
    (coulombComplexLinearFromReal_restrict (fderiv ℝ f z) hI)).differentiableAt

end RepulsiveCoulomb
