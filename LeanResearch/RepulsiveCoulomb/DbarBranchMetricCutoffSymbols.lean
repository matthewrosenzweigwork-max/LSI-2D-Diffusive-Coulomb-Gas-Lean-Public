module

public import LeanResearch.RepulsiveCoulomb.DbarBranchExteriorPrincipalSymbol
public import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCutoffDerivative

@[expose] public section

/-! The real cutoff differential gives exactly twice the transformed dbar
symbol. Both the scalar adjoint and the half-Frobenius exterior symbols have
the same metric-dual bound, with the Wirtinger factor1/2 retained. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace RepulsiveCoulomb

theorem dbarSelfAdjoint_gradient_dual_norm {N : ℕ} {θ : CoulombConfig N → ℝ}
    (z : CoulombConfig N) (R : CoulombConfig N →L[ℂ] CoulombConfig N)
    (hR : ∀ a b, inner ℂ (R a) b = inner ℂ a (R b)) :
    ‖(fderiv ℝ θ z).comp (R.restrictScalars ℝ)‖ = ‖R (gradient θ z)‖ := by
  have hreal (x y : CoulombConfig N) : inner ℝ x y = (inner ℂ x y).re := by
    simp only [PiLp.inner_apply, Complex.inner, RCLike.inner_apply', Complex.re_sum, mul_comm]
  have he : (fderiv ℝ θ z).comp (R.restrictScalars ℝ) = innerSL ℝ (R (gradient θ z)) := by
    ext v
    change fderiv ℝ θ z (R v) = inner ℝ (R (gradient θ z)) v
    rw [← inner_gradient_left]
    simp only [hreal]
    exact congrArg Complex.re (hR (gradient θ z) v).symm
  rw [he, innerSL_apply_norm]

theorem dbarSelfAdjoint_real_cutoff_norm {N : ℕ} {θ : CoulombConfig N → ℝ}
    {z : CoulombConfig N} (hθ : DifferentiableAt ℝ θ z)
    (R : CoulombConfig N →L[ℂ] CoulombConfig N)
    (hR : ∀ a b, inner ℂ (R a) b = inner ℂ a (R b)) :
    ‖R (coulombDbar (fun x => (θ x : ℂ)) z)‖ =
      (1 / 2 : ℝ) * ‖(fderiv ℝ θ z).comp (R.restrictScalars ℝ)‖ := by
  rw [coulombDbar_real hθ, map_smul, norm_smul,
    dbarSelfAdjoint_gradient_dual_norm z R hR]
  norm_num

theorem dbarSelfAdjoint_real_cutoff_divergence {N : ℕ} {θ : CoulombConfig N → ℝ}
    {z : CoulombConfig N} (hθ : DifferentiableAt ℝ θ z)
    (R : CoulombConfig N →L[ℂ] CoulombConfig N)
    (hR : ∀ a b, inner ℂ (R a) b = inner ℂ a (R b)) (u : CoulombConfig N) :
    (∑ j, coulombDCoordinate (fun x => (θ x : ℂ)) z j * R u j) =
      inner ℂ (R (coulombDbar (fun x => (θ x : ℂ)) z)) u := by
  rw [hR, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, Complex.star_def]
  apply Finset.sum_congr rfl
  intro j _
  rw [coulombDCoordinate_real hθ, coulombDbar_apply, coulombDbarCoordinate_real hθ]
  simp only [map_div₀, map_ofNat] <;> ring

theorem coulombMetricCutoff_transformed_dbar_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} {R : ℝ}, 0 < R → ∀ z ∈ coulombDomain N,
      ‖dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
        (coulombDbar (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) z)‖ ≤ C / (2 * R) := by
  obtain ⟨C, hC, hb⟩ := coulombMetricCutoff_metric_dual_bound
  refine ⟨C, hC, ?_⟩
  intro N R hR z hz
  rw [dbarSelfAdjoint_real_cutoff_norm
    ((coulombMetricCutoff_contDiff (N := N) hR).differentiable (by simp) z)
    _ (dbarGraphMetricInverseRoot_selfAdjoint_pairing _)]
  calc
    _ ≤ (1 / 2 : ℝ) * (C / R) := mul_le_mul_of_nonneg_left (hb hR z hz) (by norm_num)
    _ = _ := by ring

theorem coulombMetricCutoff_joint_symbol_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} {R : ℝ}, 0 < R → ∀ z ∈ coulombDomain N,
      ∀ u : CoulombConfig N,
      ‖∑ j, coulombDCoordinate (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) z j *
        dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) u j‖ ≤
          (C / (2 * R)) * ‖u‖ ∧
      dbarAlternatingMatrixSq (dbarVectorWedge
        (dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
          (coulombDbar (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) z)) u) ≤
          (C / (2 * R)) ^ 2 * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := coulombMetricCutoff_transformed_dbar_bound
  refine ⟨C, hC, ?_⟩
  intro N R hR z hz u
  let a := dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
    (coulombDbar (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) z)
  have ha : ‖a‖ ≤ C / (2 * R) := hb hR z hz
  constructor
  · rw [dbarSelfAdjoint_real_cutoff_divergence
      ((coulombMetricCutoff_contDiff (N := N) hR).differentiable (by simp) z)
      _ (dbarGraphMetricInverseRoot_selfAdjoint_pairing _)]
    exact (norm_inner_le_norm a u).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  · exact (dbarVectorWedge_bound a u).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg a) ha 2) (sq_nonneg _))

end RepulsiveCoulomb
