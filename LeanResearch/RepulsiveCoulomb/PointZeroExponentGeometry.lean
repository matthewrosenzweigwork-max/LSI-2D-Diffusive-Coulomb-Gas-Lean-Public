module

public import LeanResearch.RepulsiveCoulomb.PointRectifiableConformalMetric
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-! The zero-total-exponent case of the literal finite point-weight geometry.
Nonnegative exponents with zero sum all vanish, including at repeated locations.
The identity is an actual global flattening with exact metric constant one and
positive real Jacobian equal to the raw weight. No sector-budget division occurs. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointExponent_eq_zero_of_sum_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 0) (j : Fin m) : a j = 0 := by
  have hle : a j ≤ ∑ i, a i :=
    Finset.single_le_sum (fun i _ ↦ ha i) (Finset.mem_univ j)
  exact le_antisymm (hsum ▸ hle) (ha j)

theorem rawPointWeight_eq_one_of_sum_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 0) (y : Fin m → ℂ) (z : ℂ) :
    rawPointWeight a y z = 1 := by
  simp [rawPointWeight, pointExponent_eq_zero_of_sum_zero ha hsum]

theorem pointConformalDensity_eq_one_of_sum_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 0) (y : Fin m → ℂ) (z : ℂ) :
    pointConformalDensity a y z = 1 := by
  simp [pointConformalDensity, rawPointWeight_eq_one_of_sum_zero ha hsum]

/-- The actual smooth-path infimum is Euclidean, proved from its competitors. -/
theorem pointSmoothConformalEDist_eq_euclidean_of_sum_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 0) (y : Fin m → ℂ) (x z : ℂ) :
    pointSmoothConformalEDist a y x z = ENNReal.ofReal ‖z - x‖ := by
  apply le_antisymm
  · let γ : ℝ → ℂ := fun t ↦ x + t • (z - x)
    have hd (t : ℝ) : deriv γ t = z - x := by
      have h : HasDerivAt γ (z - x) t := by
        simpa [γ] using ((hasDerivAt_id t).smul_const (z - x)).const_add x
      exact h.deriv
    have h := pointSmoothConformalEDist_le_path a y
      (γ := γ) (s := 0) (t := 1) (by fun_prop) zero_le_one
    have hlen : pointConformalPathELength a y γ 0 1 = ENNReal.ofReal ‖z - x‖ := by
      simp [pointConformalPathELength, pointConformalDensity_eq_one_of_sum_zero ha hsum, hd]
    rw [hlen] at h
    simpa [γ] using h
  · by_contra hbad
    obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y
      (lt_of_not_ge hbad)
    have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hγ.contDiffOn zero_le_one
    rw [h0, h1] at h
    have he : pointConformalPathELength a y γ 0 1 =
        ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv γ t‖ₑ := by
      simp [pointConformalPathELength, pointConformalDensity_eq_one_of_sum_zero ha hsum]
    rw [he, ofReal_norm] at hlen
    exact (not_lt_of_ge h) hlen

/-- This is the all-continuous-rectifiable-curve distance used in the manuscript. -/
theorem pointRectifiableConformalEDist_eq_euclidean_of_sum_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 0) (y : Fin m → ℂ) (x z : ℂ) :
    pointRectifiableConformalEDist a y x z = ENNReal.ofReal ‖z - x‖ := by
  rw [pointRectifiableConformalEDist_eq_smooth ha,
    pointSmoothConformalEDist_eq_euclidean_of_sum_zero ha hsum]

theorem pointSmoothConformalMetricSpace_dist_eq_euclidean_of_sum_zero
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 0)
    (y : Fin m → ℂ) (x z : ℂ) :
    @dist ℂ (pointSmoothConformalMetricSpace ha y).toDist x z = dist x z := by
  rw [pointSmoothConformalMetricSpace_dist,
    pointSmoothConformalEDist_eq_euclidean_of_sum_zero ha hsum,
    ENNReal.toReal_ofReal (norm_nonneg _), dist_eq_norm, norm_sub_rev]

/-- An explicit, smooth identity homeomorphism, with the literal raw Jacobian
and the source's sharp symmetric constant sqrt(1 + q/2) = 1 when q = 0. -/
theorem exists_pointZeroExponent_identity_flattening {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 0) (y : Fin m → ℂ) :
    ∃ F : ℂ ≃ₜ ℂ, F = Homeomorph.refl ℂ ∧
      ContDiff ℝ 1 (F : ℂ → ℂ) ∧
      Real.sqrt (1 + (∑ j, a j) / 2) = 1 ∧
      (∀ z, (fderiv ℝ (F : ℂ → ℂ) z).toLinearMap.det = rawPointWeight a y z) ∧
      (∀ z, 0 < (fderiv ℝ (F : ℂ → ℂ) z).toLinearMap.det ∧
        ‖fderiv ℝ (F : ℂ → ℂ) z‖ ^ 2 ≤ (fderiv ℝ (F : ℂ → ℂ) z).toLinearMap.det) ∧
      (∀ x z, ‖F z - F x‖ = (pointRectifiableConformalEDist a y x z).toReal) ∧
      (∀ x z,
        (Real.sqrt (1 + (∑ j, a j) / 2))⁻¹ *
          (pointRectifiableConformalEDist a y x z).toReal ≤ ‖F z - F x‖ ∧
        ‖F z - F x‖ ≤ Real.sqrt (1 + (∑ j, a j) / 2) *
          (pointRectifiableConformalEDist a y x z).toReal) := by
  refine ⟨Homeomorph.refl ℂ, rfl, contDiff_id, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hsum]
  · intro z
    change (fderiv ℝ (id : ℂ → ℂ) z).toLinearMap.det = rawPointWeight a y z
    rw [fderiv_id]
    change LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ) = _
    rw [LinearMap.det_id, rawPointWeight_eq_one_of_sum_zero ha hsum]
  · intro z
    change 0 < (fderiv ℝ (id : ℂ → ℂ) z).toLinearMap.det ∧
      ‖fderiv ℝ (id : ℂ → ℂ) z‖ ^ 2 ≤ (fderiv ℝ (id : ℂ → ℂ) z).toLinearMap.det
    rw [fderiv_id, ContinuousLinearMap.norm_id]
    change 0 < LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ) ∧
      (1 : ℝ) ^ 2 ≤ LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
    simp
  · intro x z
    change ‖z - x‖ = (pointRectifiableConformalEDist a y x z).toReal
    rw [pointRectifiableConformalEDist_eq_euclidean_of_sum_zero ha hsum,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  · intro x z
    simp [hsum, pointRectifiableConformalEDist_eq_euclidean_of_sum_zero ha hsum,
      ENNReal.toReal_ofReal (norm_nonneg _)]

end RepulsiveCoulomb
