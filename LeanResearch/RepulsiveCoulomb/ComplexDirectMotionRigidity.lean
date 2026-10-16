import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.LinearCombination

/-! SOURCE-ONLY, UNCOMPILED. The seam rigidity step uses direct complex rigid
motions z ↦ u*z+b. Full Euclidean motions do not satisfy the two-anchor rule:
reflection across the seam is the counterexample. Existing cyclic-order
orientation is therefore a real geometric obligation in the surgery atlas. -/
noncomputable section
namespace RepulsiveCoulomb

/-- Explicit direct Euclidean motion, with its actual inverse. -/
def complexDirectMotion (u b : ℂ) (hu : ‖u‖ = 1) : ℂ ≃ᵢ ℂ where
  toFun z := u * z + b
  invFun w := u⁻¹ * (w - b)
  left_inv z := by
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
    simp [hu0]
  right_inv w := by
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
    simp [hu0]
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro x y
    simp only [dist_eq_norm, add_sub_add_right_eq_sub, ← mul_sub, norm_mul, hu, one_mul]

/-- Agreement at two distinct actual arclength points forces the whole direct
motion. No differentiability or assumed equality across a seam is used. -/
theorem complexDirectMotion_coefficients_eq_of_two_points
    {u v b d x y : ℂ} (hxy : x ≠ y)
    (hx : u * x + b = v * x + d) (hy : u * y + b = v * y + d) :
    u = v ∧ b = d := by
  have hprod : (u - v) * (x - y) = 0 := by
    linear_combination hx - hy
  have huv : u = v := sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hxy))
  refine ⟨huv, ?_⟩
  rw [huv] at hx
  exact add_left_cancel hx

theorem complexDirectMotion_eq_of_two_points
    {u v b d x y : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hxy : x ≠ y)
    (hx : complexDirectMotion u b hu x = complexDirectMotion v d hv x)
    (hy : complexDirectMotion u b hu y = complexDirectMotion v d hv y) :
    complexDirectMotion u b hu = complexDirectMotion v d hv := by
  obtain ⟨huv, hbd⟩ := complexDirectMotion_coefficients_eq_of_two_points hxy hx hy
  subst v
  subst d
  rfl

end RepulsiveCoulomb
