import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
import Mathlib.Analysis.Complex.Convex

/-! The exact turn of the actual linear interpolation of two noncuspidal
one-sided tangent vectors. This supplies the local corner calculation in the
secant-triangle proof. It does not assume a corner-turn certificate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def euclideanCornerBlend (u v : ℂ) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * u + (t : ℂ) * v

@[simp] theorem euclideanCornerBlend_zero (u v : ℂ) :
    euclideanCornerBlend u v 0 = u := by simp [euclideanCornerBlend]

@[simp] theorem euclideanCornerBlend_one (u v : ℂ) :
    euclideanCornerBlend u v 1 = v := by simp [euclideanCornerBlend]

theorem euclideanCornerBlend_div (u v : ℂ) (hu : u ≠ 0) (t : ℝ) :
    euclideanCornerBlend u v t / u =
      (1 - t) • (1 : ℂ) + t • (v / u) := by
  simp only [euclideanCornerBlend, Complex.real_smul, Complex.ofReal_sub,
    Complex.ofReal_one, mul_one]
  field_simp

theorem euclideanCornerBlend_div_mem_slitPlane {u v : ℂ} (hu : u ≠ 0)
    (hcorner : v / u ∈ Complex.slitPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    euclideanCornerBlend u v t / u ∈ Complex.slitPlane := by
  rw [euclideanCornerBlend_div u v hu t]
  exact Complex.starConvex_one_slitPlane hcorner (sub_nonneg.mpr ht.2) ht.1
    (sub_add_cancel 1 t)

theorem euclideanCornerBlend_ne_zero {u v : ℂ} (hu : u ≠ 0)
    (hcorner : v / u ∈ Complex.slitPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    euclideanCornerBlend u v t ≠ 0 := by
  intro h
  have hn := Complex.slitPlane_ne_zero (euclideanCornerBlend_div_mem_slitPlane hu hcorner ht)
  exact hn (by rw [h, zero_div])

/-- A continuous argument for the actual blended tangent is written explicitly.
Its endpoint increment is exactly the principal argument of the tangent ratio. -/
theorem euclideanCornerBlend_angle_lift {u v : ℂ} (hu : u ≠ 0)
    (hcorner : v / u ∈ Complex.slitPlane) :
    ∃ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ ∧
      (∀ t, Circle.exp (θ t) = euclideanDirection (euclideanCornerBlend u v t)
        (euclideanCornerBlend_ne_zero hu hcorner t.2)) ∧
      θ 1 - θ 0 = Complex.arg (v / u) := by
  let θ : Icc (0 : ℝ) 1 → ℝ := fun t =>
    Complex.arg (euclideanCornerBlend u v t / u) + Complex.arg u
  have hcont : Continuous θ := by
    apply Continuous.add _ continuous_const
    apply continuous_iff_continuousAt.mpr
    intro t
    have hq : Continuous (fun t : Icc (0 : ℝ) 1 => euclideanCornerBlend u v t / u) := by
      unfold euclideanCornerBlend
      fun_prop
    exact (Complex.continuousAt_arg
      (euclideanCornerBlend_div_mem_slitPlane hu hcorner t.2)).comp
        (f := fun t : Icc (0 : ℝ) 1 => euclideanCornerBlend u v t / u)
        (x := t) hq.continuousAt
  refine ⟨θ, hcont, fun t => ?_, ?_⟩
  · change Circle.exp (Complex.arg (euclideanCornerBlend u v t / u) + Complex.arg u) = _
    rw [Circle.exp_add, circle_exp_arg_vector_ratio _ _
      (euclideanCornerBlend_ne_zero hu hcorner t.2) hu,
      ← euclideanDirection_arg u hu, Circle.exp_arg]
    simp
  · simp [θ, hu]

/-- Every continuous lift of the actual blended tangent measures the same
principal corner turn. -/
theorem euclideanCornerBlend_lift_increment {u v : ℂ} (hu : u ≠ 0)
    (hcorner : v / u ∈ Complex.slitPlane)
    {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hlift : ∀ t, Circle.exp (θ t) = euclideanDirection (euclideanCornerBlend u v t)
      (euclideanCornerBlend_ne_zero hu hcorner t.2)) :
    θ 1 - θ 0 = Complex.arg (v / u) := by
  obtain ⟨φ, hφ, hφlift, hφinc⟩ := euclideanCornerBlend_angle_lift hu hcorner
  rw [euclidean_angle_lift_increment_eq hθ hφ (fun t => (hlift t).trans (hφlift t).symm)
    (0 : Icc (0 : ℝ) 1) 1]
  exact hφinc

end RepulsiveCoulomb
