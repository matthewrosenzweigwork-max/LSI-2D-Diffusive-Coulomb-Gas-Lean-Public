import LeanResearch.RepulsiveCoulomb.PointConformalConnection
import LeanResearch.RepulsiveCoulomb.PointArgumentLiftDerivative
import LeanResearch.RepulsiveCoulomb.JordanConformalTurnTransport

/-! Actual phase and point-argument transport identities. A fixed developed
nonzero tangent determines the tangent-angle increment, and continuous argument
lifts of the literal puncture factors differentiate to the literal connection.
These are local/arc identities, not global winding or Gauss--Bonnet assumptions. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem euclideanDirection_cexp (z : ℂ) :
    euclideanDirection (Complex.exp z) (Complex.exp_ne_zero z) = Circle.exp z.im := by
  have he : Complex.exp z = (Real.exp z.re : ℂ) * (Circle.exp z.im : ℂ) := by
    rw [Circle.coe_exp, Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]
  apply Circle.ext
  rw [euclideanDirection_coe, Complex.norm_exp, he, mul_comm,
    mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos z.re).ne')]

/-- This exact increment is derived from actual parallel transport, with no
choice of an integer multiple or a prescribed turn supplied by the caller. -/
theorem parallel_phase_tangent_increment {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {v G : X → ℂ} {θ : X → ℝ} {w : ℂ}
    (hw : w ≠ 0) (hv : ∀ x, v x ≠ 0) (hG : Continuous G) (hθ : Continuous θ)
    (hlift : ∀ x, Circle.exp (θ x) = euclideanDirection (v x) (hv x))
    (hparallel : ∀ x, Complex.exp (G x) * v x = w) (a b : X) :
    θ b - θ a = (G a).im - (G b).im := by
  have hexp (x : X) : Circle.exp (θ x + (G x).im) = Circle.exp (Complex.arg w) := by
    rw [Circle.exp_add, hlift x, ← euclideanDirection_cexp, mul_comm,
      ← euclideanDirection_mul _ _ (Complex.exp_ne_zero _) (hv x)]
    have he : euclideanDirection (Complex.exp (G x) * v x)
        (mul_ne_zero (Complex.exp_ne_zero _) (hv x)) = euclideanDirection w hw := by
      apply Circle.ext
      simp only [euclideanDirection_coe, hparallel x]
    rw [he, ← euclideanDirection_arg w hw, Circle.exp_arg]
  have h := euclidean_angle_lift_increment_eq (hθ.add (Complex.continuous_im.comp hG))
    continuous_const hexp a b
  change (θ b + (G b).im) - (θ a + (G a).im) = Complex.arg w - Complex.arg w at h
  linarith

/-- Differentiate the weighted sum of actual argument lifts of all active
puncture factors. Zero weights require no avoidance of their nominal locations. -/
theorem hasDerivAt_point_weighted_argument {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {η : ℝ → ℂ} {t : ℝ}
    (hη : DifferentiableAt ℝ η t) (hp : η t ∉ pointPunctures a y)
    (ψ : Fin m → ℝ → ℝ) (hψ : ∀ j, ContinuousAt (ψ j) t)
    (hlift : ∀ j, a j ≠ 0 → ∀ᶠ s in 𝓝 t,
      Complex.exp ((ψ j s : ℂ) * Complex.I) = (η s - y j) / (‖η s - y j‖ : ℂ)) :
    HasDerivAt (fun s => ∑ j, (a j / 2) * ψ j s)
      (pointConformalConnection a y (η t) * deriv η t).im t := by
  have hterm (j : Fin m) : HasDerivAt (fun s => (a j / 2) * ψ j s)
      ((a j / 2) * (deriv η t / (η t - y j)).im) t := by
    by_cases haj : a j = 0
    · simp only [haj, zero_div, zero_mul]
      exact hasDerivAt_const t (0 : ℝ)
    · have hne : η t - y j ≠ 0 := sub_ne_zero.mpr (fun he =>
        hp ⟨j, lt_of_le_of_ne (ha j) (Ne.symm haj), he⟩)
      have hd := hasDerivAt_continuous_argument_lift (hη.sub_const (y j)) hne
        (hψ j) (hlift j haj)
      have hderiv : deriv (fun s => η s - y j) t = deriv η t :=
        (hη.hasDerivAt.sub_const (y j)).deriv
      rw [hderiv] at hd
      exact hd.const_mul (a j / 2)
  have hsum : HasDerivAt (fun s => ∑ j, (a j / 2) * ψ j s)
      (∑ j, (a j / 2) * (deriv η t / (η t - y j)).im) t := by
    convert! HasDerivAt.sum (u := Finset.univ) (fun j _ => hterm j) using 1
    ext s
    simp
  have heq : (∑ j, (a j / 2) * (deriv η t / (η t - y j)).im) =
      (pointConformalConnection a y (η t) * deriv η t).im := by
    rw [pointConformalConnection_eq_reciprocal_sum, Finset.sum_mul, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    have halg : (((a j / 2 : ℝ) : ℂ) / (η t - y j)) * deriv η t =
        ((a j / 2 : ℝ) : ℂ) * (deriv η t / (η t - y j)) := by ring
    rw [halg]
    simp
  rw [heq] at hsum
  exact hsum

end RepulsiveCoulomb
