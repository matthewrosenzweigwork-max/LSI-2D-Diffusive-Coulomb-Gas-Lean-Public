import LeanResearch.RepulsiveCoulomb.JordanOneRegularPointWinding
import LeanResearch.RepulsiveCoulomb.JordanSmoothWindingOrientation
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Move the actual positive inside orientation to any regular parameter of
a C0 simple periodic loop. A global position-angle lift is constructed, and
its increment is shown invariant under the actual basepoint shift. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem positive_inside_argument_forces_left_normal_at
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hdiff : DifferentiableAt ℝ γ a) (hd : deriv γ a ≠ 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ)
    {w : ℂ} (hw : w ∈ U) {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      (γ t - w) / (‖γ t - w‖ : ℂ)) (hturn : θ 1 - θ 0 = 2 * Real.pi) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      γ a + (ε : ℂ) * Complex.I * deriv γ a ∈ U ∧
      γ a - (ε : ℂ) * Complex.I * deriv γ a ∈ V := by
  let v : ℝ → ℂ := fun t => γ t - w
  have hv : Continuous v := hγ.sub continuous_const
  have hne (t : ℝ) : v t ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hnot : w ∈ (γ '' Icc (0 : ℝ) 1)ᶜ := hcover ▸ Or.inl hw
    rw [periodic_loop_closed_image_eq_range hp] at hnot
    exact hnot ⟨t, he⟩
  obtain ⟨Ψ, hΨ, _, hΨcircle⟩ := exists_euclidean_angle_lift hv hne 0 (Complex.arg (v 0)) (by
    rw [← euclideanDirection_arg (v 0) (hne 0)]
    exact Circle.exp_arg _)
  have hΨlift (t : ℝ) : Complex.exp ((Ψ t : ℂ) * Complex.I) = v t / (‖v t‖ : ℂ) := by
    simpa only [Circle.coe_exp, euclideanDirection_coe] using
      congrArg (fun z : Circle => (z : ℂ)) (hΨcircle t)
  have heq := euclidean_angle_lift_increment_eq hθ (hΨ.comp continuous_subtype_val)
    (fun t => by
      apply Circle.ext
      simpa only [Circle.coe_exp, Function.comp_def] using (hlift t).trans (hΨlift t).symm)
    (0 : Icc (0 : ℝ) 1) 1
  change θ 1 - θ 0 = Ψ 1 - Ψ 0 at heq
  have hvp : Function.Periodic v 1 := by intro t; change γ (t + 1) - w = γ t - w; rw [hp]
  have hinc := periodic_vector_argument_increment hvp hΨ hΨlift a
  let Γ : ℝ → ℂ := fun t => γ (t + a)
  have hΓc : Continuous Γ := by dsimp [Γ]; fun_prop
  have hΓp : Function.Periodic Γ 1 := by
    intro t
    change γ (t + 1 + a) = γ (t + a)
    rw [show t + 1 + a = (t + a) + 1 by ring, hp]
  have hΓi : InjOn Γ (Ico (0 : ℝ) 1) := periodic_simple_loop_shift_injOn hp hinj ha
  have hDa : HasDerivAt γ (deriv γ a) (0 + a) := by simpa only [zero_add] using hdiff.hasDerivAt
  have hΓD : HasDerivAt Γ (deriv γ a) 0 := hDa.comp_add_const 0 a
  have hΓreg : deriv Γ 0 ≠ 0 := by rw [hΓD.deriv]; exact hd
  have hΓimage : Γ '' Icc (0 : ℝ) 1 = γ '' Icc (0 : ℝ) 1 := periodic_loop_shift_closed_image hp a
  have hcoverΓ : U ∪ V = (Γ '' Icc (0 : ℝ) 1)ᶜ := by rwa [hΓimage]
  let Θ : Icc (0 : ℝ) 1 → ℝ := fun t => Ψ (t.1 + a)
  have hΘ : Continuous Θ := hΨ.comp (continuous_subtype_val.add continuous_const)
  have hΘlift (t : Icc (0 : ℝ) 1) : Complex.exp ((Θ t : ℂ) * Complex.I) =
      (Γ t - w) / (‖Γ t - w‖ : ℂ) := hΨlift (t.1 + a)
  have hΘturn : Θ 1 - Θ 0 = 2 * Real.pi := by
    change Ψ (1 + a) - Ψ (0 + a) = 2 * Real.pi
    rw [zero_add, add_comm 1 a, hinc, ← heq, hturn]
  obtain ⟨r, hr, hnormals⟩ := positive_inside_argument_forces_left_normal hΓc hΓD.differentiableAt
    hΓp hΓi hΓreg hU hUc hV hVc hK hcoverΓ hw hΘ hΘlift hΘturn
  have hΓ0 : Γ 0 = γ a := by simp only [Γ, zero_add]
  rw [hΓ0, hΓD.deriv] at hnormals
  exact ⟨r, hr, hnormals⟩

end RepulsiveCoulomb
