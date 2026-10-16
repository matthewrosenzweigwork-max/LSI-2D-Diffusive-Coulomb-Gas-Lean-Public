module

public import LeanResearch.RepulsiveCoulomb.JordanArgumentHomotopy

@[expose] public section

/-! Actual argument increments are preserved by the endpoint-fixed local
corner homotopies, even though the corner arcs themselves are not closed.
This permits a genuine finite telescoping transport without first building a
separate global homotopy or assuming a winding identity. Records-only draft. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- A continuous nonvanishing homotopy through endpoint-fixed actual vector arcs
preserves the increment of any continuous real argument lifts. -/
theorem endpoint_fixed_vector_arc_argument_homotopy
    (F : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ) (hF : Continuous F)
    (hne : ∀ p, F p ≠ 0)
    (hstart : ∀ s, F (s, 0) = F (0, 0)) (hfinish : ∀ s, F (s, 1) = F (0, 1))
    (θ₀ θ₁ : Icc (0 : ℝ) 1 → ℝ) (hθ₀ : Continuous θ₀) (hθ₁ : Continuous θ₁)
    (hlift₀ : ∀ t, Complex.exp ((θ₀ t : ℂ) * Complex.I) = F (0, t) / (‖F (0, t)‖ : ℂ))
    (hlift₁ : ∀ t, Complex.exp ((θ₁ t : ℂ) * Complex.I) = F (1, t) / (‖F (1, t)‖ : ℂ)) :
    θ₀ 1 - θ₀ 0 = θ₁ 1 - θ₁ 0 := by
  let S := fun p => euclideanDirection (F p) (hne p)
  have hS : Continuous S := continuous_euclideanDirection hF hne
  obtain ⟨A, hA, hAlift⟩ := exists_square_circle_angle_lift S hS
  have hstarts (s : Icc (0 : ℝ) 1) : S (s, 0) = S (0, 0) := by
    apply Circle.ext
    simp only [S, euclideanDirection_coe, hstart s]
  have hfinishes (s : Icc (0 : ℝ) 1) : S (s, 1) = S (0, 1) := by
    apply Circle.ext
    simp only [S, euclideanDirection_coe, hfinish s]
  have hDcont : Continuous (fun s : Icc (0 : ℝ) 1 => A (s, 1) - A (s, 0)) :=
    (hA.comp (continuous_id.prodMk continuous_const)).sub
      (hA.comp (continuous_id.prodMk continuous_const))
  have hDexp (s : Icc (0 : ℝ) 1) : Circle.exp (A (s, 1) - A (s, 0)) = S (0, 1) / S (0, 0) := by
    rw [Circle.exp_sub, hAlift, hAlift, hstarts, hfinishes]
  have hD := Circle.isCoveringMap_exp.const_of_comp hDcont
    (by intro a b; exact (hDexp a).trans (hDexp b).symm)
    (0 : Icc (0 : ℝ) 1) 1
  have hleft : Continuous (fun t : Icc (0 : ℝ) 1 => A (0, t)) :=
    hA.comp (continuous_const.prodMk continuous_id)
  have hright : Continuous (fun t : Icc (0 : ℝ) 1 => A (1, t)) :=
    hA.comp (continuous_const.prodMk continuous_id)
  have hi₀ := euclidean_angle_lift_increment_eq hθ₀ hleft
    (fun t => by
      change Circle.exp (θ₀ t) = Circle.exp (A (0, t))
      rw [hAlift]
      apply Circle.ext
      exact hlift₀ t) (0 : Icc (0 : ℝ) 1) 1
  have hi₁ := euclidean_angle_lift_increment_eq hθ₁ hright
    (fun t => by
      change Circle.exp (θ₁ t) = Circle.exp (A (1, t))
      rw [hAlift]
      apply Circle.ext
      exact hlift₁ t) (0 : Icc (0 : ℝ) 1) 1
  exact hi₀.trans (hD.trans hi₁.symm)

/-- Apply the endpoint-fixed vector theorem to an actual physical corner
homotopy avoiding a chosen observation point. -/
theorem endpoint_fixed_arc_point_argument_homotopy
    (F : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ) (hF : Continuous F)
    (hstart : ∀ s, F (s, 0) = F (0, 0)) (hfinish : ∀ s, F (s, 1) = F (0, 1))
    (w : ℂ) (havoid : ∀ p, F p ≠ w)
    (θ₀ θ₁ : Icc (0 : ℝ) 1 → ℝ) (hθ₀ : Continuous θ₀) (hθ₁ : Continuous θ₁)
    (hlift₀ : ∀ t, Complex.exp ((θ₀ t : ℂ) * Complex.I) =
      (F (0, t) - w) / (‖F (0, t) - w‖ : ℂ))
    (hlift₁ : ∀ t, Complex.exp ((θ₁ t : ℂ) * Complex.I) =
      (F (1, t) - w) / (‖F (1, t) - w‖ : ℂ)) :
    θ₀ 1 - θ₀ 0 = θ₁ 1 - θ₁ 0 := by
  exact endpoint_fixed_vector_arc_argument_homotopy (fun p => F p - w)
    (hF.sub continuous_const) (fun p => sub_ne_zero.mpr (havoid p))
    (fun s => by rw [hstart]) (fun s => by rw [hfinish]) θ₀ θ₁ hθ₀ hθ₁ hlift₀ hlift₁

end RepulsiveCoulomb
