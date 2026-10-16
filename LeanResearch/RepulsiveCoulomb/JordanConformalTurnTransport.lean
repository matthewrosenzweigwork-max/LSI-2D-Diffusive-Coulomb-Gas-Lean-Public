import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Actual turn transport through a noncritical holomorphic coordinate chart.
A single-valued real angle of the actual complex derivative is constructed on
the simply connected chart domain. The change of an arc's tangent turn is then
an endpoint correction. Corners themselves keep their actual principal turn.
Records-only phase-four candidate, not yet checked. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem euclideanDirection_mul (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    euclideanDirection (z * w) (mul_ne_zero hz hw) =
      euclideanDirection z hz * euclideanDirection w hw := by
  apply Circle.ext
  simp only [euclideanDirection_coe, Circle.coe_mul, norm_mul, Complex.ofReal_mul]
  exact (div_mul_div_comm z (‖z‖ : ℂ) w (‖w‖ : ℂ)).symm

/-- Multiplication by the same nonzero conformal derivative preserves the
actual principal corner argument, including reflex corner conventions. -/
theorem conformal_corner_principal_turn (g u v : ℂ) (hg : g ≠ 0) :
    Complex.arg ((g * v) / (g * u)) = Complex.arg (v / u) := by
  congr 1
  field_simp

/-- Construct an angle of the actual chart differential. No logarithm or
angle-lift certificate is an input. -/
theorem exists_chart_derivative_angle {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {H : ℂ → ℂ}
    (hG : ContinuousOn (deriv H) U) (hne : ∀ z ∈ U, deriv H z ≠ 0) :
    ∃ ψ : U → ℝ, Continuous ψ ∧
      ∀ z : U, Circle.exp (ψ z) = euclideanDirection (deriv H z) (hne z z.2) := by
  letI := hUc.simplyConnectedSpace
  letI := hU.locallyPathConnectedSpace
  obtain ⟨z₀, hz₀⟩ := hUc.nonempty
  let z : U := ⟨z₀, hz₀⟩
  have hGc : Continuous (fun z : U => deriv H z) :=
    hG.comp_continuous continuous_subtype_val (fun z => z.2)
  obtain ⟨ψ, hψ, _, hψlift⟩ := exists_euclidean_angle_lift hGc
    (fun z : U => hne z z.2) z (Complex.arg (deriv H z)) (by
      rw [← euclideanDirection_arg (deriv H z) (hne z z.2)]
      exact Circle.exp_arg _)
  exact ⟨ψ, hψ, hψlift⟩

/-- There is a common endpoint correction for the turns of ALL actual regular
arcs in the chart. Consequently two replacements with the same endpoints have
exactly the same change of turn after applying the chart. -/
theorem exists_conformal_arc_turn_endpoint_correction {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsSimplyConnected U) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H U) (hG : ContinuousOn (deriv H) U)
    (hne : ∀ z ∈ U, deriv H z ≠ 0) :
    ∃ ψ : U → ℝ, Continuous ψ ∧
      ∀ (η : ℝ → ℂ) (hη : ContDiff ℝ 1 η)
        (hηU : MapsTo η (Icc (0 : ℝ) 1) U)
        (hηreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv η t ≠ 0)
        (θ Θ : Icc (0 : ℝ) 1 → ℝ),
        Continuous θ → Continuous Θ →
        (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) = deriv η t / (‖deriv η t‖ : ℂ)) →
        (∀ t, Complex.exp ((Θ t : ℂ) * Complex.I) =
          deriv (H ∘ η) t / (‖deriv (H ∘ η) t‖ : ℂ)) →
        (Θ 1 - Θ 0) - (θ 1 - θ 0) =
          ψ ⟨η 1, hηU (by norm_num)⟩ - ψ ⟨η 0, hηU (by norm_num)⟩ := by
  obtain ⟨ψ, hψ, hψlift⟩ := exists_chart_derivative_angle hU hUc hG hne
  refine ⟨ψ, hψ, ?_⟩
  intro η hη hηU hηreg θ Θ hθ hΘ hθlift hΘlift
  let ηU : Icc (0 : ℝ) 1 → U := fun t => ⟨η t, hηU t.2⟩
  have hηUc : Continuous ηU :=
    (hη.continuous.comp continuous_subtype_val).subtype_mk _
  let α : Icc (0 : ℝ) 1 → ℝ := fun t => ψ (ηU t) + θ t
  have hα : Continuous α := (hψ.comp hηUc).add hθ
  have hD (t : Icc (0 : ℝ) 1) :
      deriv (H ∘ η) t = deriv H (η t) * deriv η t := by
    have hHt : HasDerivAt H (deriv H (η t)) (η t) :=
      ((hH (η t) (hηU t.2)).differentiableAt (hU.mem_nhds (hηU t.2))).hasDerivAt
    have hηt : HasDerivAt η (deriv η (t : ℝ)) (t : ℝ) :=
      ((hη.differentiable (by norm_num)) (t : ℝ)).hasDerivAt
    exact (hHt.comp (t : ℝ) hηt).deriv
  have hαlift (t : Icc (0 : ℝ) 1) : Circle.exp (α t) = Circle.exp (Θ t) := by
    have hθcircle : Circle.exp (θ t) = euclideanDirection (deriv η t) (hηreg t t.2) := by
      apply Circle.ext
      exact hθlift t
    have hΘcircle : Circle.exp (Θ t) = euclideanDirection
        (deriv H (η t) * deriv η t) (mul_ne_zero (hne _ (hηU t.2)) (hηreg _ t.2)) := by
      apply Circle.ext
      simpa only [Circle.coe_exp, euclideanDirection_coe, hD] using hΘlift t
    change Circle.exp (ψ (ηU t) + θ t) = Circle.exp (Θ t)
    rw [Circle.exp_add, hψlift, hθcircle, hΘcircle,
      euclideanDirection_mul _ _ (hne _ (hηU t.2)) (hηreg _ t.2)]
  have hinc := euclidean_angle_lift_increment_eq hα hΘ hαlift
    (0 : Icc (0 : ℝ) 1) 1
  change (ψ (ηU 1) + θ 1) - (ψ (ηU 0) + θ 0) = Θ 1 - Θ 0 at hinc
  have hzero : ηU 0 = ⟨η 0, hηU (by norm_num)⟩ := by apply Subtype.ext; simp [ηU]
  have hone : ηU 1 = ⟨η 1, hηU (by norm_num)⟩ := by apply Subtype.ext; simp [ηU]
  rw [hzero, hone] at hinc
  linarith

end RepulsiveCoulomb
