import LeanResearch.RepulsiveCoulomb.JordanSmoothSecantSquare
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! A genuine, geometrically supported smooth turning theorem.

For a regular C¹ simple periodic loop with the supporting line chosen at the
basepoint, unit positive tangent and the whole curve in the upper half-plane,
the actual tangent-angle increment is `2π`. The secant square is constructed
from the curve. No turning-index or Gauss--Bonnet certificate is assumed.

This does NOT yet cover the finite-corner input of the full task, and does not
identify the sign with the bounded Jordan component. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

private def reverseUnitParameter (r : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨1 - r.1, by constructor <;> linarith [r.2.1, r.2.2]⟩

private theorem reverseUnitParameter_continuous : Continuous reverseUnitParameter := by
  exact (continuous_const.sub continuous_subtype_val).subtype_mk _

private theorem square_angle_doubling
    (S : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → Circle)
    (htop : ∀ s, S (s, 1) = S (0, 1))
    (hside : ∀ r, S (1, r) = -S (0, reverseUnitParameter r))
    (A : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℝ) (hA : Continuous A)
    (hlift : ∀ p, Circle.exp (A p) = S p) :
    A (1, 0) - A (0, 0) = 2 * (A (0, 1) - A (0, 0)) := by
  have htopA : A (1, 1) = A (0, 1) :=
    Circle.isCoveringMap_exp.const_of_comp
      (hA.comp (continuous_id.prodMk continuous_const))
      (by intro a b; change Circle.exp (A (a, 1)) = Circle.exp (A (b, 1))
          rw [hlift, hlift, htop a, htop b]) 1 0
  have hdiffcont : Continuous (fun r => A (1, r) - A (0, reverseUnitParameter r)) :=
    (hA.comp (continuous_const.prodMk continuous_id)).sub
      (hA.comp (continuous_const.prodMk reverseUnitParameter_continuous))
  have hdiffexp (r : Icc (0 : ℝ) 1) :
      Circle.exp (A (1, r) - A (0, reverseUnitParameter r)) = -1 := by
    rw [Circle.exp_sub, hlift, hlift, hside, neg_div, div_self']
  have hdiff := Circle.isCoveringMap_exp.const_of_comp hdiffcont
    (by intro a b; exact (hdiffexp a).trans (hdiffexp b).symm)
    (0 : Icc (0 : ℝ) 1) 1
  have hr0 : reverseUnitParameter 0 = 1 := by apply Subtype.ext; simp [reverseUnitParameter]
  have hr1 : reverseUnitParameter 1 = 0 := by apply Subtype.ext; simp [reverseUnitParameter]
  change A (1, 0) - A (0, reverseUnitParameter 0) =
    A (1, 1) - A (0, reverseUnitParameter 1) at hdiff
  rw [hr0, hr1] at hdiff
  linarith

/-- The circle argument is continuous on the upper semicircle including both
real-axis endpoints.  This avoids crossing the principal branch cut. -/
theorem continuous_circle_arg_of_im_nonneg {X : Type*} [TopologicalSpace X]
    {S : X → Circle} (hS : Continuous S) (him : ∀ x, 0 ≤ (S x : ℂ).im) :
    Continuous (fun x => Complex.arg (S x : ℂ)) := by
  have heq : (fun x => Complex.arg (S x : ℂ)) =
      (fun x => Real.arccos (S x : ℂ).re) := by
    funext x
    rw [Complex.arg_of_im_nonneg_of_ne_zero (him x) (Circle.coe_ne_zero _),
      Circle.norm_coe, div_one]
  rw [heq]
  exact Real.continuous_arccos.comp
    (Complex.continuous_re.comp (continuous_subtype_val.comp hS))

private theorem supported_square_turn
    (S : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → Circle) (hS : Continuous S)
    (htop : ∀ s, S (s, 1) = S (0, 1))
    (hside : ∀ r, S (1, r) = -S (0, reverseUnitParameter r))
    (him : ∀ r, 0 ≤ (S (0, r) : ℂ).im)
    (hstart : S (0, 0) = 1) (hend : S (0, 1) = -1)
    (A : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℝ) (hA : Continuous A)
    (hlift : ∀ p, Circle.exp (A p) = S p) :
    A (1, 0) - A (0, 0) = 2 * Real.pi := by
  have hleft : Continuous (fun r : Icc (0 : ℝ) 1 => S (0, r)) :=
    hS.comp (continuous_const.prodMk continuous_id)
  have harg := continuous_circle_arg_of_im_nonneg hleft him
  have hinc := euclidean_angle_lift_increment_eq
    (hA.comp (continuous_const.prodMk continuous_id)) harg
    (fun r => (hlift (0, r)).trans (Circle.exp_arg (S (0, r))).symm)
    (0 : Icc (0 : ℝ) 1) 1
  have harg0 : Complex.arg (S (0, 0) : ℂ) = 0 := by rw [hstart]; simp
  have harg1 : Complex.arg (S (0, 1) : ℂ) = Real.pi := by rw [hend]; simp [Complex.arg_neg_one]
  change A (0, 1) - A (0, 0) =
    Complex.arg (S (0, 1) : ℂ) - Complex.arg (S (0, 0) : ℂ) at hinc
  rw [harg0, harg1, sub_zero] at hinc
  rw [square_angle_doubling S htop hside A hA hlift, hinc]

theorem periodic_loop_deriv_one_eq_zero {γ : ℝ → ℂ} (hp : Function.Periodic γ 1) :
    deriv γ 1 = deriv γ 0 := by
  have heq : (fun t : ℝ => γ (t + 1)) = γ := funext hp
  have h := congrArg (fun f : ℝ → ℂ => deriv f 0) heq
  simpa only [deriv_comp_add_const, zero_add] using h

theorem euclideanSecantSquare_left_im_nonneg {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hbase : deriv γ 0 = 1)
    (hsupport : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ (γ r - γ 0).im)
    (r : Icc (0 : ℝ) 1) :
    0 ≤ (euclideanSecantSquare γ (0, (r : ℝ))).im := by
  by_cases hr0 : (r : ℝ) = 0
  · simp [hr0, hbase]
  by_cases hr1 : (r : ℝ) = 1
  · simp [hr1, hbase]
  have hr : (r : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne r.2.1 (Ne.symm hr0), lt_of_le_of_ne r.2.2 hr1⟩
  have hscale := euclideanSecantScale_pos hr
  have heq := congrArg Complex.im (euclideanSecantSquare_smul hγ hp 0 r)
  simp only [mul_zero, zero_add, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at heq
  have hn := hsupport r r.2
  nlinarith

/-- Actual Euclidean total turn for a supported, normalized regular C¹ simple
periodic loop.  Every geometric and angle-lifting input is the actual curve;
there is no total-turn, angle-sum, triangulation, or Gauss--Bonnet hypothesis. -/
theorem regular_simple_supported_loop_total_turn
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hbase : deriv γ 0 = 1)
    (hsupport : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ (γ r - γ 0).im)
    {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hθlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      deriv γ t / (‖deriv γ t‖ : ℂ)) :
    θ 1 - θ 0 = 2 * Real.pi := by
  let S : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → Circle := fun p =>
    euclideanDirection (euclideanSecantSquare γ (p.1, p.2))
      (euclideanSecantSquare_ne_zero hγ hp hinj hregular p.1 p.2)
  have hS : Continuous S := continuous_euclideanDirection
    ((euclideanSecantSquare_continuous hγ hp).comp (by fun_prop)) _
  obtain ⟨A, hA, hlift⟩ := exists_square_circle_angle_lift S hS
  have htop : ∀ s, S (s, 1) = S (0, 1) := by
    intro s
    apply Circle.ext
    simp [S]
  have hside : ∀ r, S (1, r) = -S (0, reverseUnitParameter r) := by
    intro r
    apply Circle.ext
    simp only [S, euclideanDirection_coe, Circle.coe_neg, reverseUnitParameter]
    change euclideanSecantSquare γ (1, (r : ℝ)) /
      (‖euclideanSecantSquare γ (1, (r : ℝ))‖ : ℂ) =
      -(euclideanSecantSquare γ (0, 1 - (r : ℝ)) /
        (‖euclideanSecantSquare γ (0, 1 - (r : ℝ))‖ : ℂ))
    rw [euclideanSecantSquare_side_symmetry hγ hp r (periodic_loop_deriv_one_eq_zero hp),
      norm_neg, neg_div]
  have him : ∀ r, 0 ≤ (S (0, r) : ℂ).im := by
    intro r
    change 0 ≤ (euclideanSecantSquare γ (0, (r : ℝ)) /
      (‖euclideanSecantSquare γ (0, (r : ℝ))‖ : ℂ)).im
    rw [Complex.div_ofReal_im]
    exact div_nonneg (euclideanSecantSquare_left_im_nonneg hγ hp hbase hsupport r)
      (norm_nonneg _)
  have hstart : S (0, 0) = 1 := by
    apply Circle.ext
    simp [S, hbase]
  have hend : S (0, 1) = -1 := by
    apply Circle.ext
    simp [S, hbase]
  have hturn := supported_square_turn S hS htop hside him hstart hend A hA hlift
  have hAbottom : Continuous (fun t : Icc (0 : ℝ) 1 => A (t, 0)) :=
    hA.comp (continuous_id.prodMk continuous_const)
  have hinc := euclidean_angle_lift_increment_eq hθ hAbottom
    (fun t => by
      change Circle.exp (θ t) = Circle.exp (A (t, 0))
      rw [hlift]
      apply Circle.ext
      simpa [Circle.coe_exp, S] using hθlift t)
    (0 : Icc (0 : ℝ) 1) 1
  exact hinc.trans hturn

end RepulsiveCoulomb
