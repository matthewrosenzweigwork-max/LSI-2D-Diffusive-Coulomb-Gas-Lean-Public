import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
import LeanResearch.RepulsiveCoulomb.JordanBezierCorner
import Mathlib.Analysis.Calculus.DSlope

/-! Actual point-argument lifts on a regular embedded C1 arc, including
observation at either endpoint. The vanishing endpoint chord is desingularized
by its divided difference. Thus a continuous lift reaches both endpoints
without pretending that the argument of zero is a direction. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The chord with its single possible endpoint zero divided out with the
positive source factor. The right endpoint uses the negative divided difference. -/
def pointArcPointVector (η : ℝ → ℂ) (p : ℂ) (u : ℝ) : ℂ :=
  if p = η 0 then dslope η 0 u else if p = η 1 then -dslope η 1 u else η u - p

theorem continuous_pointArcPointVector {η : ℝ → ℂ} (hη : ContDiff ℝ 1 η) (p : ℂ) :
    Continuous (pointArcPointVector η p) := by
  have hd (k : ℝ) : Continuous (dslope η k) := by
    apply continuousOn_univ.mp
    exact (continuousOn_dslope (s := univ) Filter.univ_mem).mpr
      ⟨hη.continuous.continuousOn, hη.differentiable (by norm_num) k⟩
  unfold pointArcPointVector
  split_ifs
  · exact hd 0
  · exact (hd 1).neg
  · exact hη.continuous.sub continuous_const

theorem pointArcPointVector_ne_zero {η : ℝ → ℂ}
    (hi : InjOn η (Icc (0 : ℝ) 1))
    (hreg : ∀ u ∈ Icc (0 : ℝ) 1, deriv η u ≠ 0)
    {p : ℂ} (hp : ∀ u ∈ Ioo (0 : ℝ) 1, η u ≠ p)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : pointArcPointVector η p u ≠ 0 := by
  have hd (k : ℝ) (hk : k ∈ Icc (0 : ℝ) 1) : dslope η k u ≠ 0 := by
    by_cases huk : u = k
    · subst u
      rw [dslope_same]
      exact hreg k hk
    · intro hzero
      have he := sub_smul_dslope η k u
      rw [hzero, smul_zero] at he
      exact huk (hi hu hk (sub_eq_zero.mp he.symm))
  unfold pointArcPointVector
  split_ifs with h0 h1
  · exact hd 0 (by norm_num)
  · exact neg_ne_zero.mpr (hd 1 (by norm_num))
  · apply sub_ne_zero.mpr
    by_cases hu0 : u = 0
    · subst u
      exact Ne.symm h0
    by_cases hu1 : u = 1
    · subst u
      exact Ne.symm h1
    exact hp u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩

/-- On the open arc the regularized vector has exactly the direction of
the actual chord. Both endpoint factors used in this comparison are positive. -/
theorem pointArcPointVector_direction {η : ℝ → ℂ}
    (hi : InjOn η (Icc (0 : ℝ) 1))
    (hreg : ∀ u ∈ Icc (0 : ℝ) 1, deriv η u ≠ 0)
    {p : ℂ} (hp : ∀ u ∈ Ioo (0 : ℝ) 1, η u ≠ p)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    euclideanDirection (pointArcPointVector η p u)
        (pointArcPointVector_ne_zero hi hreg hp ⟨hu.1.le, hu.2.le⟩) =
      euclideanDirection (η u - p) (sub_ne_zero.mpr (hp u hu)) := by
  have hv := pointArcPointVector_ne_zero hi hreg hp ⟨hu.1.le, hu.2.le⟩
  by_cases h0 : p = η 0
  · have hfactor : η u - p = u • pointArcPointVector η p u := by
      rw [pointArcPointVector, if_pos h0, h0]
      simpa only [sub_zero] using (sub_smul_dslope η (0 : ℝ) u).symm
    have hdir := euclideanDirection_smul_pos hv hu.1
    apply Circle.ext
    simpa only [euclideanDirection_coe, ← hfactor] using
      (congrArg (fun z : Circle => (z : ℂ)) hdir).symm
  by_cases h1 : p = η 1
  · have hfactor : η u - p = (1 - u) • pointArcPointVector η p u := by
      rw [pointArcPointVector, if_neg h0, if_pos h1, h1]
      calc
        η u - η 1 = (u - 1) • dslope η 1 u := (sub_smul_dslope η 1 u).symm
        _ = (1 - u) • -dslope η 1 u := by
          rw [smul_neg, ← neg_smul]
          congr 1
          ring
    have hdir := euclideanDirection_smul_pos hv (sub_pos.mpr hu.2)
    apply Circle.ext
    simpa only [euclideanDirection_coe, ← hfactor] using
      (congrArg (fun z : Circle => (z : ℂ)) hdir).symm
  apply Circle.ext
  simp only [euclideanDirection_coe, pointArcPointVector, if_neg h0, if_neg h1]

/-- Construct the continuous point-argument lift through the literal
regularized chord; only avoidance of the open arc is required. -/
theorem exists_regular_arc_point_argument_lift {η : ℝ → ℂ}
    (hη : ContDiff ℝ 1 η) (hi : InjOn η (Icc (0 : ℝ) 1))
    (hreg : ∀ u ∈ Icc (0 : ℝ) 1, deriv η u ≠ 0)
    (p : ℂ) (hp : ∀ u ∈ Ioo (0 : ℝ) 1, η u ≠ p) :
    ∃ ψ : Icc (0 : ℝ) 1 → ℝ, Continuous ψ ∧
      (∀ u, Complex.exp ((ψ u : ℂ) * Complex.I) =
        pointArcPointVector η p u / (‖pointArcPointVector η p u‖ : ℂ)) ∧
      ∀ u : Icc (0 : ℝ) 1, u.1 ∈ Ioo (0 : ℝ) 1 →
        Complex.exp ((ψ u : ℂ) * Complex.I) = (η u - p) / (‖η u - p‖ : ℂ) := by
  obtain ⟨ψ, hψ, hlift⟩ := exists_interval_euclidean_angle_lift
    ((continuous_pointArcPointVector hη p).comp continuous_subtype_val)
    (fun u => pointArcPointVector_ne_zero hi hreg hp u.2)
  refine ⟨ψ, hψ, hlift, ?_⟩
  intro u hu
  rw [hlift]
  exact congrArg (fun z : Circle => (z : ℂ)) (pointArcPointVector_direction hi hreg hp hu)

end RepulsiveCoulomb
