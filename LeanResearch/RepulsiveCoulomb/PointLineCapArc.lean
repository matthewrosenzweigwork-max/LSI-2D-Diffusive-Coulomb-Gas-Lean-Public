module

public import LeanResearch.RepulsiveCoulomb.PointCircleCapArc
public import LeanResearch.RepulsiveCoulomb.PointRadialSectorNormalization
public import LeanResearch.RepulsiveCoulomb.CircleTransverseCorner
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Records-only, uncompiled. Choose the literal counterclockwise arc from the
positive crossing to the negative crossing. Its width is strictly between zero
and one full turn. This is a geometric choice, not a supplied Jordan side. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

@[simp] theorem lineCapArc_zero (R α β : ℝ) :
    pointCircleCapArc R α β 0 = pointRadialSectorPoint R α := by
  simp only [pointCircleCapArc, mul_zero, add_zero]

@[simp] theorem lineCapArc_one (R α β : ℝ) :
    pointCircleCapArc R α β 1 = pointRadialSectorPoint R β := by
  simp only [pointCircleCapArc, mul_one, add_sub_cancel]

/-- Equal-radius distinct points determine a positive circular interval of
width below 2π. The positive crossing's principal argument is only an origin
for the lift; the closing arc never uses a principal-angle truncation. -/
theorem exists_lineCapArc_angles {p q : ℂ} {R : ℝ} (hR : 0 < R)
    (hp : ‖p‖ = R) (hq : ‖q‖ = R) (hpq : p ≠ q) :
    ∃ α β : ℝ, α < β ∧ β < α + 2 * Real.pi ∧
      pointCircleCapArc R α β 0 = q ∧ pointCircleCapArc R α β 1 = p := by
  obtain ⟨c, hc, θ, hθ, hθ2, hq0, hpθ, hratio⟩ :=
    exists_pointRadialSector_normalization (hq.trans hp.symm) hpq.symm
  let α := Complex.arg q
  have hqne : q ≠ 0 := norm_pos_iff.mp (by rw [hq]; exact hR)
  have hbase : pointRadialSectorPoint R α = q := by
    rw [← hq]
    exact Complex.norm_mul_exp_arg_mul_I q
  have hend : pointRadialSectorPoint R (α + θ) = p := by
    calc
      pointRadialSectorPoint R (α + θ) =
          pointRadialSectorPoint R α * (Circle.exp θ : ℂ) := by
        simp only [pointRadialSectorPoint, Circle.exp_add, Circle.coe_mul]
        ring
      _ = q * (Circle.exp θ : ℂ) := by rw [hbase]
      _ = p := by
        rw [← hratio]
        exact mul_div_cancel₀ p hqne
  exact ⟨α, α + θ, by linarith, by linarith,
    by rw [lineCapArc_zero]; exact hbase, by rw [lineCapArc_one]; exact hend⟩

theorem lineCapArc_injOn {R α β : ℝ} (hR : 0 < R)
    (hab : α < β) (hwidth : β < α + 2 * Real.pi) :
    InjOn (pointCircleCapArc R α β) (Icc (0 : ℝ) 1) := by
  intro s hs t ht he
  have hsangle : α + (β - α) * s ∈ Ico α (α + 2 * Real.pi) := by
    constructor
    · nlinarith [mul_nonneg (sub_pos.mpr hab).le hs.1]
    · have h := mul_le_mul_of_nonneg_left hs.2 (sub_pos.mpr hab).le
      nlinarith
  have htangle : α + (β - α) * t ∈ Ico α (α + 2 * Real.pi) := by
    constructor
    · nlinarith [mul_nonneg (sub_pos.mpr hab).le ht.1]
    · have h := mul_le_mul_of_nonneg_left ht.2 (sub_pos.mpr hab).le
      nlinarith
  have hphase : (Circle.exp (α + (β - α) * s) : ℂ) =
      (Circle.exp (α + (β - α) * t) : ℂ) :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne') he
  have hang := Circle.exp_injOn_Ico (a := α) (b := α + 2 * Real.pi) (by linarith)
    hsangle htangle (Subtype.ext hphase)
  nlinarith [sub_pos.mpr hab]

/-- Counterclockwise is literal: every velocity is a strictly positive multiple
of I times its radius vector. -/
theorem lineCapArc_positive_circle_velocity {R α β : ℝ}
    (hab : α < β) (t : ℝ) :
    ∃ k : ℝ, 0 < k ∧ deriv (pointCircleCapArc R α β) t =
      k • (Complex.I * pointCircleCapArc R α β t) :=
  ⟨β - α, sub_pos.mpr hab, (hasDerivAt_pointCircleCapArc R α β t).deriv⟩

/-- Both joins are genuinely noncuspidal whenever the actual line velocities
have the expected nonzero radial component. No corner-angle value is assumed. -/
theorem lineCapArc_transverse_joins {c : ℝ → ℂ} {tm tp R α β : ℝ}
    (hab : α < β)
    (hzero : pointCircleCapArc R α β 0 = c tp)
    (hone : pointCircleCapArc R α β 1 = c tm)
    (hm : physicalRadialProjection (c tm) (deriv c tm) < 0)
    (hp : 0 < physicalRadialProjection (c tp) (deriv c tp)) :
    deriv (pointCircleCapArc R α β) 0 / deriv c tp ∈ Complex.slitPlane ∧
      deriv c tm / deriv (pointCircleCapArc R α β) 1 ∈ Complex.slitPlane := by
  rw [(hasDerivAt_pointCircleCapArc R α β 0).deriv,
    (hasDerivAt_pointCircleCapArc R α β 1).deriv, hzero, hone]
  exact ⟨transverse_circle_corner_mem_slitPlane (sub_pos.mpr hab).ne' hp.ne',
    transverse_circle_corner_reverse_mem_slitPlane (sub_pos.mpr hab).ne' hm.ne⟩

end RepulsiveCoulomb
