module

public import LeanResearch.RepulsiveCoulomb.JordanSecantAverage

@[expose] public section

/-! The actual closed secant square of a regular C¹ periodic simple loop.
The diagonal and closing-edge values are constructed by averaged derivatives;
nonvanishing follows from actual injectivity, not an extension certificate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- A square parametrization of ordered pairs, with the top collapsed to the
closing pair `(0,1)` and the bottom equal to the diagonal. -/
def euclideanSecantSquare (γ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  euclideanPeriodicSecant γ ((1 - p.2) * p.1, (1 - p.2) * p.1 + p.2)

theorem euclideanSecantSquare_continuous {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1) :
    Continuous (euclideanSecantSquare γ) :=
  (euclideanPeriodicSecant_continuous hγ hp).comp (by fun_prop)

@[simp] theorem euclideanSecantSquare_bottom (γ : ℝ → ℂ) (s : ℝ) :
    euclideanSecantSquare γ (s, 0) = deriv γ s := by
  simp [euclideanSecantSquare, euclideanPeriodicSecant]

@[simp] theorem euclideanSecantSquare_top (γ : ℝ → ℂ) (s : ℝ) :
    euclideanSecantSquare γ (s, 1) = -deriv γ 0 := by
  norm_num [euclideanSecantSquare, euclideanPeriodicSecant]

/-- Injectivity on the half-open standard period is enough even when one
secant endpoint is the closing endpoint `1`. -/
theorem periodic_simple_loop_secant_ne_zero {γ : ℝ → ℂ}
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 1) (hst : s < t) (hgap : t - s < 1) :
    γ t - γ s ≠ 0 := by
  intro hz
  have heq := sub_eq_zero.mp hz
  by_cases ht1 : t = 1
  · subst t
    have hs0 : 0 < s := by linarith
    have hs1 : s < 1 := hst
    have h10 : γ 1 = γ 0 := by simpa using hp 0
    have h0s := hinj (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
      ⟨hs, hs1⟩ (h10.symm.trans heq)
    linarith
  · have ht1' : t < 1 := lt_of_le_of_ne ht ht1
    have hts := hinj ⟨hs.trans hst.le, ht1'⟩ ⟨hs, hst.trans ht1'⟩ heq
    exact (ne_of_lt hst) hts.symm

def euclideanSecantScale (r : ℝ) : ℝ := if r ≤ 1 / 2 then r else 1 - r

theorem euclideanSecantScale_pos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < euclideanSecantScale r := by
  unfold euclideanSecantScale
  split_ifs <;> linarith [hr.1, hr.2]

theorem euclideanSecantScale_symm (r : ℝ) :
    euclideanSecantScale (1 - r) = euclideanSecantScale r := by
  unfold euclideanSecantScale
  split_ifs <;> linarith

/-- Exact positive-scale formula for every square secant. -/
theorem euclideanSecantSquare_smul {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1) (s r : ℝ) :
    euclideanSecantScale r • euclideanSecantSquare γ (s, r) =
      γ ((1 - r) * s + r) - γ ((1 - r) * s) := by
  have hgap : (1 - r) * s + r - (1 - r) * s = r := by ring
  have hwrap : (1 - r) * s + r - 1 - (1 - r) * s = -(1 - r) := by ring
  unfold euclideanSecantSquare euclideanPeriodicSecant euclideanSecantScale
  simp only [hgap]
  split_ifs with hr
  · simpa only [hgap] using euclideanAverageDerivative_smul hγ
      ((1 - r) * s) ((1 - r) * s + r)
  · have h := euclideanAverageDerivative_smul hγ
      ((1 - r) * s) ((1 - r) * s + r - 1)
    rw [hp.sub_eq, hwrap, neg_smul] at h
    simpa only [smul_neg] using h

/-- Actual Jordan injectivity and regularity remove every zero of the closed
secant square, including both exceptional boundary edges. -/
theorem euclideanSecantSquare_ne_zero {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (s r : Icc (0 : ℝ) 1) : euclideanSecantSquare γ (s, r) ≠ 0 := by
  by_cases hr0 : (r : ℝ) = 0
  · simpa [hr0] using hregular s s.2
  by_cases hr1 : (r : ℝ) = 1
  · simpa [hr1] using neg_ne_zero.mpr (hregular 0 (by norm_num))
  have hr : (r : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne r.2.1 (Ne.symm hr0), lt_of_le_of_ne r.2.2 hr1⟩
  have ha : 0 ≤ (1 - (r : ℝ)) * s := mul_nonneg (by linarith [r.2.2]) s.2.1
  have hb : (1 - (r : ℝ)) * s + r ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left s.2.2 (show 0 ≤ 1 - (r : ℝ) by linarith [r.2.2])
    nlinarith
  have hab : (1 - (r : ℝ)) * s < (1 - (r : ℝ)) * s + r := by linarith [hr.1]
  have hgap : (1 - (r : ℝ)) * s + r - (1 - (r : ℝ)) * s < 1 := by linarith [hr.2]
  intro hz
  have h := euclideanSecantSquare_smul hγ hp s r
  rw [hz, smul_zero] at h
  exact periodic_simple_loop_secant_ne_zero hp hinj ha hb hab hgap h.symm

/-- The two side edges of the secant square are the same chord family with
opposite directions and reversed parameter. -/
theorem euclideanSecantSquare_side_symmetry {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1) (r : Icc (0 : ℝ) 1)
    (hderiv : deriv γ 1 = deriv γ 0) :
    euclideanSecantSquare γ (1, (r : ℝ)) =
      -euclideanSecantSquare γ (0, 1 - (r : ℝ)) := by
  by_cases hr0 : (r : ℝ) = 0
  · simp [hr0, hderiv]
  by_cases hr1 : (r : ℝ) = 1
  · simp [hr1]
  have hr : (r : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne r.2.1 (Ne.symm hr0), lt_of_le_of_ne r.2.2 hr1⟩
  have hleft := euclideanSecantSquare_smul hγ hp 0 (1 - r)
  have hright := euclideanSecantSquare_smul hγ hp 1 r
  have h10 : γ 1 = γ 0 := by simpa using hp 0
  simp only [mul_zero, zero_add, euclideanSecantScale_symm] at hleft
  simp only [mul_one, sub_add_cancel, h10] at hright
  apply smul_right_injective ℂ (euclideanSecantScale_pos hr).ne'
  change euclideanSecantScale (r : ℝ) • euclideanSecantSquare γ (1, (r : ℝ)) =
    euclideanSecantScale (r : ℝ) • -euclideanSecantSquare γ (0, 1 - (r : ℝ))
  rw [smul_neg, hleft, hright, neg_sub]

/-- Any continuous circle-valued square has a real angle lift. This follows
from path lifting followed by homotopy lifting, so no disk lift is an input. -/
theorem exists_square_circle_angle_lift
    (S : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → Circle) (hS : Continuous S) :
    ∃ A : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℝ, Continuous A ∧
      ∀ p, Circle.exp (A p) = S p := by
  let left : C(Icc (0 : ℝ) 1, Circle) :=
    ⟨fun r => S (0, r), hS.comp (continuous_const.prodMk continuous_id)⟩
  obtain ⟨L, hL, _⟩ := Circle.isCoveringMap_exp.exists_path_lifts left
    (Complex.arg (left 0 : ℂ)) (Circle.exp_arg (left 0)).symm
  let H : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, Circle) := ⟨S, hS⟩
  have H₀ (r : Icc (0 : ℝ) 1) : H (0, r) = Circle.exp (L r) :=
    (congrFun hL r).symm
  let A := Circle.isCoveringMap_exp.liftHomotopy H L H₀
  exact ⟨A, A.continuous,
    fun p => congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H L H₀) p⟩

/-- The normalized closed secant square of an actual regular simple periodic
loop has a constructed continuous real angle. -/
theorem exists_regular_simple_loop_secant_square_angle {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) :
    ∃ A : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℝ, Continuous A ∧
      ∀ p, Circle.exp (A p) = euclideanDirection
        (euclideanSecantSquare γ (p.1, p.2))
        (euclideanSecantSquare_ne_zero hγ hp hinj hregular p.1 p.2) := by
  apply exists_square_circle_angle_lift
  exact continuous_euclideanDirection
    ((euclideanSecantSquare_continuous hγ hp).comp (by fun_prop)) _

end RepulsiveCoulomb
