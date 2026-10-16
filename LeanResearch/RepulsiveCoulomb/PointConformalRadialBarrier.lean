module

public import LeanResearch.RepulsiveCoulomb.PointConformalMetricBarrier
public import Mathlib.Analysis.Calculus.FDeriv.Norm

@[expose] public section

/-! A smooth proper radial scalar function, constant near all punctures and with
physical derivative controlled by rho outside a configuration-dependent disk. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointConformalRadius {m : ℕ} (y : Fin m → ℂ) : ℝ := 1 + ∑ j, ‖y j‖

theorem pointConformalRadius_pos {m : ℕ} (y : Fin m → ℂ) : 0 < pointConformalRadius y := by
  unfold pointConformalRadius
  positivity

theorem pointConformalRadius_bound {m : ℕ} (y : Fin m → ℂ) (j : Fin m) :
    ‖y j‖ + 1 ≤ pointConformalRadius y := by
  have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) ↦ norm_nonneg (y k)) (Finset.mem_univ j)
  unfold pointConformalRadius
  linarith

theorem pointConformalDensity_one_le_of_far {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : pointConformalRadius y ≤ ‖z‖) : 1 ≤ pointConformalDensity a y z := by
  have hw : 1 ≤ rawPointWeight a y z := by
    apply Finset.one_le_prod₀
    intro j _
    apply Real.one_le_rpow
    · have htri : ‖z‖ ≤ ‖z - y j‖ + ‖y j‖ := by
        simpa using norm_add_le (z - y j) (y j)
      linarith [pointConformalRadius_bound y j]
    · exact ha j
  simpa [pointConformalDensity] using Real.sqrt_le_sqrt hw

/-- It vanishes on the inner disk and equals the Euclidean radius outside twice the radius. -/
def smoothRadialEscape (R : ℝ) (hR : 0 < R) (z : ℂ) : ℝ :=
  (1 - pointCutoffBump 0 R hR z) * ‖z‖

theorem smoothRadialEscape_eq_zero {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) R) : smoothRadialEscape R hR z = 0 := by
  simp [smoothRadialEscape, pointCutoffBump_one 0 R hR hz]

theorem smoothRadialEscape_eq_norm {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : 2 * R ≤ ‖z‖) : smoothRadialEscape R hR z = ‖z‖ := by
  have hb : pointCutoffBump 0 R hR z = 0 :=
    (pointCutoffBump 0 R hR).zero_of_le_dist (by simpa [pointCutoffBump] using hz)
  simp [smoothRadialEscape, hb]

theorem smoothRadialEscape_eventually_zero {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) : smoothRadialEscape R hR =ᶠ[𝓝 z] 0 := by
  filter_upwards [(pointCutoffBump 0 R hR).eventuallyEq_one_of_mem_ball hz] with p hp
  simp [smoothRadialEscape, hp]

theorem smoothRadialEscape_contDiff {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothRadialEscape R hR) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact contDiffAt_const.congr_of_eventuallyEq
      (smoothRadialEscape_eventually_zero hR (mem_ball_self hR))
  · exact (contDiffAt_const.sub (pointCutoffBump_contDiff 0 R hR).contDiffAt).mul
      (contDiffAt_norm ℝ hz)

theorem smoothRadialEscape_fderiv_zero {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) : fderiv ℝ (smoothRadialEscape R hR) z = 0 := by
  rw [(smoothRadialEscape_eventually_zero hR hz).fderiv_eq]
  exact fderiv_const_apply 0

theorem smoothRadialEscape_fderiv_bounded : ∃ C : ℝ, 0 < C ∧
    ∀ (R : ℝ) (hR : 0 < R) (z : ℂ), ‖fderiv ℝ (smoothRadialEscape R hR) z‖ ≤ C := by
  obtain ⟨B, hB, hbound⟩ := exists_pointCutoffBump_gradient_bound
  refine ⟨1 + 2 * B, by positivity, ?_⟩
  intro R hR z
  by_cases hz : z ∈ ball (0 : ℂ) R
  · rw [smoothRadialEscape_fderiv_zero hR hz, norm_zero]
    positivity
  have hz0 : z ≠ 0 := fun he ↦ hz (he ▸ mem_ball_self hR)
  let b : ℂ → ℝ := pointCutoffBump 0 R hR
  have hbd : DifferentiableAt ℝ b z :=
    ((pointCutoffBump_contDiff 0 R hR).differentiable (by simp)) z
  have hnd : DifferentiableAt ℝ (fun z : ℂ ↦ ‖z‖) z := (contDiffAt_norm ℝ hz0).differentiableAt (by simp : (1 : WithTop ℕ∞) ≠ 0)
  have hbn : ‖1 - b z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (pointCutoffBump 0 R hR).le_one)]
    linarith [(pointCutoffBump 0 R hR).nonneg (x := z)]
  have hnn : ‖fderiv ℝ (fun z : ℂ ↦ ‖z‖) z‖ ≤ 1 :=
    by simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm : LipschitzWith 1 (fun z : ℂ ↦ ‖z‖)) (x₀ := z)
  have he : fderiv ℝ (smoothRadialEscape R hR) z =
      (1 - b z) • fderiv ℝ (fun z : ℂ ↦ ‖z‖) z + ‖z‖ • (-fderiv ℝ b z) := by
    change fderiv ℝ ((fun w : ℂ ↦ 1 - b w) * (fun w : ℂ ↦ ‖w‖)) z = _
    rw [fderiv_mul (hbd.const_sub 1) hnd, fderiv_const_sub 1]
  rw [he]
  apply (norm_add_le _ _).trans
  have hfirst : ‖(1 - b z) • fderiv ℝ (fun z : ℂ ↦ ‖z‖) z‖ ≤ 1 := by
    rw [norm_smul]
    exact (mul_le_mul hbn hnn (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hsecond : ‖‖z‖ • (-fderiv ℝ b z)‖ ≤ 2 * B := by
    by_cases hout : z ∈ closedBall (0 : ℂ) (2 * R)
    · rw [norm_smul, norm_neg, norm_norm]
      have hb : ‖fderiv ℝ b z‖ ≤ B / R := by
        rw [← TauCeti.norm_gradient_eq_norm_fderiv]
        exact hbound 0 R hR z
      have hn : ‖z‖ ≤ 2 * R := by simpa using hout
      calc
        _ ≤ (2 * R) * (B / R) := mul_le_mul hn hb (norm_nonneg _) (by positivity)
        _ = 2 * B := by field_simp
    · have hd : fderiv ℝ b z = 0 := fderiv_of_notMem_tsupport ℝ
        (by simpa [b, pointCutoffBump_support] using hout)
      simp [hd, hB.le]
  linarith

theorem pointConformal_radial_bound {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x z : ℂ,
      ‖z‖ ≤ 2 * pointConformalRadius y + ‖x‖ +
        C * (pointSmoothConformalEDist a y x z).toReal := by
  obtain ⟨C, hC, hb⟩ := smoothRadialEscape_fderiv_bounded
  let R := pointConformalRadius y
  have hR : 0 < R := pointConformalRadius_pos y
  let φ := smoothRadialEscape R hR
  have hφ : ContDiff ℝ 1 φ := (smoothRadialEscape_contDiff hR).of_le (by simp)
  have hdom (z : ℂ) : ‖fderiv ℝ φ z‖ ≤ C * pointConformalDensity a y z := by
    by_cases hz : z ∈ ball (0 : ℂ) R
    · rw [smoothRadialEscape_fderiv_zero hR hz, norm_zero]
      exact mul_nonneg hC.le (pointConformalDensity_nonneg a y z)
    · have hfar : R ≤ ‖z‖ := by simpa [mem_ball, not_lt] using hz
      exact (hb R hR z).trans (le_mul_of_one_le_right hC.le
        (pointConformalDensity_one_le_of_far ha y hfar))
  refine ⟨C, hC, ?_⟩
  intro x z
  have hnon : 0 ≤ C * (pointSmoothConformalEDist a y x z).toReal :=
    mul_nonneg hC.le ENNReal.toReal_nonneg
  by_cases hz : ‖z‖ ≤ 2 * R
  · linarith [norm_nonneg x]
  have heq : φ z = ‖z‖ := smoothRadialEscape_eq_norm hR (le_of_not_ge hz)
  have hx : φ x ≤ ‖x‖ := by
    apply mul_le_of_le_one_left (norm_nonneg _)
    have hb0 := (pointCutoffBump 0 R hR).nonneg (x := x)
    linarith
  have hbar := pointConformal_metric_barrier a y hφ hC hdom x z
  have hreal : |φ z - φ x| ≤ C * (pointSmoothConformalEDist a y x z).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (pointSmoothConformalEDist_lt_top ha y x z)).ne hbar
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le, Real.norm_eq_abs] using h
  rw [heq] at hreal
  have habs := le_abs_self (‖z‖ - φ x)
  dsimp only [R] at *
  linarith

end RepulsiveCoulomb
