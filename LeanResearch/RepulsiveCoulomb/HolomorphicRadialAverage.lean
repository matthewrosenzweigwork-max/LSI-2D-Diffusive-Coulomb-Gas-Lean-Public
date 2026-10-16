module

public import LeanResearch.RepulsiveCoulomb.PointConformalPunctureFactor
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Weighted radial averaging for construction of a local cone coordinate.
All integrals use the actual holomorphic factor; no differential equation or
cone-chart existence is assumed. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology Interval
namespace RepulsiveCoulomb

def holomorphicRadialAverage (α : ℝ) (p : ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (α + 1) • ∫ t in (0 : ℝ)..1, t ^ α • g (p + t • (z - p))

def holomorphicRadialAverageDerivative (α : ℝ) (p : ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (α + 1) • ∫ t in (0 : ℝ)..1, t ^ α • ((t : ℂ) * deriv g (p + t • (z - p)))

theorem holomorphicRadialAverage_center {α : ℝ} (hα : 0 ≤ α) (p : ℂ) (g : ℂ → ℂ) :
    holomorphicRadialAverage α p g p = g p := by
  have he : α + 1 ≠ 0 := by linarith
  simp only [holomorphicRadialAverage, sub_self, smul_zero, add_zero]
  rw [intervalIntegral.integral_smul_const, integral_rpow (Or.inl (by linarith))]
  have hc : (α : ℂ) + 1 ≠ 0 := by exact_mod_cast he
  simp [Real.zero_rpow he, hc]

theorem radialSegment_mem_closedBall {p z : ℂ} {R t : ℝ} (hz : z ∈ closedBall p R)
    (ht : t ∈ Icc (0 : ℝ) 1) : p + t • (z - p) ∈ closedBall p R := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans
    (by simpa [mem_closedBall, dist_eq_norm] using hz)

/-- Differentiation under the weighted radial integral on a smaller disk. -/
theorem holomorphicRadialAverage_hasDerivAt {α : ℝ} (hα : 0 ≤ α) (p : ℂ)
    {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (ball p R))
    {z : ℂ} (hz : z ∈ ball p (R / 2)) :
    HasDerivAt (holomorphicRadialAverage α p g)
      (holomorphicRadialAverageDerivative α p g z) z := by
  let S := closedBall p (R / 2)
  have hS : S ⊆ ball p R := closedBall_subset_ball (by linarith)
  have hgc : ContinuousOn g S := hg.continuousOn.mono hS
  have hgdc : ContinuousOn (deriv g) S := hg.deriv.continuousOn.mono hS
  obtain ⟨B, hB⟩ := (isCompact_closedBall p (R / 2)).exists_bound_of_continuousOn hgdc
  let F : ℂ → ℝ → ℂ := fun w t ↦ t ^ α • g (p + t • (w - p))
  let D : ℂ → ℝ → ℂ := fun w t ↦ t ^ α • ((t : ℂ) * deriv g (p + t • (w - p)))
  have hcont (w : ℂ) (hw : w ∈ S) : ContinuousOn (F w) (Icc (0 : ℝ) 1) := by
    apply (Real.continuous_rpow_const hα).continuousOn.smul
    exact hgc.comp (by fun_prop) (fun t ht ↦ radialSegment_mem_closedBall hw ht)
  have hdcont (w : ℂ) (hw : w ∈ S) : ContinuousOn (D w) (Icc (0 : ℝ) 1) := by
    apply (Real.continuous_rpow_const hα).continuousOn.smul
    apply (Complex.continuous_ofReal.continuousOn).mul
    exact hgdc.comp (by fun_prop) (fun t ht ↦ radialSegment_mem_closedBall hw ht)
  have hparam : ∀ᶠ w in 𝓝 z, w ∈ ball p (R / 2) := isOpen_ball.mem_nhds hz
  have hdiff (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (w : ℂ) (hw : w ∈ ball p (R / 2)) :
      HasDerivAt (fun w ↦ F w t) (D w t) w := by
    have hw' := hS (radialSegment_mem_closedBall (ball_subset_closedBall hw) ⟨ht.1.le, ht.2⟩)
    have hlin : HasDerivAt (fun w : ℂ ↦ p + t • (w - p)) (t : ℂ) w := by
      simpa using (((hasDerivAt_id w).sub_const p).const_smul t).const_add p
    convert (((hg _ hw').differentiableAt.hasDerivAt.comp w hlin).const_smul (t ^ α)) using 1
    · rfl
    · change t ^ α • ((t : ℂ) * deriv g (p + t • (w - p))) = _
      rw [mul_comm (t : ℂ)]
  have hbound (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (w : ℂ) (hw : w ∈ ball p (R / 2)) :
      ‖D w t‖ ≤ |B| := by
    have hb := hB (p + t • (w - p))
      (radialSegment_mem_closedBall (ball_subset_closedBall hw) ⟨ht.1.le, ht.2⟩)
    have hp0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1.le _
    have hp1 : t ^ α ≤ 1 := Real.rpow_le_one ht.1.le ht.2 hα
    dsimp only [D]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp0, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
    have hn := norm_nonneg (deriv g (p + t • (w - p)))
    calc
      _ ≤ 1 * (1 * |B|) := mul_le_mul hp1
        (mul_le_mul ht.2 (hb.trans (le_abs_self B)) hn zero_le_one)
        (mul_nonneg ht.1.le hn) zero_le_one
      _ = _ := by ring
  have H := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (bound := fun _ ↦ |B|) (μ := (volume : Measure ℝ))
    (s := ball p (R / 2)) (a := 0) (b := 1) (isOpen_ball.mem_nhds hz)
    (hparam.mono (fun w hw ↦ by
      simpa only [uIoc_of_le zero_le_one] using ((hcont w (ball_subset_closedBall hw)).mono
        Ioc_subset_Icc_self).aestronglyMeasurable (μ := (volume : Measure ℝ)) measurableSet_Ioc))
    ((hcont z (ball_subset_closedBall hz)).intervalIntegrable_of_Icc zero_le_one)
    (by simpa only [uIoc_of_le zero_le_one] using
      ((hdcont z (ball_subset_closedBall hz)).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := (volume : Measure ℝ)) measurableSet_Ioc)
    (Eventually.of_forall fun t ht w hw ↦ hbound t (by simpa using ht) w hw)
    (intervalIntegrable_const)
    (Eventually.of_forall fun t ht w hw ↦ hdiff t (by simpa using ht) w hw)
  exact H.2.const_smul (α + 1)

end RepulsiveCoulomb
