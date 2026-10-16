module

public import LeanResearch.RepulsiveCoulomb.PointWeightFormApproximation
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-! Actual smooth cutoff functions at a point, with scale-explicit physical
gradient control. The scale bound is derived from a single compactly
supported Mathlib bump and the real Frechet chain rule.
-/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology
namespace RepulsiveCoulomb

def unitPointBump : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩

def pointCutoffBump (c : ℂ) (ε : ℝ) (hε : 0 < ε) : ContDiffBump c :=
  ⟨ε, 2 * ε, hε, by linarith⟩

theorem pointCutoffBump_eq_scaled (c : ℂ) (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    pointCutoffBump c ε hε z = unitPointBump (ε⁻¹ • (z - c)) := by
  simp only [ContDiffBump.apply, pointCutoffBump, unitPointBump,
    mul_div_cancel_right₀ 2 hε.ne', div_one, inv_one, sub_zero, one_smul]

theorem pointCutoffBump_contDiff (c : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (pointCutoffBump c ε hε) := (pointCutoffBump c ε hε).contDiff

theorem pointCutoffBump_one (c : ℂ) (ε : ℝ) (hε : 0 < ε) {z : ℂ}
    (hz : z ∈ closedBall c ε) : pointCutoffBump c ε hε z = 1 :=
  (pointCutoffBump c ε hε).one_of_mem_closedBall hz

theorem pointCutoffBump_support (c : ℂ) (ε : ℝ) (hε : 0 < ε) :
    tsupport (pointCutoffBump c ε hε) = closedBall c (2 * ε) :=
  (pointCutoffBump c ε hε).tsupport_eq

theorem pointCutoffBump_gradient_zero (c : ℂ) (ε : ℝ) (hε : 0 < ε) {z : ℂ}
    (hz : z ∉ closedBall c (2 * ε)) : gradient (pointCutoffBump c ε hε) z = 0 :=
  TauCeti.gradient_of_notMem_tsupport (by rwa [pointCutoffBump_support])

theorem unitPointBump_fderiv_bounded : ∃ C : ℝ, 0 < C ∧
    ∀ z : ℂ, ‖fderiv ℝ (unitPointBump : ℂ → ℝ) z‖ ≤ C := by
  have hc : Continuous (fderiv ℝ (unitPointBump : ℂ → ℝ)) :=
    (unitPointBump.contDiff (n := ⊤)).continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro z
  by_cases hz : z ∈ closedBall (0 : ℂ) 2
  · exact (hC z hz).trans (by linarith [le_abs_self C])
  · have hsupport : z ∉ tsupport (unitPointBump : ℂ → ℝ) := by
      simpa only [ContDiffBump.tsupport_eq, unitPointBump] using hz
    rw [fderiv_of_notMem_tsupport ℝ hsupport, norm_zero]
    positivity

/-- One scale-independent constant controls every translated/rescaled bump. -/
theorem exists_pointCutoffBump_gradient_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (c : ℂ) (ε : ℝ) (hε : 0 < ε) (z : ℂ),
      ‖gradient (pointCutoffBump c ε hε) z‖ ≤ C / ε := by
  obtain ⟨C, hC, hbound⟩ := unitPointBump_fderiv_bounded
  refine ⟨C, hC, ?_⟩
  intro c ε hε z
  let T : ℂ → ℂ := fun x ↦ ε⁻¹ • (x - c)
  have hT : HasFDerivAt T (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ) z :=
    ((hasFDerivAt_id z).sub_const c).const_smul ε⁻¹
  have h := ((unitPointBump.contDiff (n := ⊤)).differentiable (by simp) (T z)).hasFDerivAt.comp z hT
  have hfun : (pointCutoffBump c ε hε : ℂ → ℝ) = (unitPointBump : ℂ → ℝ) ∘ T := by
    funext x
    exact pointCutoffBump_eq_scaled c ε hε x
  rw [TauCeti.norm_gradient_eq_norm_fderiv, hfun, h.fderiv]
  calc
    ‖(fderiv ℝ (unitPointBump : ℂ → ℝ) (T z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖
        ≤ ‖fderiv ℝ (unitPointBump : ℂ → ℝ) (T z)‖ * ‖ε⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * ‖ε⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ :=
      mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
    _ = C / ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), ContinuousLinearMap.norm_id]
      simp [div_eq_mul_inv]

def pointCutoffTestFunction (c : ℂ) (ε : ℝ) (hε : 0 < ε) : TestFunction (⊤ : Opens ℂ) ℝ ⊤ :=
  ⟨pointCutoffBump c ε hε, (pointCutoffBump c ε hε).contDiff,
    (pointCutoffBump c ε hε).hasCompactSupport, by simp⟩

end RepulsiveCoulomb
