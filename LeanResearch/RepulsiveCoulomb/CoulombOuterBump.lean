module

public import LeanResearch.RepulsiveCoulomb.CoulombAmbientCore

@[expose] public section

/-! Scale-explicit ambient Euclidean outer bumps in the literal particle space. -/
noncomputable section
open Set MeasureTheory Metric
open scoped Topology
namespace RepulsiveCoulomb

def coulombOuterBump (N : ℕ) (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : CoulombConfig (N + 2)) :=
  ⟨R, 2 * R, hR, by linarith⟩

def coulombUnitBump (N : ℕ) : ContDiffBump (0 : CoulombConfig (N + 2)) :=
  ⟨1, 2, by norm_num, by norm_num⟩

theorem coulombOuterBump_eq_scaled (N : ℕ) (R : ℝ) (hR : 0 < R) (z : CoulombConfig (N + 2)) :
    coulombOuterBump N R hR z = coulombUnitBump N (R⁻¹ • z) := by
  simp only [ContDiffBump.apply, coulombOuterBump, coulombUnitBump,
    mul_div_cancel_right₀ 2 hR.ne', div_one, inv_one, sub_zero, one_smul]

theorem coulombUnitBump_fderiv_bounded (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : CoulombConfig (N + 2), ‖fderiv ℝ (coulombUnitBump N) z‖ ≤ B := by
  have hc : Continuous (fderiv ℝ (coulombUnitBump N)) :=
    ((coulombUnitBump N).contDiff (n := ⊤)).continuous_fderiv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : CoulombConfig (N + 2)) 2).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro z
  by_cases hz : z ∈ closedBall (0 : CoulombConfig (N + 2)) 2
  · exact (hB z hz).trans (by linarith [le_abs_self B])
  · have hs : z ∉ tsupport (coulombUnitBump N : CoulombConfig (N + 2) → ℝ) := by
      simpa only [ContDiffBump.tsupport_eq, coulombUnitBump] using hz
    rw [fderiv_of_notMem_tsupport ℝ hs, norm_zero]
    positivity

theorem coulombOuterBump_gradient_bound (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (R : ℝ) (hR : 0 < R) (z : CoulombConfig (N + 2)),
      ‖gradient (coulombOuterBump N R hR) z‖ ≤ B / R := by
  obtain ⟨B, hB, hb⟩ := coulombUnitBump_fderiv_bounded N
  refine ⟨B, hB, ?_⟩
  intro R hR z
  let T : CoulombConfig (N + 2) → CoulombConfig (N + 2) := fun x => R⁻¹ • x
  have hT : HasFDerivAt T (R⁻¹ • ContinuousLinearMap.id ℝ (CoulombConfig (N + 2))) z :=
    (hasFDerivAt_id z).const_smul R⁻¹
  have h := ((coulombUnitBump N).contDiff (n := ⊤)).differentiable (by simp) (T z) |>.hasFDerivAt.comp z hT
  have he : (coulombOuterBump N R hR : CoulombConfig (N + 2) → ℝ) = (coulombUnitBump N) ∘ T :=
    funext (fun x => coulombOuterBump_eq_scaled N R hR x)
  rw [TauCeti.norm_gradient_eq_norm_fderiv, he, h.fderiv]
  calc
    _ ≤ ‖fderiv ℝ (coulombUnitBump N) (T z)‖ *
        ‖R⁻¹ • ContinuousLinearMap.id ℝ (CoulombConfig (N + 2))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B * ‖R⁻¹ • ContinuousLinearMap.id ℝ (CoulombConfig (N + 2))‖ :=
      mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
    _ = B / R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), ContinuousLinearMap.norm_id]
      simp [div_eq_mul_inv]

def coulombOuterTestFunction (N n : ℕ) : TestFunction (⊤ : TopologicalSpace.Opens (CoulombConfig (N + 2))) ℝ ⊤ :=
  ⟨coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n),
    (coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n)).contDiff,
    (coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n)).hasCompactSupport, by simp⟩

end RepulsiveCoulomb

