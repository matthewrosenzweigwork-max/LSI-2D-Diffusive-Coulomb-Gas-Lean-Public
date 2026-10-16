module

public import LeanResearch.RepulsiveCoulomb.CoulombFormInner
public import LeanResearch.RepulsiveCoulomb.CoulombFormDenseValue
public import LeanResearch.RepulsiveCoulomb.CoulombFormGlobalCompactness
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

@[expose] public section

/-! The actual variational resolvent candidate V V*, with compactness and
self-adjointness. Identification with the unbounded associated operator and
its dense domain is a separate graph construction, not assumed here. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
namespace RepulsiveCoulomb

def coulombFormResolvent (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp ℝ 2 (coulombMeasure N β) →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  (coulombFormValueL N hβ).comp (coulombFormValueL N hβ).adjoint

theorem coulombFormResolvent_adjoint (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombFormResolvent N hβ).adjoint = coulombFormResolvent N hβ := by
  simp only [coulombFormResolvent, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem coulombFormResolvent_inner (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f g : Lp ℝ 2 (coulombMeasure N β)) :
    inner ℝ (coulombFormResolvent N hβ f) g =
      inner ℝ ((coulombFormValueL N hβ).adjoint f) ((coulombFormValueL N hβ).adjoint g) :=
  (ContinuousLinearMap.adjoint_inner_right (coulombFormValueL N hβ)
    ((coulombFormValueL N hβ).adjoint f) g).symm

theorem coulombFormResolvent_nonneg (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : Lp ℝ 2 (coulombMeasure N β)) :
    0 ≤ inner ℝ (coulombFormResolvent N hβ f) f := by
  rw [coulombFormResolvent_inner, real_inner_self_eq_norm_sq]
  positivity

theorem coulombFormValueL_isCompactOperator (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsCompactOperator (coulombFormValueL N hβ) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (coulombFormValueL N hβ).toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
  have hs : Metric.closedBall (0 : CoulombFormDomain N hβ) 1 =
      {u : CoulombFormDomain N hβ | ‖u‖ ≤ 1} := by
    ext u
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq]
  rw [hs]
  exact coulombFormValue_global_compact hβ 1

theorem coulombFormResolvent_isCompactOperator (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsCompactOperator (coulombFormResolvent N hβ) :=
  (coulombFormValueL_isCompactOperator N hβ).comp_clm (coulombFormValueL N hβ).adjoint

theorem coulombFormResolvent_variational (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : Lp ℝ 2 (coulombMeasure N β)) (v : CoulombFormDomain N hβ) :
    inner ℝ (coulombFormResolvent N hβ f) (coulombFormValueL N hβ v) +
      coulombFormEnergyPair N hβ ((coulombFormValueL N hβ).adjoint f) v =
      inner ℝ f (coulombFormValueL N hβ v) := by
  have h := ContinuousLinearMap.adjoint_inner_left (coulombFormValueL N hβ) v f
  rw [coulombForm_inner_eq N hβ] at h
  exact h

theorem coulombFormResolvent_eq_zero_iff (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : Lp ℝ 2 (coulombMeasure N β)) : coulombFormResolvent N hβ f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have hh : inner ℝ ((coulombFormValueL N hβ).adjoint f)
        ((coulombFormValueL N hβ).adjoint f) = 0 := by
      rw [← coulombFormResolvent_inner N hβ, hf, inner_zero_left]
    have ha : (coulombFormValueL N hβ).adjoint f = 0 :=
      (inner_self_eq_zero (𝕜 := ℝ)).mp hh
    apply coulombFormValueL_annihilator hβ f
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_right (coulombFormValueL N hβ), ha, inner_zero_right]
  · rintro rfl
    exact map_zero _

theorem coulombFormResolvent_injective (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Function.Injective (coulombFormResolvent N hβ) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (coulombFormResolvent_eq_zero_iff N hβ (f - g)).mp
  rw [map_sub, hfg, sub_self]

theorem coulombFormResolvent_denseRange (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    DenseRange (coulombFormResolvent N hβ) := by
  change Dense (LinearMap.range (coulombFormResolvent N hβ).toLinearMap :
    Set (Lp ℝ 2 (coulombMeasure N β)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro f hf
  have hh := hf (coulombFormResolvent N hβ f) ⟨f, rfl⟩
  rw [coulombFormResolvent_inner N hβ] at hh
  have ha : (coulombFormValueL N hβ).adjoint f = 0 :=
    (inner_self_eq_zero (𝕜 := ℝ)).mp hh
  apply coulombFormValueL_annihilator hβ f
  intro u
  rw [← ContinuousLinearMap.adjoint_inner_right (coulombFormValueL N hβ), ha, inner_zero_right]

end RepulsiveCoulomb
