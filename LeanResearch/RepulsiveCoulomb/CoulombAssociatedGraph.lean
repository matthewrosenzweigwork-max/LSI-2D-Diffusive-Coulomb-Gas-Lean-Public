import LeanResearch.RepulsiveCoulomb.CoulombFormResolvent
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The actual unbounded associated-operator graph, constructed from the
injective variational resolvent. The graph constructor's default branch is
explicitly excluded. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
namespace RepulsiveCoulomb

def coulombAssociatedGraph (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Submodule ℝ (Lp ℝ 2 (coulombMeasure N β) × Lp ℝ 2 (coulombMeasure N β)) :=
  LinearMap.range (((coulombFormResolvent N hβ).prod
    (ContinuousLinearMap.id ℝ _ - coulombFormResolvent N hβ)).toLinearMap)

theorem coulombAssociatedGraph_mem {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (x g : Lp ℝ 2 (coulombMeasure N β)) :
    (x, g) ∈ coulombAssociatedGraph N hβ ↔
      ∃ h, coulombFormResolvent N hβ h = x ∧ h - coulombFormResolvent N hβ h = g := by
  change (∃ h, (coulombFormResolvent N hβ h, h - coulombFormResolvent N hβ h) = (x, g)) ↔ _
  simp only [Prod.mk.injEq]

theorem coulombAssociatedGraph_vertical_zero (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (p : Lp ℝ 2 (coulombMeasure N β) × Lp ℝ 2 (coulombMeasure N β))
    (hp : p ∈ coulombAssociatedGraph N hβ) (hx : p.1 = 0) : p.2 = 0 := by
  obtain ⟨h, hh, hg⟩ := (coulombAssociatedGraph_mem hβ p.1 p.2).mp hp
  have hz : h = 0 := (coulombFormResolvent_eq_zero_iff N hβ h).mp (hh.trans hx)
  simpa only [hz, map_zero, sub_self] using hg.symm

def coulombAssociatedOperator (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp ℝ 2 (coulombMeasure N β) →ₗ.[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  (coulombAssociatedGraph N hβ).toLinearPMap

theorem coulombAssociatedOperator_graph (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombAssociatedOperator N hβ).graph = coulombAssociatedGraph N hβ :=
  Submodule.toLinearPMap_graph_eq _ (coulombAssociatedGraph_vertical_zero N hβ)

theorem coulombAssociatedOperator_domain (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombAssociatedOperator N hβ).domain = (coulombFormResolvent N hβ).range := by
  change (coulombAssociatedGraph N hβ).map (LinearMap.fst ℝ _ _) = _
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hab, hx⟩
    obtain ⟨h, ha, hb⟩ := (coulombAssociatedGraph_mem hβ a b).mp hab
    exact ⟨h, ha.trans hx⟩
  · rintro ⟨h, rfl⟩
    exact ⟨(coulombFormResolvent N hβ h, h - coulombFormResolvent N hβ h),
      (coulombAssociatedGraph_mem hβ _ _).mpr ⟨h, rfl, rfl⟩, rfl⟩

theorem coulombAssociatedOperator_denseDomain (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Dense ((coulombAssociatedOperator N hβ).domain : Set (Lp ℝ 2 (coulombMeasure N β))) := by
  rw [coulombAssociatedOperator_domain]
  exact coulombFormResolvent_denseRange N hβ

end RepulsiveCoulomb
