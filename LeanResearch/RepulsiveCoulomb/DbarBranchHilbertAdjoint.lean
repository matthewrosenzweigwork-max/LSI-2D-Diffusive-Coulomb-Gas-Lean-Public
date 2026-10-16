import LeanResearch.RepulsiveCoulomb.DbarBranchComplexGraph
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The genuine maximal unbounded dbar operator and its Hilbert adjoint.
The domain is proved dense before Mathlib's adjoint is used, so its
non-dense-domain junk-value branch is excluded. No basic estimate or
adjoint graph-core density is asserted. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions LinearPMap
namespace RepulsiveCoulomb

def coulombMaxDbarPMap (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp ℂ 2 (coulombMeasure N β) →ₗ.[ℂ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombMaxDbarComplexGraph hβ).toLinearPMap

theorem coulombMaxDbarPMap_graph (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombMaxDbarPMap N hβ).graph = coulombMaxDbarComplexGraph hβ := by
  apply Submodule.toLinearPMap_graph_eq
  intro J hJ hzero
  have hJ' : (J.1, J.2) ∈ coulombMaxDbarGraph hβ := hJ
  rw [hzero] at hJ'
  exact coulombMaxDbarGraph_unique hβ hJ' (coulombMaxDbarGraph hβ).zero_mem

theorem coulombMaxDbarPMap_isClosed (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombMaxDbarPMap N hβ).IsClosed := by
  rw [LinearPMap.IsClosed, coulombMaxDbarPMap_graph]
  exact coulombMaxDbarComplexGraph_isClosed hβ

theorem coulombMaxDbarPMap_dense_domain (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Dense ((coulombMaxDbarPMap N hβ).domain : Set (Lp ℂ 2 (coulombMeasure N β))) := by
  apply (coulombComplexCoreValue_denseRange N hβ).mono
  rintro f ⟨ψ, rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph (y := coulombComplexCoreDbar hβ ψ)
  rw [coulombMaxDbarPMap_graph]
  exact coulombComplexCore_mem_maxDbarGraph hβ ψ

theorem coulombMaxDbarPMap_core_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤)
    (hψ : coulombComplexCoreValue hβ ψ ∈ (coulombMaxDbarPMap N hβ).domain) :
    coulombMaxDbarPMap N hβ ⟨coulombComplexCoreValue hβ ψ, hψ⟩ = coulombComplexCoreDbar hβ ψ := by
  apply Eq.symm
  apply (LinearPMap.image_iff hψ).mpr
  rw [coulombMaxDbarPMap_graph]
  exact coulombComplexCore_mem_maxDbarGraph hβ ψ

def coulombMaxDbarAdjoint (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) →ₗ.[ℂ] Lp ℂ 2 (coulombMeasure N β) :=
  (coulombMaxDbarPMap N hβ).adjoint

theorem coulombMaxDbarAdjoint_isFormalAdjoint (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombMaxDbarAdjoint N hβ).IsFormalAdjoint (coulombMaxDbarPMap N hβ) :=
  LinearPMap.adjoint_isFormalAdjoint (coulombMaxDbarPMap_dense_domain N hβ)

theorem coulombMaxDbarAdjoint_isClosed (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombMaxDbarAdjoint N hβ).IsClosed :=
  LinearPMap.adjoint_isClosed (coulombMaxDbarPMap_dense_domain N hβ)

theorem coulombMaxDbarAdjoint_graph (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombMaxDbarAdjoint N hβ).graph = (coulombMaxDbarComplexGraph hβ).adjoint := by
  rw [coulombMaxDbarAdjoint,
    LinearPMap.adjoint_graph_eq_graph_adjoint (coulombMaxDbarPMap_dense_domain N hβ),
    coulombMaxDbarPMap_graph]

theorem coulombMaxDbarAdjoint_graph_iff {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    (g, h) ∈ (coulombMaxDbarAdjoint N hβ).graph ↔
      ∀ f k, (f, k) ∈ coulombMaxDbarGraph hβ → inner ℂ k g = inner ℂ f h := by
  rw [coulombMaxDbarAdjoint_graph, Submodule.mem_adjoint_iff]
  simp only [sub_eq_zero]
  rfl

end RepulsiveCoulomb
