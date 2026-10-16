module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreIBP
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section

/-! The genuine auxiliary minimal operator is the closure of the actual core
T0 f=R dbar f. Dense compact formal-adjoint tests prove its single-valuedness.
Its Hilbert adjoint is characterized by actual core testing; no density in
that adjoint's graph norm is asserted. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology LinearPMap
namespace RepulsiveCoulomb

def coulombAuxiliaryCoreJetLinear (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    TestFunction (coulombDomain N) ℂ ⊤ →ₗ[ℂ]
      (Lp ℂ 2 (coulombMeasure N β) × Lp (CoulombConfig N) 2 (coulombMeasure N β)) :=
  (coulombComplexCoreValueLinear N hβ).prod (coulombAuxiliaryCoreDerivativeL N hβ)

def coulombAuxiliaryMinimalGraph (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ClosedSubmodule ℂ (Lp ℂ 2 (coulombMeasure N β) × Lp (CoulombConfig N) 2 (coulombMeasure N β)) :=
  (LinearMap.range (coulombAuxiliaryCoreJetLinear N hβ)).closure

theorem coulombAuxiliaryMinimalGraph_coe (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombAuxiliaryMinimalGraph N hβ : Set _) = closure (range (coulombAuxiliaryCoreJetLinear N hβ)) := by
  rw [coulombAuxiliaryMinimalGraph, Submodule.coe_closure, LinearMap.coe_range]

theorem coulombAuxiliaryCore_mem_minimalGraph {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    (coulombComplexCoreValue hβ φ, coulombAuxiliaryCoreDerivativeL N hβ φ) ∈
      coulombAuxiliaryMinimalGraph N hβ := by
  change (coulombComplexCoreValue hβ φ, coulombAuxiliaryCoreDerivativeL N hβ φ) ∈
    (coulombAuxiliaryMinimalGraph N hβ : Set _)
  rw [coulombAuxiliaryMinimalGraph_coe]
  exact subset_closure ⟨φ, rfl⟩

theorem coulombAuxiliaryMinimalGraph_core_pairing {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {J : Lp ℂ 2 (coulombMeasure N β) × Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hJ : J ∈ coulombAuxiliaryMinimalGraph N hβ)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    inner ℂ J.2 (coulombComplexVectorCoreValue hβ u) =
      inner ℂ J.1 (coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ u)) := by
  have hc : IsClosed {J : Lp ℂ 2 (coulombMeasure N β) × Lp (CoulombConfig N) 2 (coulombMeasure N β) |
      inner ℂ J.2 (coulombComplexVectorCoreValue hβ u) =
        inner ℂ J.1 (coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ u))} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  change J ∈ (coulombAuxiliaryMinimalGraph N hβ : Set _) at hJ
  rw [coulombAuxiliaryMinimalGraph_coe] at hJ
  apply (closure_minimal (s := range (coulombAuxiliaryCoreJetLinear N hβ)) _ hc) hJ
  rintro _ ⟨φ, rfl⟩
  exact coulombAuxiliaryCore_ibp hβ φ u

theorem coulombAuxiliaryMinimalGraph_zero_of_value_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {J : Lp ℂ 2 (coulombMeasure N β) × Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hJ : J ∈ coulombAuxiliaryMinimalGraph N hβ) (hz : J.1 = 0) : J.2 = 0 := by
  apply coulombComplexVectorCoreValue_annihilator hβ J.2
  intro u
  have h := coulombAuxiliaryMinimalGraph_core_pairing hβ hJ u
  rw [hz, inner_zero_left] at h
  have hc := congrArg (starRingEnd ℂ) h
  simpa only [inner_conj_symm, map_zero] using hc

def coulombAuxiliaryMinimalDbar (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp ℂ 2 (coulombMeasure N β) →ₗ.[ℂ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombAuxiliaryMinimalGraph N hβ).toSubmodule.toLinearPMap

theorem coulombAuxiliaryMinimalDbar_graph (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombAuxiliaryMinimalDbar N hβ).graph = (coulombAuxiliaryMinimalGraph N hβ).toSubmodule := by
  apply Submodule.toLinearPMap_graph_eq
  intro J hJ hz
  exact coulombAuxiliaryMinimalGraph_zero_of_value_zero hβ hJ hz

theorem coulombAuxiliaryMinimalDbar_isClosed (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombAuxiliaryMinimalDbar N hβ).IsClosed := by
  rw [LinearPMap.IsClosed, coulombAuxiliaryMinimalDbar_graph]
  exact (coulombAuxiliaryMinimalGraph N hβ).isClosed

theorem coulombAuxiliaryMinimalDbar_dense_domain (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Dense ((coulombAuxiliaryMinimalDbar N hβ).domain : Set (Lp ℂ 2 (coulombMeasure N β))) := by
  apply (coulombComplexCoreValue_denseRange N hβ).mono
  rintro _ ⟨φ, rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph (y := coulombAuxiliaryCoreDerivativeL N hβ φ)
  rw [coulombAuxiliaryMinimalDbar_graph]
  exact coulombAuxiliaryCore_mem_minimalGraph hβ φ

def coulombAuxiliaryDbarAdjoint (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) →ₗ.[ℂ] Lp ℂ 2 (coulombMeasure N β) :=
  (coulombAuxiliaryMinimalDbar N hβ).adjoint

theorem coulombAuxiliaryDbarAdjoint_graph_iff {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    (g, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph ↔
      ∀ φ : TestFunction (coulombDomain N) ℂ ⊤,
        inner ℂ (coulombAuxiliaryCoreDerivativeL N hβ φ) g = inner ℂ (coulombComplexCoreValue hβ φ) h := by
  rw [coulombAuxiliaryDbarAdjoint,
    LinearPMap.adjoint_graph_eq_graph_adjoint (coulombAuxiliaryMinimalDbar_dense_domain N hβ),
    coulombAuxiliaryMinimalDbar_graph, Submodule.mem_adjoint_iff]
  simp only [sub_eq_zero]
  constructor
  · intro hgh φ
    exact hgh _ _ (coulombAuxiliaryCore_mem_minimalGraph hβ φ)
  · intro hc f k hfk
    have hclosed : IsClosed {J : Lp ℂ 2 (coulombMeasure N β) × Lp (CoulombConfig N) 2 (coulombMeasure N β) |
        inner ℂ J.2 g = inner ℂ J.1 h} :=
      isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
    change (f, k) ∈ (coulombAuxiliaryMinimalGraph N hβ : Set _) at hfk
    rw [coulombAuxiliaryMinimalGraph_coe] at hfk
    apply (closure_minimal (s := range (coulombAuxiliaryCoreJetLinear N hβ)) _ hclosed) hfk
    rintro _ ⟨φ, rfl⟩
    exact hc φ

end RepulsiveCoulomb
