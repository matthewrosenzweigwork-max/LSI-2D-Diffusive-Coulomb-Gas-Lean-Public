import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCompatibility

/-! Closed-graph separation in the genuine L2 product Hilbert space. The
ordinary product used to store the graph is transported through the explicit
WithLp2 equivalence; no inner-product structure is inferred on its max norm. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped Topology LinearPMap
namespace RepulsiveCoulomb

theorem dbarClosedGraph_mem_of_adjoint_tests
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (G : ClosedSubmodule ℂ (E × F)) (x : E) (y : F)
    (ht : ∀ u v, (u, v) ∈ G.toSubmodule.adjoint → inner ℂ v x = inner ℂ u y) :
    (x, y) ∈ G := by
  let e : WithLp 2 (E × F) ≃L[ℂ] E × F := WithLp.prodContinuousLinearEquiv 2 ℂ E F
  let H : ClosedSubmodule ℂ (WithLp 2 (E × F)) := G.mapEquiv e.symm
  letI : CompleteSpace H.toSubmodule := H.isClosed.completeSpace_coe
  have hH : e.symm (x, y) ∈ H.toSubmodule.orthogonal.orthogonal := by
    intro w hw
    have hpair : ((WithLp.ofLp w).2, -(WithLp.ofLp w).1) ∈ G.toSubmodule.adjoint := by
      apply (Submodule.mem_adjoint_iff _ _).mpr
      intro a b hab
      have habH : e.symm (a, b) ∈ H := by
        change (a, b) ∈ G at hab
        change e.symm (a, b) ∈ G.mapEquiv e.symm
        exact (ClosedSubmodule.mem_mapEquiv_iff' (f := e.symm) (s := G) (a, b)).mpr hab
      have hh := hw (e.symm (a, b)) habH
      change inner ℂ a (WithLp.ofLp w).1 + inner ℂ b (WithLp.ofLp w).2 = 0 at hh
      change inner ℂ b (WithLp.ofLp w).2 - inner ℂ a (-(WithLp.ofLp w).1) = 0
      rw [inner_neg_right]
      linear_combination hh
    have hh := ht (WithLp.ofLp w).2 (-(WithLp.ofLp w).1) hpair
    rw [inner_neg_left] at hh
    change inner ℂ (WithLp.ofLp w).1 x + inner ℂ (WithLp.ofLp w).2 y = 0
    linear_combination -hh
  rw [Submodule.orthogonal_orthogonal] at hH
  change e.symm (x, y) ∈ G.mapEquiv e.symm at hH
  exact (ClosedSubmodule.mem_mapEquiv_iff' (f := e.symm) (s := G) (x, y)).mp hH

theorem coulombAuxiliaryMinimalGraph_of_adjoint_tests {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) (d : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (ht : ∀ u v, (u, v) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph →
      inner ℂ v f = inner ℂ u d) :
    (f, d) ∈ coulombAuxiliaryMinimalGraph N hβ := by
  apply dbarClosedGraph_mem_of_adjoint_tests (coulombAuxiliaryMinimalGraph N hβ) f d
  intro u v huv
  apply ht u v
  rw [coulombAuxiliaryDbarAdjoint,
    LinearPMap.adjoint_graph_eq_graph_adjoint (coulombAuxiliaryMinimalDbar_dense_domain N hβ),
    coulombAuxiliaryMinimalDbar_graph]
  exact huv

end RepulsiveCoulomb
