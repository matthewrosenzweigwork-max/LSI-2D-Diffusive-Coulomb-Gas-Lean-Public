module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryBasicEstimate
public import LeanResearch.RepulsiveCoulomb.DbarBranchClosedGraphVariational

@[expose] public section

/-! The actual curvature-weighted dual construction. A Euclidean-L2 datum
alpha enters the auxiliary space as R*alpha, and its dual norm is exactly
bounded by sqrt(2/beta)*norm(alpha). No uniform coercivity in the full
auxiliary norm or closed-range assertion is inferred. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped LinearPMap
namespace RepulsiveCoulomb

theorem coulombAuxiliary_adjoint_inverseRoot_bound {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    ‖coulombInverseRootL2L N β u‖ ≤ Real.sqrt (2 / β) * ‖h‖ := by
  have hb := coulombAuxiliary_adjoint_basic_estimate hβ huh hu
  have hc : 0 ≤ 2 / β := (div_pos (by norm_num : (0 : ℝ) < 2) hβ).le
  have hs : ‖coulombInverseRootL2L N β u‖ ^ 2 ≤ (2 / β) * ‖h‖ ^ 2 := by
    calc
      _ = (2 / β) * ((β / 2) * ‖coulombInverseRootL2L N β u‖ ^ 2) := by
        field_simp [hβ.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb hc
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hc]
  exact hs

theorem coulombAuxiliary_datum_pairing_bound {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (α : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (hα : coulombInverseRootL2L N β α ∈ coulombAuxiliaryCompatibility N hβ)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph) :
    ‖inner ℂ (coulombInverseRootL2L N β α) u‖ ≤
      (Real.sqrt (2 / β) * ‖α‖) * ‖h‖ := by
  let v := coulombAuxiliaryCompatibilityProjection N hβ u
  have hvh : (v, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph :=
    coulombAuxiliaryCompatibilityProjection_adjoint_graph hβ huh
  have hv : v ∈ coulombAuxiliaryCompatibility N hβ := Submodule.starProjection_apply_mem _ u
  have hbound := coulombAuxiliary_adjoint_inverseRoot_bound hβ hvh hv
  calc
    _ = ‖inner ℂ (coulombInverseRootL2L N β α) v‖ :=
      congrArg norm (coulombAuxiliaryCompatibilityProjection_datum_pairing hβ hα u)
    _ = ‖inner ℂ α (coulombInverseRootL2L N β v)‖ :=
      congrArg norm (coulombInverseRootL2L_selfAdjoint_pairing β α v)
    _ ≤ ‖α‖ * ‖coulombInverseRootL2L N β v‖ := norm_inner_le_norm _ _
    _ ≤ ‖α‖ * (Real.sqrt (2 / β) * ‖h‖) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = _ := by ring

theorem coulombAuxiliary_curvature_solution {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (α : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (hα : coulombInverseRootL2L N β α ∈ coulombAuxiliaryCompatibility N hβ) :
    ∃ f : Lp ℂ 2 (coulombMeasure N β),
      (f, coulombInverseRootL2L N β α) ∈ coulombAuxiliaryMinimalGraph N hβ ∧
        ‖f‖ ^ 2 ≤ (2 / β) * ‖α‖ ^ 2 := by
  let C : ℝ := Real.sqrt (2 / β) * ‖α‖
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hbound : ∀ u h, (u, h) ∈ (coulombAuxiliaryMinimalGraph N hβ).toSubmodule.adjoint →
      ‖inner ℂ (coulombInverseRootL2L N β α) u‖ ≤ C * ‖h‖ := by
    intro u h huh
    have hg : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph := by
      rw [coulombAuxiliaryDbarAdjoint,
        LinearPMap.adjoint_graph_eq_graph_adjoint (coulombAuxiliaryMinimalDbar_dense_domain N hβ),
        coulombAuxiliaryMinimalDbar_graph]
      exact huh
    exact coulombAuxiliary_datum_pairing_bound hβ α hα hg
  obtain ⟨f, hgraph, hnorm⟩ := dbarClosedGraph_solution_of_pairing_bound
    (coulombAuxiliaryMinimalGraph N hβ) (coulombInverseRootL2L N β α) hC hbound
  refine ⟨f, hgraph, ?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg f) hnorm 2
  have hc : 0 ≤ 2 / β := (div_pos (by norm_num : (0 : ℝ) < 2) hβ).le
  simpa only [C, mul_pow, Real.sq_sqrt hc] using hs

end RepulsiveCoulomb
