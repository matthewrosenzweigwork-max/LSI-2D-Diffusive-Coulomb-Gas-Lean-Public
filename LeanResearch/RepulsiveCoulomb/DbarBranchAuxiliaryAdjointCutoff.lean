import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCutoffCoreProduct
import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryMinimalOperator

/-! The exact proper-cutoff product rule on the genuine Hilbert adjoint
of the auxiliary minimal operator. Its domain is preserved, and the values
converge in the actual adjoint graph by the proved vanishing error estimate. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology LinearPMap
namespace RepulsiveCoulomb

theorem coulombAuxiliaryDbarAdjoint_cutoff_graph {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph) :
    (coulombMetricCutoffL2L hR (CoulombConfig N) u,
      coulombMetricCutoffL2L hR ℂ h - coulombCutoffAdjointErrorL β hR u) ∈
        (coulombAuxiliaryDbarAdjoint N hβ).graph := by
  have htest := (coulombAuxiliaryDbarAdjoint_graph_iff hβ u h).mp huh
  apply (coulombAuxiliaryDbarAdjoint_graph_iff hβ _ _).mpr
  intro φ
  have hprod := coulombAuxiliaryCutoffCore_product hβ hR φ
  have hprod' :
      coulombMetricCutoffL2L hR (CoulombConfig N) (coulombAuxiliaryCoreDerivativeL N hβ φ) =
        coulombAuxiliaryCoreDerivativeL N hβ (coulombMetricCutoffCore hR φ) -
          coulombComplexVectorCoreValue hβ (coulombAuxiliaryCutoffErrorCore hR φ) := by
    rw [hprod]
    abel
  calc
    _ = inner ℂ
        (coulombMetricCutoffL2L hR (CoulombConfig N) (coulombAuxiliaryCoreDerivativeL N hβ φ)) u :=
      coulombMetricCutoffL2L_inner hR _ _
    _ = inner ℂ (coulombAuxiliaryCoreDerivativeL N hβ (coulombMetricCutoffCore hR φ)) u -
        inner ℂ (coulombComplexVectorCoreValue hβ (coulombAuxiliaryCutoffErrorCore hR φ)) u := by
      rw [hprod', inner_sub_left]
    _ = inner ℂ (coulombComplexCoreValue hβ (coulombMetricCutoffCore hR φ)) h -
        inner ℂ (coulombComplexCoreValue hβ φ) (coulombCutoffAdjointErrorL β hR u) := by
      rw [htest, coulombAuxiliaryCutoffErrorCore_inner hβ hR φ u]
    _ = inner ℂ (coulombComplexCoreValue hβ φ) (coulombMetricCutoffL2L hR ℂ h) -
        inner ℂ (coulombComplexCoreValue hβ φ) (coulombCutoffAdjointErrorL β hR u) := by
      rw [coulombMetricCutoffCore_value hβ hR φ, ← coulombMetricCutoffL2L_inner hR]
    _ = _ := (inner_sub_right _ _ _).symm

theorem coulombAuxiliaryDbarAdjoint_cutoff_tendsto {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    Tendsto (fun n : ℕ =>
      (coulombMetricCutoffL2L (by positivity : 0 < (n : ℝ) + 1) (CoulombConfig N) u,
        coulombMetricCutoffL2L (by positivity : 0 < (n : ℝ) + 1) ℂ h -
          coulombCutoffAdjointErrorL β (by positivity : 0 < (n : ℝ) + 1) u))
      atTop (𝓝 (u, h)) := by
  have hv := coulombMetricCutoffL2L_tendsto hβ u
  have hh := (coulombMetricCutoffL2L_tendsto hβ h).sub (coulombCutoffAdjointErrorL_tendsto_zero hβ u)
  simpa only [sub_zero] using hv.prodMk_nhds hh

end RepulsiveCoulomb
