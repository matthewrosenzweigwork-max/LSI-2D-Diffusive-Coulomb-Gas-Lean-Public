module

public import LeanResearch.RepulsiveCoulomb.DbarBranchLocalMollifier
public import LeanResearch.RepulsiveCoulomb.DbarBranchCoreCompatibility

@[expose] public section

/-! Reflected normalized mollifiers are actual collision-free test functions
when their full support ball avoids collisions. Their exact derivative sign
is needed for preservation of the weak Cauchy-Riemann equations. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombMollifier_reflection_tsupport {N : ℕ}
    (ψ : ContDiffBump (0 : CoulombConfig N)) (z : CoulombConfig N) :
    tsupport (fun y : CoulombConfig N => ψ.normed volume (z - y)) ⊆ closedBall z ψ.rOut := by
  have hsub := tsupport_comp_subset_preimage (ψ.normed volume)
    (show Continuous (fun y : CoulombConfig N => z - y) by fun_prop)
  intro y hy
  have hy' := hsub hy
  rw [ψ.tsupport_normed_eq] at hy'
  simpa only [mem_preimage, mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using hy'

def coulombMollifierTest {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N)) (z : CoulombConfig N)
    (hball : closedBall z ψ.rOut ⊆ coulombDomain N) : TestFunction (coulombDomain N) ℝ ⊤ where
  toFun y := ψ.normed volume (z - y)
  contDiff' := ψ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := ψ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft z)
  tsupport_subset' := (coulombMollifier_reflection_tsupport ψ z).trans hball

theorem coulombMollifierTest_apply {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    (z : CoulombConfig N) (hball : closedBall z ψ.rOut ⊆ coulombDomain N) (y : CoulombConfig N) :
    coulombMollifierTest ψ z hball y = ψ.normed volume (z - y) := rfl

theorem coulombMollifierTest_lineDeriv {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    (z : CoulombConfig N) (hball : closedBall z ψ.rOut ⊆ coulombDomain N) (y v : CoulombConfig N) :
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v (coulombMollifierTest ψ z hball)) y =
      -fderiv ℝ (ψ.normed volume) (z - y) v := by
  simp only [TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true]
  rw [((coulombMollifierTest ψ z hball).contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv]
  change fderiv ℝ (fun w : CoulombConfig N => ψ.normed volume (z - w)) y v = _
  have hd := ((ψ.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))).differentiable (by simp) (z - y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_sub z)
  have hfd := hd.fderiv
  change fderiv ℝ (fun w : CoulombConfig N => ψ.normed volume (z - w)) y = _ at hfd
  rw [hfd]
  simp

theorem coulombMollifierTest_indicator_pairing {N : ℕ}
    (ψ : ContDiffBump (0 : CoulombConfig N)) (z : CoulombConfig N)
    {K : Set (CoulombConfig N)} (hKΩ : K ⊆ coulombDomain N) (hball : closedBall z ψ.rOut ⊆ K)
    (f : CoulombConfig N → ℂ) :
    (fun y => coulombMollifierTest ψ z (hball.trans hKΩ) y • K.indicator f y) =
      fun y => coulombMollifierTest ψ z (hball.trans hKΩ) y • f y := by
  funext y
  by_cases hy : y ∈ K
  · rw [indicator_of_mem hy]
  · have hy' : y ∉ tsupport (coulombMollifierTest ψ z (hball.trans hKΩ) : CoulombConfig N → ℝ) :=
      fun hs => hy (hball (coulombMollifier_reflection_tsupport ψ z hs))
    rw [image_eq_zero_of_notMem_tsupport hy', zero_smul, zero_smul]

theorem coulombMollifierTest_lineDeriv_indicator_pairing {N : ℕ}
    (ψ : ContDiffBump (0 : CoulombConfig N)) (z v : CoulombConfig N)
    {K : Set (CoulombConfig N)} (hKΩ : K ⊆ coulombDomain N) (hball : closedBall z ψ.rOut ⊆ K)
    (f : CoulombConfig N → ℂ) :
    (fun y => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
        (coulombMollifierTest ψ z (hball.trans hKΩ))) y • K.indicator f y) =
      fun y => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
        (coulombMollifierTest ψ z (hball.trans hKΩ))) y • f y := by
  funext y
  by_cases hy : y ∈ K
  · rw [indicator_of_mem hy]
  · have hy' : y ∉ tsupport (coulombMollifierTest ψ z (hball.trans hKΩ) : CoulombConfig N → ℝ) :=
      fun hs => hy (hball (coulombMollifier_reflection_tsupport ψ z hs))
    have hd := TauCeti.lineDeriv_eq_zero_of_notMem_tsupport
      (coulombMollifierTest ψ z (hball.trans hKΩ)) hy' v
    simp only [TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true, hd, zero_smul]

end RepulsiveCoulomb
