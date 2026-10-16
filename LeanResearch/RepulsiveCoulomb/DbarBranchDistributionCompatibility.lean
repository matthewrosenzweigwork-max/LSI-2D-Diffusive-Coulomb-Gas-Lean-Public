import LeanResearch.RepulsiveCoulomb.DbarBranchMaximalGraph
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Distributional Wirtinger operators and genuine compatibility of maximal
weak dbar data. Mixed derivatives commute because smooth test Hessians are
symmetric; no weak regularity or analytic estimate is used. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

theorem coulombTest_lineDeriv_commute {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (v w : CoulombConfig N) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ :
      TestFunction (coulombDomain N) ℝ ⊤) =
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ :
      TestFunction (coulombDomain N) ℝ ⊤) := by
  have hfun (a : CoulombConfig N) :
      ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a φ : TestFunction (coulombDomain N) ℝ ⊤) :
        CoulombConfig N → ℝ) = fun z => fderiv ℝ (φ : CoulombConfig N → ℝ) z a := by
    funext z
    simp only [TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true]
    exact (φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv
  ext z
  simp only [TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true]
  rw [hfun, hfun]
  have hdd : DifferentiableAt ℝ (fderiv ℝ (φ : CoulombConfig N → ℝ)) z :=
    (φ.contDiff.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  rw [(hdd.clm_apply (differentiableAt_const w)).lineDeriv_eq_fderiv,
    (hdd.clm_apply (differentiableAt_const v)).lineDeriv_eq_fderiv,
    fderiv_clm_apply hdd (differentiableAt_const w),
    fderiv_clm_apply hdd (differentiableAt_const v)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using (φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

def coulombDistributionDbarCoordinateL (N : ℕ) (i : Fin N) :
    Distribution (coulombDomain N) ℂ ⊤ →L[ℝ] Distribution (coulombDomain N) ℂ ⊤ :=
  (1 / 2 : ℝ) •
    (Distribution.lineDerivCLM (coulombCoordinateInjection N i 1) +
      (Distribution.mapCLM (Complex.I • ContinuousLinearMap.id ℝ ℂ)).comp
        (Distribution.lineDerivCLM (coulombCoordinateInjection N i Complex.I)))

theorem coulombDistributionDbarCoordinateL_apply {N : ℕ} (i : Fin N)
    (T : Distribution (coulombDomain N) ℂ ⊤) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombDistributionDbarCoordinateL N i T φ =
      -((1 / 2 : ℝ) •
        (T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i 1) φ) +
          Complex.I * T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i Complex.I) φ))) := by
  simp only [coulombDistributionDbarCoordinateL, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    Distribution.mapCLM_apply, Distribution.lineDerivCLM_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem coulombDistributionDbarCoordinateL_commute {N : ℕ} (i j : Fin N)
    (T : Distribution (coulombDomain N) ℂ ⊤) :
    coulombDistributionDbarCoordinateL N i (coulombDistributionDbarCoordinateL N j T) =
      coulombDistributionDbarCoordinateL N j (coulombDistributionDbarCoordinateL N i T) := by
  ext φ
  simp only [coulombDistributionDbarCoordinateL_apply]
  rw [coulombTest_lineDeriv_commute φ (coulombCoordinateInjection N j 1) (coulombCoordinateInjection N i 1),
    coulombTest_lineDeriv_commute φ (coulombCoordinateInjection N j Complex.I) (coulombCoordinateInjection N i 1),
    coulombTest_lineDeriv_commute φ (coulombCoordinateInjection N j 1) (coulombCoordinateInjection N i Complex.I),
    coulombTest_lineDeriv_commute φ (coulombCoordinateInjection N j Complex.I) (coulombCoordinateInjection N i Complex.I)]
  simp only [Complex.real_smul]
  ring

theorem coulombMaxDbarGraph_distribution_iff {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    (f, g) ∈ coulombMaxDbarGraph hβ ↔ ∀ i,
      coulombL2Distribution hβ ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) g) =
        coulombDistributionDbarCoordinateL N i (coulombL2Distribution hβ f) := by
  constructor
  · intro h i
    ext φ
    rw [coulombDistributionDbarCoordinateL_apply]
    have hi := h i φ
    rw [coulombWeakDbarConstraintL_apply] at hi
    exact eq_neg_of_add_eq_zero_left hi
  · intro h i φ
    rw [coulombWeakDbarConstraintL_apply]
    have hi := congrArg (fun T : Distribution (coulombDomain N) ℂ ⊤ => T φ) (h i)
    rw [coulombDistributionDbarCoordinateL_apply] at hi
    rw [hi, neg_add_cancel]

theorem coulombMaxDbarGraph_distribution_compatible {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : Lp ℂ 2 (coulombMeasure N β)} {g : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hfg : (f, g) ∈ coulombMaxDbarGraph hβ) (i j : Fin N) :
    coulombDistributionDbarCoordinateL N i
      (coulombL2Distribution hβ ((coulombCoordinate j).compLpL 2 (coulombMeasure N β) g)) =
    coulombDistributionDbarCoordinateL N j
      (coulombL2Distribution hβ ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) g)) := by
  have h := (coulombMaxDbarGraph_distribution_iff hβ f g).mp hfg
  rw [h i, h j]
  exact coulombDistributionDbarCoordinateL_commute i j _

end RepulsiveCoulomb
