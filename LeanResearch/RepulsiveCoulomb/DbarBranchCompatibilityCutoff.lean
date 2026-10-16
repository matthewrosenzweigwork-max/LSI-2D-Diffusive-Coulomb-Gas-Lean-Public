import LeanResearch.RepulsiveCoulomb.DbarBranchRawPairingTestAlgebra
import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCutoffSymbols

/-! The exact weak cutoff product equation for the closed compatibility
subspace. The additional source is defined by literal derivatives of the
actual cutoff and compact raw pairings, not an assumed boundary formula. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombAuxiliaryCutoffRawSourceL {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (i j : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) →L[ℂ] ℂ :=
  let θ := coulombMetricCutoffTest (N := N) hR
  (1 / 2 : ℂ) •
    (coulombAuxiliaryRawPairingL hβ j (coulombRealCoreProduct
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i 1) θ) φ) +
      Complex.I • coulombAuxiliaryRawPairingL hβ j (coulombRealCoreProduct
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i Complex.I) θ) φ) -
      coulombAuxiliaryRawPairingL hβ i (coulombRealCoreProduct
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N j 1) θ) φ) -
      Complex.I • coulombAuxiliaryRawPairingL hβ i (coulombRealCoreProduct
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N j Complex.I) θ) φ))

theorem coulombAuxiliaryCurl_cutoff_leibniz {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (i j : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombAuxiliaryCurlConstraintL hβ i j φ (coulombMetricCutoffL2L hR (CoulombConfig N) u) +
      coulombAuxiliaryCutoffRawSourceL hβ hR i j φ u =
      coulombAuxiliaryCurlConstraintL hβ i j
        (coulombRealCoreProduct (coulombMetricCutoffTest hR) φ) u := by
  simp only [coulombAuxiliaryCurlConstraintL_apply, coulombAuxiliaryCutoffRawSourceL,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul]
  simp_rw [coulombAuxiliaryRawPairing_cutoff hβ hR,
    coulombRealCoreProduct_lineDeriv, coulombAuxiliaryRawPairing_add_test]
  ring

theorem coulombAuxiliaryCompatibility_cutoff_weak {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ)
    (i j : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombAuxiliaryCurlConstraintL hβ i j φ (coulombMetricCutoffL2L hR (CoulombConfig N) u) =
      -coulombAuxiliaryCutoffRawSourceL hβ hR i j φ u := by
  have h := coulombAuxiliaryCurl_cutoff_leibniz hβ hR i j φ u
  rw [hu i j (coulombRealCoreProduct (coulombMetricCutoffTest hR) φ)] at h
  exact eq_neg_of_add_eq_zero_left h

theorem coulombRealCutoff_raw_source_pointwise {N : ℕ}
    (θ φ : TestFunction (coulombDomain N) ℝ ⊤) (z v : CoulombConfig N) (i j : Fin N) :
    (1 / 2 : ℂ) *
      ((coulombRealCoreProduct (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
          (coulombCoordinateInjection N i 1) θ) φ z) • v j +
        Complex.I * ((coulombRealCoreProduct (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
          (coulombCoordinateInjection N i Complex.I) θ) φ z) • v j) -
        (coulombRealCoreProduct (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
          (coulombCoordinateInjection N j 1) θ) φ z) • v i -
        Complex.I * ((coulombRealCoreProduct (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
          (coulombCoordinateInjection N j Complex.I) θ) φ z) • v i)) =
      φ z • dbarVectorWedge (coulombDbar (fun x => (θ x : ℂ)) z) v i j := by
  have hp (η : TestFunction (coulombDomain N) ℝ ⊤) :
      coulombRealCoreProduct η φ z = η z * φ z := rfl
  have hd (w : CoulombConfig N) :
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w θ) z =
        fderiv ℝ (θ : CoulombConfig N → ℝ) z w := by
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) θ (by simp)]
  simp only [hp, hd, dbarVectorWedge, coulombDbar_apply]
  rw [coulombDbarCoordinate_real (θ.contDiff.differentiable (by simp) z),
    coulombDbarCoordinate_real (θ.contDiff.differentiable (by simp) z),
    coulomb_real_axis_derivative, coulomb_imag_axis_derivative,
    coulomb_real_axis_derivative, coulomb_imag_axis_derivative]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  conv_rhs => rw [← Complex.re_add_im (gradient (θ : CoulombConfig N → ℝ) z i),
    ← Complex.re_add_im (gradient (θ : CoulombConfig N → ℝ) z j)]
  ring

end RepulsiveCoulomb
