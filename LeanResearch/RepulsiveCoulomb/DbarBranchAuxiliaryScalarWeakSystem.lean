import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliarySystemDirections

/-! The scalar row of the actual auxiliary adjoint is identified with the
literal finite weak divergence system after w=rho*u. Its input has only local
integrability; individual coordinate derivatives are never assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators LinearPMap
namespace RepulsiveCoulomb

def coulombDensityInputComponent {N : ℕ} (β : ℝ)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (b : Fin N) (z : CoulombConfig N) : ℂ :=
  (coulombDensity N β z : ℂ) * u z b

theorem coulombDensityInputComponent_locallyIntegrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (b : Fin N) :
    LocallyIntegrableOn (coulombDensityInputComponent β u b) (coulombDomain N) volume := by
  have hu := (EuclideanSpace.proj (𝕜 := ℂ) b).locallyIntegrableOn_comp
    (coulombL2_locallyIntegrableOn hβ u)
  exact hu.continuousOn_mul
    (fun z hz => (coulombComplexDensity_contDiffAt β hz).continuousAt.continuousWithinAt)
    (coulombDomain N).isOpen.isLocallyClosed

theorem coulombAuxiliaryScalarDensityPrincipal_integral {N : ℕ}
    (w : Fin N → CoulombConfig N → ℂ)
    (hw : ∀ b, LocallyIntegrableOn (w b) (coulombDomain N) volume)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    -(∑ b, ∑ d : Fin N × Bool, ∫ z,
      (fderiv ℝ (φ : CoulombConfig N → ℝ) z (dbarSystemDirection N d)) •
        (coulombAuxiliaryScalarDensityPrincipal b d z * w b z)) =
      ∑ j, ∫ z, coulombDCoordinate (fun x => (φ x : ℂ)) z j *
        (∑ b, coulombInverseRootMatrix z j b * w b z) := by
  have hi (b : Fin N) (d : Fin N × Bool) : Integrable (fun z =>
      (fderiv ℝ (φ : CoulombConfig N → ℝ) z (dbarSystemDirection N d)) •
        (coulombAuxiliaryScalarDensityPrincipal b d z * w b z)) volume := by
    have h := coulombLocalCoefficient_test_integrable (coulombAuxiliaryScalarDensityPrincipal b d)
      (fun z hz => coulombAuxiliaryScalarDensityPrincipal_contDiffAt b d hz)
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (dbarSystemDirection N d) φ) (hw b)
    convert h using 1
    ext z
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) φ (by simp)]
  have hjb (j b : Fin N) : Integrable (fun z =>
      coulombDCoordinate (fun x => (φ x : ℂ)) z j *
        (coulombInverseRootMatrix z j b * w b z)) volume := by
    have h := coulombLocalCoefficient_complex_test_integrable
      (fun z => coulombInverseRootMatrix z j b)
      (fun z hz => coulombInverseRootMatrix_entry_contDiffAt j b hz)
      (coulombDCoreCoordinateL N j (TestFunction.postcompCLM Complex.ofRealCLM φ)) (hw b)
    simpa only [coulombDCoreCoordinateL_apply, TestFunction.postcompCLM_apply,
      Function.comp_def, Complex.ofRealCLM_apply] using! h
  have hj (j : Fin N) : Integrable (fun z =>
      coulombDCoordinate (fun x => (φ x : ℂ)) z j *
        (∑ b, coulombInverseRootMatrix z j b * w b z)) volume := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun b _ => hjb j b)
  have hb (b : Fin N) := integral_finsetSum Finset.univ (fun d _ => hi b d)
  simp_rw [← hb]
  rw [← integral_finsetSum Finset.univ (fun b _ =>
    integrable_finsetSum Finset.univ (fun d _ => hi b d))]
  rw [← integral_neg, ← integral_finsetSum Finset.univ (fun j _ => hj j)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    simp only [Fintype.sum_prod_type, Complex.real_smul]
    rw [Finset.sum_comm]
    simp_rw [coulombAuxiliaryScalarDensityPrincipal_direction_sum]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_neg_distrib, neg_mul, neg_neg]

theorem coulombAuxiliaryDbarAdjoint_scalar_weakSystem {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph) :
    DbarLocalWeakDivergenceSystem
      (fun _ : Unit => coulombAuxiliaryScalarDensityPrincipal)
      (fun (_ : Unit) (_ : Fin N) (_ : CoulombConfig N) => 0)
      (dbarSystemDirection N) (coulombDensityInputComponent β u)
      (fun (_ : Unit) z => (coulombDensity N β z : ℂ) * h z) := by
  intro a φ
  simp only [zero_mul, smul_zero, integral_zero, Finset.sum_const_zero, add_zero]
  rw [coulombAuxiliaryScalarDensityPrincipal_integral _ (coulombDensityInputComponent_locallyIntegrable hβ u) φ]
  rw [coulombAuxiliaryAdjoint_density_flux_weak hβ huh φ]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [dbarCLMMatrix_apply]
    rfl

end RepulsiveCoulomb
