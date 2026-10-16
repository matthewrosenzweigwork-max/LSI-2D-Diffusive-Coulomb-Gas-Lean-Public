module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryRawWeakIntegral

@[expose] public section

/-! The raw exterior row is the literal finite weak divergence system in the
same density-scaled input as the scalar row. The source is the actual cutoff
error. All local integrability comes from the original Gibbs-L2 input. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombAuxiliaryRawCurlDensityPrincipal_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (w : Fin N → CoulombConfig N → ℂ)
    (hw : ∀ b, LocallyIntegrableOn (w b) (coulombDomain N) volume)
    (i j : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∑ b, ∑ d : Fin N × Bool, ∫ z,
      (fderiv ℝ (φ : CoulombConfig N → ℝ) z (dbarSystemDirection N d)) •
        (coulombAuxiliaryRawCurlDensityPrincipal β i j b d z * w b z)) =
      ∫ z, coulombDbarCoordinate (fun x => (φ x : ℂ)) z i *
        (∑ b, coulombDensityRootMatrix β z j b * w b z) -
        coulombDbarCoordinate (fun x => (φ x : ℂ)) z j *
          (∑ b, coulombDensityRootMatrix β z i b * w b z) := by
  have hi (b : Fin N) (d : Fin N × Bool) : Integrable (fun z =>
      (fderiv ℝ (φ : CoulombConfig N → ℝ) z (dbarSystemDirection N d)) •
        (coulombAuxiliaryRawCurlDensityPrincipal β i j b d z * w b z)) volume := by
    have h := coulombLocalCoefficient_test_integrable
      (coulombAuxiliaryRawCurlDensityPrincipal β i j b d)
      (fun z hz => coulombAuxiliaryRawCurlDensityPrincipal_contDiffAt hβ i j b d hz)
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (dbarSystemDirection N d) φ) (hw b)
    convert h using 1
    ext z
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) φ (by simp)]
  have hb (b : Fin N) := integral_finsetSum Finset.univ (fun d _ => hi b d)
  simp_rw [← hb]
  rw [← integral_finsetSum Finset.univ (fun b _ =>
    integrable_finsetSum Finset.univ (fun d _ => hi b d))]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    have hpoint (b : Fin N) := coulombAuxiliaryRawCurlDensityPrincipal_direction_sum β
      (TestFunction.postcompCLM Complex.ofRealCLM φ : CoulombConfig N → ℂ) z i j b (w b z)
    simp_rw [coulombRealCore_complex_fderiv] at hpoint
    have hφ : (TestFunction.postcompCLM Complex.ofRealCLM φ : CoulombConfig N → ℂ) =
        fun x => (φ x : ℂ) := rfl
    rw [hφ] at hpoint
    simp only [Complex.real_smul]
    simp_rw [hpoint]
    simp only [Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

def coulombAuxiliaryCutoffRawSource {N : ℕ} {β : ℝ} (R : ℝ)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (p : Fin N × Fin N) (z : CoulombConfig N) : ℂ :=
  dbarVectorWedge (coulombDbar (fun x => (coulombMetricCutoff R x : ℂ)) z)
    (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) p.1 p.2

theorem coulombAuxiliaryCutoffRawSource_locallyIntegrable {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (p : Fin N × Fin N) :
    LocallyIntegrableOn (coulombAuxiliaryCutoffRawSource R u p) (coulombDomain N) volume := by
  let θ : TestFunction (coulombDomain N) ℂ ⊤ :=
    TestFunction.postcompCLM Complex.ofRealCLM (coulombMetricCutoffTest hR)
  let a := coulombDbarCoreCoordinateL N p.1 θ
  let b := coulombDbarCoreCoordinateL N p.2 θ
  have hi := (coulombAuxiliaryRaw_locallyIntegrable hβ u p.2).continuousOn_mul
    a.continuous.continuousOn (coulombDomain N).isOpen.isLocallyClosed
  have hj := (coulombAuxiliaryRaw_locallyIntegrable hβ u p.1).mul_continuousOn
    b.continuous.continuousOn (coulombDomain N).isOpen.isLocallyClosed
  have h := hi.sub hj
  simpa only [a, b, θ, coulombDbarCoreCoordinateL_apply, Pi.sub_apply,
    coulombAuxiliaryCutoffRawSource, dbarVectorWedge, coulombDbar_apply] using! h

theorem coulombAuxiliaryCompatibility_raw_weakSystem {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    DbarLocalWeakDivergenceSystem
      (fun p : Fin N × Fin N => coulombAuxiliaryRawCurlDensityPrincipal β p.1 p.2)
      (fun (_ : Fin N × Fin N) (_ : Fin N) (_ : CoulombConfig N) => 0)
      (dbarSystemDirection N)
      (coulombDensityInputComponent β (coulombMetricCutoffL2L hR (CoulombConfig N) u))
      (coulombAuxiliaryCutoffRawSource R u) := by
  intro p φ
  simp only [zero_mul, smul_zero, integral_zero, Finset.sum_const_zero, add_zero]
  rw [coulombAuxiliaryRawCurlDensityPrincipal_integral hβ _
    (coulombDensityInputComponent_locallyIntegrable hβ _) p.1 p.2 φ]
  change (∫ z, φ z • dbarVectorWedge
    (coulombDbar (fun x => (coulombMetricCutoff R x : ℂ)) z)
      (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) p.1 p.2) = _
  rw [coulombAuxiliaryCutoff_raw_exterior_equation hβ hR hu p.1 p.2 φ]
  congr 1
  apply integral_congr_ae
  filter_upwards [coulombDomain_ae N] with z hz
  change _ = coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.1 *
    (∑ b, coulombDensityRootMatrix β z p.2 b * ((coulombDensity N β z : ℂ) *
      (coulombMetricCutoffL2L hR (CoulombConfig N) u z) b)) -
    coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.2 *
      (∑ b, coulombDensityRootMatrix β z p.1 b * ((coulombDensity N β z : ℂ) *
        (coulombMetricCutoffL2L hR (CoulombConfig N) u z) b))
  rw [coulombDensityRootMatrix_density_action hβ hz,
    coulombDensityRootMatrix_density_action hβ hz]

end RepulsiveCoulomb
