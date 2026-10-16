module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactIntegrationByParts
public import LeanResearch.RepulsiveCoulomb.DbarBranchLocalCoreMultiplier
public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCore

@[expose] public section

/-! The actual weighted formal adjoint on compact complex tests. It is the
literal -rho^{-1} partial(rho phi), with the normalized Coulomb density rho.
This does not identify a maximal formal domain with any closed-operator adjoint. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ComplexConjugate
namespace RepulsiveCoulomb

def coulombDCoreCoordinateL (N : ℕ) (i : Fin N) :
    TestFunction (coulombDomain N) ℂ ⊤ →L[ℂ] TestFunction (coulombDomain N) ℂ ⊤ :=
  let dx : TestFunction (coulombDomain N) ℂ ⊤ →L[ℂ] TestFunction (coulombDomain N) ℂ ⊤ :=
    TestFunction.lineDerivCLM ℂ (coulombCoordinateInjection N i 1)
  let dy : TestFunction (coulombDomain N) ℂ ⊤ →L[ℂ] TestFunction (coulombDomain N) ℂ ⊤ :=
    TestFunction.lineDerivCLM ℂ (coulombCoordinateInjection N i Complex.I)
  (TestFunction.postcompCLM ((1 / 2 : ℂ) • ContinuousLinearMap.id ℂ ℂ)).comp
    (dx - (TestFunction.postcompCLM (Complex.I • ContinuousLinearMap.id ℂ ℂ)).comp dy)

theorem coulombDCoreCoordinateL_apply {N : ℕ} (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    coulombDCoreCoordinateL N i φ z = coulombDCoordinate φ z i := by
  change (1 / 2 : ℂ) *
    ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ (coulombCoordinateInjection N i 1) φ) z -
      Complex.I * (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ (coulombCoordinateInjection N i Complex.I) φ) z) = _
  simp only [TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true]
  rw [(φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv,
    (φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv]
  unfold coulombDCoordinate
  ring

def coulombWeightedCoreAdjointCoordinate {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) : TestFunction (coulombDomain N) ℂ ⊤ :=
  -coulombComplexCoreDensityDiv hβ (coulombDCoreCoordinateL N i (coulombComplexCoreDensityMul β φ))

theorem coulombWeightedCoreAdjointCoordinate_apply {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    coulombWeightedCoreAdjointCoordinate hβ i φ z =
      -coulombDCoordinate (fun x => (coulombDensity N β x : ℂ) * φ x) z i /
        (coulombDensity N β z : ℂ) := by
  change -(coulombComplexCoreDensityDiv hβ
    (coulombDCoreCoordinateL N i (coulombComplexCoreDensityMul β φ)) z) = _
  rw [coulombComplexCoreDensityDiv_apply, coulombDCoreCoordinateL_apply]
  change -(coulombDCoordinate (fun x => (coulombDensity N β x : ℂ) * φ x) z i /
    (coulombDensity N β z : ℂ)) = _
  ring

theorem dbarComplexCore_weighted_pair_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) :
    Integrable (fun z => conj (φ z) * ψ z) (coulombMeasure N β) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  exact ((Complex.conjCLE.continuous.comp φ.continuous).mul ψ.continuous).integrable_of_hasCompactSupport
    (φ.hasCompactSupport.comp_left (map_zero (starRingEnd ℂ))).mul_right

theorem dbarCoulomb_integral_density {N : ℕ} {β : ℝ} (hβ : 0 < β) (f : CoulombConfig N → ℂ) :
    (∫ z, f z ∂coulombMeasure N β) = ∫ z, (coulombDensity N β z : ℂ) * f z := by
  rw [coulombMeasure_eq_withDensity hβ,
    integral_withDensity_eq_integral_toReal_smul
      (coulombDensity_continuous hβ.le).measurable.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    simp only [ENNReal.toReal_ofReal (coulombDensity_nonneg β z), Complex.real_smul]

theorem coulombWeightedCoreAdjointCoordinate_ibp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) (i : Fin N) :
    (∫ z, conj (φ z) * coulombDbarCoreCoordinateL N i ψ z ∂coulombMeasure N β) =
      ∫ z, conj (coulombWeightedCoreAdjointCoordinate hβ i φ z) * ψ z ∂coulombMeasure N β := by
  have hleft := dbarComplexCore_weighted_pair_integrable hβ φ (coulombDbarCoreCoordinateL N i ψ)
  have hright := dbarComplexCore_weighted_pair_integrable hβ (coulombWeightedCoreAdjointCoordinate hβ i φ) ψ
  let q := coulombComplexCoreDensityMul β φ
  have hq : (q : CoulombConfig N → ℂ) = fun z => (coulombDensity N β z : ℂ) * φ z := rfl
  calc
    _ = ∫ z, conj (q z) * coulombDbarCoordinate ψ z i := by
      rw [dbarCoulomb_integral_density hβ]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        rw [coulombDbarCoreCoordinateL_apply]
        change (coulombDensity N β z : ℂ) * (conj (φ z) * coulombDbarCoordinate ψ z i) =
          conj ((coulombDensity N β z : ℂ) * φ z) * coulombDbarCoordinate ψ z i
        simp only [map_mul, Complex.conj_ofReal]
        ring
    _ = ∫ z, conj (-coulombDCoordinate q z i) * ψ z := dbarComplexCore_hermitian_ibp q ψ i
    _ = _ := by
      rw [dbarCoulomb_integral_density hβ]
      apply integral_congr_ae
      filter_upwards [coulombDomain_ae N] with z hz
      have hρ : (coulombDensity N β z : ℂ) ≠ 0 := by
        exact_mod_cast (coulombDensity_pos_off_collisions hβ hz).ne'
      rw [coulombWeightedCoreAdjointCoordinate_apply, hq]
      simp only [map_div₀, map_neg, Complex.conj_ofReal]
      field_simp [hρ] <;> ring

end RepulsiveCoulomb
