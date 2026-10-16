import LeanResearch.RepulsiveCoulomb.DbarBranchLocalDistribution
import Mathlib.MeasureTheory.Function.L2Space

/-! Each genuine Lebesgue test pairing is continuous on weighted L2, by
restriction to the test support and the local lower density bound. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

def coulombComplexTestOnSupport {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Lp ℂ 2 (volume.restrict (tsupport (φ : CoulombConfig N → ℝ))) :=
  ((Complex.continuous_ofReal.comp φ.continuous).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.comp_left Complex.ofReal_zero)).toLp (fun z => (φ z : ℂ))

theorem coulombComplexTestOnSupport_coe {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombComplexTestOnSupport φ =ᵐ[volume.restrict (tsupport (φ : CoulombConfig N → ℝ))]
      fun z => (φ z : ℂ) :=
  MemLp.coeFn_toLp _

def coulombL2TestPairingL {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Lp ℂ 2 (coulombMeasure N β) →L[ℝ] ℂ :=
  ((innerSL ℂ (coulombComplexTestOnSupport φ)).restrictScalars ℝ).comp
    (coulombL2RestrictToVolume hβ φ.hasCompactSupport φ.tsupport_subset Subset.rfl ℂ)

theorem coulombL2TestPairingL_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (f : Lp ℂ 2 (coulombMeasure N β)) :
    coulombL2TestPairingL hβ φ f = coulombL2Distribution hβ f φ := by
  rw [coulombL2Distribution_apply]
  change inner ℂ (coulombComplexTestOnSupport φ)
    (coulombL2RestrictToVolume hβ φ.hasCompactSupport φ.tsupport_subset Subset.rfl ℂ f) = _
  rw [L2.inner_def]
  calc
    _ = ∫ z in tsupport (φ : CoulombConfig N → ℝ), φ z • f z := by
      apply integral_congr_ae
      filter_upwards [coulombComplexTestOnSupport_coe φ,
        coulombL2RestrictToVolume_coe hβ φ.hasCompactSupport φ.tsupport_subset Subset.rfl f]
        with z hφ hf
      simp only [hφ, hf, RCLike.inner_apply', Complex.conj_ofReal, RCLike.real_smul_eq_coe_mul]
      rfl
    _ = ∫ z, φ z • f z :=
      setIntegral_eq_integral_of_ae_compl_eq_zero (Eventually.of_forall fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport hz, zero_smul])

theorem coulombL2Distribution_eval_continuous {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Continuous (fun f : Lp ℂ 2 (coulombMeasure N β) => coulombL2Distribution hβ f φ) := by
  have he : (fun f : Lp ℂ 2 (coulombMeasure N β) => coulombL2Distribution hβ f φ) =
      coulombL2TestPairingL hβ φ :=
    funext (fun f => (coulombL2TestPairingL_apply hβ φ f).symm)
  rw [he]
  exact (coulombL2TestPairingL hβ φ).continuous

end RepulsiveCoulomb
