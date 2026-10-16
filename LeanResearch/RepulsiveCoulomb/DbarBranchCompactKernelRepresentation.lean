import LeanResearch.RepulsiveCoulomb.DbarBranchVolumeTestPairing
import LeanResearch.RepulsiveCoulomb.DbarBranchMollifierRepresentation
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual Lebesgue-L2 convolution by an arbitrary smooth compact real
kernel, including signed directional derivatives of mollifiers. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace TopologicalSpace
open scoped Topology Distributions Convolution
namespace RepulsiveCoulomb

def dbarVolumeKernelLp {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  ∫ y, ψ y • Measure.translateLp volume 2 (-y) f


theorem dbarVolumeKernelLp_integrable {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Integrable (fun y => ψ y • Measure.translateLp volume 2 (-y) f) volume := by
  have hc : Continuous (fun y : CoulombConfig N =>
      ψ y • Measure.translateLp volume 2 (-y) f) :=
    ψ.continuous.smul
      ((Measure.continuous_translateLp (mu := volume) (p := 2) (by norm_num) f).comp continuous_neg)
  exact hc.integrable_of_hasCompactSupport ψ.hasCompactSupport.smul_right

theorem dbarVolumeKernelLp_test_integral {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) :
    coulombVolumeTestPairingL φ (dbarVolumeKernelLp ψ f) =
      ∫ y, ψ y • coulombVolumeTestPairingL φ (Measure.translateLp volume 2 (-y) f) := by
  rw [dbarVolumeKernelLp]
  rw [← (coulombVolumeTestPairingL φ).integral_comp_comm (dbarVolumeKernelLp_integrable ψ f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => map_smul (coulombVolumeTestPairingL φ) (ψ y) _

theorem dbarVolumeKernelLp_scalar_test {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hf : Integrable (f : CoulombConfig N → ℂ) volume)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) :
    coulombVolumeTestPairingL φ (dbarVolumeKernelLp ψ f) =
      ∫ x, φ x • (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : CoulombConfig N → ℂ)) x := by
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hψ : Integrable (ψ) volume :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hj := (hψ.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf).bdd_smul C
    (φ.continuous.comp continuous_fst).aestronglyMeasurable
    (Eventually.of_forall fun p : CoulombConfig N × CoulombConfig N => hC p.1)
  have hs := integral_integral_swap
    (f := fun x y : CoulombConfig N => φ x • (ψ y • f (x - y))) hj
  calc
    _ = ∫ y, ∫ x, φ x • (ψ y • f (x - y)) := by
      rw [dbarVolumeKernelLp_test_integral]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [coulombVolumeTestPairingL_translate, ← integral_smul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [sub_eq_add_neg]
          exact smul_comm _ _ _
    _ = ∫ x, ∫ y, φ x • (ψ y • f (x - y)) := hs.symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (∫ y, φ x • (ψ y • f (x - y))) =
          φ x • (∫ y, ψ y • f (x - y))
        exact integral_smul _ _

theorem dbarVolumeKernelLp_coe {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hf : Integrable (f : CoulombConfig N → ℂ) volume) :
    dbarVolumeKernelLp ψ f =ᵐ[volume]
      ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : CoulombConfig N → ℂ) := by
  let v : CoulombConfig N → ℂ := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    (f : CoulombConfig N → ℂ)
  have hmloc : LocallyIntegrableOn (dbarVolumeKernelLp ψ f : CoulombConfig N → ℂ)
      (⊤ : Opens (CoulombConfig N)) volume :=
    ((Lp.memLp (dbarVolumeKernelLp ψ f)).locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hvcont : ContDiff ℝ (⊤ : ℕ∞) v :=
    ψ.hasCompactSupport.contDiff_convolution_left (μ := volume) (n := (⊤ : ℕ∞)) (ContinuousLinearMap.lsmul ℝ ℝ)
      ψ.contDiff hf.locallyIntegrable
  have hvloc : LocallyIntegrableOn v (⊤ : Opens (CoulombConfig N)) volume :=
    hvcont.continuous.locallyIntegrable.locallyIntegrableOn _
  have he : Distribution.ofFun (⊤ : Opens (CoulombConfig N)) (dbarVolumeKernelLp ψ f) volume ⊤ =
      Distribution.ofFun (⊤ : Opens (CoulombConfig N)) v volume ⊤ := by
    ext φ
    rw [Distribution.ofFun_apply hmloc, Distribution.ofFun_apply hvloc,
      ← coulombVolumeTestPairingL_apply]
    exact dbarVolumeKernelLp_scalar_test ψ f hf φ
  have h := Distribution.ofFun_injective hmloc hvloc he
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

end RepulsiveCoulomb
