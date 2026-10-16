module

public import LeanResearch.RepulsiveCoulomb.DbarBranchVolumeTestPairing
public import LeanResearch.RepulsiveCoulomb.DbarBranchLocalMollifier
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Identify the actual Bochner L2 mollifier with the scalar convolution by
continuous test pairings and Fubini. This avoids point evaluation on L2. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace TopologicalSpace
open scoped Topology Distributions Convolution
namespace RepulsiveCoulomb

theorem coulombVolumeLpMollify_integrable {N : ℕ}
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Integrable (fun y => ψ.normed volume y • Measure.translateLp volume 2 (-y) f) volume := by
  have hc : Continuous (fun y : CoulombConfig N =>
      ψ.normed volume y • Measure.translateLp volume 2 (-y) f) :=
    (ψ.continuous_normed (μ := volume)).smul
      ((Measure.continuous_translateLp (mu := volume) (p := 2) (by norm_num) f).comp continuous_neg)
  exact hc.integrable_of_hasCompactSupport (ψ.hasCompactSupport_normed (μ := volume)).smul_right

theorem coulombVolumeLpMollify_test_integral {N : ℕ}
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) :
    coulombVolumeTestPairingL φ (coulombVolumeLpMollify ψ f) =
      ∫ y, ψ.normed volume y • coulombVolumeTestPairingL φ (Measure.translateLp volume 2 (-y) f) := by
  rw [coulombVolumeLpMollify, convolution_def]
  change coulombVolumeTestPairingL φ (∫ y, ψ.normed volume y • Measure.translateLp volume 2 (0 - y) f) = _
  simp only [zero_sub]
  rw [← (coulombVolumeTestPairingL φ).integral_comp_comm (coulombVolumeLpMollify_integrable ψ f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => map_smul (coulombVolumeTestPairingL φ) (ψ.normed volume y) _

theorem coulombVolumeLpMollify_scalar_test {N : ℕ}
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hf : Integrable (f : CoulombConfig N → ℂ) volume)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) :
    coulombVolumeTestPairingL φ (coulombVolumeLpMollify ψ f) =
      ∫ x, φ x • (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : CoulombConfig N → ℂ)) x := by
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hψ : Integrable (ψ.normed volume) volume :=
    (ψ.continuous_normed (μ := volume)).integrable_of_hasCompactSupport (ψ.hasCompactSupport_normed (μ := volume))
  have hj := (hψ.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf).bdd_smul C
    (φ.continuous.comp continuous_fst).aestronglyMeasurable
    (Eventually.of_forall fun p : CoulombConfig N × CoulombConfig N => hC p.1)
  have hs := integral_integral_swap
    (f := fun x y : CoulombConfig N => φ x • (ψ.normed volume y • f (x - y))) hj
  calc
    _ = ∫ y, ∫ x, φ x • (ψ.normed volume y • f (x - y)) := by
      rw [coulombVolumeLpMollify_test_integral]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [coulombVolumeTestPairingL_translate, ← integral_smul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [sub_eq_add_neg]
          exact smul_comm _ _ _
    _ = ∫ x, ∫ y, φ x • (ψ.normed volume y • f (x - y)) := hs.symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (∫ y, φ x • (ψ.normed volume y • f (x - y))) =
          φ x • (∫ y, ψ.normed volume y • f (x - y))
        exact integral_smul _ _

theorem coulombVolumeLpMollify_coe {N : ℕ}
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hf : Integrable (f : CoulombConfig N → ℂ) volume) :
    coulombVolumeLpMollify ψ f =ᵐ[volume]
      ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : CoulombConfig N → ℂ) := by
  let v : CoulombConfig N → ℂ := ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    (f : CoulombConfig N → ℂ)
  have hmloc : LocallyIntegrableOn (coulombVolumeLpMollify ψ f : CoulombConfig N → ℂ)
      (⊤ : Opens (CoulombConfig N)) volume :=
    ((Lp.memLp (coulombVolumeLpMollify ψ f)).locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hvcont : ContDiff ℝ (⊤ : ℕ∞) v :=
    (ψ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left (n := (⊤ : ℕ∞)) (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ.contDiff_normed (μ := volume)) hf.locallyIntegrable
  have hvloc : LocallyIntegrableOn v (⊤ : Opens (CoulombConfig N)) volume :=
    hvcont.continuous.locallyIntegrable.locallyIntegrableOn _
  have he : Distribution.ofFun (⊤ : Opens (CoulombConfig N)) (coulombVolumeLpMollify ψ f) volume ⊤ =
      Distribution.ofFun (⊤ : Opens (CoulombConfig N)) v volume ⊤ := by
    ext φ
    rw [Distribution.ofFun_apply hmloc, Distribution.ofFun_apply hvloc,
      ← coulombVolumeTestPairingL_apply]
    exact coulombVolumeLpMollify_scalar_test ψ f hf φ
  have h := Distribution.ofFun_injective hmloc hvloc he
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

theorem coulombScalarMollify_lp_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (coulombMeasure N β)) :
    coulombVolumeLpMollify ψ (coulombL2LocalizeVolume hβ hK hKΩ f) =ᵐ[volume] coulombScalarMollify K ψ f := by
  have hi : Integrable (coulombL2LocalizeVolume hβ hK hKΩ f : CoulombConfig N → ℂ) volume :=
    (coulombL2_indicator_integrable_volume hβ hK hKΩ f).congr
      (coulombL2LocalizeVolume_coe hβ hK hKΩ f).symm
  have hm := coulombVolumeLpMollify_coe ψ (coulombL2LocalizeVolume hβ hK hKΩ f) hi
  have hc := convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (f := ψ.normed volume)
    ae_eq_rfl (coulombL2LocalizeVolume_coe hβ hK hKΩ f)
  exact hm.trans (Eventually.of_forall fun z => congrFun hc z)

theorem coulombScalarMollify_memLp_volume {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (coulombMeasure N β)) :
    MemLp (coulombScalarMollify K ψ f) 2 volume :=
  (Lp.memLp (coulombVolumeLpMollify ψ (coulombL2LocalizeVolume hβ hK hKΩ f))).ae_eq
    (coulombScalarMollify_lp_coe hβ hK hKΩ ψ f)

end RepulsiveCoulomb
