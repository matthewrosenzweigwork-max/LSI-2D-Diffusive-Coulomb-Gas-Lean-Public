import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeAmbientLift
import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativePositiveEntropy

/-! Good-center slice selection, with actual Fubini integrability and
contractive physical-jet projection. No regularity of a parameter integral,
minimum attainment, or analytic domain correspondence is assumed. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace RepulsiveCoulomb

variable {n : ℕ}

def coulombCenterRelativeSliceError (e : CoulombCenterRotation n)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig n)) ℝ ⊤)
    (p : ℂ × CoulombConfig n) : ℝ :=
  ‖coulombCenterRelativeJetProject e (WithLp.toLp 2
      (φ (coulombCenterInsert e p.1 p.2),
        gradient (φ : CoulombConfig (n + 1) → ℝ) (coulombCenterInsert e p.1 p.2))) -
    WithLp.toLp 2 (ψ p.2, gradient (ψ : CoulombConfig n → ℝ) p.2)‖ ^ 2

theorem coulombCenterRelativeSliceError_measurable (e : CoulombCenterRotation n)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig n)) ℝ ⊤) :
    Measurable (coulombCenterRelativeSliceError e φ ψ) := by
  have hφ : Measurable (fun z => WithLp.toLp 2
      (φ z, gradient (φ : CoulombConfig (n + 1) → ℝ) z)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (CoulombConfig (n + 1))).symm.continuous.measurable.comp
      (φ.continuous.measurable.prodMk (TauCeti.continuous_gradient_testFunction φ).measurable)
  have hψ : Measurable (fun r => WithLp.toLp 2
      (ψ r, gradient (ψ : CoulombConfig n → ℝ) r)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (CoulombConfig n)).symm.continuous.measurable.comp
      (ψ.continuous.measurable.prodMk (TauCeti.continuous_gradient_testFunction ψ).measurable)
  have hi : Measurable (fun p : ℂ × CoulombConfig n => coulombCenterInsert e p.1 p.2) := by
    rw [← coulombCenterChart_symm_function]
    exact (coulombCenterChart e).symm.measurable
  exact (((coulombCenterRelativeJetProject e).measurable.comp (hφ.comp hi)).sub
    (hψ.comp measurable_snd)).norm.pow_const 2

theorem coulombCenterRelativeSliceError_integral (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig n)) ℝ ⊤) :
    Integrable (coulombCenterRelativeSliceError e φ ψ)
      ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β)) ∧
    (∫ p, coulombCenterRelativeSliceError e φ ψ p
      ∂(coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β)) ≤
      ‖coulombCoreJet hβ φ - coulombCenterRelativeJetLiftL e he hβ
        (coulombCenterRelativeAmbientJet e he hβ ψ)‖ ^ 2 := by
  letI := coulombCenterGaussian_isProbability hβ
  letI := coulombCenterRelativeMeasure_isProbability e he hβ
  let J := coulombCenterRelativeAmbientJet e he hβ ψ
  let K := coulombCoreJet hβ φ - coulombCenterRelativeJetLiftL e he hβ J
  have hm := (coulombCenter_gibbsMeasurePreserving e he hβ).symm
  have hKi : Integrable (fun p => ‖K ((coulombCenterChart e).symm p)‖ ^ 2)
      ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β)) :=
    hm.integrable_comp_of_integrable (Lp.memLp K).norm.integrable_sq
  have hc := hm.quasiMeasurePreserving.ae (coulombCoreJet_coe hβ φ)
  have hl := hm.quasiMeasurePreserving.ae (coulombCenterRelativeJetLiftL_coe e he hβ J)
  have hk := hm.quasiMeasurePreserving.ae
    (Lp.coeFn_sub (coulombCoreJet hβ φ) (coulombCenterRelativeJetLiftL e he hβ J))
  have hj := (measurePreserving_snd (μ := coulombCenterGaussian β)
    (ν := coulombCenterRelativeMeasure e β)).quasiMeasurePreserving.ae
      (coulombCenterRelativeAmbientJet_coe e he hβ ψ)
  have hle : ∀ᵐ p ∂(coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β),
      coulombCenterRelativeSliceError e φ ψ p ≤ ‖K ((coulombCenterChart e).symm p)‖ ^ 2 := by
    filter_upwards [hc, hl, hk, hj] with p hc hl hk hj
    rw [coulombCenterChart_symm_apply] at hc hl hk ⊢
    dsimp only [Pi.sub_apply] at hk
    rw [coulombCenterRelativeProjection_insert] at hl
    change J p.2 = _ at hj
    rw [hl, hj, hc] at hk
    change K (coulombCenterInsert e p.1 p.2) = _ at hk
    rw [hk]
    have h := coulombCenterRelativeJetProjectLinear_norm_le e
      (WithLp.toLp 2 (φ (coulombCenterInsert e p.1 p.2),
        gradient (φ : CoulombConfig (n + 1) → ℝ) (coulombCenterInsert e p.1 p.2)) -
          coulombCenterRelativeJetFiber e (WithLp.toLp 2
            (ψ p.2, gradient (ψ : CoulombConfig n → ℝ) p.2)))
    change ‖coulombCenterRelativeJetProject e _‖ ≤ _ at h
    rw [map_sub, coulombCenterRelativeJetProject_fiber] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hHi : Integrable (coulombCenterRelativeSliceError e φ ψ)
      ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β)) := by
    apply hKi.mono' (coulombCenterRelativeSliceError_measurable e φ ψ).aestronglyMeasurable
    filter_upwards [hle] with p hp
    have h0 : 0 ≤ coulombCenterRelativeSliceError e φ ψ p := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hp
  refine ⟨hHi, ?_⟩
  calc
    _ ≤ ∫ p, ‖K ((coulombCenterChart e).symm p)‖ ^ 2
        ∂(coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β) := integral_mono_ae hHi hKi hle
    _ = ∫ z, ‖K z‖ ^ 2 ∂coulombMeasure (n + 1) β :=
      hm.integral_comp' (fun z => ‖K z‖ ^ 2)
    _ = ‖K‖ ^ 2 := (coulombCenter_L2_norm_sq K).symm

theorem coulombCenterRelativeSliceError_norm_sq (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig n)) ℝ ⊤) (c : ℂ) :
    ‖coulombCenterRelativeCoreJet e he hβ (coulombCenterRelativeCore e he φ c) -
      coulombCenterRelativeAmbientJet e he hβ ψ‖ ^ 2 =
      ∫ r, coulombCenterRelativeSliceError e φ ψ (c, r) ∂coulombCenterRelativeMeasure e β := by
  rw [coulombCenter_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (coulombCenterRelativeCoreJet e he hβ
      (coulombCenterRelativeCore e he φ c)) (coulombCenterRelativeAmbientJet e he hβ ψ),
    coulombCenterRelativeCoreJet_coe e he hβ (coulombCenterRelativeCore e he φ c),
    coulombCenterRelativeAmbientJet_coe e he hβ ψ] with r hsub hc ha
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hc, ha]
  simp only [coulombCenterRelativeCore_apply, coulombCenterRelativeCore_gradient,
    coulombCenterRelativeSliceError, coulombCenterRelativeJetProject_apply,
    WithLp.toLp_fst, WithLp.toLp_snd, coulombCenterRelativeProjection_apply]

/-- A real center slice with no worse jet error than the whole-space error.
`exists_le_integral` is used, so no minimum attainment is assumed. -/
theorem coulombCenterRelative_exists_good_slice (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig n)) ℝ ⊤) :
    ∃ c : ℂ, ‖coulombCenterRelativeCoreJet e he hβ (coulombCenterRelativeCore e he φ c) -
      coulombCenterRelativeAmbientJet e he hβ ψ‖ ≤
      ‖coulombCoreJet hβ φ - coulombCenterRelativeJetLiftL e he hβ
        (coulombCenterRelativeAmbientJet e he hβ ψ)‖ := by
  letI := coulombCenterGaussian_isProbability hβ
  letI := coulombCenterRelativeMeasure_isProbability e he hβ
  obtain ⟨hi, hb⟩ := coulombCenterRelativeSliceError_integral e he hβ φ ψ
  obtain ⟨c, hc⟩ := exists_le_integral hi.integral_prod_left
  rw [← integral_prod _ hi] at hc
  have hs := hc.trans hb
  rw [← coulombCenterRelativeSliceError_norm_sq e he hβ φ ψ c] at hs
  refine ⟨c, ?_⟩
  nlinarith [norm_nonneg (coulombCenterRelativeCoreJet e he hβ (coulombCenterRelativeCore e he φ c) -
    coulombCenterRelativeAmbientJet e he hβ ψ),
    norm_nonneg (coulombCoreJet hβ φ - coulombCenterRelativeJetLiftL e he hβ
      (coulombCenterRelativeAmbientJet e he hβ ψ))]

end RepulsiveCoulomb
