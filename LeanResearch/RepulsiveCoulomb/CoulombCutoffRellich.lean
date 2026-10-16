module

public import LeanResearch.RepulsiveCoulomb.CoulombCutoffEnergy
public import LeanResearch.RepulsiveCoulomb.EuclideanRellichApplications

@[expose] public section

/-! A genuine localized Rellich bound for the original physical core.
Global compactness still requires uniform control of the excluded regions. -/
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
namespace RepulsiveCoulomb

theorem coulomb_testFunction_square_integrable {N : ℕ} (U : Opens (CoulombConfig N))
    (φ : TestFunction U ℝ ⊤) : Integrable (fun z => φ z ^ 2) volume :=
  (show MemLp (φ : CoulombConfig N → ℝ) 2 volume from
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).integrable_sq

theorem coulomb_testFunction_gradient_square_integrable {N : ℕ} (U : Opens (CoulombConfig N))
    (φ : TestFunction U ℝ ⊤) : Integrable (fun z => ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2) volume :=
  (show MemLp (gradient (φ : CoulombConfig N → ℝ)) 2 volume from
    (TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
      (TauCeti.hasCompactSupport_gradient_testFunction φ)).norm.integrable_sq

theorem coulombCore_local_h1_bound {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : TestFunction (coulombDomain N) ℝ ⊤,
      (∫ z in K, φ z ^ 2) + (∫ z in K, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2) ≤
        C * ‖coulombFormCore hβ φ‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := coulombForm_local_h1_bound hβ hK havoid
  refine ⟨C, hC, ?_⟩
  intro φ
  have h := hb (coulombFormCore hβ φ)
  have hv : (fun z => coulombFormValueL N hβ (coulombFormCore hβ φ) z ^ 2)
      =ᵐ[volume.restrict K] (fun z => φ z ^ 2) :=
    (ae_restrict_of_ae ((coulombMeasure_ae_iff hβ).mp (coulombFormCore_value hβ φ))).mono
      (fun z hz => congrArg (fun x : ℝ => x ^ 2) hz)
  have hg : (fun z => ‖coulombFormGradientL N hβ (coulombFormCore hβ φ) z‖ ^ 2)
      =ᵐ[volume.restrict K] (fun z => ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2) :=
    (ae_restrict_of_ae ((coulombMeasure_ae_iff hβ).mp (coulombFormCore_gradient hβ φ))).mono
      (fun z hz => congrArg (fun x : CoulombConfig N => ‖x‖ ^ 2) hz)
  rw [integral_congr_ae hv, integral_congr_ae hg] at h
  exact h

theorem coulombLocalizedCore_h1_integral_bound {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (η : TestFunction (coulombDomain N) ℝ ⊤) (U : Opens (CoulombConfig N))
    (hηU : tsupport (η : CoulombConfig N → ℝ) ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : TestFunction (coulombDomain N) ℝ ⊤,
      (∫ z in U, (coulombLocalizedCore η U hηU φ z) ^ 2) +
        (∫ z in U, ‖gradient (coulombLocalizedCore η U hηU φ : CoulombConfig N → ℝ) z‖ ^ 2) ≤
          C * ‖coulombFormCore hβ φ‖ ^ 2 := by
  obtain ⟨C, hC, hlocal⟩ := coulombCore_local_h1_bound hβ η.hasCompactSupport η.tsupport_subset
  obtain ⟨B, hB, hbound⟩ := coulomb_testFunction_c1_bound η
  refine ⟨3 * B ^ 2 * C, by positivity, ?_⟩
  intro φ
  let K := tsupport (η : CoulombConfig N → ℝ)
  let ψ := coulombLocalizedCore η U hηU φ
  have hK : MeasurableSet K := (isClosed_tsupport (η : CoulombConfig N → ℝ)).measurableSet
  have hv := coulomb_testFunction_square_integrable (coulombDomain N) φ
  have hg := coulomb_testFunction_gradient_square_integrable (coulombDomain N) φ
  have hvψ := coulomb_testFunction_square_integrable U ψ
  have hgψ := coulomb_testFunction_gradient_square_integrable U ψ
  have hi := ((hv.add hg).const_mul (3 * B ^ 2)).indicator hK
  have hp : ∀ z, ψ z ^ 2 + ‖gradient (ψ : CoulombConfig N → ℝ) z‖ ^ 2 ≤
      K.indicator (fun z => 3 * B ^ 2 * (φ z ^ 2 + ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2)) z := by
    intro z
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      exact coulombLocalizedCore_h1_pointwise_bound η U hηU φ hbound z
    · have hval : ψ z = 0 := by
        dsimp only [ψ]
        rw [coulombLocalizedCore_apply, image_eq_zero_of_notMem_tsupport hz, zero_mul]
      have hgrad : gradient (ψ : CoulombConfig N → ℝ) z = 0 :=
        coulombLocalizedCore_gradient_zero_off η U hηU φ hz
      rw [indicator_of_notMem hz, hval, hgrad]
      norm_num
  have hm : (∫ z in U, ψ z ^ 2 + ‖gradient (ψ : CoulombConfig N → ℝ) z‖ ^ 2) ≤
      ∫ z in U, K.indicator (fun z => 3 * B ^ 2 *
        (φ z ^ 2 + ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2)) z :=
    integral_mono (hvψ.add hgψ).restrict hi.restrict hp
  have hUK : (U : Set (CoulombConfig N)) ∩ K = K := inter_eq_right.mpr hηU
  rw [integral_add hvψ.restrict hgψ.restrict, setIntegral_indicator hK, hUK,
    integral_const_mul, integral_add hv.restrict hg.restrict] at hm
  have hlast := mul_le_mul_of_nonneg_left (hlocal φ) (show 0 ≤ 3 * B ^ 2 by positivity)
  apply hm.trans
  simpa only [mul_assoc] using hlast

theorem coulombLocalizedCore_rellich {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (η : TestFunction (coulombDomain N) ℝ ⊤) (U : Opens (CoulombConfig N))
    (hU : Bornology.IsBounded (U : Set (CoulombConfig N)))
    (hηU : tsupport (η : CoulombConfig N → ℝ) ⊆ U) (R : ℝ) :
    IsCompact (closure ((fun φ : TestFunction (coulombDomain N) ℝ ⊤ =>
      TauCeti.testFunctionLp (mu := volume) 2 (coulombLocalizedCore η U hηU φ)) ''
        {φ | ‖coulombFormCore hβ φ‖ ≤ R})) := by
  obtain ⟨C, hC, hb⟩ := coulombLocalizedCore_h1_integral_bound hβ η U hηU
  have hc := euclidean_testFunction_rellich U hU (C * R ^ 2)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨φ, hφ, rfl⟩
  refine ⟨coulombLocalizedCore η U hηU φ, ?_, rfl⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hφ 2
  exact (hb φ).trans (mul_le_mul_of_nonneg_left hs hC.le)

end RepulsiveCoulomb
