import LeanResearch.RepulsiveCoulomb.CoulombFirstSwap

/-! Integrated first-pair swap estimate for the original labeled core. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology
namespace RepulsiveCoulomb

theorem coulomb_core_pair_gradient_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (i j : Fin N) :
    Integrable (fun z => ‖gradient (φ : CoulombConfig N → ℝ) z i -
      gradient (φ : CoulombConfig N → ℝ) z j‖ ^ 2) (coulombMeasure N β) := by
  let _ := coulombMeasure_isProbability (N := N) hβ
  have hg : MemLp (fun z => gradient (φ : CoulombConfig N → ℝ) z) 2 (coulombMeasure N β) :=
    (TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
      (TauCeti.hasCompactSupport_gradient_testFunction φ)
  exact ((hg.continuousLinearMap_comp (coulombCoordinate i)).sub
    (hg.continuousLinearMap_comp (coulombCoordinate j))).norm.integrable_sq

theorem coulomb_core_first_swap_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) :
    Integrable (fun z => (φ z - φ (coulombSwapFirst N z)) ^ 2) (coulombMeasure (N + 2) β) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  have hf : MemLp (φ : CoulombConfig (N + 2) → ℝ) 2 (coulombMeasure (N + 2) β) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.exists_bound_of_continuousOn φ.continuous.continuousOn
  have hb (z : CoulombConfig (N + 2)) : ‖φ z‖ ≤ |M| + 1 := by
    by_cases hz : z ∈ tsupport (φ : CoulombConfig (N + 2) → ℝ)
    · exact (hM z hz).trans (by linarith [le_abs_self M])
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      positivity
  have hs : MemLp (fun z => φ (coulombSwapFirst N z)) 2 (coulombMeasure (N + 2) β) :=
    MemLp.of_bound (φ.continuous.comp (coulombSwapFirst_continuous N)).aestronglyMeasurable
      (|M| + 1) (Eventually.of_forall (fun z => hb (coulombSwapFirst N z)))
  exact (hf.sub hs).integrable_sq

theorem coulomb_core_first_swap_bound {β : ℝ} (hβ : 0 < β) :
    ∃ P : ℝ, 0 < P ∧ ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
      (∫ z, (φ z - φ (coulombSwapFirst N z)) ^ 2 ∂coulombMeasure (N + 2) β) ≤
        (2 * P) * (∫ z, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z 0 -
          gradient (φ : CoulombConfig (N + 2) → ℝ) z (Fin.succ 0)‖ ^ 2
            ∂coulombMeasure (N + 2) β) := by
  obtain ⟨P, hP, hp⟩ := coulomb_relative_core_swap_bound hβ
  refine ⟨P, hP, ?_⟩
  intro N φ
  have hF := coulomb_core_first_swap_integrable hβ φ
  have hG := coulomb_core_pair_gradient_integrable hβ φ 0 (Fin.succ 0)
  have hFo := (coulomb_relative_slice_integrability hβ hF).2
  have hGo := (coulomb_relative_slice_integrability hβ hG).2
  simp only [abs_sq] at hFo hGo
  rw [coulomb_relative_integral_tower hβ hF, coulomb_relative_integral_tower hβ hG,
    ← integral_const_mul]
  apply integral_mono hFo (hGo.const_mul (2 * P))
  intro p
  simpa only [coulombSwapFirst_relative] using hp N p.1 p.2 φ

end RepulsiveCoulomb

