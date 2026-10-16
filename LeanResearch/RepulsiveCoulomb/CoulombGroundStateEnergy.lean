module

public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCrossTerm
public import LeanResearch.RepulsiveCoulomb.CoulombCutoffRellich

@[expose] public section

/-! Literal normalized ground-state energy identity for the full particle
core, with every term genuinely integrable. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombPotential_gradient_continuousOn {N : ℕ} (β : ℝ) :
    ContinuousOn (gradient (coulombPotential (N := N) β)) (coulombDomain N) := by
  intro z hz
  have hc := (coulombPotential_contDiffAt β hz).continuousAt_fderiv (by simp)
  exact ((InnerProductSpace.toDual ℝ (CoulombConfig N)).symm.continuous.continuousAt.comp hc).continuousWithinAt

theorem coulombCore_potential_energy_integrable {N : ℕ} (β : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Integrable (fun z : CoulombConfig N => ‖gradient (coulombPotential β) z‖ ^ 2 * φ z ^ 2) := by
  have hi : LocallyIntegrableOn (fun z : CoulombConfig N => ‖gradient (coulombPotential β) z‖ ^ 2)
      (coulombDomain N) volume :=
    ((coulombPotential_gradient_continuousOn (N := N) β).norm.pow 2).locallyIntegrableOn
      (coulombDomain N).isOpen.measurableSet
  have h := TauCeti.integrable_smul_of_locallyIntegrableOn hi (coulombCoreSquare φ)
  simpa only [coulombCoreSquare_apply, smul_eq_mul, mul_comm] using h

theorem coulombMeasure_integral_density_of_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig N → ℝ) (_hf : Integrable f (coulombMeasure N β)) :
    (∫ x, f x ∂coulombMeasure N β) = ∫ x : CoulombConfig N, coulombDensity N β x * f x := by
  rw [coulombMeasure_eq_withDensity hβ,
    integral_withDensity_eq_integral_toReal_smul
      (coulombDensity_continuous hβ.le).measurable.ennreal_ofReal (by simp)]
  congr 1
  funext z
  simp only [ENNReal.toReal_ofReal (coulombDensity_nonneg β z), smul_eq_mul]

theorem coulombGroundState_energy_density {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) :
    coulombDensity N β z * ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 =
      ‖gradient (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) z‖ ^ 2 +
      (1 / 4 : ℝ) * (‖gradient (coulombPotential β) z‖ ^ 2 * (coulombGroundStateCore hβ φ z) ^ 2) +
      coulombGroundStateCore hβ φ z * inner ℝ
        (gradient (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) z) (gradient (coulombPotential β) z) := by
  have h := congrArg (fun v : CoulombConfig N => ‖v‖ ^ 2)
    (coulombGroundStateCore_gradient_identity hβ φ z)
  rw [norm_add_sq_real] at h
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (coulombDensity_nonneg β z), inner_smul_right, smul_eq_mul, div_pow] at h
  nlinarith only [h]

theorem coulombGroundState_energy_identity {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ x, ‖gradient (φ : CoulombConfig N → ℝ) x‖ ^ 2 ∂coulombMeasure N β) =
      (∫ x : CoulombConfig N, ‖gradient (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) x‖ ^ 2) +
      (1 / 4 : ℝ) * (∫ x : CoulombConfig N, ‖gradient (coulombPotential β) x‖ ^ 2 *
        (coulombGroundStateCore hβ φ x) ^ 2) -
      (N : ℝ) * β * (∫ x : CoulombConfig N, (coulombGroundStateCore hβ φ x) ^ 2) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  let ψ := coulombGroundStateCore hβ φ
  have hw : Integrable (fun x => ‖gradient (φ : CoulombConfig N → ℝ) x‖ ^ 2)
      (coulombMeasure N β) :=
    (show MemLp (gradient (φ : CoulombConfig N → ℝ)) 2 (coulombMeasure N β) from
      (TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
        (TauCeti.hasCompactSupport_gradient_testFunction φ)).norm.integrable_sq
  have hE := coulomb_testFunction_gradient_square_integrable (coulombDomain N) ψ
  have hS := coulombCore_potential_energy_integrable β ψ
  have hX := coulombCore_potential_cross_integrable β ψ
  calc
    _ = ∫ x : CoulombConfig N, coulombDensity N β x * ‖gradient (φ : CoulombConfig N → ℝ) x‖ ^ 2 :=
      coulombMeasure_integral_density_of_integrable hβ _ hw
    _ = ∫ x : CoulombConfig N, (‖gradient (ψ : CoulombConfig N → ℝ) x‖ ^ 2 +
        (1 / 4 : ℝ) * (‖gradient (coulombPotential β) x‖ ^ 2 * ψ x ^ 2)) +
        ψ x * inner ℝ (gradient (ψ : CoulombConfig N → ℝ) x) (gradient (coulombPotential β) x) :=
      integral_congr_ae (Eventually.of_forall (coulombGroundState_energy_density hβ φ))
    _ = _ := by
      rw [integral_add (by convert! hE.add (hS.const_mul (1 / 4 : ℝ)) using 1) hX,
        integral_add hE (hS.const_mul (1 / 4 : ℝ)), integral_const_mul,
        coulombCore_potential_cross_integral β ψ]
      ring

end RepulsiveCoulomb
