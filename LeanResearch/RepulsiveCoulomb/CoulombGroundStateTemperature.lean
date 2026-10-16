module

public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateInverseCore
public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateEnergy
public import LeanResearch.RepulsiveCoulomb.CoulombPotentialGradient

@[expose] public section

/-! Exact fixed-core temperature comparison for normalized ground states.
All integrals here have compact collision-free support. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombPotential_gradient_temperature {N : ℕ} (β : ℝ)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    gradient (coulombPotential β) z = β • gradient (coulombPotential (1 : ℝ)) z := by
  rw [coulombPotential_gradient β hz, coulombPotential_gradient 1 hz,
    smul_sub, one_smul, smul_smul]
  congr 1
  congr 1
  ring

theorem coulombCore_potential_energy_temperature {N : ℕ} (β : ℝ)
    (ψ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z : CoulombConfig N, ‖gradient (coulombPotential β) z‖ ^ 2 * ψ z ^ 2) =
      β ^ 2 * (∫ z : CoulombConfig N, ‖gradient (coulombPotential (1 : ℝ)) z‖ ^ 2 * ψ z ^ 2) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    by_cases hz : z ∈ coulombDomain N
    · rw [coulombPotential_gradient_temperature β hz]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    · have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hz (ψ.tsupport_subset ht))
      simp [hzero]

theorem coulombInverseGroundState_energy_identity {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z, ‖gradient (coulombInverseGroundStateCore hβ ψ : CoulombConfig N → ℝ) z‖ ^ 2
      ∂coulombMeasure N β) =
      (∫ z : CoulombConfig N, ‖gradient (ψ : CoulombConfig N → ℝ) z‖ ^ 2) +
      (β ^ 2 / 4) * (∫ z : CoulombConfig N,
        ‖gradient (coulombPotential (1 : ℝ)) z‖ ^ 2 * ψ z ^ 2) -
      (N : ℝ) * β * (∫ z : CoulombConfig N, ψ z ^ 2) := by
  rw [coulombGroundState_energy_identity hβ, coulombGroundState_inverse_core,
    coulombCore_potential_energy_temperature]
  ring

theorem coulombInverseGroundState_energy_comparison {N : ℕ} {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (ψ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z, ‖gradient (coulombInverseGroundStateCore hβ ψ : CoulombConfig N → ℝ) z‖ ^ 2
      ∂coulombMeasure N β) =
    (∫ z, ‖gradient (coulombInverseGroundStateCore hγ ψ : CoulombConfig N → ℝ) z‖ ^ 2
      ∂coulombMeasure N γ) +
      ((β ^ 2 - γ ^ 2) / 4) * (∫ z : CoulombConfig N,
        ‖gradient (coulombPotential (1 : ℝ)) z‖ ^ 2 * ψ z ^ 2) -
      (N : ℝ) * (β - γ) * (∫ z : CoulombConfig N, ψ z ^ 2) := by
  rw [coulombInverseGroundState_energy_identity hβ,
    coulombInverseGroundState_energy_identity hγ]
  ring

theorem coulombInverseGroundState_drift_energy_bound {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (ψ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z : CoulombConfig N, ‖gradient (coulombPotential (1 : ℝ)) z‖ ^ 2 * ψ z ^ 2) ≤
      4 * ((∫ z, ‖gradient (coulombInverseGroundStateCore hβ ψ : CoulombConfig N → ℝ) z‖ ^ 2
        ∂coulombMeasure N β) + (N : ℝ) * β * (∫ z : CoulombConfig N, ψ z ^ 2)) / β ^ 2 := by
  have hE := coulombInverseGroundState_energy_identity hβ ψ
  have hG : 0 ≤ ∫ z : CoulombConfig N, ‖gradient (ψ : CoulombConfig N → ℝ) z‖ ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
  nlinarith only [hE, hG]

end RepulsiveCoulomb
