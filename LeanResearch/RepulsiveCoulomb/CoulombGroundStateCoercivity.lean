import LeanResearch.RepulsiveCoulomb.CoulombGroundStateEnergy
import LeanResearch.RepulsiveCoulomb.CoulombPotentialGradient

/-! Explicit fixed-particle ground-state coercivity on the original core.
The closed-domain and compact-temperature consequences are separate steps. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

def coulombGroundStateShift (N : ℕ) (β : ℝ) : ℝ :=
  (N : ℝ) * β + β * (β / (N : ℝ)) * ((coulombPairs N).card : ℝ) / 2

theorem coulombGroundStateShift_nonneg (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ coulombGroundStateShift N β := by
  unfold coulombGroundStateShift
  positivity

theorem coulombCore_quadratic_moment_integrable {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Integrable (fun z : CoulombConfig N => ‖z‖ ^ 2 * φ z ^ 2) := by
  have hs : HasCompactSupport (fun z : CoulombConfig N => ‖z‖ ^ 2 * φ z ^ 2) :=
    (φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_left
  exact ((continuous_norm.pow 2).mul (φ.continuous.pow 2)).integrable_of_hasCompactSupport hs

theorem coulombGroundState_mass_identity {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z : CoulombConfig N, (coulombGroundStateCore hβ φ z) ^ 2) =
      ∫ z, φ z ^ 2 ∂coulombMeasure N β := by
  letI := coulombMeasure_isProbability (N := N) hβ
  have hi : Integrable (fun z : CoulombConfig N => φ z ^ 2) (coulombMeasure N β) :=
    (show MemLp (φ : CoulombConfig N → ℝ) 2 (coulombMeasure N β) from
      φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).integrable_sq
  rw [coulombMeasure_integral_density_of_integrable hβ _ hi]
  exact integral_congr_ae (Eventually.of_forall (coulombGroundStateCore_sq hβ φ))

theorem coulombGroundState_core_coercivity {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z : CoulombConfig N, ‖gradient (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) z‖ ^ 2) +
      (β ^ 2 / 4) * (∫ z : CoulombConfig N, ‖z‖ ^ 2 * (coulombGroundStateCore hβ φ z) ^ 2) +
      (∫ z : CoulombConfig N, (coulombGroundStateCore hβ φ z) ^ 2) ≤
    (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) +
      (coulombGroundStateShift N β + 1) * (∫ z, φ z ^ 2 ∂coulombMeasure N β) := by
  let ψ := coulombGroundStateCore hβ φ
  let D := 2 * β * (β / (N : ℝ)) * ((coulombPairs N).card : ℝ)
  have hm := coulombCore_quadratic_moment_integrable ψ
  have hmass := coulomb_testFunction_square_integrable (coulombDomain N) ψ
  have hS := coulombCore_potential_energy_integrable β ψ
  have hp (z : CoulombConfig N) :
      β ^ 2 * (‖z‖ ^ 2 * ψ z ^ 2) - D * ψ z ^ 2 ≤
        ‖gradient (coulombPotential β) z‖ ^ 2 * ψ z ^ 2 := by
    by_cases hz : z ∈ coulombDomain N
    · calc
        _ = (β ^ 2 * ‖z‖ ^ 2 - D) * ψ z ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (coulombPotential_gradient_sq_lower β hz) (sq_nonneg _)
    · have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hz (ψ.tsupport_subset ht))
      simp [hzero]
  have hb := integral_mono ((hm.const_mul (β ^ 2)).sub (hmass.const_mul D)) hS hp
  simp only [Pi.sub_apply] at hb
  rw [integral_sub (hm.const_mul (β ^ 2)) (hmass.const_mul D), integral_const_mul,
    integral_const_mul] at hb
  have he := coulombGroundState_energy_identity hβ φ
  have hmassEq := coulombGroundState_mass_identity hβ φ
  change _ ≤ (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) +
    (coulombGroundStateShift N β + 1) * (∫ z, φ z ^ 2 ∂coulombMeasure N β)
  rw [he, ← hmassEq]
  dsimp only [ψ, D, coulombGroundStateShift] at hb ⊢
  nlinarith only [hb]

end RepulsiveCoulomb
