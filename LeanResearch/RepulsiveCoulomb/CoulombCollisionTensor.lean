module

public import LeanResearch.RepulsiveCoulomb.CoulombCollisionCutoff

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RepulsiveCoulomb

def coulombFrozenGaussian (N : ℕ) (β : ℝ) (p : ℂ × CoulombConfig N) : ℝ :=
  Real.exp (-(β / 4) * ‖p.1‖ ^ 2) * Real.exp (-(β / 4) * ‖p.2‖ ^ 2)

theorem coulombFrozenGaussian_nonneg (N : ℕ) (β : ℝ) (p : ℂ × CoulombConfig N) :
    0 ≤ coulombFrozenGaussian N β p := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

theorem coulombFrozenGaussian_integrable (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (coulombFrozenGaussian N β) := by
  rw [Measure.volume_eq_prod ℂ (CoulombConfig N)]
  exact (integrable_planar_gaussian (by positivity : 0 < β / 4)).mul_prod
    (integrable_coulomb_gaussian N (by positivity : 0 < β / 4))

theorem coulombDensity_relative_le_power (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℂ × CoulombConfig N) (u : ℂ),
      coulombDensity (N + 2) β (coulombRelativeInsert p.1 u p.2) ≤
        C * coulombFrozenGaussian N β p * ‖u‖ ^ (β / ((N + 2 : ℕ) : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := coulombDensity_le_gaussian_collision_power hβ
    (0, (Fin.succ 0 : Fin (N + 2))) ((mem_coulombPairs _).mpr (Fin.succ_pos _))
  let α := β / ((N + 2 : ℕ) : ℝ)
  refine ⟨C * (Real.sqrt 2) ^ α, mul_pos hC (Real.rpow_pos_of_pos (Real.sqrt_pos.2 (by norm_num)) _), ?_⟩
  intro p u
  have h := hb (coulombRelativeInsert p.1 u p.2)
  rw [coulombRelativeInsert_norm_sq, coulombRelative_pair_difference,
    norm_real_smul_rpow _ _ (Real.sqrt_nonneg 2)] at h
  have he : Real.exp (-(β / 4) * (‖p.1‖ ^ 2 + (‖u‖ ^ 2 + ‖p.2‖ ^ 2))) ≤
      coulombFrozenGaussian N β p := by
    unfold coulombFrozenGaussian
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖u‖]
  calc
    _ ≤ _ := h
    _ ≤ C * coulombFrozenGaussian N β p * ((Real.sqrt 2) ^ α * ‖u‖ ^ α) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le) (by positivity)
    _ = _ := by ring

theorem coulombFirstCollisionBump_energy_pullback (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ z, ‖gradient (coulombFirstCollisionBump N ε hε) z‖ ^ 2 ∂coulombMeasure (N + 2) β) =
      ∫ q : (ℂ × CoulombConfig N) × ℂ,
        coulombDensity (N + 2) β (coulombRelativeInsert q.1.1 q.2 q.1.2) *
          ‖gradient (pointCutoffBump 0 ε hε) q.2‖ ^ 2 := by
  rw [coulombFirstCollisionBump_energy_density_integral N hβ]
  have hm := (coulombRelativeFrozenFirst_measurePreserving N).symm
  have he := hm.integral_comp' (fun z => coulombDensity (N + 2) β z *
    ‖gradient (coulombFirstCollisionBump N ε hε) z‖ ^ 2)
  have heq (q : (ℂ × CoulombConfig N) × ℂ) :
      (coulombRelativeFrozenFirst N).symm q = coulombRelativeInsert q.1.1 q.2 q.1.2 :=
    coulombRelativeFrozenFirst_symm_apply q.1 q.2
  simpa only [heq, coulombFirstCollisionBump_gradient_norm,
    coulombRelativeProjection_insert] using he.symm

end RepulsiveCoulomb

